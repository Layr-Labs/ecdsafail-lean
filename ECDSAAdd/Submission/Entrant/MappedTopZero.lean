import ECDSAAdd.Submission.Entrant.AdderSpineBridgeDraft
import ECDSAAdd.Arithmetic.MappedAdder
import ECDSAAdd.Arithmetic.PoolLayout
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical

/-! Known-zero top output of a mapped in-place adder whose two highest mapped
source bits read the same wire (`p` and `¬p`). If the old adder's final top
output bit is zero, its last carry `z` equals `Y ⊕ p ⊕ 1` and need not be
computed by a Toffoli: `Y` itself temporarily holds the carry and is erased by
the original measured correction. The measurement count is unchanged. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.MappedTopZero
open Arithmetic RecordedQuantum Challenge AdderSpineBridgeResearch

private theorem cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

/-! ### Exact syntax split of a mapped adder at its top two bits -/

def mPrefix : List MappedBit → List Wire → List Wire → Wire → Program
  | b::bs,y::ys,z::zs,cin => mappedMajority b y cin z++mPrefix bs ys zs z
  | _,_,_,_ => []

def mSuffix : List MappedBit → List Wire → List Wire → Wire → Program
  | b::bs,y::ys,z::zs,cin => mSuffix bs ys zs z++mappedEraseCarry b y cin z++mappedSum b y cin
  | _,_,_,_ => []

/-- The literal two-bit terminal of `mappedAdd`. -/
def mLeaf (b B : MappedBit) (y c Y z : Wire) : Program :=
  mappedMajority b y c z++mappedSum B Y z++mappedEraseCarry b y c z++mappedSum b y c

theorem madd_split (bs : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (b B : MappedBit) (y Y z : Wire)
    (hy : bs.length=ys.length) (hc : bs.length=cs.length) :
    mappedAdd (bs++[b,B]) (ys++[y,Y]) (cs++[z]) cin=
      mPrefix bs ys cs cin++mLeaf b B y (lastCarry cs cin) Y z++mSuffix bs ys cs cin := by
  induction bs generalizing ys cs cin with
  | nil =>
    have ey : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy.symm)
    have ec : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc.symm)
    subst ys; subst cs
    simp only [List.nil_append,mappedAdd,mPrefix,mSuffix,mLeaf,lastCarry,List.append_nil,
      List.append_assoc]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hy
    | cons y0 ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        have hy' : xs.length=ys.length := by simpa using hy
        have hc' : xs.length=cs.length := by simpa using hc
        have step : mappedAdd ((x::xs)++[b,B]) ((y0::ys)++[y,Y]) ((c::cs)++[z]) cin=
            mappedMajority x y0 cin c++mappedAdd (xs++[b,B]) (ys++[y,Y]) (cs++[z]) c++
              mappedEraseCarry x y0 cin c++mappedSum x y0 cin := by
          cases xs <;> cases ys <;> rfl
        rw [step,ih ys cs c hy' hc']
        simp only [mPrefix,mSuffix,lastCarry,List.append_assoc]

/-! ### The specific top leaf: source bits `p` (bit k) and `¬p` (bit k+1) -/

def lowBit (p : Wire) : MappedBit := {wire:=some p,flip:=false}
def highBit (p : Wire) : MappedBit := {wire:=some p,flip:=true}

/-- The old terminal: computes the last carry into `z` with one Toffoli. -/
def oldTop (p y c Y z : Wire) : Program := mLeaf (lowBit p) (highBit p) y c Y z

/-- The replacement: `Y ⊕ p ⊕ 1` already equals the last carry, so `Y` is used
as the measured carry host. No Toffoli; one measurement, as before. -/
def newTop (p y c Y : Wire) : Program :=
  [.X Y,.CX p Y]++eraseCarry p y c Y++[.CX p y,.CX c y]

theorem oldTop_eq (p y c Y z : Wire) :
    oldTop p y c Y z=
      majority p y c z++[.CX p Y,.X Y,.CX z Y]++eraseCarry p y c z++[.CX p y,.CX c y] := by
  simp [oldTop,mLeaf,lowBit,highBit,mappedMajority,mappedSum,mappedEraseCarry]

/-- The old terminal's final top output, as a function of its input bits. -/
def topOut (p y c Y : Wire) (b : BasisState) : Bool :=
  ((b Y^^b p)^^true)^^carryBit (b p) (b y) (b c)

private def postS (p y c Y : Wire) (s : State) : State :=
  ⟨s.phase,writeBit (writeBit s.basis Y false) y ((s.basis y^^s.basis p)^^s.basis c)⟩

theorem old_run (p y c Y z : Wire) (nd : [p,y,c,Y,z].Nodup) (s : State) (m : List Bool)
    (clean : s.basis z=false) (ready : topOut p y c Y s.basis=false) :
    run (oldTop p y c Y z) m s=postS p y c Y s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hpy,hpc,hpY,hpz⟩,⟨hyc,hyY,hyz⟩,⟨hcY,hcz⟩,hYz⟩ := nd
  have nd4 : [p,y,c,z].Nodup := by simp_all
  let K := carryBit (s.basis p) (s.basis y) (s.basis c)
  let s1 : State := ⟨s.phase,writeBit s.basis z K⟩
  let s2 : State := ⟨s.phase,writeBit (writeBit s.basis z K) Y false⟩
  let s3 : State := ⟨s.phase,writeBit s.basis Y false⟩
  have first (tape : List Bool) : run (majority p y c z) tape s=s1 := by
    rw [majority_correct p y c z nd4]
    simp only [s1,K,clean,Bool.false_xor]
  have second (tape : List Bool) : run [.CX p Y,.X Y,.CX z Y] tape s1=s2 := by
    simp only [run,s1,s2]
    apply congrArg (State.mk s.phase)
    have r := ready
    simp only [topOut] at r
    funext q
    by_cases hq : q=Y
    · subst hq
      simp [writeBit,Function.update,hpY,Ne.symm hYz,hYz,K] at r ⊢
      cases h1 : s.basis q <;> cases h2 : s.basis p <;>
        cases h3 : carryBit (s.basis p) (s.basis y) (s.basis c) <;> simp_all
    · simp [writeBit,Function.update,hq]
  have relation : s2.basis z=carryBit (s2.basis p) (s2.basis y) (s2.basis c) := by
    simp [s2,K,writeBit,Function.update,hYz,Ne.symm hYz,hpz,hpY,hyz,hyY,hcz,hcY]
  have third (tape : List Bool) : run (eraseCarry p y c z) tape s2=s3 := by
    rw [eraseCarry_correct p y c z hpz hyz hcz s2 relation]
    simp only [s2,s3]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqz : q=z
    · subst hqz; simp [writeBit,Function.update,hYz,clean]
    · by_cases hqY : q=Y <;> simp_all [writeBit,Function.update]
  have fourth (tape : List Bool) : run [.CX p y,.CX c y] tape s3=postS p y c Y s := by
    simp only [run,s3,postS]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqy : q=y
    · subst hqy; simp [writeBit,Function.update,hpY,hcY,hyY,Ne.symm hpy,Ne.symm hyc]
    · by_cases hqY : q=Y <;> simp_all [writeBit,Function.update]
  rw [oldTop_eq]
  simp only [cat,first,second,third,fourth]

theorem new_run (p y c Y : Wire) (nd : [p,y,c,Y].Nodup) (s : State) (n : List Bool)
    (ready : topOut p y c Y s.basis=false) :
    run (newTop p y c Y) n s=postS p y c Y s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hpy,hpc,hpY⟩,⟨hyc,hyY⟩,hcY⟩ := nd
  let K := carryBit (s.basis p) (s.basis y) (s.basis c)
  let s1 : State := ⟨s.phase,writeBit s.basis Y K⟩
  let s2 : State := ⟨s.phase,writeBit s.basis Y false⟩
  have first (tape : List Bool) : run [.X Y,.CX p Y] tape s=s1 := by
    simp only [run,s1]
    apply congrArg (State.mk s.phase)
    have r := ready
    simp only [topOut] at r
    funext q
    by_cases hq : q=Y
    · subst hq
      simp [writeBit,Function.update,hpY,K] at r ⊢
      cases h1 : s.basis q <;> cases h2 : s.basis p <;>
        cases h3 : carryBit (s.basis p) (s.basis y) (s.basis c) <;> simp_all
    · simp [writeBit,Function.update,hq]
  have relation : s1.basis Y=carryBit (s1.basis p) (s1.basis y) (s1.basis c) := by
    simp [s1,K,writeBit,Function.update,hpY,hyY,hcY]
  have second (tape : List Bool) : run (eraseCarry p y c Y) tape s1=s2 := by
    rw [eraseCarry_correct p y c Y hpY hyY hcY s1 relation]
    simp only [s1,s2]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq : q=Y <;> simp [writeBit,Function.update,hq]
  have third (tape : List Bool) : run [.CX p y,.CX c y] tape s2=postS p y c Y s := by
    simp only [run,s2,postS]
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hqy : q=y
    · subst hqy; simp [writeBit,Function.update,hpY,hcY,hyY,Ne.symm hpy,Ne.symm hyc]
    · by_cases hqY : q=Y <;> simp_all [writeBit,Function.update]
  simp only [newTop,cat,first,second,third]

/-- Exact complete-State replacement of the terminal, for arbitrary records. -/
theorem top_replace (p y c Y z : Wire) (nd : [p,y,c,Y,z].Nodup) (s : State) (m n : List Bool)
    (clean : s.basis z=false) (ready : topOut p y c Y s.basis=false) :
    run (oldTop p y c Y z) m s=run (newTop p y c Y) n s := by
  have nd4 : [p,y,c,Y].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd ⊢
    tauto
  rw [old_run p y c Y z nd s m clean ready,new_run p y c Y nd4 s n ready]

/-- The old terminal's high output, without any readiness premise. Its measured
unwind does not touch `Y`. -/
theorem old_high (p y c Y z : Wire) (nd : [p,y,c,Y,z].Nodup) (s : State) (m : List Bool)
    (clean : s.basis z=false) :
    (run (oldTop p y c Y z) m s).basis Y=topOut p y c Y s.basis := by
  have nd4 : [p,y,c,z].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at nd ⊢
    tauto
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hpy,hpc,hpY,hpz⟩,⟨hyc,hyY,hyz⟩,⟨hcY,hcz⟩,hYz⟩ := nd
  let K := carryBit (s.basis p) (s.basis y) (s.basis c)
  let s1 : State := ⟨s.phase,writeBit s.basis z K⟩
  have first (tape : List Bool) : run (majority p y c z) tape s=s1 := by
    rw [majority_correct p y c z nd4]
    simp only [s1,K,clean,Bool.false_xor]
  have away : Y∉wires (eraseCarry p y c z++[.CX p y,.CX c y]) := by
    simp_all [eraseCarry,wires,Instr.wires,correctionWires,ne_comm]
  have regroup : oldTop p y c Y z=
      (majority p y c z++[.CX p Y,.X Y,.CX z Y])++(eraseCarry p y c z++[.CX p y,.CX c y]) := by
    rw [oldTop_eq]; simp only [List.append_assoc]
  rw [regroup,cat,run_preserves_outside _ _ _ Y away,cat,first]
  simp [run,s1,K,topOut,writeBit,Function.update,hpY,Ne.symm hYz,hYz,hpz]

theorem oldTop_counts (p y c Y z : Wire) :
    toffoliCount (oldTop p y c Y z)=1 ∧ measurementCount (oldTop p y c Y z)=1 := by
  rw [oldTop_eq]; exact ⟨rfl,rfl⟩

theorem newTop_counts (p y c Y : Wire) :
    toffoliCount (newTop p y c Y)=0 ∧ measurementCount (newTop p y c Y)=1 := ⟨rfl,rfl⟩

theorem top_slots (p y c Y z : Wire) :
    gateSlots (oldTop p y c Y z)=gateSlots (newTop p y c Y)+7 := by
  rw [oldTop_eq]; rfl

theorem newTop_wires (p y c Y z : Wire) : wires (newTop p y c Y)⊆wires (oldTop p y c Y z) := by
  rw [oldTop_eq]
  intro q hq
  simp only [newTop,majority,eraseCarry,wires_append,Finset.mem_union] at hq ⊢
  simp [wires,Instr.wires,correctionWires] at hq ⊢
  tauto

theorem newTop_physical (p y c Y : Wire) (nd : [p,y,c,Y].Nodup) :
    GatePhysical (newTop p y c Y) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newTop,eraseCarry,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

/-- Whole-State replacement inside an arbitrary prefix and suffix, under the
old program's proved final top output. Same record ordinals. -/
theorem whole_top (P R : Program) (p y c Y z : Wire) (nd : [p,y,c,Y,z].Nodup)
    (s : State) (m : List Bool)
    (clean : s.basis z=false) (hzP : z∉wires P) (hYR : Y∉wires R)
    (top : (run (P++oldTop p y c Y z++R) [] s).basis Y=false) :
    run (P++oldTop p y c Y z++R) m s=run (P++newTop p y c Y++R) m s := by
  let t:=run P m s
  let t0:=run P [] s
  have tc : t.basis z=false := (run_preserves_outside P m s z hzP).trans clean
  have tc0 : t0.basis z=false := (run_preserves_outside P [] s z hzP).trans clean
  have top0 : (run (oldTop p y c Y z) [] t0).basis Y=false := by
    have h:=top
    simp only [cat,List.drop_nil] at h
    rw [run_preserves_outside R [] _ Y hYR] at h
    exact h
  have pb : t.basis=t0.basis := run_basis_records P s s m [] rfl
  have ready : topOut p y c Y t.basis=false := by
    rw [pb,←old_high p y c Y z nd t0 [] tc0]; exact top0
  have eqn:=top_replace p y c Y z nd t (m.drop (measurementCount P))
    (m.drop (measurementCount P)) tc ready
  have co:=(oldTop_counts p y c Y z).2
  have cn:=(newTop_counts p y c Y).2
  simpa only [cat,measurementCount_append,co,cn,List.drop_drop,Nat.add_comm,t] using
    congrArg (run R ((m.drop (measurementCount P)).drop 1)) eqn

/-! ### Support of the split pieces -/

theorem lastCarry_cat (xs ys : List Wire) (cin : Wire) :
    lastCarry (xs++ys) cin=lastCarry ys (lastCarry xs cin) := by
  induction xs generalizing cin with
  | nil => rfl
  | cons x xs ih => exact ih x

theorem mPrefix_support (bs : List MappedBit) (ys cs : List Wire) (cin : Wire) :
    wires (mPrefix bs ys cs cin)⊆(cin::(mappedWires bs++ys++cs)).toFinset := by
  induction bs generalizing ys cs cin with
  | nil => simp [mPrefix,wires]
  | cons b bs ih =>
    cases ys with
    | nil => simp [mPrefix,wires]
    | cons y ys =>
      cases cs with
      | nil => simp [mPrefix,wires]
      | cons z zs =>
        intro q hq
        simp only [mPrefix,wires_append,Finset.mem_union] at hq
        rcases hq with hq|hq
        · have h := (mappedBit_wires b y cin z).1 hq
          simp [mappedWires] at h ⊢
          tauto
        · have h := ih ys zs z hq
          simp [mappedWires] at h ⊢
          rcases h with h|h|h|h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem mSuffix_support (bs : List MappedBit) (ys cs : List Wire) (cin : Wire) :
    wires (mSuffix bs ys cs cin)⊆(cin::(mappedWires bs++ys++cs)).toFinset := by
  induction bs generalizing ys cs cin with
  | nil => simp [mSuffix,wires]
  | cons b bs ih =>
    cases ys with
    | nil => simp [mSuffix,wires]
    | cons y ys =>
      cases cs with
      | nil => simp [mSuffix,wires]
      | cons z zs =>
        intro q hq
        simp only [mSuffix,wires_append,Finset.mem_union] at hq
        rcases hq with (hq|hq)|hq
        · have h := ih ys zs z hq
          simp [mappedWires] at h ⊢
          rcases h with h|h|h|h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        · have h := (mappedBit_wires b y cin z).2.1 hq
          simp [mappedWires] at h ⊢
          tauto
        · have h := (mappedBit_wires b y cin z).2.2 hq
          simp [mappedWires] at h ⊢
          tauto

theorem mem_block (w : Nat → Wire) (a n : Nat) (q : Wire) (h : q ∈ wireBlock w a n) :
    ∃ i : Nat, a ≤ i ∧ i < a + n ∧ w i = q := by
  obtain ⟨i,hi,e⟩ := List.mem_map.mp h
  simp only [List.mem_range'_1] at hi
  exact ⟨i,hi.1,hi.2,e⟩

/-! ### The first-carry-trimmed 257-bit mapped adder (`hAddT` shape) -/

def eraseLow (w : Nat → Wire) : Program :=
  mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540)
def sumLow (w : Nat → Wire) : Program := mappedSum {wire:=none,flip:=true} (w 1) (w 1797)

/-- Literally `[CX,CX] ++ hPost` for source bits `D`. -/
def oldT (D : List MappedBit) (w : Nat → Wire) : Program :=
  [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++
    (mappedAdd D.tail (wireBlock w 1 257).tail (wireBlock w 1540 256).tail (w 1540) ++
      mappedEraseCarry {wire:=none,flip:=true} (w 1) (w 1797) (w 1540) ++
      mappedSum {wire:=none,flip:=true} (w 1) (w 1797))

def topP (D : List MappedBit) (w : Nat → Wire) : Program :=
  [.CX (w 1) (w 1540),.CX (w 1797) (w 1540)] ++
    mPrefix (D.tail.take 254) (wireBlock w 2 254) (wireBlock w 1541 254) (w 1540)

def topR (D : List MappedBit) (w : Nat → Wire) : Program :=
  mSuffix (D.tail.take 254) (wireBlock w 2 254) (wireBlock w 1541 254) (w 1540) ++
    eraseLow w++sumLow w

/-- The adder with both its first and its last carry Toffoli removed. -/
def topT (D : List MappedBit) (w : Nat → Wire) (p : Wire) : Program :=
  topP D w++newTop p (w 256) (w 1794) (w 257)++topR D w

theorem oldT_split (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=257) (hdrop : D.drop 255=[lowBit p,highBit p]) :
    oldT D w=topP D w++oldTop p (w 256) (w 1794) (w 257) (w 1795)++topR D w := by
  have dT : D.tail=D.tail.take 254++[lowBit p,highBit p] := by
    cases D with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.tail_cons]
      have e : ds.drop 254=[lowBit p,highBit p] := hdrop
      rw [←e,List.take_append_drop]
  have yT : (wireBlock w 1 257).tail=wireBlock w 2 254++[w 256,w 257] := by
    have t : (wireBlock w 1 257).tail=wireBlock w 2 256 := rfl
    rw [t,←wireBlock_append w 2 254 2]; rfl
  have cT : (wireBlock w 1540 256).tail=wireBlock w 1541 254++[w 1795] := by
    have t : (wireBlock w 1540 256).tail=wireBlock w 1541 255 := rfl
    rw [t,←wireBlock_append w 1541 254 1]; rfl
  have lc : lastCarry (wireBlock w 1541 254) (w 1540)=w 1794 := by
    rw [←wireBlock_append w 1541 253 1,lastCarry_cat]; rfl
  have l1 : (D.tail.take 254).length=(wireBlock w 2 254).length := by
    simp [wireBlock_length,hlen]
  have l2 : (D.tail.take 254).length=(wireBlock w 1541 254).length := by
    simp [wireBlock_length,hlen]
  rw [oldT,dT,yT,cT,madd_split _ _ _ _ _ _ _ _ _ l1 l2,lc]
  simp only [topP,topR,eraseLow,sumLow,oldTop,List.append_assoc]

theorem topT_counts (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=257) (hdrop : D.drop 255=[lowBit p,highBit p]) :
    toffoliCount (topT D w p)+1=toffoliCount (oldT D w) ∧
      measurementCount (topT D w p)=measurementCount (oldT D w) ∧
      gateSlots (topT D w p)+7=gateSlots (oldT D w) := by
  have o := oldTop_counts p (w 256) (w 1794) (w 257) (w 1795)
  have n := newTop_counts p (w 256) (w 1794) (w 257)
  have sl := top_slots p (w 256) (w 1794) (w 257) (w 1795)
  rw [oldT_split D w p hlen hdrop,topT]
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  omega

theorem topT_wires (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=257) (hdrop : D.drop 255=[lowBit p,highBit p]) :
    wires (topT D w p)⊆wires (oldT D w) := by
  rw [oldT_split D w p hlen hdrop,topT]
  simp only [wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) (newTop_wires _ _ _ _ _))
    (Finset.Subset.refl _)

theorem topT_physical (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=257) (hdrop : D.drop 255=[lowBit p,highBit p])
    (nd : [p,w 256,w 1794,w 257].Nodup) (h : GatePhysical (oldT D w)) :
    GatePhysical (topT D w p) := by
  rw [oldT_split D w p hlen hdrop] at h
  rw [topT]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨⟨h.1.1,newTop_physical _ _ _ _ nd⟩,h.2⟩

/-- Exact replacement on every record, given the old adder's final top output
bit is zero and its retired last carry starts clean. -/
theorem topT_run (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=257) (hdrop : D.drop 255=[lowBit p,highBit p])
    (hDw : ∀ q∈mappedWires D,q=p)
    (inj : ∀ i j,i<1798 → j<1798 → w i=w j → i=j)
    (hpi : p=w 1028)
    (s : State) (m : List Bool) (clean : s.basis (w 1795)=false)
    (top : (run (oldT D w) [] s).basis (w 257)=false) :
    run (topT D w p) m s=run (oldT D w) m s := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
    fun e => h (inj i j hi hj e)
  have hp (i : Nat) (hi : i<1798) (h : i≠1028) : p≠w i := by
    rw [hpi]; exact ne 1028 i (by omega) hi (Ne.symm h)
  have nd : [p,w 256,w 1794,w 257,w 1795].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    refine ⟨⟨hp 256 (by omega) (by omega),hp 1794 (by omega) (by omega),hp 257 (by omega) (by omega),hp 1795 (by omega) (by omega)⟩,
      ⟨ne _ _ (by omega) (by omega) (by omega),ne _ _ (by omega) (by omega) (by omega),
        ne _ _ (by omega) (by omega) (by omega)⟩,
      ⟨ne _ _ (by omega) (by omega) (by omega),ne _ _ (by omega) (by omega) (by omega)⟩,
      ne _ _ (by omega) (by omega) (by omega)⟩
  have bitsW (q : Wire) (hq : q∈mappedWires (D.tail.take 254)) : q=p := by
    apply hDw
    simp only [mappedWires,List.mem_flatMap] at hq ⊢
    obtain ⟨b,hb,hqb⟩ := hq
    exact ⟨b,List.mem_of_mem_tail (List.mem_of_mem_take hb),hqb⟩
  have hzP : w 1795∉wires (topP D w) := by
    intro h
    simp only [topP,wires_append,Finset.mem_union] at h
    rcases h with h|h
    · simp [wires,Instr.wires] at h
      rcases h with e|e|e <;> exact ne _ _ (by omega) (by omega) (by omega) e.symm
    · have h' := List.mem_toFinset.mp (mPrefix_support _ _ _ _ h)
      simp only [List.mem_cons,List.mem_append] at h'
      rcases h' with e|(e|e)|e
      · exact ne _ _ (by omega) (by omega) (by omega) e
      · exact hp 1795 (by omega) (by omega) (bitsW _ e).symm
      · obtain ⟨i,h1,h2,h3⟩ := mem_block w 2 254 _ e
        exact absurd (inj i 1795 (by omega) (by omega) h3) (by omega)
      · obtain ⟨i,h1,h2,h3⟩ := mem_block w 1541 254 _ e
        exact absurd (inj i 1795 (by omega) (by omega) h3) (by omega)
  have hYR : w 257∉wires (topR D w) := by
    intro h
    simp only [topR,wires_append,Finset.mem_union] at h
    rcases h with (h|h)|h
    · have h' := List.mem_toFinset.mp (mSuffix_support _ _ _ _ h)
      simp only [List.mem_cons,List.mem_append] at h'
      rcases h' with e|(e|e)|e
      · exact ne _ _ (by omega) (by omega) (by omega) e
      · exact hp 257 (by omega) (by omega) (bitsW _ e).symm
      · obtain ⟨i,h1,h2,h3⟩ := mem_block w 2 254 _ e
        exact absurd (inj i 257 (by omega) (by omega) h3) (by omega)
      · obtain ⟨i,h1,h2,h3⟩ := mem_block w 1541 254 _ e
        exact absurd (inj i 257 (by omega) (by omega) h3) (by omega)
    · have h' := List.mem_toFinset.mp ((mappedBit_wires {wire:=none,flip:=true} (w 1) (w 1797) (w 1540)).2.1 h)
      simp at h'
      rcases h' with e|e|e <;> exact ne _ _ (by omega) (by omega) (by omega) e
    · have h' := List.mem_toFinset.mp ((mappedBit_wires {wire:=none,flip:=true} (w 1) (w 1797) (w 1797)).2.2 h)
      simp at h'
      rcases h' with e|e <;> exact ne _ _ (by omega) (by omega) (by omega) e
  have top' : (run (topP D w++oldTop p (w 256) (w 1794) (w 257) (w 1795)++topR D w) [] s).basis (w 257)=false := by
    rw [←oldT_split D w p hlen hdrop]; exact top
  rw [oldT_split D w p hlen hdrop,topT]
  exact (whole_top (topP D w) (topR D w) p (w 256) (w 1794) (w 257) (w 1795) nd s m clean hzP hYR top').symm

end ECDSAAdd.Entrant.MappedTopZero

#print axioms ECDSAAdd.Entrant.MappedTopZero.madd_split
#print axioms ECDSAAdd.Entrant.MappedTopZero.top_replace

#print axioms ECDSAAdd.Entrant.MappedTopZero.topT_run
#print axioms ECDSAAdd.Entrant.MappedTopZero.topT_counts
#print axioms ECDSAAdd.Entrant.MappedTopZero.topT_physical
