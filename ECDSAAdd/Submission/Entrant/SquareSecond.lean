-- Source member declarations adapted from public submission d187aa2c-5827-478e-bc04-ca2166700b6e.
import ECDSAAdd.Submission.Entrant.CarryWindow
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.KnownSecondCarryDevelop
open Arithmetic

def head (expected : Bool) (a b c : Wire) : Program :=
  [.CX a c,.CX b c]++(if expected then [.X c] else [])

theorem head_correct (expected : Bool) (a b c : Wire) (hb:b≠c)
    (s : State) (m : List Bool) :
    run (head expected a b c) m s=
      ⟨s.phase,writeBit s.basis c (((s.basis c ^^ s.basis a) ^^ s.basis b) ^^ expected)⟩ := by
  cases expected <;> simp only [head,Bool.false_eq_true,if_false,if_true,List.cons_append,List.nil_append,run]
  all_goals
    apply congrArg (State.mk s.phase)
    funext q
    by_cases hq:q=c <;> simp [writeBit,Function.update,hq,hb]

theorem head_eq_majority (expected : Bool) (a b a' b' cin c : Wire)
    (hn:[a,b,cin,c].Nodup) (hb:b'≠c)
    (s : State) (m : List Bool)
    (ready:sumBit (s.basis a') (s.basis b') (carryBit (s.basis a) (s.basis b) (s.basis cin))=expected) :
    run (head expected a' b' c) m s=run (majority a b cin c) m s := by
  rw [head_correct expected a' b' c hb,majority_correct a b cin c hn]
  have solve (x y z k d : Bool) (h:sumBit x y k=d) : (((z ^^ x) ^^ y) ^^ d)=(z ^^ k) := by
    cases x <;> cases y <;> cases z <;> cases k <;> cases d <;> simp_all [sumBit]
  rw [solve _ _ _ _ _ ready]

theorem head_counts (expected : Bool) (a b c : Wire) :
    toffoliCount (head expected a b c)=0 ∧ measurementCount (head expected a b c)=0 := by
  cases expected <;> simp [head,toffoliCount,measurementCount]

theorem head_physical (expected : Bool) (a b c : Wire) (ha:a≠c) (hb:b≠c) :
    GatePhysical (head expected a b c) := by
  cases expected <;> simp [head,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ha,hb]

#print axioms head_eq_majority
#print axioms head_physical
end ECDSAAdd.Entrant.KnownSecondCarryDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.KnownSecondAddDevelop
open Arithmetic Instr KnownSecondCarryDevelop

def add (expected : Bool) (x y cs : List Wire) (cin : Wire) : Program :=
  match x,y,cs with
  | a::a'::as,b::b'::bs,c::cs =>
    head expected a' b' c ++ Arithmetic.addInPlace (a'::as) (b'::bs) cs c ++
      eraseCarry a b cin c ++ [CX a b,CX cin b]
  | _,_,_ => Arithmetic.addInPlace x y cs cin

theorem add_eq (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) (hn:[a,b,cin,c].Nodup) (hb:b'≠c)
    (s : State) (m : List Bool)
    (ready:sumBit (s.basis a') (s.basis b') (carryBit (s.basis a) (s.basis b) (s.basis cin))=expected) :
    run (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) m s =
      run (Arithmetic.addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) m s := by
  simp only [add,Arithmetic.addInPlace,List.append_assoc]
  rw [run_append (head expected a' b' c),run_append (majority a b cin c)]
  have hm : measurementCount (head expected a' b' c)=measurementCount (majority a b cin c) := by
    simp [head_counts,majority,measurementCount]
  rw [hm,head_eq_majority expected a b a' b' cin c hn hb _ _ ready]

theorem add_counts (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) :
    toffoliCount (add expected (a::a'::as) (b::b'::bs) (c::cs) cin)+1 =
      toffoliCount (Arithmetic.addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) ∧
    measurementCount (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) =
      measurementCount (Arithmetic.addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  simp only [add,Arithmetic.addInPlace,toffoliCount_append,measurementCount_append]
  have h:=head_counts expected a' b' c
  simp [h,majority,toffoliCount,measurementCount]
  omega

#print axioms add_eq
#print axioms add_counts
end ECDSAAdd.Entrant.KnownSecondAddDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.KnownSecondValueDevelop
open Arithmetic

theorem second (a a' b b' : Wire) (as bs : List Wire) (s : BasisState) :
    (sumBit (s a') (s b') (carryBit (s a) (s b) false)).toNat =
      (regValue (a::a'::as) s+regValue (b::b'::bs) s)/2%2 := by
  cases ha:s a <;> cases hb:s b <;> cases ha':s a' <;> cases hb':s b' <;>
    simp [regValue,ha,hb,ha',hb',sumBit,carryBit] <;> omega

theorem ready_true (a a' b b' cin : Wire) (as bs : List Wire) (s : BasisState)
    (hc:s cin=false)
    (h:(regValue (a::a'::as) s+regValue (b::b'::bs) s)/2%2=1) :
    sumBit (s a') (s b') (carryBit (s a) (s b) (s cin))=true := by
  rw [hc]
  have e := second a a' b b' as bs s
  rw [h] at e
  cases he:sumBit (s a') (s b') (carryBit (s a) (s b) false) <;> simp_all

#print axioms ready_true
end ECDSAAdd.Entrant.KnownSecondValueDevelop
end

section
namespace ECDSAAdd.Entrant.KnownSecondAddDevelop
open Arithmetic Instr KnownSecondCarryDevelop
set_option autoImplicit false

theorem add_physical (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) (ha:a'≠c) (hb:b'≠c)
    (old:GatePhysical (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)) :
    GatePhysical (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  simp only [addInPlace,gatePhysical_append] at old
  simp only [add,gatePhysical_append]
  exact ⟨⟨⟨head_physical expected a' b' c ha hb,old.1.1.2⟩,old.1.2⟩,old.2⟩

theorem add_slots (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) :
    Challenge.gateSlots (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) ≤
      Challenge.gateSlots (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  cases expected <;> simp [add,addInPlace,head,majority,Challenge.gateSlots,Challenge.instructionSlots] <;> omega

#print axioms add_physical
#print axioms add_slots
end ECDSAAdd.Entrant.KnownSecondAddDevelop
end

section
namespace ECDSAAdd.Entrant.KnownSecondAddDevelop
open Arithmetic Instr KnownSecondCarryDevelop
set_option autoImplicit false

theorem add_support (expected : Bool) (a a' b b' c cin : Wire)
    (as bs cs : List Wire) (hx:(a::a'::as).length=(b::b'::bs).length)
    (hc:(c::cs).length+1=(b::b'::bs).length) :
    wires (add expected (a::a'::as) (b::b'::bs) (c::cs) cin) ⊆
      wires (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have tail:=addInPlace_wires (a'::as) (b'::bs) cs c (by simpa using hx) (by simpa using hc)
  have hs:wires (head expected a' b' c)⊆wires (addInPlace (a'::as) (b'::bs) cs c) := by
    rw [tail]
    cases expected <;> intro q hq <;>
      simp [head,wires,Instr.wires] at hq ⊢ <;> tauto
  simp only [add,addInPlace,wires_append]
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with ((h|h)|h)|h
  · exact Or.inl (Or.inl (Or.inr (hs h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

#print axioms add_support
end ECDSAAdd.Entrant.KnownSecondAddDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic Instr

def sub (x y cs : List Wire) (cin : Wire) : Program :=
  notRegister y ++ KnownSecondAddDevelop.add true x y cs cin ++ notRegister y

theorem complement32 (a u : Nat) (hbit:a/2%2=0) :
    (u+(2^32-1-(a+u)%2^32))/2%2=1 := by
  have h:(a+u)%2^32<2^32 := Nat.mod_lt _ (by decide)
  omega

theorem square_second32 (M : Nat) : (M^2%2^32)/2%2=0 := by
  have h:M%4=0 ∨ M%4=1 ∨ M%4=2 ∨ M%4=3 := by omega
  have h4:M^2%4=0 ∨ M^2%4=1 := by
    rcases h with h|h|h|h <;> simp [Nat.pow_mod,h]
  have mod4:(M^2%2^32)%4=M^2%4 := Nat.mod_mod_of_dvd _ (by decide)
  rcases h4 with h4|h4 <;> omega

theorem sub_eq (a a' b b' c cin : Wire) (as bs cs : List Wire)
    (hn:(cin::((a::a'::as)++(b::b'::bs)++(c::cs))).Nodup)
    (hl:(b::b'::bs).length=32) (v u : Nat) (hbit:v/2%2=0)
    (s : State) (m : List Bool) (hc:s.basis cin=false)
    (hx:regValue (a::a'::as) s.basis=u)
    (hy:regValue (b::b'::bs) s.basis=(v+u)%2^32) :
    run (sub (a::a'::as) (b::b'::bs) (c::cs) cin) m s =
      run (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) m s := by
  have cnt:=fun q=>List.nodup_iff_count_le_one.mp hn q
  have yn:(b::b'::bs).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append,beq_iff_eq] at h ⊢
    omega
  have off (q : Wire) (hq:q=cin ∨ q∈a::a'::as ∨ q=c) : q∉b::b'::bs := by
    intro hy
    have h:=cnt q
    have pos:=List.count_pos_iff.mpr hy
    simp only [List.count_cons,beq_iff_eq] at pos
    simp only [List.count_cons,List.count_append,beq_iff_eq] at h
    rcases hq with rfl|hx|rfl
    · simp only [if_true] at h pos
      omega
    · have x:=List.count_pos_iff.mpr hx
      simp only [List.count_cons,beq_iff_eq] at x
      omega
    · simp only [if_true] at h pos
      omega
  have small:[a,b,cin,c].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have h:=cnt q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bc:b'≠c := by intro he;apply off c (Or.inr (Or.inr rfl));simp [←he]
  simp only [sub,subInPlace,List.append_assoc]
  rw [run_append (notRegister (b::b'::bs)),run_append (notRegister (b::b'::bs))]
  rw [run_append (KnownSecondAddDevelop.add true (a::a'::as) (b::b'::bs) (c::cs) cin),
    run_append (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)]
  have cm:measurementCount (KnownSecondAddDevelop.add true (a::a'::as) (b::b'::bs) (c::cs) cin)=
      measurementCount (addInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) :=
    (KnownSecondAddDevelop.add_counts true a a' b b' c cin as bs cs).2
  rw [cm]
  apply congrArg (fun st=>run (notRegister (b::b'::bs)) _ st)
  apply KnownSecondAddDevelop.add_eq true a a' b b' c cin as bs cs small bc
  apply KnownSecondValueDevelop.ready_true a a' b b' cin as bs
  · rw [notRegister_correct _ yn]
    simpa [off cin (Or.inl rfl)] using hc
  · rw [notRegister_correct _ yn]
    have xv:regValue (a::a'::as) (fun w=>if w∈b::b'::bs then !s.basis w else s.basis w)=u := by
      rw [←hx]
      apply regValue_congr
      intro q hq
      simp [off q (Or.inr (Or.inl hq))]
    have yv:regValue (b::b'::bs) (fun w=>if w∈b::b'::bs then !s.basis w else s.basis w)=2^32-1-(v+u)%2^32 := by
      rw [regValue_congr (b::b'::bs) _ (fun w=> !s.basis w) (by intro q hq;simp [hq]),regValue_complement,hl,hy]
    rw [xv,yv]
    exact complement32 v u hbit

#print axioms sub_eq
#print axioms square_second32
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic Instr
set_option autoImplicit false

theorem sub_counts (a a' b b' c cin : Wire) (as bs cs : List Wire) :
    toffoliCount (sub (a::a'::as) (b::b'::bs) (c::cs) cin)+1 =
      toffoliCount (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) ∧
    measurementCount (sub (a::a'::as) (b::b'::bs) (c::cs) cin) =
      measurementCount (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have h:=KnownSecondAddDevelop.add_counts true a a' b b' c cin as bs cs
  simp only [sub,subInPlace,toffoliCount_append,measurementCount_append,
    (notRegister_counts _).1,(notRegister_counts _).2,Nat.zero_add,Nat.add_zero]
  exact h

theorem sub_physical (a a' b b' c cin : Wire) (as bs cs : List Wire)
    (ha:a'≠c) (hb:b'≠c)
    (old:GatePhysical (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin)) :
    GatePhysical (sub (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  simp only [subInPlace,gatePhysical_append] at old
  simp only [sub,gatePhysical_append]
  exact ⟨⟨old.1.1,KnownSecondAddDevelop.add_physical true a a' b b' c cin as bs cs ha hb old.1.2⟩,old.2⟩

theorem sub_support (a a' b b' c cin : Wire) (as bs cs : List Wire)
    (hx:(a::a'::as).length=(b::b'::bs).length)
    (hc:(c::cs).length+1=(b::b'::bs).length) :
    wires (sub (a::a'::as) (b::b'::bs) (c::cs) cin) ⊆
      wires (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have h:=KnownSecondAddDevelop.add_support true a a' b b' c cin as bs cs hx hc
  simp only [sub,subInPlace,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)

theorem sub_slots (a a' b b' c cin : Wire) (as bs cs : List Wire) :
    Challenge.gateSlots (sub (a::a'::as) (b::b'::bs) (c::cs) cin) ≤
      Challenge.gateSlots (subInPlace (a::a'::as) (b::b'::bs) (c::cs) cin) := by
  have h:=KnownSecondAddDevelop.add_slots true a a' b b' c cin as bs cs
  simp only [sub,subInPlace,Challenge.gateSlots_append]
  omega

#print axioms sub_counts
#print axioms sub_physical
#print axioms sub_support
#print axioms sub_slots
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic

theorem shape (x : List Wire) (h:2≤x.length) : ∃a b xs,x=a::b::xs := by
  cases x with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs => exact ⟨a,b,xs,rfl⟩

theorem lists_eq (x y cs : List Wire) (cin : Wire)
    (hn:(cin::x++y++cs).Nodup) (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (v u : Nat) (hbit:v/2%2=0) (s : State) (m : List Bool) (hc:s.basis cin=false)
    (hx:regValue x s.basis=u) (hy:regValue y s.basis=(v+u)%2^32) :
    run (sub x y cs cin) m s=run (subInPlace x y cs cin) m s := by
  obtain ⟨a,a',as,rfl⟩:=shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs => exact sub_eq a a' b b' c cin as bs cs hn ly v u hbit s m hc hx hy

theorem lists_resources (x y cs : List Wire) (cin : Wire)
    (hn:(cin::x++y++cs).Nodup) (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31)
    (old:GatePhysical (subInPlace x y cs cin)) :
    toffoliCount (sub x y cs cin)+1=toffoliCount (subInPlace x y cs cin) ∧
    measurementCount (sub x y cs cin)=measurementCount (subInPlace x y cs cin) ∧
    GatePhysical (sub x y cs cin) ∧ wires (sub x y cs cin)⊆wires (subInPlace x y cs cin) ∧
    Challenge.gateSlots (sub x y cs cin)≤Challenge.gateSlots (subInPlace x y cs cin) := by
  obtain ⟨a,a',as,rfl⟩:=shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs =>
    have cnt:=fun q=>List.nodup_iff_count_le_one.mp hn q
    have ac:a'≠c := by
      intro he
      have h:=cnt c
      simp only [List.count_cons,List.count_append,beq_iff_eq] at h
      simp only [he,if_true] at h
      omega
    have bc:b'≠c := by
      intro he
      have h:=cnt c
      simp only [List.count_cons,List.count_append,beq_iff_eq] at h
      simp only [he,if_true] at h
      omega
    exact ⟨(sub_counts a a' b b' c cin as bs cs).1,(sub_counts a a' b b' c cin as bs cs).2,
      sub_physical a a' b b' c cin as bs cs ac bc old,
      sub_support a a' b b' c cin as bs cs (by omega) (by simp_all),
      sub_slots a a' b b' c cin as bs cs⟩

#print axioms lists_eq
#print axioms lists_resources
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.KnownSecondSubDevelop
open Arithmetic

theorem lists_static (x y cs : List Wire) (cin : Wire)
    (lx:x.length=32) (ly:y.length=32) (lc:cs.length=31) :
    toffoliCount (sub x y cs cin)+1=toffoliCount (subInPlace x y cs cin) ∧
    measurementCount (sub x y cs cin)=measurementCount (subInPlace x y cs cin) ∧
    wires (sub x y cs cin)⊆wires (subInPlace x y cs cin) ∧
    Challenge.gateSlots (sub x y cs cin)≤Challenge.gateSlots (subInPlace x y cs cin) := by
  obtain ⟨a,a',as,rfl⟩:=shape x (by omega)
  obtain ⟨b,b',bs,rfl⟩:=shape y (by omega)
  cases cs with
  | nil => simp at lc
  | cons c cs =>
    exact ⟨(sub_counts a a' b b' c cin as bs cs).1,(sub_counts a a' b b' c cin as bs cs).2,
      sub_support a a' b b' c cin as bs cs (by omega) (by simp_all),
      sub_slots a a' b b' c cin as bs cs⟩

#print axioms lists_static
end ECDSAAdd.Entrant.KnownSecondSubDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def eSubLoSq (L : CuccaroStreamedSquareWideLayout) : Program :=
  KnownSecondSubDevelop.sub (mU L) (eLo L) ((eBank L).take 31) L.core.cin

theorem eSubLoSq_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (base : BasisState) (hc : L.PairClean base) (O A H l : Nat) (hH : H < 2^96) (hl : l < 2^32)
    (hbit:((l+2^32-regValue (hiReg L) base/2^96)%2^32)/2%2=0) :
    Triple (BState L base O (2^32*H + l) A) (eSubLoSq L)
      (BState L base O (2^32*H + (l + 2^32 - regValue (hiReg L) base / 2^96) % 2^32) A) := by
  intro s m h
  obtain ⟨_, _, f3, _, f5⟩ := eK_facts L hw hn base hc O _ A s.basis h
  let u := regValue (hiReg L) base / 2^96
  have hu : regValue (mU L) s.basis = u := by rw [hi96 L hw, f5]
  have hv := eReg_split L hw s.basis
  rw [h.2.1] at hv
  have hl0 := eLo_lt L hw s.basis
  have hm := eMid_lt L hw s.basis
  have key : regValue (eLo L) s.basis = l ∧ regValue (eMid L) s.basis = H ∧
      s.basis (eU L) = false ∧ s.basis (eV L) = false := by
    cases e1 : s.basis (eU L) <;> cases e2 : s.basis (eV L) <;>
      simp only [e1, e2, Bool.false_eq_true, if_false, if_true] at hv <;>
      first | omega | (exact ⟨by omega, by omega, rfl, rfl⟩)
  obtain ⟨k1, k2, k3, k4⟩ := key
  have nd := lo_nodup L hw hn 31 (by omega)
  have nd2 : (L.core.cin :: (mU L ++ eLo L ++ (eBank L).take 31)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.count_cons, List.count_append] at c ⊢
    omega
  have hu32:u<2^32 := by
    rw [←hu]
    have z:=regValue_lt (mU L) s.basis
    rwa [mU_length L hw] at z
  have restore:(((l+2^32-u)%2^32)+u)%2^32=l := by omega
  have eq:=KnownSecondSubDevelop.lists_eq (mU L) (eLo L) ((eBank L).take 31) L.core.cin nd2
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))
    ((l+2^32-u)%2^32) u hbit s m f3 hu (by rw [restore];exact k1)
  change run (eSubLoSq L) m s=run (eSubLo L) m s at eq
  rw [eq]
  exact eSubLo_step L hw hn base hc O A H l hH hl s m h

#print axioms eSubLoSq_step
end ECDSAAdd.Entrant.ControlLoan1589BFFold
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem eSubLoSq_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    toffoliCount (eSubLoSq L)=30 ∧ measurementCount (eSubLoSq L)=31 ∧
    GatePhysical (eSubLoSq L) ∧ wires (eSubLoSq L)⊆oldE L ∧
    Challenge.gateSlots (eSubLoSq L)≤448 := by
  have nd := lo_nodup L hw hn 31 (by omega)
  have nd2 : (L.core.cin :: (mU L ++ eLo L ++ (eBank L).take 31)).Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have c := List.nodup_iff_count_le_one.mp nd q
    simp only [List.count_cons,List.count_append] at c ⊢
    omega
  have rr:=KnownSecondSubDevelop.lists_resources (mU L) (eLo L) ((eBank L).take 31) L.core.cin nd2
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega)) (eSubLo_physical L hw hn)
  change toffoliCount (eSubLoSq L)+1=toffoliCount (eSubLo L) ∧
    measurementCount (eSubLoSq L)=measurementCount (eSubLo L) ∧ GatePhysical (eSubLoSq L) ∧
    wires (eSubLoSq L)⊆wires (eSubLo L) ∧ Challenge.gateSlots (eSubLoSq L)≤Challenge.gateSlots (eSubLo L) at rr
  have counts:=lo_counts L hw
  exact ⟨by omega,by omega,rr.2.2.1,rr.2.2.2.1.trans (eSubLo_oldE L hw),
    rr.2.2.2.2.trans (eSubLo_slots L hw)⟩

#print axioms eSubLoSq_resources
end ECDSAAdd.Entrant.ControlLoan1589BFFold
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem eSubLoSq_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    toffoliCount (eSubLoSq L)=30 ∧ measurementCount (eSubLoSq L)=31 ∧
    wires (eSubLoSq L)⊆oldE L ∧ Challenge.gateSlots (eSubLoSq L)≤448 := by
  have rr:=KnownSecondSubDevelop.lists_static (mU L) (eLo L) ((eBank L).take 31) L.core.cin
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))
  change toffoliCount (eSubLoSq L)+1=toffoliCount (eSubLo L) ∧
    measurementCount (eSubLoSq L)=measurementCount (eSubLo L) ∧
    wires (eSubLoSq L)⊆wires (eSubLo L) ∧ Challenge.gateSlots (eSubLoSq L)≤Challenge.gateSlots (eSubLo L) at rr
  have counts:=lo_counts L hw
  exact ⟨by omega,by omega,rr.2.2.1.trans (eSubLo_oldE L hw),
    rr.2.2.2.trans (eSubLo_slots L hw)⟩

theorem eSubLoSq_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (eSubLoSq L) := (eSubLoSq_resources L hw hn).2.2.1

theorem eSubLoSq_oldE (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    wires (eSubLoSq L)⊆oldE L := (eSubLoSq_static L hw).2.2.1

theorem eSubLoSq_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (eSubLoSq L)≤448 := (eSubLoSq_static L hw).2.2.2

#print axioms eSubLoSq_static
#print axioms eSubLoSq_physical
end ECDSAAdd.Entrant.ControlLoan1589BFFold
end
namespace ECDSAAdd.Entrant.SquareSecondStack
open ControlLoan1589BFFold CarryWindowCache Arithmetic.CuccaroStreamedSquareWideLayout

def wRestoreS (L : CuccaroStreamedSquareWideLayout) : Program :=
 eAddB L++(eSubLoSq L++padM L 720)
def bBodyS (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(wFoldCK L++(eFoldTq L c++wRestoreS L)))
theorem bBodyS_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (bBodyS L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0


  let u := b1/2^96
  let d := W/2^128 - u
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  -- wFoldCK
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have w1 := wBuild_step L hw hn base hc O2 (2^32*H + l' + 2^128*K)
  rw [hb1] at w1
  have wm := wMidFullCK_step L hw hn base hc O2 (2^32*H + l' + 2^128*K) b1 hb1 hb1lt hO2 H l' K hH hl' hK rfl
  have w5 := wUnbuildKnown_step L hw hn base hc O3 (2^32*H + l' + 2^128*K)
  rw [hb1] at w5
  have kc := kapClr_step L hw hn base hc O3 0 H l' hH hl'
  rw [hb1] at kc
  change Triple (BState L base O3 (2^32*H + l' + 2^128*(if l' < u then 1 else 0)) 0) (kapClr L)
    (BState L base O3 (2^32*H + l') 0) at kc
  rw [hKif] at kc
  have w3 := eSubK_step L hw hn base hc O3 (2^32*H + l') 0 b1 (by omega) hb1
  have tw : Triple (BState L base O2 b0 0) (wFoldCK L) (BState L base O3 E1 0) :=
    k1.seq (w1.seq (wm.seq (w5.seq (kc.seq w3))))
  -- eFoldTq
  have f1 := eFlip_step L hw hn base c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn base hc O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn base c hcw O4 (flipE g E1) 0
  rw [flipE_flipE] at f3
  have tf : Triple (BState L base O3 E1 0) (eFoldTq L c) (BState L base O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestoreS
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn base hc O4 E1 0 b1 hb1 (by rw [bk]; omega)
  rw [bk] at r2
  have bit32 : ((l'+2^32-u)%2^32)/2%2=0 := by
    have recover:(l'+2^32-u)%2^32=b0%2^32 := by
      show (((b0%2^32+u)%2^32)+2^32-u)%2^32=b0%2^32
      omega
    rw [recover]
    change ((M^2%2^128)%2^32)/2%2=0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have r3 := eSubLoSq_step L hw hn base hc O4 0 H l' hH hl' (by rw [hb1];exact bit32)
  rw [hb1] at r3
  have bb : 2^32*H + (l' + 2^32 - u) % 2^32 = b0 := by
    show 2^32*(b0/2^32) + ((b0%2^32 + u)%2^32 + 2^32 - u) % 2^32 = b0; omega
  rw [bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 720
  have tr : Triple (BState L base O4 E1 0) (wRestoreS L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have conv2 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv2))
  rw [key] at all
  exact all



theorem sub_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 toffoliCount (eSubLoSq L)+1=toffoliCount (eSubLo L) ∧
 measurementCount (eSubLoSq L)=measurementCount (eSubLo L) ∧
 wires (eSubLoSq L)⊆wires (eSubLo L) ∧ Challenge.gateSlots (eSubLoSq L)≤Challenge.gateSlots (eSubLo L) := by
 exact KnownSecondSubDevelop.lists_static (mU L) (eLo L) ((eBank L).take 31) L.core.cin
    (mU_length L hw) (eLo_length L hw) (eBank_take_length L hw 31 (by omega))

theorem bBodyS_delta (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (bBodyS L c)+1=toffoliCount (bBodyCK L c) ∧
 measurementCount (bBodyS L c)=measurementCount (bBodyCK L c) ∧
 wires (bBodyS L c)⊆wires (bBodyCK L c) ∧ Challenge.gateSlots (bBodyS L c)≤Challenge.gateSlots (bBodyCK L c) := by
 have r:=sub_rel L hw
 refine ⟨?_,?_,?_,?_⟩
 · simp only [bBodyS,bBodyCK,wRestoreS,wRestoreCK,toffoliCount_append];omega
 · simp only [bBodyS,bBodyCK,wRestoreS,wRestoreCK,measurementCount_append];omega
 · simp only [bBodyS,bBodyCK,wRestoreS,wRestoreCK,wires_append]
   exact Finset.union_subset_union (Finset.Subset.refl _)
     (Finset.union_subset_union (Finset.Subset.refl _)
       (Finset.union_subset_union (Finset.Subset.refl _)
         (Finset.union_subset_union (Finset.Subset.refl _)
           (Finset.union_subset_union (Finset.Subset.refl _)
             (Finset.union_subset_union r.2.2.1 (Finset.Subset.refl _))))))
 · simp only [bBodyS,bBodyCK,wRestoreS,wRestoreCK,Challenge.gateSlots_append];omega

theorem bBodyS_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (bBodyS L c)=4800 ∧ measurementCount (bBodyS L c)=5924 := by
 have d:=bBodyS_delta L hw c
 have b:=bBodyCK_counts L hw c
 exact ⟨by omega,by omega⟩

theorem bBodyS_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
 (hn : (c::L.wires).Nodup) : GatePhysical (bBodyS L c) := by
 have h:=bBodyCK_physical L hw c hn
 simp only [bBodyCK,wRestoreCK,gatePhysical_append] at h
 simp only [bBodyS,wRestoreS,gatePhysical_append]
 exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,
   eSubLoSq_physical L hw (List.nodup_cons.mp hn).2,h.2.2.2.2.2.2⟩

theorem bBodyS_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 QRel.Le (bBodyS L c) (bBody L c) := by
 have d:=bBodyS_delta L hw c
 have b:=bBodyCK_le L hw c
 exact ⟨d.2.2.1.trans b.1,d.2.2.2.trans b.2⟩

theorem bBodyS_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (c : Wire) :
 wires (bBodyS L c)⊆(c::L.wires).toFinset := (bBodyS_delta L hw c).2.2.1.trans (bBodyCK_support L hw hn c)

theorem bBodyS_rel (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (bBodyS L c)+1023=toffoliCount (bBody L c) ∧
 measurementCount (bBodyS L c)+4=measurementCount (bBody L c) ∧ QRel.Le (bBodyS L c) (bBody L c) := by
 have d:=bBodyS_delta L hw c
 have b:=bBodyCK_rel L hw c
 exact ⟨by omega,by omega,bBodyS_le L hw c⟩
#print axioms bBodyS_frame
#print axioms bBodyS_physical
#print axioms bBodyS_rel
end ECDSAAdd.Entrant.SquareSecondStack
