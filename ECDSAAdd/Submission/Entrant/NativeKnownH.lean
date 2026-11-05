import ECDSAAdd.Arithmetic.NativeFirstKnownInverse
import ECDSAAdd.Arithmetic.NativeKnownPhysical
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Challenge.Contract
import ECDSAAdd.Baselines.SlotNativeFirst

/-! Known-output inverse of the native first tick with the roles of the two words swapped.

`NativeFirstKnown.inverse` undoes the K word with a full inverse adder (256 Toffolis) and then
erases the H word against the restored `x` with a known-output receiver (0 Toffolis).
Here the H word is undone first with its inverse adder (`hAdd w true`, 252 Toffolis), which
restores the low copy of `x`; the K word is then erased against that copy with a
known-output receiver (0 Toffolis). The measurement count is unchanged (252 + 256). -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.NativeKnownH
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect

def zbit : MappedBit := {wire:=none,flip:=false}

/-- Value the K tail must leave in `wireBlock w 771 257`: bits 2..255 of `x` (read from
the restored low copy) followed by three zero bits. -/
def desiredK (w : Nat → Wire) : List MappedBit :=
  mappedRead (wireBlock w 2 254) false++[zbit,zbit,zbit]

def kReceiver (w : Nat → Wire) : Program :=
  sealedProgram (KnownOutputAdder.program (kBits w true) (wireBlock w 771 257) (desiredK w)
    (wireBlock w 1540 256) (w 770))

def inverse (w : Nat → Wire) : Program :=
  hAdd w true++((kReceiver w++[.X (w 770)])++(inverseUnmiddle w++inverseBack w))


/-! Local copies of the private cancellation helpers of `NativeFirstKnownInverse`. -/

private theorem state_of_value_frame (r : List Wire) (s t : State)
    (hp : t.phase=s.phase) (hv : regValue r t.basis=regValue r s.basis)
    (he : ∀q,q∉r → t.basis q=s.basis q) : t=s := by
  apply congrArg₂ State.mk hp
  funext q
  by_cases hq : q∈r
  · exact (regValue_eq_iff r _ _).mp hv q hq
  · exact he q hq

private theorem copy_cancel (src dst : List Wire) (hl : src.length=dst.length)
    (hn : (src++dst).Nodup) (s : State) (m n : List Bool) :
    run (copyRegister none src dst) n (run (copyRegister none src dst) m s)=s := by
  have f := copyRegister_correct none src dst hl hn (by simp) s m
  have i := copyRegister_correct none src dst hl hn (by simp)
    (run (copyRegister none src dst) m s) n
  have srcKeep := regValue_congr src (run (copyRegister none src dst) m s).basis s.basis
    (fun q hq => f.2.1 q (List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hq))
  apply state_of_value_frame dst s _ (i.1.trans f.1)
  · rw [i.2.2,f.2.2]
    simp only [copyValue]
    rw [srcKeep,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  · intro q hq; exact (i.2.1 q hq).trans (f.2.1 q hq)

private theorem rotate_reverse (r : List Wire) :
    (rotateRight r).reverse=rotateLeft r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      rw [rotateRight,rotateLeft,List.reverse_append,ih]
      rfl

private theorem rotate_proper (r : List Wire) (hn : r.Nodup) :
    ProperProgram (rotateRight r) := by
  induction r with
  | nil => simp [rotateRight,ProperProgram]
  | cons a r ih =>
    cases r with
    | nil => simp [rotateRight,ProperProgram]
    | cons b r =>
      have nd := List.nodup_cons.mp hn
      have ne : a≠b := fun h => nd.1 (by simp [h])
      exact (properProgram_append _ _).mpr
        ⟨by simp [swapBits,ProperProgram,ProperGate,ne,Ne.symm ne],ih nd.2⟩

private theorem rotate_cancel (r : List Wire) (hn : r.Nodup) (s : State) (m n : List Bool) :
    run (rotateLeft r) n (run (rotateRight r) m s)=s := by
  rw [←rotate_reverse]
  exact run_reverse_proper _ (rotate_proper r hn) s m n

private theorem front_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 771 255++wireBlock w 1 255).Nodup)
    (h0 : w 770≠w 1028) (h1 : w 1028≠w 0) :
    run (inverseBack w) n (run (inverseFront w) m s)=s := by
  let P : Program := [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]
  have hp : ProperProgram P := by simp [P,ProperProgram,ProperGate,h0,h1]
  have c := copy_cancel (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) hn (run P m s) m n
  have hm : measurementCount P=0 := properProgram_measurementCount P hp
  have cm := (lowCopy_counts w).2
  change run (lowCopy w++P.reverse) n (run (P++lowCopy w) m s)=s
  rw [run_append,run_take,run_append,run_take,hm,cm,List.drop_zero]
  simp only [List.drop_zero]
  rw [show run (lowCopy w) n (run (lowCopy w) m (run P m s))=run P m s from c]
  exact run_reverse_proper P hp s m n

private theorem middle_cancel (w : Nat → Wire) (s : State) (m n : List Bool)
    (hn : (wireBlock w 770 258).Nodup) (hne : w 1028≠w 770) :
    run (inverseUnmiddle w) n (run (inverseMiddle w) m s)=s := by
  rw [inverseUnmiddle,inverseMiddle,run_append,run_take,run_append,run_take,
    (rotate_counts (wireBlock w 770 258)).2.2.2,
    show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,List.drop_zero]
  rw [rotate_cancel _ hn]
  exact properGate_involution (.CX (w 1028) (w 770)) hne s m n

theorem regValue_cons' (a : Wire) (bs : List Wire) (st : BasisState) :
    regValue (a::bs) st=(st a).toNat+2*regValue bs st := by
  show (if st a then 1 else 0)+2*regValue bs st=_
  cases st a <;> simp

theorem block770 (w : Nat → Wire) : wireBlock w 770 258=w 770::wireBlock w 771 257 := by
  simp [wireBlock,List.range'_succ]

theorem middle_keep (w : Nat → Wire) (s : State) (m : List Bool) (q : Wire)
    (hq : q∉wireBlock w 770 258) :
    (run (inverseMiddle w) m s).basis q=s.basis q ∧ (run (inverseMiddle w) m s).phase=s.phase := by
  have q770 : q≠w 770 := fun h => hq (by rw [block770]; simp [h])
  rw [inverseMiddle,run_append,run_take,show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,
    List.drop_zero]
  have r := rotate_frame (wireBlock w 770 258) (run [.CX (w 1028) (w 770)] [] s)
    (m.drop 0)
  refine ⟨(r.2.1 q hq).trans ?_,r.1.trans ?_⟩
  · simp [run,writeBit,q770]
  · simp [run]


/-- Arithmetic core: after the front (parity extraction and low copy) the copied bits 2..255
equal the K tail's pre-forward value, i.e. bits 1..257 of the middle state. -/
theorem copy_matches (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) (x : Nat)
    (hx : x<2^256) (s : State) (mF : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    regValue (wireBlock w 2 254) (run (inverseFront w) mF s).basis=
      regValue (wireBlock w 771 257) (run (inverseMiddle w) [] (run (inverseFront w) mF s)).basis := by
  let P : Program := [.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)]
  let t := run P mF s
  let u := run (lowCopy w) mF t
  have pm : measurementCount P=0 := rfl
  have front : run (inverseFront w) mF s=u := by
    rw [inverseFront,run_append,run_take,pm,List.drop_zero]
  rw [front]
  have ne0 (i : Nat) (hi : i<1798) (h : i≠0) : w i≠w 0 := index_ne w hn i 0 hi (by omega) h
  have ne1028 (i : Nat) (hi : i<1798) (h : i≠1028) : w i≠w 1028 := index_ne w hn i 1028 hi (by omega) h
  -- P only writes w 0 and w 1028
  have tKeep (i : Nat) (hi : i<1798) (h0 : i≠0) (h1 : i≠1028) : t.basis (w i)=s.basis (w i) := by
    simp [t,P,run,writeBit,ne0 i hi h0,ne1028 i hi h1]
  have t1028 : t.basis (w 1028)=s.basis (w 770) := by
    have one : s.basis (w 1028)=false := ready.one
    have a : w 1028≠w 0 := ne0 1028 (by omega) (by omega)
    simp [t,P,run,writeBit,a,one]
  -- the low copy
  have copy := copyRegister_correct none (wireBlock w 771 255) (wireBlock w 1 255)
    (by simp [wireBlock_length]) (copy_inputs_nd w hn) (by simp) t mF
  have aZero : regValue (wireBlock w 0 258) s.basis=0 := ready.a
  have dest0 : regValue (wireBlock w 1 255) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [tKeep i (by omega) (by omega) (by omega)]
    exact (regValue_zero _ _).mp aZero _ (List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩)
  have uOut : ∀q,q∉wireBlock w 1 255 → u.basis q=t.basis q := by
    simpa only [lowCopy] using copy.2.1
  have uCopy : regValue (wireBlock w 1 255) u.basis=regValue (wireBlock w 771 255) t.basis := by
    simpa only [lowCopy,copyValue,dest0,Nat.zero_xor] using copy.2.2
  have uKeep (i : Nat) (hi : i<1798) (h : 256 ≤ i) (h0 : i≠1028) : u.basis (w i)=s.basis (w i) := by
    rw [uOut _ (block_not_mem w hn i 1 255 hi (by omega) (by omega))]
    exact tKeep i hi (by omega) h0
  have u1028 : u.basis (w 1028)=s.basis (w 770) := by
    rw [uOut _ (block_not_mem w hn 1028 1 255 (by omega) (by omega) (by omega))]
    exact t1028
  -- left side: bits 2..255 of the copy are bits 772..1025 of s
  have t771 : regValue (wireBlock w 771 255) t.basis=regValue (wireBlock w 771 255) s.basis := by
    apply regValue_congr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact tKeep i (by omega) (by omega) (by omega)
  have lhs : regValue (wireBlock w 2 254) u.basis=regValue (wireBlock w 772 254) s.basis := by
    have e := uCopy.trans t771
    rw [←wireBlock_append w 1 1 254,←wireBlock_append w 771 1 254,regValue_append,regValue_append,
      wireBlock_length,wireBlock_length] at e
    have a := regValue_lt (wireBlock w 1 1) u.basis
    have b := regValue_lt (wireBlock w 771 1) s.basis
    rw [wireBlock_length] at a b
    norm_num only [Nat.reducePow,pow_one] at e a b
    omega
  -- right side: the middle state
  let c := run [.CX (w 1028) (w 770)] [] u
  have cKeep (q : Wire) (hq : q≠w 770) : c.basis q=u.basis q := by
    simp [c,run,writeBit,hq]
  have c770 : c.basis (w 770)=false := by
    have e : u.basis (w 770)=s.basis (w 770) := uKeep 770 (by omega) (by omega) (by omega)
    simp [c,run,writeBit,u1028,e]
  have blockND := block_nodup w hn 770 258 (by omega)
  have cTail : regValue (wireBlock w 771 257) c.basis=regValue (wireBlock w 771 257) s.basis := by
    apply regValue_congr
    intro q hq
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    rw [cKeep _ (index_ne w hn i 770 (by omega) (by omega) (by omega))]
    exact uKeep i (by omega) (by omega) (by omega)
  have cVal : regValue (wireBlock w 770 258) c.basis=2*regValue (wireBlock w 771 257) s.basis := by
    rw [block770,regValue_cons',c770,cTail]
    simp
  have rot := rotateRight_spec (wireBlock w 770 258) blockND
    (2*regValue (wireBlock w 771 257) s.basis) (by omega) c [] cVal
  have midEq : run (inverseMiddle w) [] u=run (rotateRight (wireBlock w 770 258)) [] c := by
    rw [inverseMiddle,run_append,run_take,show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,
      List.drop_zero]
  rw [midEq]
  have mVal := rot.2
  change regValue (wireBlock w 770 258) _=_ at mVal
  generalize run (rotateRight (wireBlock w 770 258)) [] c=M at mVal ⊢
  rw [block770,regValue_cons'] at mVal
  have bit := Bool.toNat_le (M.basis (w 770))
  -- s: x = bits 770..1025, top two bits zero
  have xv : regValue (wireBlock w 770 258) s.basis=x := ready.b
  rw [←wireBlock_append w 770 1 257] at xv
  rw [regValue_append,wireBlock_length] at xv
  have topSplit : regValue (wireBlock w 771 257) s.basis=
      regValue (wireBlock w 771 1) s.basis+2*regValue (wireBlock w 772 256) s.basis := by
    rw [←wireBlock_append w 771 1 256,regValue_append,wireBlock_length]; norm_num
  have hiSplit : regValue (wireBlock w 772 256) s.basis=
      regValue (wireBlock w 772 254) s.basis+2^254*regValue (wireBlock w 1026 2) s.basis := by
    rw [←wireBlock_append w 772 254 2,regValue_append,wireBlock_length]
  have b1 := regValue_lt (wireBlock w 771 1) s.basis
  have b0 := regValue_lt (wireBlock w 770 1) s.basis
  rw [wireBlock_length] at b1 b0
  have top0 : regValue (wireBlock w 1026 2) s.basis=0 := by
    by_contra hne
    have pos : 1≤regValue (wireBlock w 1026 2) s.basis := Nat.one_le_iff_ne_zero.mpr hne
    have big : 2^256≤x := by
      rw [←xv,topSplit,hiSplit]
      have : (2:Nat)^256=2^1*(2*(2^254*1)) := by norm_num
      nlinarith
    omega
  rw [lhs]
  rw [hiSplit,top0] at topSplit
  norm_num only [Nat.reducePow,pow_one,mul_zero,add_zero] at mVal topSplit b1
  omega

theorem desiredK_length (w : Nat → Wire) : (desiredK w).length=257 := by
  simp [desiredK,mappedRead,wireBlock_length]

theorem desiredK_value (w : Nat → Wire) (s : BasisState) :
    mappedValue (desiredK w) s=regValue (wireBlock w 2 254) s := by
  simp [desiredK,mappedValue_append,mappedRead_value,mappedValue,MappedBit.value,zbit,
    mappedRead_length,wireBlock_length]

theorem desiredK_wires (w : Nat → Wire) :
    mappedWires (desiredK w)=wireBlock w 2 254 := by
  simp only [desiredK,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    zbit,Option.toList_none,List.nil_append,List.append_nil]
  exact mappedRead_wires _ false

theorem desiredK_fresh (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    ∀q∈mappedWires (desiredK w),q∉w 770::(wireBlock w 771 257++wireBlock w 1540 256) := by
  intro q hq
  rw [desiredK_wires] at hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  simp only [List.mem_cons,List.mem_append,not_or]
  exact ⟨index_ne w hn i 770 (by omega) (by omega) (by omega),
    block_not_mem w hn i 771 257 (by omega) (by omega) (by omega),
    block_not_mem w hn i 1540 256 (by omega) (by omega) (by omega)⟩

theorem kReceiver_counts (w : Nat → Wire) :
    toffoliCount (kReceiver w)=0 ∧ measurementCount (kReceiver w)=256 := by
  have h := KnownOutputAdder.program_counts (kBits w true) (desiredK w)
    (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)
    (by simp [kBits_length,wireBlock_length])
    (by simp [desiredK_length,wireBlock_length]) (by simp [wireBlock_length])
  simpa only [kReceiver,sealedProgram_eq,wireBlock_length] using h

theorem inverse_counts (w : Nat → Wire) :
    toffoliCount (inverse w)=252 ∧ measurementCount (inverse w)=508 := by
  have h := hAdd_counts w true
  have k := kReceiver_counts w
  have c := lowCopy_counts w
  have r := rotate_counts (wireBlock w 770 258)
  simp [inverse,inverseUnmiddle,inverseBack,toffoliCount_append,measurementCount_append,
    h.1,h.2,k.1,k.2,c.1,c.2,r.2.2.1,r.2.2.2,toffoliCount,measurementCount]


theorem middle_phase (w : Nat → Wire) (s : State) (m : List Bool) :
    (run (inverseMiddle w) m s).phase=s.phase := by
  rw [inverseMiddle,run_append,run_take,show measurementCount [.CX (w 1028) (w 770)]=0 from rfl,
    List.drop_zero]
  exact (rotate_frame (wireBlock w 770 258) _ _).1.trans (by simp [run])

theorem middle_records (w : Nat → Wire) (s : State) (m : List Bool) :
    run (inverseMiddle w) m s=run (inverseMiddle w) [] s := by
  have mm : measurementCount (inverseMiddle w)=0 := by
    rw [inverseMiddle,measurementCount_append,(rotate_counts _).2.1]; rfl
  rw [←run_take (inverseMiddle w) m s,←run_take (inverseMiddle w) [] s,mm,List.take_zero,List.take_zero]

attribute [local irreducible] run mappedAdd hAdd kAdd kTail NativeFirstDirect.forward lowCopy
  rotateRight rotateLeft kReceiver inverseFront inverseBack inverseMiddle inverseUnmiddle

theorem inverse_roundtrip (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<2^256) (s : State) (mF mI : List Bool)
    (ready : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis) :
    run (inverse w) mI (run (NativeFirstDirect.forward w) mF s)=s := by
  obtain ⟨u,eu⟩ : ∃u,run (inverseFront w) mF s=u := ⟨_,rfl⟩
  have initialCarry : regValue (wireBlock w 1540 257) s.basis=0 := ready.carry
  have clean : ∀q∈wireBlock w 1540 256,s.basis q=false := by
    intro q hq
    exact (regValue_zero _ _).mp initialCarry q
      (block_subset w 1540 256 257 (by omega) q hq)
  have frontAway (i : Nat) (hi : i<1798) (h0 : i≠0) (h770 : i≠770) (h1028 : i≠1028)
      (hs : ¬(771≤ i ∧ i<1026)) (hd : ¬(1≤ i ∧ i<256)) : w i∉wires (inverseFront w) := by
    have flags : w i∉wires ([.CX (w 770) (w 1028),.CX (w 1028) (w 0),.X (w 0)] : Program) := by
      simp [wires,Instr.wires,index_ne w hn i 0 hi (by omega) h0,
        index_ne w hn i 770 hi (by omega) h770,index_ne w hn i 1028 hi (by omega) h1028]
    have copyAway : w i∉wires (lowCopy w) := by
      rw [lowCopy,copyRegister_wires none (wireBlock w 771 255) (wireBlock w 1 255)
        (by simp [wireBlock_length])]
      split_ifs
      · simp
      · simp only [Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,not_or]
        exact ⟨block_not_mem w hn i 771 255 hi (by omega) (by omega),
          block_not_mem w hn i 1 255 hi (by omega) (by omega)⟩
    rw [inverseFront,wires_append,Finset.mem_union,not_or]
    exact ⟨flags,copyAway⟩
  have uc : ∀q∈wireBlock w 1540 256,u.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    rw [←eu]
    exact (run_preserves_outside _ mF s _ (frontAway j (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega))).trans (clean _ hq)
  have ui : u.basis (w 1797)=false := by
    rw [←eu]
    exact (run_preserves_outside _ mF s _ (frontAway 1797 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega))).trans ready.cin
  have ha := hAdd_spec w false u mF (h_inputs_nd w hn) (h_sources_fresh w hn false)
    (fun q hq => uc q (block_subset w 1540 252 256 (by omega) q hq))
  obtain ⟨v,ev⟩ : ∃v,run (hAdd w false) mF u=v := ⟨_,rfl⟩
  rw [ev] at ha
  have hAway (i : Nat) (hi : i<1798) (h : ¬(4≤ i ∧ i<257)) : w i∉wireBlock w 4 253 :=
    block_not_mem w hn i 4 253 hi (by omega) (by omega)
  have vc : ∀q∈wireBlock w 1540 256,v.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact (ha.2.1 _ (hAway j (by omega) (by omega))).trans (uc _ hq)
  obtain ⟨z,ez⟩ : ∃z,run (inverseMiddle w) (mF.drop 252) v=z := ⟨_,rfl⟩
  have zc : ∀q∈wireBlock w 1540 256,z.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    rw [←ez]
    exact (middle_keep w v _ _ (block_not_mem w hn j 770 258 (by omega) (by omega) (by omega))).1.trans
      (vc _ hq)
  have fm : measurementCount (inverseFront w)=0 := by
    rw [inverseFront,measurementCount_append,(lowCopy_counts w).2]; rfl
  have mm : measurementCount (inverseMiddle w)=0 := by
    rw [inverseMiddle,measurementCount_append,(rotate_counts _).2.1]; rfl
  have fr : NativeFirstDirect.forward w=
      inverseFront w++(hAdd w false++(inverseMiddle w++kAdd w false)) := by
    simp only [NativeFirstDirect.forward,inverseFront,inverseMiddle,List.append_assoc]
  have fRun : run (NativeFirstDirect.forward w) mF s=
      run (kAdd w false) (mF.drop 252) z := by
    rw [fr,run_append,run_take,fm,List.drop_zero]
    rw [run_append,run_take,(hAdd_counts w false).2]
    rw [run_append,run_take,mm,List.drop_zero,eu,ev,ez]
  rw [fRun]
  generalize ht0 : run (kAdd w false) (mF.drop 252) z=t0
  have kf := kAdd_spec w false z (mF.drop 252) (k_inputs_nd w hn) (k_sources_fresh w hn false) zc
  rw [ht0] at kf
  -- t0 agrees with v outside the K block
  have t0v : ∀q,q∉wireBlock w 770 258 → t0.basis q=v.basis q := by
    intro q hq
    rw [←ez] at kf
    exact (kf.2.1 q (by rw [←block770]; exact hq)).trans (middle_keep w v _ q hq).1
  have t0phase : t0.phase=v.phase := by
    rw [←ez] at kf
    exact kf.1.trans (middle_phase w v _)
  have notK (i : Nat) (hi : i<1798) (h : ¬(770≤ i ∧ i<1028)) : w i∉wireBlock w 770 258 :=
    block_not_mem w hn i 770 258 hi (by omega) (by omega)
  have t0c : ∀q∈wireBlock w 1540 252,t0.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact (t0v _ (notK j (by omega) (by omega))).trans (vc _ (block_subset w 1540 252 256 (by omega) _ hq))
  have v1797 : v.basis (w 1797)=u.basis (w 1797) := ha.2.1 _ (hAway 1797 (by omega) (by omega))
  have t0i : t0.basis (w 1797)=false :=
    (t0v _ (notK 1797 (by omega) (by omega))).trans (v1797.trans ui)
  -- undo the H word
  have hb := hAdd_spec w true t0 (mI.take 252) (h_inputs_nd w hn) (h_sources_fresh w hn true) t0c
  generalize ht1 : run (hAdd w true) (mI.take 252) t0=t1 at hb
  have hcancel := hAdd_cancel w u mF (mI.take 252) (h_inputs_nd w hn) (fun i => h_sources_fresh w hn i)
    (block_not_mem w hn 1028 4 253 (by omega) (by omega) (by omega))
    (fun q hq => uc q (block_subset w 1540 252 256 (by omega) q hq)) ui
  rw [ev] at hcancel
  have vc252 : ∀q∈wireBlock w 1540 252,v.basis q=false :=
    fun q hq => vc q (block_subset w 1540 252 256 (by omega) q hq)
  have hv := hAdd_spec w true v (mI.take 252) (h_inputs_nd w hn) (h_sources_fresh w hn true) vc252
  rw [hcancel] at hv
  have t0H : regValue (wireBlock w 4 253) t0.basis=regValue (wireBlock w 4 253) v.basis := by
    apply regValue_congr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact t0v _ (notK j (by omega) (by omega))
  have t0f : t0.basis (w 1028)=v.basis (w 1028) := t0v _ (notK 1028 (by omega) (by omega))
  have t0i' : t0.basis (w 1797)=v.basis (w 1797) := t0v _ (notK 1797 (by omega) (by omega))
  have t1H : regValue (wireBlock w 4 253) t1.basis=regValue (wireBlock w 4 253) u.basis := by
    rw [hb.2.2,t0H,t0f,t0i',←hv.2.2]
  have t1Hbits : ∀q∈wireBlock w 4 253,t1.basis q=u.basis q :=
    (regValue_eq_iff _ _ _).mp t1H
  -- outside the K block, t1 is u
  have t1u : ∀q,q∉wireBlock w 770 258 → t1.basis q=u.basis q := by
    intro q hq
    by_cases hH : q∈wireBlock w 4 253
    · exact t1Hbits q hH
    · exact (hb.2.1 q hH).trans ((t0v q hq).trans (ha.2.1 q hH))
  have t1phase : t1.phase=u.phase := hb.1.trans (t0phase.trans ha.1)
  -- the K inverse on t1 lands on the middle state of u
  have kflag : w 1028∉w 770::wireBlock w 771 257 := by
    rw [←block770]; exact notK 1028 (by omega) (by omega)
  have M_eq (r : List Bool) : run (kAdd w true) r t1=run (inverseMiddle w) [] u := by
    have kc := kAdd_cancel w z (mF.drop 252) r (k_inputs_nd w hn) (fun i => k_sources_fresh w hn i)
      kflag zc
    rw [ht0] at kc
    have t1c : ∀q∈wireBlock w 1540 256,t1.basis q=false := by
      intro q hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hj
      rw [t1u _ (notK j (by omega) (by omega))]
      exact uc _ hq
    have k1 := kAdd_spec w true t1 r (k_inputs_nd w hn) (k_sources_fresh w hn true) t1c
    have t0c' : ∀q∈wireBlock w 1540 256,t0.basis q=false := by
      intro q hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hj
      exact (t0v _ (notK j (by omega) (by omega))).trans (vc _ hq)
    have k0 := kAdd_spec w true t0 r (k_inputs_nd w hn) (k_sources_fresh w hn true) t0c'
    rw [kc] at k0
    -- t1 and t0 agree on the K block and the parity flag
    have kb : regValue (w 770::wireBlock w 771 257) t1.basis=regValue (w 770::wireBlock w 771 257) t0.basis := by
      apply regValue_congr
      intro q hq
      rw [←block770] at hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hj
      exact hb.2.1 _ (hAway j (by omega) (by omega))
    have f1 : t1.basis (w 1028)=t0.basis (w 1028) := hb.2.1 _ (hAway 1028 (by omega) (by omega))
    have zM := pool_run_agrees (inverseMiddle w) (wireBlock w 770 258++[w 1028]).toFinset
      (by
        intro q hq
        rw [inverseMiddle,wires_append] at hq
        simp only [Finset.mem_union] at hq
        rcases hq with hq|hq
        · simp [wires,Instr.wires] at hq
          rcases hq with rfl|rfl
          · simp
          · rw [block770]; simp
        · rw [(rotate_wires _).1] at hq
          split_ifs at hq
          · simp at hq
          · simp only [List.mem_toFinset] at hq
            simp [hq])
      [] v u ha.1
      (by
        intro q hq
        simp only [List.mem_toFinset,List.mem_append,List.mem_singleton] at hq
        rcases hq with hq|rfl
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
          simp only [List.mem_range'_1] at hj
          exact ha.2.1 _ (hAway j (by omega) (by omega))
        · exact ha.2.1 _ (hAway 1028 (by omega) (by omega)))
    rw [←middle_records w v (mF.drop 252),ez] at zM
    have regEq : regValue (w 770::wireBlock w 771 257) (run (kAdd w true) r t1).basis=
        regValue (w 770::wireBlock w 771 257) (run (inverseMiddle w) [] u).basis := by
      rw [k1.2.2,kb,f1,←k0.2.2]
      apply regValue_congr
      intro q hq
      exact zM.2 q (by simp only [List.mem_toFinset,List.mem_append]; left; rw [block770]; exact hq)
    apply State.extensionality
    · exact k1.1.trans (t1phase.trans (middle_phase w u []).symm)
    · funext q
      by_cases hq : q∈w 770::wireBlock w 771 257
      · exact (regValue_eq_iff _ _ _).mp regEq q hq
      · rw [k1.2.1 q hq]
        have hq' : q∉wireBlock w 770 258 := by rw [block770]; exact hq
        exact (t1u q hq').trans (middle_keep w u [] q hq').1.symm
  -- the known-output receiver is ready on t1
  have kRun (r : List Bool) : run (kReceiver w) r t1=run (kTail w true) r t1 := by
    rw [kReceiver,sealedProgram_run,kTail]
    have t1c : ∀q∈wireBlock w 1540 256,t1.basis q=false := by
      intro q hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hj
      rw [t1u _ (notK j (by omega) (by omega))]
      exact uc _ hq
    apply KnownOutputAdder.program_eq_mappedAdd _ _ _ _ _ (k_inputs_nd w hn)
      (k_sources_fresh w hn true) (desiredK_fresh w hn)
      (by simp [kBits_length,wireBlock_length])
      (by simp [desiredK_length,wireBlock_length]) (by simp [wireBlock_length]) t1 r t1c
    apply KnownOutputAdder.ready_of_value _ _ _ _ _
      (by simp [kBits_length,wireBlock_length]) (by simp [desiredK_length,wireBlock_length])
    have tail := kTail_spec w true t1 (r.take (measurementCount (kTail w true))) (k_inputs_nd w hn)
      (k_sources_fresh w hn true) t1c
    have kr := kAdd_run w true t1 r
    rw [M_eq r] at kr
    have tailVal : regValue (wireBlock w 771 257)
        (run (kTail w true) (r.take (measurementCount (kTail w true))) t1).basis=
        regValue (wireBlock w 771 257) (run (inverseMiddle w) [] u).basis := by
      rw [kr]
      apply regValue_congr
      intro q hq
      have ne : q≠w 770 := fun e =>
        block_not_mem w hn 770 771 257 (by omega) (by omega) (by omega) (e ▸ hq)
      simp [writeBit,ne]
    rw [desiredK_value,kBits_value,wireBlock_length]
    have lhs : regValue (wireBlock w 2 254) t1.basis=regValue (wireBlock w 2 254) u.basis := by
      apply regValue_congr
      intro q hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      simp only [List.mem_range'_1] at hj
      exact t1u _ (notK j (by omega) (by omega))
    have cm := copy_matches w hn x hx s mF ready
    rw [eu] at cm
    rw [lhs,cm,←tailVal,tail.2.2]
  -- assemble
  have ir : inverse w=hAdd w true++((kReceiver w++[.X (w 770)])++(inverseUnmiddle w++inverseBack w)) := rfl
  have um : measurementCount (inverseUnmiddle w)=0 := by
    rw [inverseUnmiddle,measurementCount_append,(rotate_counts _).2.2.2]; rfl
  have kAddEq : kAdd w true=kTail w true++[.X (w 770)] := by simp only [kAdd,kTail]
  have mk : measurementCount (kTail w true)=256 := by
    have h := (kAdd_counts w true).2
    rw [kAddEq,measurementCount_append] at h
    have z : measurementCount [Instr.X (w 770)]=0 := rfl
    omega
  have kxAll (r : List Bool) : run (kReceiver w++[.X (w 770)]) r t1=run (inverseMiddle w) [] u := by
    rw [←M_eq r,kAddEq,run_append,run_append,(kReceiver_counts w).2,mk,kRun]
  rw [ir,run_append,(hAdd_counts w true).2,ht1,run_append,kxAll,run_append,um,List.drop_zero,
    List.take_zero]
  rw [middle_cancel w u _ _ (block_nodup w hn 770 258 (by omega))
    (index_ne w hn 1028 770 (by omega) (by omega) (by omega))]
  rw [←eu]
  exact front_cancel w s _ _ (copy_inputs_nd w hn)
    (index_ne w hn 770 1028 (by omega) (by omega) (by omega))
    (index_ne w hn 1028 0 (by omega) (by omega) (by omega))


/-! Physicality, support and slots. -/

theorem kReceiver_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (kReceiver w) := by
  rw [kReceiver,sealedProgram_eq]
  apply KnownOutputAdder.program_physical
  · simp [kBits_length,wireBlock_length]
  · simp [desiredK_length,wireBlock_length]
  · simp [wireBlock_length]
  · exact k_inputs_nd w hn
  · intro b hb q hq
    apply k_sources_fresh w hn true q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
  · intro b hb q hq
    apply desiredK_fresh w hn q
    exact List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩

theorem inverse_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (inverse w) := by
  have ha := (adds_physical w hn true).1
  have kr := kReceiver_physical w hn
  have cp : GatePhysical (lowCopy w) := by
    rw [lowCopy]; exact copyRegister_physical none _ _ (copy_inputs_nd w hn) (by simp)
  have ro := (rotate_physical (wireBlock w 770 258) (block_nodup w hn _ _ (by omega))).2
  have n1 := index_ne w hn 770 1028 (by omega) (by omega) (by omega)
  have n2 := index_ne w hn 1028 0 (by omega) (by omega) (by omega)
  have n3 := index_ne w hn 1028 770 (by omega) (by omega) (by omega)
  have post : GatePhysical [.X (w 0),.CX (w 1028) (w 0),.CX (w 770) (w 1028)] := by
    simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,n1,n2]
  have mid : GatePhysical [.CX (w 1028) (w 770)] := by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,n3]
  have xg : GatePhysical [.X (w 770)] := by simp [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate]
  simp only [inverse,inverseUnmiddle,inverseBack,gatePhysical_append]
  exact ⟨ha,⟨kr,xg⟩,⟨ro,mid⟩,cp,post⟩

/-- Every target, every used carry and the carry-in of a mapped adder are touched by it. -/
theorem mappedAdd_mem : ∀ (bits : List MappedBit) (ys carry : List Wire) (cin : Wire),
    bits.length=ys.length → carry.length+1=ys.length → 0<ys.length →
    cin∈wires (mappedAdd bits ys carry cin) ∧ (∀q∈carry,q∈wires (mappedAdd bits ys carry cin)) ∧
      ∀q∈ys,q∈wires (mappedAdd bits ys carry cin)
  | [],_,_,_,hb,hc,hy => by simp at hb; omega
  | _,[],_,_,hb,hc,hy => by simp at hy
  | [b],[y],carry,cin,hb,hc,hy => by
    have c0 : carry=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
    subst c0
    simp [mappedAdd,mappedSum,wires,Instr.wires,wires_append]
  | b::b'::bits,y::y'::ys,c::cs,cin,hb,hc,hy => by
    have ih := mappedAdd_mem (b'::bits) (y'::ys) cs c (by simpa using hb) (by simpa using hc)
      (by simp)
    have sumIn : cin∈wires (mappedSum b y cin) ∧ y∈wires (mappedSum b y cin) := by
      simp [mappedSum,wires,Instr.wires,wires_append]
    simp only [mappedAdd,wires_append,Finset.mem_union]
    refine ⟨Or.inr sumIn.1,?_,?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact Or.inl (Or.inl (Or.inr ih.1))
      · exact Or.inl (Or.inl (Or.inr (ih.2.1 q hq)))
    · intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact Or.inr sumIn.2
      · exact Or.inl (Or.inl (Or.inr (ih.2.2 q hq)))
  | _::_::_,_::_::_,[],_,hb,hc,hy => by simp at hc
  | [_],_::_::_,_,_,hb,hc,hy => by simp at hb
  | _::_::_,[_],_,_,hb,hc,hy => by simp at hb

/-- Every target and the carry-in of a known-output adder are touched by it. -/
theorem koa_mem : ∀ (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire),
    bits.length=ys.length → sums.length=ys.length → carry.length+1=ys.length → 0<ys.length →
    cin∈wires (KnownOutputAdder.program bits ys sums carry cin) ∧
      ∀q∈ys,q∈wires (KnownOutputAdder.program bits ys sums carry cin)
  | [],_,_,_,_,hb,hs,hc,hy => by simp at hb; omega
  | _,_,[],_,_,hb,hs,hc,hy => by simp at hy
  | [b],[d],[y],carry,cin,hb,hs,hc,hy => by
    simp [KnownOutputAdder.program,mappedSum,wires,Instr.wires,wires_append]
  | b::b'::bits,d::d'::ds,y::y'::ys,c::cs,cin,hb,hs,hc,hy => by
    have ih := koa_mem (b'::bits) (d'::ds) (y'::ys) cs c (by simpa using hb) (by simpa using hs)
      (by simpa using hc) (by simp)
    have sumIn : cin∈wires (mappedSum b y cin) ∧ y∈wires (mappedSum b y cin) := by
      simp [mappedSum,wires,Instr.wires,wires_append]
    simp only [KnownOutputAdder.program,wires_append,Finset.mem_union]
    refine ⟨Or.inr sumIn.1,?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact Or.inr sumIn.2
    · exact Or.inl (Or.inl (Or.inr (ih.2 q hq)))
  | _::_::_,_::_::_,_::_::_,[],_,hb,hs,hc,hy => by simp at hc
  | [_],_,_::_::_,_,_,hb,hs,hc,hy => by simp at hb
  | _::_::_,_,[_],_,_,hb,hs,hc,hy => by simp at hb
  | _,[],_::_,_,_,hb,hs,hc,hy => by simp at hs
  | [_],_::_::_,[_],_,_,hb,hs,hc,hy => by simp at hs
  | _::_::_,[_],_::_::_,_,_,hb,hs,hc,hy => by simp at hs

attribute [local irreducible] wires KnownOutputAdder.program in
/-- The swapped inverse touches no wire outside the original known inverse. -/
theorem inverse_wires_sub (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    wires (inverse w)⊆wires (NativeFirstKnown.inverse w) := by
  have oldShape : NativeFirstKnown.inverse w=
      kAdd w true++(inverseUnmiddle w++(NativeFirstKnown.hReceiver w++inverseBack w)) := by
    simp only [NativeFirstKnown.inverse,List.append_assoc]
  have inOld : ∀q,(q∈wires (kAdd w true) ∨ q∈wires (inverseUnmiddle w) ∨
      q∈wires (NativeFirstKnown.hReceiver w) ∨ q∈wires (inverseBack w)) →
      q∈wires (NativeFirstKnown.inverse w) := by
    intro q hq
    rw [oldShape]
    simp only [wires_append,Finset.mem_union]
    tauto
  -- pieces of the old inverse
  have kOld := mappedAdd_mem (kBits w true) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770)
    (by simp [kBits_length,wireBlock_length]) (by simp [wireBlock_length]) (by simp [wireBlock_length])
  have kSub : wires (mappedAdd (kBits w true) (wireBlock w 771 257) (wireBlock w 1540 256) (w 770))⊆
      wires (kAdd w true) := by
    intro q hq; simp only [kAdd,wires_append,Finset.mem_union]; exact Or.inl hq
  have hOld := koa_mem (hBits w true) (NativeFirstKnown.desired w) (wireBlock w 4 253)
    (wireBlock w 1540 252) (w 1797) (by simp [hBits_length,wireBlock_length])
    (by simp [NativeFirstKnown.desired_length,wireBlock_length]) (by simp [wireBlock_length])
    (by simp [wireBlock_length])
  have hSub : wires (KnownOutputAdder.program (hBits w true) (wireBlock w 4 253)
      (NativeFirstKnown.desired w) (wireBlock w 1540 252) (w 1797))=wires (NativeFirstKnown.hReceiver w) := by
    rw [NativeFirstKnown.hReceiver,sealedProgram_eq]
  have hr := rotate_wires (wireBlock w 770 258)
  simp only [wireBlock_length,show ¬(258<2) by omega,if_false] at hr
  have midIn : w 1028∈wires (inverseUnmiddle w) ∧ w 770∈wires (inverseUnmiddle w) := by
    simp [inverseUnmiddle,wires_append,wires,Instr.wires]
  have rotIn (q : Wire) (hq : q∈wireBlock w 770 258) : q∈wires (inverseUnmiddle w) := by
    simp only [inverseUnmiddle,wires_append,Finset.mem_union]
    left; rw [hr.2]; exact List.mem_toFinset.mpr hq
  have copyIn (q : Wire) (hq : q∈wireBlock w 1 255) : q∈wires (inverseBack w) := by
    simp only [inverseBack,wires_append,Finset.mem_union]
    left
    rw [lowCopy,copyRegister_wires none _ _ (by simp [wireBlock_length])]
    simp only [show (wireBlock w 771 255).isEmpty=false from by simp [wireBlock],Bool.false_eq_true,
      if_false,Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append]
    exact Or.inr hq
  have blockIdx (a n : Nat) (q : Wire) (hq : q∈wireBlock w a n) : ∃i,a ≤ i ∧ i<a+n ∧ q=w i := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hi
    exact ⟨i,hi.1,hi.2,rfl⟩
  have mem (a n i : Nat) (h1 : a ≤ i) (h2 : i<a+n) : w i∈wireBlock w a n :=
    List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  intro q hq
  simp only [inverse,inverseUnmiddle,inverseBack,wires_append,Finset.mem_union] at hq
  rcases hq with hq|(hq|hq)|hq|hq
  · -- hAdd w true
    have sup := mappedAdd_wires_subset (hBits w true) (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
      (by simpa only [hAdd] using hq)
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at sup
    rcases sup with ((h|h)|h)|h
    · rw [hBits_wire w true q h]; exact inOld _ (Or.inr (Or.inl midIn.1))
    · obtain ⟨i,h1,h2,rfl⟩ := blockIdx 4 253 q h
      by_cases top : i=256
      · subst top
        have t := hOld.2 _ (mem 4 253 256 (by omega) (by omega))
        rw [hSub] at t
        exact inOld _ (Or.inr (Or.inr (Or.inl t)))
      · exact inOld _ (Or.inr (Or.inr (Or.inr (copyIn _ (mem 1 255 i (by omega) (by omega))))))
    · obtain ⟨i,h1,h2,rfl⟩ := blockIdx 1540 252 q h
      exact inOld _ (Or.inl (kSub (kOld.2.1 _ (mem 1540 256 i (by omega) (by omega)))))
    · subst h
      have t := hOld.1
      rw [hSub] at t
      exact inOld _ (Or.inr (Or.inr (Or.inl t)))
  · -- kReceiver
    rw [kReceiver,(sealedProgram_cost _).2.2] at hq
    have sup := KnownOutputAdder.program_support (kBits w true) (desiredK w) (wireBlock w 771 257)
      (wireBlock w 1540 256) (w 770) hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at sup
    rcases sup with (((h|h)|h)|h)|h
    · rw [kBits_wire w true q h]; exact inOld _ (Or.inr (Or.inl midIn.1))
    · rw [desiredK_wires] at h
      obtain ⟨i,h1,h2,rfl⟩ := blockIdx 2 254 q h
      exact inOld _ (Or.inr (Or.inr (Or.inr (copyIn _ (mem 1 255 i (by omega) (by omega))))))
    · obtain ⟨i,h1,h2,rfl⟩ := blockIdx 771 257 q h
      exact inOld _ (Or.inr (Or.inl (rotIn _ (mem 770 258 i (by omega) (by omega)))))
    · exact inOld _ (Or.inl (kSub (kOld.2.1 q h)))
    · subst h; exact inOld _ (Or.inr (Or.inl midIn.2))
  · -- X w 770
    simp [wires,Instr.wires] at hq
    subst hq; exact inOld _ (Or.inr (Or.inl midIn.2))
  · exact inOld _ (Or.inr (Or.inl (by simpa only [inverseUnmiddle,wires_append,Finset.mem_union] using hq)))
  · exact inOld _ (Or.inr (Or.inr (Or.inr (by simpa only [inverseBack,wires_append,Finset.mem_union] using hq))))

/-- Crude slot bound (no kernel evaluation): the piece-wise slot lemmas of the baselines. -/
theorem inverse_gateSlots_le (w : Nat → Wire) : Challenge.gateSlots (inverse w)≤10000 := by
  have hh := Baselines.mappedAdd_gateSlots_le (hBits w true) (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
  have hk := Baselines.knownAdder_gateSlots_le (kBits w true) (desiredK w) (wireBlock w 771 257)
    (wireBlock w 1540 256) (w 770)
  have hr := Baselines.rotate_gateSlots_le (wireBlock w 770 258)
  simp only [hBits_length,kBits_length,wireBlock_length] at hh hk hr
  rw [ECDSAAdd.Entrant.NativeKnownH.inverse,kReceiver,sealedProgram_eq,hAdd,inverseUnmiddle,
    inverseBack,lowCopy]
  have e1 : Challenge.gateSlots [Instr.X (w 770)]=1 := rfl
  have e2 : Challenge.gateSlots [Instr.CX (w 1028) (w 770)]=1 := rfl
  have e3 : Challenge.gateSlots [Instr.X (w 0),Instr.CX (w 1028) (w 0),Instr.CX (w 770) (w 1028)]=3 := rfl
  simp only [Challenge.gateSlots_append,Baselines.copyRegister_gateSlots,wireBlock_length,e1,e2,e3]
  omega

end ECDSAAdd.Entrant.NativeKnownH
