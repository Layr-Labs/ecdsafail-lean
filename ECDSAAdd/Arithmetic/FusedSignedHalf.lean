import ECDSAAdd.Math.FusedSignedHalf
import ECDSAAdd.Arithmetic.TrailingZeroCompare
import ECDSAAdd.Arithmetic.MeasuredMaskedAdder
import ECDSAAdd.Arithmetic.MaskedConstant
import ECDSAAdd.Arithmetic.ConditionalXor
import ECDSAAdd.Arithmetic.SignedWord
import Mathlib.Data.Nat.Bitwise
import ECDSAAdd.Arithmetic.Rotate

/-!
Actual gate capsules for the exact fused signed half. The mathematical blueprint
is attributed to the incumbent's signed-sum/fold architecture and local verified
SignedWord kernels. Complete kernel assembly is not yet asserted by this module.
-/
namespace ECDSAAdd.Arithmetic

/-- Exact output-side parity erasure. The low three bits are irrelevant because
the fixed half-threshold is divisible by eight. -/
def fusedHalfParityClear (x T carry : List Wire) (cin q : Wire) : Program :=
  compareLtMultipleEight x T carry cin q (FusedSignedHalf.halfThreshold p) ++ [.X q]

/-- The actual cleanup stream consumes the known parity, preserves every other wire,
and restores phase for every independent measurement record. -/
theorem fusedHalfParityClear_correct (x T carry : List Wire) (cin q : Wire)
    (hn : (q::cin::(x++T++carry)).Nodup) (hx : 3≤x.length)
    (hT : T.length=x.length) (hc : carry.length=x.length)
    (hK : FusedSignedHalf.halfThreshold p<2^x.length) (s : State) (m : List Bool)
    (hT0 : regValue T s.basis=0) (hc0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (hq : s.basis q=decide (FusedSignedHalf.halfThreshold p≤regValue x s.basis)) :
    (run (fusedHalfParityClear x T carry cin q) m s).phase=s.phase ∧
    (∀ w,w≠q → (run (fusedHalfParityClear x T carry cin q) m s).basis w=s.basis w) ∧
    (run (fusedHalfParityClear x T carry cin q) m s).basis q=false := by
  let progCmp := compareLtMultipleEight x T carry cin q (FusedSignedHalf.halfThreshold p)
  let t := run progCmp m s
  have hcmp := compareLtMultipleEight_correct x T carry cin q (FusedSignedHalf.halfThreshold p)
    hn hx hT hc hK FusedSignedHalf.secp_halfThreshold_multiple_eight s m hT0 hc0 hi
  have hbool : (s.basis q ^^ decide (regValue x s.basis<FusedSignedHalf.halfThreshold p))=true := by
    rw [hq]
    by_cases hh : regValue x s.basis<FusedSignedHalf.halfThreshold p
    · simp [hh,show ¬FusedSignedHalf.halfThreshold p≤regValue x s.basis by omega]
    · simp [hh,show FusedSignedHalf.halfThreshold p≤regValue x s.basis by omega]
  have hqt : t.basis q=true := hcmp.2.2.trans hbool
  rw [fusedHalfParityClear,run_append,run_take]
  change t.phase=s.phase ∧
    (∀ w,w≠q → (writeBit t.basis q (!t.basis q)) w=s.basis w) ∧
    (writeBit t.basis q (!t.basis q)) q=false
  refine ⟨hcmp.1,?_,?_⟩
  · intro w hw
    simpa [writeBit,hw] using hcmp.2.1 w hw
  · simp [writeBit,hqt]

/-- The same emitted comparator/correction stream has n-3 Toffolis and measurements. -/
theorem fusedHalfParityClear_counts (x T carry : List Wire) (cin q : Wire)
    (hT : T.length=x.length) (hc : carry.length=x.length) :
    toffoliCount (fusedHalfParityClear x T carry cin q)=x.length-3 ∧
    measurementCount (fusedHalfParityClear x T carry cin q)=x.length-3 := by
  have hh := compareLtMultipleEight_counts x T carry cin q (FusedSignedHalf.halfThreshold p) hT hc
  simp only [fusedHalfParityClear,toffoliCount_append,measurementCount_append,hh.1,hh.2,
    toffoliCount,measurementCount,Nat.add_zero]
  constructor <;> trivial
/-- Compute the raw signed guard copy and the two correction-selector ANDs.
The guard is copied before the arithmetic correction overwrites it. -/
def fusedCorrectionFlagsSeed (sg a h j l m : Wire) : Program :=
  [.CX sg j,.CCX a h l,.CCX a j m]

/-- Reset selector flags in dependency order, with exact immediate phase correction.
The guard need not still exist in the changed target word: j=b AND h. -/
def fusedCorrectionFlagsErase (b a h j l m : Wire) : Program :=
  eraseMask a [j] [m] ++ eraseMask a [h] [l] ++ eraseMask b [h] [j]

private theorem fused_erase_bit_correct (c a t : Wire) (hn : [c,a,t].Nodup)
    (s : State) (m : List Bool) (ht : s.basis t=(s.basis c && s.basis a)) :
    (run (eraseMask c [a] [t]) m s).phase=s.phase ∧
    (∀ w,w≠t → (run (eraseMask c [a] [t]) m s).basis w=s.basis w) ∧
    (run (eraseMask c [a] [t]) m s).basis t=false := by
  have hv : regValue [t] s.basis=(if s.basis c then regValue [a] s.basis else 0) := by
    rw [show regValue [t] s.basis=if s.basis t then 1 else 0 by rfl,
      show regValue [a] s.basis=if s.basis a then 1 else 0 by rfl,ht]
    cases s.basis c <;> cases s.basis a <;> rfl
  obtain ⟨hp,he,hz⟩ := eraseMask_correct c [a] [t] (by rfl) (by simpa using hn) s m hv
  exact ⟨hp,fun w hw => he w (by simpa using hw),(regValue_zero _ _).mp hz t (by simp)⟩

/-- Full raw selector seed, independent of the input phase or any measurement record. -/
theorem fusedCorrectionFlagsSeed_correct (b sg a h j l m : Wire)
    (hn : [b,sg,a,h,j,l,m].Nodup) (s : State) (record : List Bool)
    (hj : s.basis j=false) (hl : s.basis l=false) (hm : s.basis m=false)
    (hs : s.basis sg=(s.basis b && s.basis h)) :
    (run (fusedCorrectionFlagsSeed sg a h j l m) record s).phase=s.phase ∧
    (∀ w,w≠j → w≠l → w≠m →
      (run (fusedCorrectionFlagsSeed sg a h j l m) record s).basis w=s.basis w) ∧
    (run (fusedCorrectionFlagsSeed sg a h j l m) record s).basis j=(s.basis b && s.basis h) ∧
    (run (fusedCorrectionFlagsSeed sg a h j l m) record s).basis l=(s.basis a && s.basis h) ∧
    (run (fusedCorrectionFlagsSeed sg a h j l m) record s).basis m=(s.basis a && (s.basis b && s.basis h)) := by
  have hh := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at hh
  have haj : a≠j := by tauto
  have hal : a≠l := by tauto
  have hhj : h≠j := by tauto
  have hlj : l≠j := by tauto
  have hmj : m≠j := by tauto
  have hml : m≠l := by tauto
  refine ⟨rfl,?_,?_,?_,?_⟩
  · intro w hwj hwl hwm
    simp [fusedCorrectionFlagsSeed,run,writeBit,hwj,hwl,hwm]
  · simp [fusedCorrectionFlagsSeed,run,writeBit,hj,hs,Ne.symm hlj,Ne.symm hmj]
  · simp [fusedCorrectionFlagsSeed,run,writeBit,hj,hl,haj,hhj,hlj,Ne.symm hml]
  · simp [fusedCorrectionFlagsSeed,run,writeBit,hj,hm,haj,hal,hs,hml,hmj,Ne.symm hlj]

/-- Every selector and guard-copy bit is cleaned, while all other wires and phase are restored.
This remains correct after the original signed guard bit has been overwritten. -/
theorem fusedCorrectionFlagsErase_correct (b a h j l m : Wire)
    (hn : [b,a,h,j,l,m].Nodup) (s : State) (record : List Bool)
    (hj : s.basis j=(s.basis b && s.basis h))
    (hl : s.basis l=(s.basis a && s.basis h))
    (hm : s.basis m=(s.basis a && s.basis j)) :
    (run (fusedCorrectionFlagsErase b a h j l m) record s).phase=s.phase ∧
    (∀ w,w≠j → w≠l → w≠m →
      (run (fusedCorrectionFlagsErase b a h j l m) record s).basis w=s.basis w) ∧
    (run (fusedCorrectionFlagsErase b a h j l m) record s).basis j=false ∧
    (run (fusedCorrectionFlagsErase b a h j l m) record s).basis l=false ∧
    (run (fusedCorrectionFlagsErase b a h j l m) record s).basis m=false := by
  have hh := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at hh
  have haM : a≠m := by tauto
  have hhM : h≠m := by tauto
  have hbM : b≠m := by tauto
  have hlM : l≠m := by tauto
  have haL : a≠l := by tauto
  have hhL : h≠l := by tauto
  have hbL : b≠l := by tauto
  have hjL : j≠l := by tauto
  have hjM : j≠m := by tauto
  have hmL : m≠l := Ne.symm hlM
  have hmJ : m≠j := Ne.symm hjM
  have hlJ : l≠j := Ne.symm hjL
  have h1n : [a,j,m].Nodup := by simp; tauto
  have h2n : [a,h,l].Nodup := by simp; tauto
  have h3n : [b,h,j].Nodup := by simp; tauto
  let r1 := record
  let r2 := record.drop 1
  let r3 := record.drop 2
  let s1 := run (eraseMask a [j] [m]) r1 s
  let s2 := run (eraseMask a [h] [l]) r2 s1
  have f1 := fused_erase_bit_correct a j m h1n s r1 hm
  have hv2 : s1.basis l=(s1.basis a && s1.basis h) := by
    rw [f1.2.1 l hlM,f1.2.1 a haM,f1.2.1 h hhM]
    exact hl
  have f2 := fused_erase_bit_correct a h l h2n s1 r2 hv2
  have hv3 : s2.basis j=(s2.basis b && s2.basis h) := by
    rw [f2.2.1 j hjL,f2.2.1 b hbL,f2.2.1 h hhL,
      f1.2.1 j hjM,f1.2.1 b hbM,f1.2.1 h hhM]
    exact hj
  have f3 := fused_erase_bit_correct b h j h3n s2 r3 hv3
  have hc1 : measurementCount (eraseMask a [j] [m])=1 := by rfl
  have hc2 : measurementCount (eraseMask a [h] [l])=1 := by rfl
  rw [fusedCorrectionFlagsErase,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,hc1,hc2]
  change (run (eraseMask b [h] [j]) r3 s2).phase=s.phase ∧ _
  refine ⟨f3.1.trans (f2.1.trans f1.1),?_,f3.2.2,?_,?_⟩
  · intro w hwj hwl hwm
    exact (f3.2.1 w hwj).trans ((f2.2.1 w hwl).trans (f1.2.1 w hwm))
  · exact (f3.2.1 l hlJ).trans f2.2.2
  · exact (f3.2.1 m hmJ).trans ((f2.2.1 m hmL).trans f1.2.2)

/-- Actual selector gate streams cost two Toffolis and three cleanup measurements. -/
theorem fusedCorrectionFlags_counts (b sg a h j l m : Wire) :
    toffoliCount (fusedCorrectionFlagsSeed sg a h j l m)=2 ∧
    measurementCount (fusedCorrectionFlagsSeed sg a h j l m)=0 ∧
    toffoliCount (fusedCorrectionFlagsErase b a h j l m)=0 ∧
    measurementCount (fusedCorrectionFlagsErase b a h j l m)=3 := by
  simp [fusedCorrectionFlagsSeed,fusedCorrectionFlagsErase,eraseMask,toffoliCount,measurementCount]

/-- Clifford load of the correction word. The sign/selector XORs are distributed
through the three fixed words; no nonlinear word mask is computed. -/
def fusedCorrectionWordLoad (a j l m : Wire) (C : List Wire) (P D N : Nat) : Program :=
  maskedConstant a C P ++ maskedConstant l C P ++ maskedConstant m C P ++
  maskedConstant j C D ++ maskedConstant m C D ++ maskedConstant l C N ++ maskedConstant m C N

def fusedCorrectionWordValue (A J L M : Bool) (P D N : Nat) : Nat :=
  ((((((if A then P else 0) ^^^ (if L then P else 0)) ^^^ (if M then P else 0)) ^^^
    (if J then D else 0)) ^^^ (if M then D else 0)) ^^^ (if L then N else 0)) ^^^ (if M then N else 0)

/-- The distributed Clifford XOR load equals the intended three selector words. -/
theorem fusedCorrectionWordValue_selector (A J L M : Bool) (P D N : Nat) :
    fusedCorrectionWordValue A J L M P D N=
      ((if (A ^^ L ^^ M) then P else 0) ^^^ (if (J ^^ M) then D else 0)) ^^^
        (if (L ^^ M) then N else 0) := by
  cases A <;> cases J <;> cases L <;> cases M <;>
    simp [fusedCorrectionWordValue,Nat.xor_comm,Nat.xor_left_comm]

private def FusedWordFrame (C : List Wire) (base : BasisState) (V : Nat) (s : BasisState) : Prop :=
  regValue C s=V ∧ ∀ w,w∉C → s w=base w

/-- Loading or unloading preserves all selector inputs, all outside words and phase. -/
theorem fusedCorrectionWordLoad_correct (a j l m : Wire) (C : List Wire) (P D N : Nat)
    (hn : ([a,j,l,m]++C).Nodup) (hP : P<2^C.length) (hD : D<2^C.length) (hN : N<2^C.length)
    (s : State) (record : List Bool) :
    (run (fusedCorrectionWordLoad a j l m C P D N) record s).phase=s.phase ∧
    (∀ w,w∉C → (run (fusedCorrectionWordLoad a j l m C P D N) record s).basis w=s.basis w) ∧
    regValue C (run (fusedCorrectionWordLoad a j l m C P D N) record s).basis=
      regValue C s.basis ^^^ fusedCorrectionWordValue (s.basis a) (s.basis j) (s.basis l) (s.basis m) P D N := by
  have hnd := List.nodup_append'.mp hn
  have hc (c : Wire) (hcm : c∈[a,j,l,m]) : c∉C := List.disjoint_left.mp hnd.2.2 hcm
  let F := FusedWordFrame C s.basis
  have stage (c : Wire) (K V : Nat) (hcm : c∈[a,j,l,m]) (hK : K<2^C.length) :
      Triple (F V) (maskedConstant c C K) (F (V ^^^ (if s.basis c then K else 0))) := by
    intro st ms h
    obtain ⟨hf,he,hv⟩ := maskedConstant_correct c C K hnd.2.1 (hc c hcm) hK st ms
    exact ⟨hf,by simpa only [h.1,h.2 c (hc c hcm)] using hv,
      fun w hw => (he w hw).trans (h.2 w hw)⟩
  let V := regValue C s.basis
  let U := if s.basis a then P else 0
  let Vp := if s.basis l then P else 0
  let Wp := if s.basis m then P else 0
  let Ud := if s.basis j then D else 0
  let Vd := if s.basis m then D else 0
  let Un := if s.basis l then N else 0
  let Vn := if s.basis m then N else 0
  have h1 := stage a P V (by simp) hP
  have h2 := stage l P (V ^^^ U) (by simp) hP
  have h3 := stage m P ((V ^^^ U) ^^^ Vp) (by simp) hP
  have h4 := stage j D (((V ^^^ U) ^^^ Vp) ^^^ Wp) (by simp) hD
  have h5 := stage m D ((((V ^^^ U) ^^^ Vp) ^^^ Wp) ^^^ Ud) (by simp) hD
  have h6 := stage l N (((((V ^^^ U) ^^^ Vp) ^^^ Wp) ^^^ Ud) ^^^ Vd) (by simp) hN
  have h7 := stage m N ((((((V ^^^ U) ^^^ Vp) ^^^ Wp) ^^^ Ud) ^^^ Vd) ^^^ Un) (by simp) hN
  have hall := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7
  have hcircuit : Triple (F V) (fusedCorrectionWordLoad a j l m C P D N)
      (F (((((((V ^^^ U) ^^^ Vp) ^^^ Wp) ^^^ Ud) ^^^ Vd) ^^^ Un) ^^^ Vn)) := by
    simpa only [fusedCorrectionWordLoad,List.append_assoc] using hall
  obtain ⟨hf,hv⟩ := hcircuit s record ⟨rfl,fun _ _ => rfl⟩
  refine ⟨hf,hv.2,?_⟩
  simpa only [FusedWordFrame,fusedCorrectionWordValue,V,U,Vp,Wp,Ud,Vd,Un,Vn,Nat.xor_assoc] using hv.1

/-- The actual fixed-word selector load has no Toffoli or measurement cost. -/
theorem fusedCorrectionWordLoad_counts (a j l m : Wire) (C : List Wire) (P D N : Nat) :
    toffoliCount (fusedCorrectionWordLoad a j l m C P D N)=0 ∧
    measurementCount (fusedCorrectionWordLoad a j l m C P D N)=0 := by
  simp only [fusedCorrectionWordLoad,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts a C P).1,(maskedConstant_counts a C P).2,
    (maskedConstant_counts l C P).1,(maskedConstant_counts l C P).2,
    (maskedConstant_counts m C P).1,(maskedConstant_counts m C P).2,
    (maskedConstant_counts j C D).1,(maskedConstant_counts j C D).2,
    (maskedConstant_counts m C D).1,(maskedConstant_counts m C D).2,
    (maskedConstant_counts l C N).1,(maskedConstant_counts l C N).2,
    (maskedConstant_counts m C N).1,(maskedConstant_counts m C N).2]
  trivial

/-- One full-width correction addition, with its source word Clifford-cleared afterwards. -/
def fusedCorrectionApply (a j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P D N : Nat) : Program :=
  fusedCorrectionWordLoad a j l m C P D N ++ addInPlace C R carry cin ++
    fusedCorrectionWordLoad a j l m C P D N

/-- Exact modular-word correction with only the target word changed. -/
theorem fusedCorrectionApply_correct (a j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P D N : Nat) (hn : (cin::([a,j,l,m]++C++R++carry)).Nodup)
    (hCR : C.length=R.length) (hcarry : carry.length+1=R.length)
    (hP : P<2^C.length) (hD : D<2^C.length) (hN : N<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (fusedCorrectionApply a j l m C R carry cin P D N) record s).phase=s.phase ∧
    (∀ w,w∉R → (run (fusedCorrectionApply a j l m C R carry cin P D N) record s).basis w=s.basis w) ∧
    regValue R (run (fusedCorrectionApply a j l m C R carry cin P D N) record s).basis=
      (regValue R s.basis+fusedCorrectionWordValue (s.basis a) (s.basis j) (s.basis l) (s.basis m) P D N)%2^R.length := by
  have hload : ([a,j,l,m]++C).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at hh ⊢
    omega
  have hadd : (cin::(C++R++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at hh ⊢
    omega
  have hpair := List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hadd).2).1
  have hd : C.Disjoint R := hpair.2.2
  have outside (w : Wire) (hw : w∈[a,j,l,m]++carry++[cin]) : w∉C ∧ w∉R := by
    have hh := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ho
    constructor <;> intro hm <;> have hh' := List.count_pos_iff.mpr hm <;> omega
  let F := fusedCorrectionWordValue (s.basis a) (s.basis j) (s.basis l) (s.basis m) P D N
  let Q := PairFrame C R s.basis
  have reads (A Z : Nat) (st : BasisState) (h : Q A Z st) :
      regValue carry st=0 ∧ st cin=false ∧
      fusedCorrectionWordValue (st a) (st j) (st l) (st m) P D N=F := by
    have he (w : Wire) (hw : w∈[a,j,l,m]++carry++[cin]) :=
      h.2.2 w (outside w hw).1 (outside w hw).2
    refine ⟨(regValue_congr _ _ _ (fun w hw => he w (by simp [hw]))).trans hk0,
      (he cin (by simp)).trans hi,?_⟩
    rw [he a (by simp),he j (by simp),he l (by simp),he m (by simp)]
  have load (A Z : Nat) : Triple (Q A Z) (fusedCorrectionWordLoad a j l m C P D N) (Q (A^^^F) Z) := by
    intro st ms h
    obtain ⟨hf,he,hv⟩ := fusedCorrectionWordLoad_correct a j l m C P D N hload hP hD hN st ms
    exact ⟨hf,PairFrame.update_temp C R _ _ _ A Z _ hd h he
      (by simpa only [h.1,(reads A Z st.basis h).2.2] using hv)⟩
  have add (Z : Nat) : Triple (Q F Z) (addInPlace C R carry cin) (Q F ((Z+F)%2^R.length)) := by
    intro st ms h
    have hr := reads F Z st.basis h
    obtain ⟨hf,he,hv⟩ := addInPlace_correct C R carry cin hadd hCR hcarry st ms
      ((regValue_zero _ _).mp hr.1)
    exact ⟨hf,PairFrame.update_dst C R _ _ _ F Z _ hd h he
      (by simpa only [h.1,h.2.1,hr.2.1,Bool.toNat_false,Nat.add_zero,Nat.zero_add,Nat.add_comm] using hv)⟩
  let Z := regValue R s.basis
  have h1 := load 0 Z
  have h2 := add Z
  have h3 := load F ((Z+F)%2^R.length)
  simp only [Nat.zero_xor] at h1
  simp only [Nat.xor_self] at h3
  have hprog : Triple (Q 0 Z) (fusedCorrectionApply a j l m C R carry cin P D N)
      (Q 0 ((Z+F)%2^R.length)) := by
    simpa only [fusedCorrectionApply,List.append_assoc] using (h1.seq h2).seq h3
  obtain ⟨hf,hv⟩ := hprog s record ⟨hC0,rfl,fun _ _ _ => rfl⟩
  refine ⟨hf,?_,hv.2.1⟩
  intro w hw
  by_cases hc : w∈C
  · exact (regValue_eq_iff _ _ _).mp (hv.1.trans hC0.symm) w hc
  · exact hv.2.2 w hc hw

/-- Exact cost of the same one-addition correction stream. -/
theorem fusedCorrectionApply_counts (a j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P D N : Nat) (hCR : C.length=R.length) (hcarry : carry.length+1=R.length) :
    toffoliCount (fusedCorrectionApply a j l m C R carry cin P D N)=R.length-1 ∧
    measurementCount (fusedCorrectionApply a j l m C R carry cin P D N)=R.length-1 := by
  have hl := fusedCorrectionWordLoad_counts a j l m C P D N
  have ha := addInPlace_counts C R carry cin hCR hcarry
  simp only [fusedCorrectionApply,toffoliCount_append,measurementCount_append,
    hl.1,hl.2,ha.1,ha.2,Nat.zero_add,Nat.add_zero]
  trivial

/-- The unsigned machine comparison recovers the mathematical reduction bit.
Two full guard bits keep every valid positive sum below the machine modulus. -/
theorem fusedRawReduction (w p X Y : Nat) (b : Bool)
    (hX : X<p) (hY : Y<p) (hwidth : 2*p<2^w) :
    (!decide (signedWordValue w b Y X<p))=
      FusedSignedHalf.reduction p (FusedSignedHalf.signedSum b X Y) := by
  cases b
  · have hsum : X+Y<2^w := by omega
    rw [show signedWordValue w false Y X=X+Y by simp [signedWordValue,Nat.mod_eq_of_lt hsum]]
    change (!decide (X+Y<p))=decide (¬(0≤(X:Int)+(Y:Int) ∧ (X:Int)+(Y:Int)<(p:Int)))
    rw [←decide_not]
    apply decide_eq_decide.mpr
    omega
  · by_cases hxy : Y≤X
    · have hsmall : X-Y<2^w := by omega
      have hr : signedWordValue w true Y X=X-Y := by
        simp only [signedWordValue,if_true]
        rw [show X+2^w-Y=(X-Y)+2^w by omega,Nat.add_mod]
        simp [Nat.mod_eq_of_lt hsmall]
      rw [hr]
      change (!decide (X-Y<p))=decide (¬(0≤(X:Int)-(Y:Int) ∧ (X:Int)-(Y:Int)<(p:Int)))
      rw [←decide_not]
      apply decide_eq_decide.mpr
      omega
    · have hsmall : X+2^w-Y<2^w := by omega
      have hr : signedWordValue w true Y X=X+2^w-Y := by
        simp [signedWordValue,Nat.mod_eq_of_lt hsmall]
      rw [hr]
      change (!decide (X+2^w-Y<p))=decide (¬(0≤(X:Int)-(Y:Int) ∧ (X:Int)-(Y:Int)<(p:Int)))
      rw [←decide_not]
      apply decide_eq_decide.mpr
      omega

private theorem fused_const_compare_correct (x C carry : List Wire) (cin h : Wire)
    (K : Nat) (hn : (h::cin::(x++C++carry)).Nodup)
    (hC : x.length=C.length) (hk : carry.length=C.length) (hK : K<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false) :
    (run (compareLtConst none x C carry cin h K) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (compareLtConst none x C carry cin h K) record s).basis w=s.basis w) ∧
    (run (compareLtConst none x C carry cin h K) record s).basis h=
      (s.basis h ^^ decide (regValue x s.basis<K)) := by
  obtain ⟨hf,hv⟩ := compareLtConst_spec x C carry cin h hn hC hk K hK
    (regValue x s.basis) (s.basis h) s record ⟨⟨⟨⟨rfl,hC0⟩,hk0⟩,hi⟩,rfl⟩
  simp only [Holds.holds] at hv
  refine ⟨hf,?_,hv.2⟩
  intro w hw
  by_cases hx : w∈x
  · exact (regValue_eq_iff _ _ _).mp hv.1.1.1.1 w hx
  by_cases hc : w∈C
  · exact (regValue_eq_iff _ _ _).mp (hv.1.1.1.2.trans hC0.symm) w hc
  by_cases hk' : w∈carry
  · exact (regValue_eq_iff _ _ _).mp (hv.1.1.2.trans hk0.symm) w hk'
  by_cases hi' : w=cin
  · subst w; exact hv.1.2.trans hi.symm
  apply run_preserves_outside
  rw [(compareLt_wires none x C carry cin h hC hk).2 K]
  simp [hw,hx,hc,hk',hi']

/-- Full signed raw addition and full-width normalization comparison.
The sign control doubles as the raw addition's carry input. -/
def fusedRawNormalize (b h : Wire) (Y R C addCarry compareCarry : List Wire)
    (cin : Wire) (P : Nat) : Program :=
  signedAdd b Y R addCarry ++ compareLtConst none R C compareCarry cin h P ++ [.X h]

/-- All-record machine capsule: only the target and the freshly computed reduction bit change. -/
private theorem fusedRawNormalize_with_frames_correct (b h : Wire) (Y R C addCarry compareCarry : List Wire)
    (cin : Wire) (P : Nat)
    (hnadd : (b::(Y++R++addCarry)).Nodup)
    (hncmp : (h::cin::(R++C++compareCarry)).Nodup)
    (hnR : ∀ w,w∈[h,cin]++C++compareCarry → w∉R)
    (hYR : Y.length=R.length) (hCR : C.length=R.length)
    (hadd : addCarry.length+1=R.length) (hcmp : compareCarry.length=R.length)
    (hP : P<2^R.length) (s : State) (record : List Bool)
    (hC0 : regValue C s.basis=0) (ha0 : regValue addCarry s.basis=0)
    (hk0 : regValue compareCarry s.basis=0) (hi : s.basis cin=false) (hh : s.basis h=false) :
    (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).phase=s.phase ∧
    (∀ w,w∉R → w≠h →
      (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis w=s.basis w) ∧
    regValue R (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis=
      signedWordValue R.length (s.basis b) (regValue Y s.basis) (regValue R s.basis) ∧
    (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis h=
      !decide (signedWordValue R.length (s.basis b) (regValue Y s.basis) (regValue R s.basis)<P) := by
  have hnRh (w : Wire) (hw : w∈R) : w≠h := by
    intro he
    subst w
    exact hnR h (by simp) hw
  let raw := signedWordValue R.length (s.basis b) (regValue Y s.basis) (regValue R s.basis)
  let st := run (signedAdd b Y R addCarry) record s
  have hs := signedAdd_spec b Y R addCarry hnadd hYR hadd (s.basis b)
    (regValue Y s.basis) (regValue R s.basis) s record ⟨⟨⟨rfl,rfl⟩,rfl⟩,ha0⟩
  have he (w : Wire) (hw : w∉R) : st.basis w=s.basis w :=
    (signedWord_frame b Y R addCarry hnadd hYR hadd (s.basis b)
      (regValue Y s.basis) (regValue R s.basis) s record rfl rfl rfl ha0 w hw).1
  have hsR : regValue R st.basis=raw := hs.2.1.2
  have htC : regValue C st.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => he w (hnR w (by simp [hw])))).trans hC0
  have htk : regValue compareCarry st.basis=0 :=
    (regValue_congr _ _ _ (fun w hw => he w (hnR w (by simp [hw])))).trans hk0
  have hti : st.basis cin=false := (he cin (hnR cin (by simp))).trans hi
  have hth : st.basis h=false := (he h (hnR h (by simp))).trans hh
  let r2 := record.drop (measurementCount (signedAdd b Y R addCarry))
  let ct := run (compareLtConst none R C compareCarry cin h P) r2 st
  have hc := fused_const_compare_correct R C compareCarry cin h P hncmp hCR.symm
    (by omega) (by simpa only [hCR] using hP) st r2 htC htk hti
  have hct : ct.basis h=decide (raw<P) := by simpa only [hth,hsR,Bool.false_xor] using hc.2.2
  rw [fusedRawNormalize,run_append,run_take,run_append,run_take]
  change ct.phase=s.phase ∧
    (∀ w,w∉R → w≠h → (writeBit ct.basis h (!ct.basis h)) w=s.basis w) ∧
    regValue R (writeBit ct.basis h (!ct.basis h))=raw ∧
    (writeBit ct.basis h (!ct.basis h)) h= !decide (raw<P)
  refine ⟨hc.1.trans hs.1,?_,?_,?_⟩
  · intro w hwR hwh
    simpa only [writeBit,Function.update_of_ne hwh] using (hc.2.1 w hwh).trans (he w hwR)
  · exact (regValue_congr _ _ _ (fun w hw => by
      simp only [writeBit,Function.update_of_ne (hnRh w hw)]
      exact hc.2.1 w (hnRh w hw))).trans hsR
  · simp [writeBit,hct]

theorem fusedRawNormalize_correct (b h : Wire) (Y R C addCarry compareCarry : List Wire)
    (cin : Wire) (P : Nat)
    (hn : ([b,h,cin]++Y++R++C++addCarry++compareCarry).Nodup)
    (hYR : Y.length=R.length) (hCR : C.length=R.length)
    (hadd : addCarry.length+1=R.length) (hcmp : compareCarry.length=R.length)
    (hP : P<2^R.length) (s : State) (record : List Bool)
    (hC0 : regValue C s.basis=0) (ha0 : regValue addCarry s.basis=0)
    (hk0 : regValue compareCarry s.basis=0) (hi : s.basis cin=false) (hh : s.basis h=false) :
    (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).phase=s.phase ∧
    (∀ w,w∉R → w≠h →
      (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis w=s.basis w) ∧
    regValue R (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis=
      signedWordValue R.length (s.basis b) (regValue Y s.basis) (regValue R s.basis) ∧
    (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis h=
      !decide (signedWordValue R.length (s.basis b) (regValue Y s.basis) (regValue R s.basis)<P) := by
  have hnadd : (b::(Y++R++addCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hncmp : (h::cin::(R++C++compareCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hnR (w : Wire) (hw : w∈[h,cin]++C++compareCarry) : w∉R := by
    intro hm
    have hc := List.nodup_iff_count.mp hn w
    have hwc := List.count_pos_iff.mpr hw
    have hmc := List.count_pos_iff.mpr hm
    simp only [List.count_cons,List.count_append,List.count_nil] at hc hwc
    omega
  exact fusedRawNormalize_with_frames_correct b h Y R C addCarry compareCarry cin P
    hnadd hncmp hnR hYR hCR hadd hcmp hP s record hC0 ha0 hk0 hi hh

/-- Exact alias-safe raw capsule; the addition carry may be a prefix of the full comparison carry. -/
theorem fusedRawNormalize_shared_correct (b h : Wire) (Y R C addCarry compareCarry : List Wire)
    (cin : Wire) (P : Nat)
    (hn : ([b,h,cin]++Y++R++C++compareCarry).Nodup)
    (hsub : addCarry.Sublist compareCarry)
    (hYR : Y.length=R.length) (hCR : C.length=R.length)
    (hadd : addCarry.length+1=R.length) (hcmp : compareCarry.length=R.length)
    (hP : P<2^R.length) (s : State) (record : List Bool)
    (hC0 : regValue C s.basis=0) (ha0 : regValue addCarry s.basis=0)
    (hk0 : regValue compareCarry s.basis=0) (hi : s.basis cin=false) (hh : s.basis h=false) :
    (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).phase=s.phase ∧
    (∀ w,w∉R → w≠h →
      (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis w=s.basis w) ∧
    regValue R (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis=
      signedWordValue R.length (s.basis b) (regValue Y s.basis) (regValue R s.basis) ∧
    (run (fusedRawNormalize b h Y R C addCarry compareCarry cin P) record s).basis h=
      !decide (signedWordValue R.length (s.basis b) (regValue Y s.basis) (regValue R s.basis)<P) := by
  have hnadd : (b::(Y++R++addCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    have hcount := hsub.count_le w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hncmp : (h::cin::(R++C++compareCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hnR (w : Wire) (hw : w∈[h,cin]++C++compareCarry) : w∉R := by
    intro hm
    have hc := List.nodup_iff_count.mp hn w
    have hwc := List.count_pos_iff.mpr hw
    have hmc := List.count_pos_iff.mpr hm
    simp only [List.count_cons,List.count_append,List.count_nil] at hc hwc
    omega
  exact fusedRawNormalize_with_frames_correct b h Y R C addCarry compareCarry cin P
    hnadd hncmp hnR hYR hCR hadd hcmp hP s record hC0 ha0 hk0 hi hh

/-- Both raw addition and normalization compare use every physical bit. -/
theorem fusedRawNormalize_counts (b h : Wire) (Y R C addCarry compareCarry : List Wire)
    (cin : Wire) (P : Nat) (hYR : Y.length=R.length) (hCR : C.length=R.length)
    (hadd : addCarry.length+1=R.length) (hcmp : compareCarry.length=R.length) :
    toffoliCount (fusedRawNormalize b h Y R C addCarry compareCarry cin P)=2*R.length-1 ∧
    measurementCount (fusedRawNormalize b h Y R C addCarry compareCarry cin P)=2*R.length-1 := by
  have hs := signedWord_counts b Y R addCarry hYR hadd
  have hc := (compareLt_counts none R C compareCarry cin h hCR.symm (by omega)).2.2 P
  constructor
  · rw [fusedRawNormalize,toffoliCount_append,toffoliCount_append,hs.1,hc.1]
    simp only [Option.isSome,Bool.false_eq_true,if_false,toffoliCount,Nat.add_zero,hCR]
    omega
  · rw [fusedRawNormalize,measurementCount_append,measurementCount_append,hs.2.1,hc.2]
    simp only [measurementCount,Nat.add_zero,hCR]
    omega

/-- Exact two's-complement correction word. The only added machine modulus is
for the -p selector; it disappears under the full word addition. -/
theorem fusedCorrectionWordValue_integer (p M : Nat) (hp : p≤M) (b a h : Bool) :
    (fusedCorrectionWordValue a (b&&h) (a&&h) (a&&(b&&h)) p (2*p) (M-p) : Int)=
      (FusedSignedHalf.bit (a^^h)+(if b then FusedSignedHalf.bit h else -FusedSignedHalf.bit h))*(p:Int)+
        FusedSignedHalf.bit ((a&&h)^^(a&&(b&&h)))*(M:Int) := by
  cases b <;> cases a <;> cases h <;>
    simp [fusedCorrectionWordValue,FusedSignedHalf.bit,Nat.cast_sub hp]
  omega

/-- The actual machine correction yields the proved even positive lift.
This bridge pays for the full signed word, including negative raw sums. -/
theorem fusedCorrectionMachine (w p X Y : Nat) (b : Bool)
    (hp : p%2=1) (hX : X<p) (hY : Y<p) (hwidth : 2*p<2^w) :
    (signedWordValue w b Y X+
      fusedCorrectionWordValue (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y))
        (b&&FusedSignedHalf.reduction p (FusedSignedHalf.signedSum b X Y))
        (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y)&&
          FusedSignedHalf.reduction p (FusedSignedHalf.signedSum b X Y))
        (FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y)&&
          (b&&FusedSignedHalf.reduction p (FusedSignedHalf.signedSum b X Y)))
        p (2*p) (2^w-p))%2^w=
      (FusedSignedHalf.evenLift p b (FusedSignedHalf.signedSum b X Y)).toNat := by
  let S := FusedSignedHalf.signedSum b X Y
  let H := FusedSignedHalf.reduction p S
  let A := FusedSignedHalf.parity S
  let F := fusedCorrectionWordValue A (b&&H) (A&&H) (A&&(b&&H)) p (2*p) (2^w-p)
  let raw := signedWordValue w b Y X
  let E := FusedSignedHalf.evenLift p b S
  have hf := fusedCorrectionWordValue_integer p (2^w) (by omega) b A H
  change (F:Int)=(FusedSignedHalf.bit (A^^H)+
    (if b then FusedSignedHalf.bit H else -FusedSignedHalf.bit H))*(p:Int)+
    FusedSignedHalf.bit ((A&&H)^^(A&&(b&&H)))*(2^w:Nat) at hf
  have hraw := signedWordValue_emod w b Y X (by omega)
  have hs : signedIntegerValue b (Y:Int) (X:Int)=S := by
    cases b <;> simp [signedIntegerValue,S,FusedSignedHalf.signedSum]
    ring
  rw [hs] at hraw
  change (raw:Int)%(2^w:Nat)=S%(2^w:Nat) at hraw
  have he := FusedSignedHalf.evenLift_spec p b S hp (FusedSignedHalf.signedSum_domain p X Y b hX hY)
  change 0≤E ∧ E<2*(p:Int) ∧ E%2=0 at he
  have hE : E<(2^w:Nat) := by omega
  have hzero : (FusedSignedHalf.bit ((A&&H)^^(A&&(b&&H)))*((2^w:Nat):Int))%(2^w:Nat)=0 := by
    rw [Int.mul_emod,Int.emod_self,mul_zero,Int.zero_emod]
  have hF : (F:Int)%(2^w:Nat)=
      ((FusedSignedHalf.bit (A^^H)+(if b then FusedSignedHalf.bit H else -FusedSignedHalf.bit H))*(p:Int))%(2^w:Nat) := by
    rw [hf,Int.add_emod,hzero,add_zero,Int.emod_emod]
  have hcong : ((raw:Int)+(F:Int))%(2^w:Nat)=E%(2^w:Nat) := by
    rw [Int.add_emod,hraw,hF]
    exact (Int.add_emod _ _ _).symm
  rw [Int.emod_eq_of_lt he.1 hE] at hcong
  have hm : (((raw+F)%2^w:Nat):Int)=E := by
    rw [Int.natCast_emod,Nat.cast_add]
    exact hcong
  change (raw+F)%2^w=E.toNat
  omega

/-- Temporary Clifford change of the threshold AND inputs. The same capsule
restores both q and the source parity bit after the AND is computed/erased. -/
def fusedThresholdToggle (b q e : Wire) : Program := [.CX b e,.X q]

private theorem fusedThresholdToggle_correct (b q e : Wire) (hn : [b,q,e].Nodup)
    (s : State) (record : List Bool) :
    (run (fusedThresholdToggle b q e) record s).phase=s.phase ∧
    (∀ w,w≠q → w≠e → (run (fusedThresholdToggle b q e) record s).basis w=s.basis w) ∧
    (run (fusedThresholdToggle b q e) record s).basis q= !s.basis q ∧
    (run (fusedThresholdToggle b q e) record s).basis e=(s.basis e ^^ s.basis b) := by
  have hh := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at hh
  have hqe : q≠e := by tauto
  refine ⟨rfl,?_,?_,?_⟩
  · intro w hwq hwe
    simp [fusedThresholdToggle,run,writeBit,hwq,hwe]
  · simp [fusedThresholdToggle,run,writeBit,hqe]
  · simp [fusedThresholdToggle,run,writeBit,Ne.symm hqe]

/-- Exact two-AND threshold selectors: t=b AND q and d=NOT q AND(e XOR b).
Source parity and sign/parity controls are restored immediately. -/
def fusedThresholdFlagsSeed (b q e t d : Wire) : Program :=
  [.CCX b q t] ++ fusedThresholdToggle b q e ++ [.CCX q e d] ++ fusedThresholdToggle b q e

/-- The cleanup computes the same exact AND inputs, measures the flags and
applies immediate phase corrections before restoring those inputs. -/
def fusedThresholdFlagsErase (b q e t d : Wire) : Program :=
  eraseMask b [q] [t] ++ fusedThresholdToggle b q e ++
    eraseMask q [e] [d] ++ fusedThresholdToggle b q e

/-- Seed correctness for every basis state and arbitrary incoming phase. -/
theorem fusedThresholdFlagsSeed_correct (b q e t d : Wire) (hn : [b,q,e,t,d].Nodup)
    (s : State) (record : List Bool) (ht : s.basis t=false) (hd : s.basis d=false) :
    (run (fusedThresholdFlagsSeed b q e t d) record s).phase=s.phase ∧
    (∀ w,w≠t → w≠d → (run (fusedThresholdFlagsSeed b q e t d) record s).basis w=s.basis w) ∧
    (run (fusedThresholdFlagsSeed b q e t d) record s).basis t=(s.basis b && s.basis q) ∧
    (run (fusedThresholdFlagsSeed b q e t d) record s).basis d=(!s.basis q && (s.basis e ^^ s.basis b)) := by
  have hh := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at hh
  have hbq : b≠q := by tauto
  have hqb : q≠b := Ne.symm hbq
  have hbe : b≠e := by tauto
  have heb : e≠b := Ne.symm hbe
  have hbt : b≠t := by tauto
  have htb : t≠b := Ne.symm hbt
  have hbd : b≠d := by tauto
  have hdb : d≠b := Ne.symm hbd
  have hqe : q≠e := by tauto
  have heq : e≠q := Ne.symm hqe
  have hqt : q≠t := by tauto
  have htq : t≠q := Ne.symm hqt
  have hqd : q≠d := by tauto
  have hdq : d≠q := Ne.symm hqd
  have het : e≠t := by tauto
  have hte : t≠e := Ne.symm het
  have hed : e≠d := by tauto
  have hde : d≠e := Ne.symm hed
  have htd : t≠d := by tauto
  have hdt : d≠t := Ne.symm htd
  refine ⟨rfl,?_,?_,?_⟩
  · intro w hwt hwd
    by_cases hwq : w=q
    · subst w
      simp_all [fusedThresholdFlagsSeed,fusedThresholdToggle,run,writeBit]
    by_cases hwe : w=e
    · subst w
      simp_all [fusedThresholdFlagsSeed,fusedThresholdToggle,run,writeBit]
    simp_all [fusedThresholdFlagsSeed,fusedThresholdToggle,run,writeBit]
  · simp_all [fusedThresholdFlagsSeed,fusedThresholdToggle,run,writeBit]
  · simp_all [fusedThresholdFlagsSeed,fusedThresholdToggle,run,writeBit]

/-- Complete threshold flag cleanup; all other bits, including source parity,
are restored and phase is preserved for every independent measurement record. -/
theorem fusedThresholdFlagsErase_correct (b q e t d : Wire) (hn : [b,q,e,t,d].Nodup)
    (s : State) (record : List Bool)
    (ht : s.basis t=(s.basis b && s.basis q))
    (hd : s.basis d=(!s.basis q && (s.basis e ^^ s.basis b))) :
    (run (fusedThresholdFlagsErase b q e t d) record s).phase=s.phase ∧
    (∀ w,w≠t → w≠d → (run (fusedThresholdFlagsErase b q e t d) record s).basis w=s.basis w) ∧
    (run (fusedThresholdFlagsErase b q e t d) record s).basis t=false ∧
    (run (fusedThresholdFlagsErase b q e t d) record s).basis d=false := by
  have hh := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at hh
  have hbt : b≠t := by tauto
  have hbd : b≠d := by tauto
  have hbq : b≠q := by tauto
  have hbe : b≠e := by tauto
  have hqt : q≠t := by tauto
  have hqd : q≠d := by tauto
  have hqe : q≠e := by tauto
  have het : e≠t := by tauto
  have hed : e≠d := by tauto
  have htd : t≠d := by tauto
  have nt : [b,q,t].Nodup := by simp; tauto
  have nd : [q,e,d].Nodup := by simp; tauto
  have nf : [b,q,e].Nodup := by simp; tauto
  let r2 := record.drop 1
  let r3 := record.drop 2
  let s1 := run (eraseMask b [q] [t]) record s
  let s2 := run (fusedThresholdToggle b q e) r2 s1
  let s3 := run (eraseMask q [e] [d]) r2 s2
  have f1 := fused_erase_bit_correct b q t nt s record ht
  have f2 := fusedThresholdToggle_correct b q e nf s1 r2
  have hd2 : s2.basis d=(s2.basis q && s2.basis e) := by
    rw [f2.2.1 d (Ne.symm hqd) (Ne.symm hed),f2.2.2.1,f2.2.2.2,
      f1.2.1 d (Ne.symm htd),f1.2.1 q hqt,f1.2.1 e het,f1.2.1 b hbt]
    exact hd
  have f3 := fused_erase_bit_correct q e d nd s2 r2 hd2
  have f4 := fusedThresholdToggle_correct b q e nf s3 r3
  have hft : measurementCount (eraseMask b [q] [t])=1 := by rfl
  have hfd : measurementCount (eraseMask q [e] [d])=1 := by rfl
  have hfg : measurementCount (fusedThresholdToggle b q e)=0 := by rfl
  rw [fusedThresholdFlagsErase,run_append,run_take,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,hft,hfd,hfg,Nat.add_zero]
  change (run (fusedThresholdToggle b q e) r3 s3).phase=s.phase ∧ _
  refine ⟨f4.1.trans (f3.1.trans (f2.1.trans f1.1)),?_,?_,?_⟩
  · intro w hwt hwd
    by_cases hwq : w=q
    · subst w
      rw [f4.2.2.1,f3.2.1 q hqd,f2.2.2.1,f1.2.1 q hqt]
      simp
    by_cases hwe : w=e
    · subst w
      rw [f4.2.2.2,f3.2.1 e hed,f3.2.1 b hbd,f2.2.2.2,f2.2.1 b hbq hbe,
        f1.2.1 e het,f1.2.1 b hbt]
      simp
    exact (f4.2.1 w hwq hwe).trans ((f3.2.1 w hwd).trans
      ((f2.2.1 w hwq hwe).trans (f1.2.1 w hwt)))
  · exact (f4.2.1 t (Ne.symm hqt) (Ne.symm het)).trans ((f3.2.1 t htd).trans
      ((f2.2.1 t (Ne.symm hqt) (Ne.symm het)).trans f1.2.2))
  · exact (f4.2.1 d (Ne.symm hqd) (Ne.symm hed)).trans f3.2.2

/-- All temporary threshold selectors are included in the paid emitted stream. -/
theorem fusedThresholdFlags_counts (b q e t d : Wire) :
    toffoliCount (fusedThresholdFlagsSeed b q e t d)=2 ∧
    measurementCount (fusedThresholdFlagsSeed b q e t d)=0 ∧
    toffoliCount (fusedThresholdFlagsErase b q e t d)=0 ∧
    measurementCount (fusedThresholdFlagsErase b q e t d)=2 := by
  simp [fusedThresholdFlagsSeed,fusedThresholdFlagsErase,fusedThresholdToggle,
    eraseMask,toffoliCount,measurementCount]

/-- The threshold source constant is loaded by Clifford XORs. The low-bit
selector is separate from the two even constants. -/
def fusedThresholdWordLoad (b q t d : Wire) (C : List Wire) (K P : Nat) : Program :=
  maskedConstant b C K ++ maskedConstant q C K ++ maskedConstant t C P ++ maskedConstant d C 1

def fusedThresholdWordValue (B Q T D : Bool) (K P : Nat) : Nat :=
  (((if B then K else 0) ^^^ (if Q then K else 0)) ^^^
    (if T then P else 0)) ^^^ (if D then 1 else 0)

/-- With the exact AND selector and even constants, the XOR word is the exact
integer threshold constant. In particular no carry is assumed absent. -/
theorem fusedThresholdWordValue_integer (B Q D : Bool) (K P : Nat)
    (hK : K%2=0) (hP : P%2=0) :
    (fusedThresholdWordValue B Q (B&&Q) D K P : Int)=
      FusedSignedHalf.bit (B^^Q)*(K:Int)+FusedSignedHalf.bit (B&&Q)*(P:Int)+FusedSignedHalf.bit D := by
  have heK : Even K := ⟨K/2,by omega⟩
  have heP : Even P := ⟨P/2,by omega⟩
  cases B <;> cases Q <;> cases D <;>
    simp [fusedThresholdWordValue,FusedSignedHalf.bit,Nat.xor_one_of_even heK,Nat.xor_one_of_even heP]

/-- Full word frame for loading and unloading, including arbitrary nonzero
starting words and arbitrary phase. -/
theorem fusedThresholdWordLoad_correct (b q t d : Wire) (C : List Wire) (K P : Nat)
    (hn : ([b,q,t,d]++C).Nodup) (hK : K<2^C.length) (hP : P<2^C.length)
    (h1 : 1<2^C.length) (s : State) (record : List Bool) :
    (run (fusedThresholdWordLoad b q t d C K P) record s).phase=s.phase ∧
    (∀ w,w∉C → (run (fusedThresholdWordLoad b q t d C K P) record s).basis w=s.basis w) ∧
    regValue C (run (fusedThresholdWordLoad b q t d C K P) record s).basis=
      regValue C s.basis ^^^ fusedThresholdWordValue (s.basis b) (s.basis q) (s.basis t) (s.basis d) K P := by
  have hnd := List.nodup_append'.mp hn
  have hc (c : Wire) (hcm : c∈[b,q,t,d]) : c∉C := List.disjoint_left.mp hnd.2.2 hcm
  let F := FusedWordFrame C s.basis
  have stage (c : Wire) (A V : Nat) (hcm : c∈[b,q,t,d]) (hA : A<2^C.length) :
      Triple (F V) (maskedConstant c C A) (F (V ^^^ (if s.basis c then A else 0))) := by
    intro st ms h
    obtain ⟨hf,he,hv⟩ := maskedConstant_correct c C A hnd.2.1 (hc c hcm) hA st ms
    exact ⟨hf,by simpa only [h.1,h.2 c (hc c hcm)] using hv,
      fun w hw => (he w hw).trans (h.2 w hw)⟩
  let V := regValue C s.basis
  let U := if s.basis b then K else 0
  let Vp := if s.basis q then K else 0
  let Wp := if s.basis t then P else 0
  let Ud := if s.basis d then 1 else 0
  have hfirst := stage b K V (by simp) hK
  have hsecond := stage q K (V^^^U) (by simp) hK
  have hthird := stage t P ((V^^^U)^^^Vp) (by simp) hP
  have hfourth := stage d 1 (((V^^^U)^^^Vp)^^^Wp) (by simp) h1
  have hall := ((hfirst.seq hsecond).seq hthird).seq hfourth
  have hcircuit : Triple (F V) (fusedThresholdWordLoad b q t d C K P)
      (F ((((V^^^U)^^^Vp)^^^Wp)^^^Ud)) := by
    simpa only [fusedThresholdWordLoad,List.append_assoc] using hall
  obtain ⟨hf,hv⟩ := hcircuit s record ⟨rfl,fun _ _ => rfl⟩
  refine ⟨hf,hv.2,?_⟩
  simpa only [FusedWordFrame,fusedThresholdWordValue,V,U,Vp,Wp,Ud,Nat.xor_assoc] using hv.1

/-- The physical threshold constant loader contributes no Toffoli or measurement. -/
theorem fusedThresholdWordLoad_counts (b q t d : Wire) (C : List Wire) (K P : Nat) :
    toffoliCount (fusedThresholdWordLoad b q t d C K P)=0 ∧
    measurementCount (fusedThresholdWordLoad b q t d C K P)=0 := by
  simp only [fusedThresholdWordLoad,toffoliCount_append,measurementCount_append,
    (maskedConstant_counts b C K).1,(maskedConstant_counts b C K).2,
    (maskedConstant_counts q C K).1,(maskedConstant_counts q C K).2,
    (maskedConstant_counts t C P).1,(maskedConstant_counts t C P).2,
    (maskedConstant_counts d C 1).1,(maskedConstant_counts d C 1).2]
  trivial

private theorem fused_sub_frame (x y carry : List Wire) (cin : Wire)
    (hn : (cin::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (record : List Bool)
    (hi : s.basis cin=false) (hk : regValue carry s.basis=0)
    (w : Wire) (hw : w∉y) : (run (subInPlace x y carry cin) record s).basis w=s.basis w := by
  have h := (subInPlace_spec x y carry cin hn hx hc
    (regValue x s.basis) (regValue y s.basis) s record ⟨⟨⟨rfl,rfl⟩,hi⟩,hk⟩).2
  by_cases hxw : w∈x
  · exact (regValue_eq_iff x _ _).mp h.1.1.1 w hxw
  by_cases hcw : w∈carry
  · exact (regValue_eq_iff carry _ _).mp (h.2.trans hk.symm) w hcw
  by_cases he : w=cin
  · subst w; exact h.1.2.trans hi.symm
  apply run_preserves_outside
  rw [subInPlace_wires x y carry cin hx hc]
  simpa using (show w∉cin::(x++y++carry) by simp [he,hxw,hw,hcw])

private theorem fused_add_sub_cancel (N U F : Nat) (hU : U<N) (hF : F<N) :
    ((U+F)%N+N-F)%N=U := by
  by_cases hh : U+F<N
  · rw [Nat.mod_eq_of_lt hh,show U+F+N-F=U+N by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hU]
  · have hlo : N≤U+F := by omega
    have hlt : U+F-N<N := by omega
    rw [Nat.mod_eq_sub_mod hlo,Nat.mod_eq_of_lt hlt,
      show U+F-N+N-F=U by omega,Nat.mod_eq_of_lt hU]

/-- Paid normalization-flag recovery. The threshold scratch word is modified,
compared in full, then restored by a new forward subtraction stream. -/
def fusedThresholdRecover (b q t d h : Wire) (R A C addCarry compareCarry : List Wire)
    (cin : Wire) (K P : Nat) : Program :=
  fusedThresholdWordLoad b q t d C K P ++ addInPlace C A addCarry cin ++
    compareLt none R A compareCarry cin h ++ subInPlace C A addCarry cin ++
    fusedThresholdWordLoad b q t d C K P ++ [.CX b h]

/-- Complete all-record recovery capsule. Only h changes; both arithmetic
scratch words, both full carry arrays and the carry input are restored. -/
private theorem fusedThresholdRecover_with_frames_correct (b q t d h : Wire) (R A C addCarry compareCarry : List Wire)
    (cin : Wire) (K P : Nat)
    (hload : ([b,q,t,d]++C).Nodup)
    (hadd : (cin::(C++A++addCarry)).Nodup)
    (hcmp : (h::cin::(R++A++compareCarry)).Nodup)
    (disCA : C.Disjoint A)
    (outside : ∀ w,w∈[b,q,t,d,h,cin]++R++addCarry++compareCarry → w∉C ∧ w∉A)
    (noth : ∀ w,w∈[b,q,t,d,cin]++R++addCarry++compareCarry → w≠h)
    (hRA : R.length=A.length) (hCA : C.length=A.length)
    (ha : addCarry.length+1=A.length) (hc : compareCarry.length=A.length)
    (hK : K<2^C.length) (hP : P<2^C.length) (h1 : 1<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (ha0 : regValue addCarry s.basis=0) (hc0 : regValue compareCarry s.basis=0)
    (hi : s.basis cin=false) :
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).basis w=s.basis w) ∧
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).basis h=
      ((s.basis h ^^ decide (regValue R s.basis<
        (regValue A s.basis+fusedThresholdWordValue (s.basis b) (s.basis q) (s.basis t) (s.basis d) K P)%2^A.length)) ^^ s.basis b) := by
  let F := fusedThresholdWordValue (s.basis b) (s.basis q) (s.basis t) (s.basis d) K P
  let U := regValue A s.basis
  let X := regValue R s.basis
  let V := (U+F)%2^A.length
  let H := s.basis h
  let Q := fun (W Z : Nat) (B : Bool) => PairFrame C A (writeBit s.basis h B) W Z
  have read (W Z : Nat) (B : Bool) (st : BasisState) (hQ : Q W Z B st)
      (w : Wire) (hw : w∈[b,q,t,d,cin]++R++addCarry++compareCarry) : st w=s.basis w := by
    rw [hQ.2.2 w (outside w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hw ⊢; tauto)).1 (outside w (by simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hw ⊢; tauto)).2]
    simp only [writeBit,Function.update_of_ne (noth w hw)]
  have reads (W Z : Nat) (B : Bool) (st : BasisState) (hQ : Q W Z B st) :
      regValue addCarry st=0 ∧ regValue compareCarry st=0 ∧ st cin=false ∧
      fusedThresholdWordValue (st b) (st q) (st t) (st d) K P=F ∧ regValue R st=X := by
    refine ⟨(regValue_congr _ _ _ (fun w hw => read W Z B st hQ w (by simp [hw]))).trans ha0,
      (regValue_congr _ _ _ (fun w hw => read W Z B st hQ w (by simp [hw]))).trans hc0,
      (read W Z B st hQ cin (by simp)).trans hi,?_,?_⟩
    · rw [read W Z B st hQ b (by simp),read W Z B st hQ q (by simp),
        read W Z B st hQ t (by simp),read W Z B st hQ d (by simp)]
    · exact regValue_congr _ _ _ (fun w hw => read W Z B st hQ w (by simp [hw]))
  have load (W Z : Nat) (B : Bool) : Triple (Q W Z B) (fusedThresholdWordLoad b q t d C K P) (Q (W^^^F) Z B) := by
    intro st ms hQ
    obtain ⟨hf,he,hv⟩ := fusedThresholdWordLoad_correct b q t d C K P hload hK hP h1 st ms
    exact ⟨hf,PairFrame.update_temp C A _ _ _ W Z _ disCA hQ he
      (by simpa only [hQ.1,(reads W Z B st.basis hQ).2.2.2.1] using hv)⟩
  have add (B : Bool) : Triple (Q F U B) (addInPlace C A addCarry cin) (Q F V B) := by
    intro st ms hQ
    have hr := reads F U B st.basis hQ
    obtain ⟨hf,he,hv⟩ := addInPlace_correct C A addCarry cin hadd hCA ha st ms ((regValue_zero _ _).mp hr.1)
    exact ⟨hf,PairFrame.update_dst C A _ _ _ F U _ disCA hQ he
      (by simpa only [hQ.1,hQ.2.1,hr.2.2.1,Bool.toNat_false,Nat.add_zero,Nat.zero_add,Nat.add_comm,V] using hv)⟩
  have cmp (B : Bool) : Triple (Q F V B) (compareLt none R A compareCarry cin h) (Q F V (B^^decide (X<V))) := by
    intro st ms hQ
    have hr := reads F V B st.basis hQ
    obtain ⟨hf,he,hv⟩ := compareLt_correct none R A compareCarry cin h hcmp (by simp) hRA hc st ms
      hr.2.2.1 ((regValue_zero _ _).mp hr.2.1)
    have hb : st.basis h=B := by
      rw [hQ.2.2 h (outside h (by simp)).1 (outside h (by simp)).2]
      simp [writeBit]
    refine ⟨hf,?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw => he w (by
        intro hh'; subst w; exact (outside h (by simp)).1 hw))).trans hQ.1
    · exact (regValue_congr _ _ _ (fun w hw => he w (by
        intro hh'; subst w; exact (outside h (by simp)).2 hw))).trans hQ.2.1
    · intro w hwC hwA
      by_cases hwh : w=h
      · subst w
        simpa only [hb,hr.2.2.2.2,hQ.2.1,controlValue,Bool.true_and,writeBit,Function.update_self] using hv
      · rw [he w hwh,hQ.2.2 w hwC hwA]
        simp [writeBit,hwh]
  have hu : U<2^A.length := regValue_lt A s.basis
  have hf : F<2^A.length := by
    have hh := (fusedThresholdWordLoad_correct b q t d C K P hload hK hP h1 s []).2.2
    have hl := regValue_lt C (run (fusedThresholdWordLoad b q t d C K P) [] s).basis
    simpa only [hh,hC0,Nat.zero_xor,hCA] using hl
  have sub (B : Bool) : Triple (Q F V B) (subInPlace C A addCarry cin) (Q F U B) := by
    intro st ms hQ
    have hr := reads F V B st.basis hQ
    obtain ⟨hp,ho⟩ := subInPlace_spec C A addCarry cin hadd hCA ha F V st ms
      ⟨⟨⟨hQ.1,hQ.2.1⟩,hr.2.2.1⟩,hr.1⟩
    have he := fused_sub_frame C A addCarry cin hadd hCA ha st ms hr.2.2.1 hr.1
    refine ⟨hp,PairFrame.update_dst C A _ _ _ F V _ disCA hQ he ?_⟩
    exact ho.1.1.2.trans (fused_add_sub_cancel (2^A.length) U F hu hf)
  have flip (B : Bool) : Triple (Q 0 U B) [.CX b h] (Q 0 U (B^^s.basis b)) := by
    intro st ms hQ
    have hb := read 0 U B st.basis hQ b (by simp)
    have hh : st.basis h=B := by
      rw [hQ.2.2 h (outside h (by simp)).1 (outside h (by simp)).2]
      simp [writeBit]
    refine ⟨rfl,?_,?_,?_⟩
    · exact (regValue_congr _ _ _ (fun w hw => by
        simp [run,writeBit,show w≠h by intro he; subst w; exact (outside h (by simp)).1 hw])).trans hQ.1
    · exact (regValue_congr _ _ _ (fun w hw => by
        simp [run,writeBit,show w≠h by intro he; subst w; exact (outside h (by simp)).2 hw])).trans hQ.2.1
    · intro w hwC hwA
      by_cases hwh : w=h
      · subst w; simp [run,writeBit,hb,hh]
      · simp [run,writeBit,hwh,hQ.2.2 w hwC hwA]
  have l1 := load 0 U H
  have l2 := load F U (H^^decide (X<V))
  simp only [Nat.zero_xor] at l1
  simp only [Nat.xor_self] at l2
  have hall := ((((l1.seq (add H)).seq (cmp H)).seq (sub (H^^decide (X<V)))).seq l2).seq
    (flip (H^^decide (X<V)))
  have hprog : Triple (Q 0 U H) (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P)
      (Q 0 U ((H^^decide (X<V))^^s.basis b)) := by
    simpa only [fusedThresholdRecover,List.append_assoc] using hall
  have initial : Q 0 U H s.basis := by
    refine ⟨hC0,rfl,?_⟩
    intro w _ _
    simp [writeBit,H]
  obtain ⟨hp,ho⟩ := hprog s record initial
  refine ⟨hp,?_,?_⟩
  · intro w hwh
    by_cases hwC : w∈C
    · exact (regValue_eq_iff _ _ _).mp (ho.1.trans hC0.symm) w hwC
    by_cases hwA : w∈A
    · exact (regValue_eq_iff _ _ _).mp ho.2.1 w hwA
    rw [ho.2.2 w hwC hwA]
    simp [writeBit,hwh]
  · have he := ho.2.2 h (outside h (by simp)).1 (outside h (by simp)).2
    simpa only [writeBit,Function.update_self] using he

theorem fusedThresholdRecover_correct (b q t d h : Wire) (R A C addCarry compareCarry : List Wire)
    (cin : Wire) (K P : Nat)
    (hn : ([b,q,t,d,h,cin]++R++A++C++addCarry++compareCarry).Nodup)
    (hRA : R.length=A.length) (hCA : C.length=A.length)
    (ha : addCarry.length+1=A.length) (hc : compareCarry.length=A.length)
    (hK : K<2^C.length) (hP : P<2^C.length) (h1 : 1<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (ha0 : regValue addCarry s.basis=0) (hc0 : regValue compareCarry s.basis=0)
    (hi : s.basis cin=false) :
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).basis w=s.basis w) ∧
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).basis h=
      ((s.basis h ^^ decide (regValue R s.basis<
        (regValue A s.basis+fusedThresholdWordValue (s.basis b) (s.basis q) (s.basis t) (s.basis d) K P)%2^A.length)) ^^ s.basis b) := by
  have hload : ([b,q,t,d]++C).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have hadd : (cin::(C++A++addCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have hcmp : (h::cin::(R++A++compareCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have ndCA := List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hadd).2).1
  have disCA : C.Disjoint A := ndCA.2.2
  have outside (w : Wire) (hw : w∈[b,q,t,d,h,cin]++R++addCarry++compareCarry) :
      w∉C ∧ w∉A := by
    have hh := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ho
    constructor <;> intro hm <;> have hh' := List.count_pos_iff.mpr hm <;> omega
  have noth (w : Wire) (hw : w∈[b,q,t,d,cin]++R++addCarry++compareCarry) : w≠h := by
    intro he
    subst w
    have hh := List.nodup_iff_count.mp hn h
    have ho := List.count_pos_iff.mpr hw
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hh ho
    omega
  have bh : b≠h := noth b (by simp)
  exact fusedThresholdRecover_with_frames_correct b q t d h R A C addCarry compareCarry cin K P
    hload hadd hcmp disCA outside noth hRA hCA ha hc hK hP h1 s record hC0 ha0 hc0 hi

/-- Alias-safe threshold recovery: full compare carry and restored arithmetic carry prefix may overlap. -/
theorem fusedThresholdRecover_shared_correct (b q t d h : Wire) (R A C addCarry compareCarry : List Wire)
    (cin : Wire) (K P : Nat)
    (hn : ([b,q,t,d,h,cin]++R++A++C++compareCarry).Nodup)
    (hsub : addCarry.Sublist compareCarry)
    (hRA : R.length=A.length) (hCA : C.length=A.length)
    (ha : addCarry.length+1=A.length) (hc : compareCarry.length=A.length)
    (hK : K<2^C.length) (hP : P<2^C.length) (h1 : 1<2^C.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (ha0 : regValue addCarry s.basis=0) (hc0 : regValue compareCarry s.basis=0)
    (hi : s.basis cin=false) :
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).basis w=s.basis w) ∧
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P) record s).basis h=
      ((s.basis h ^^ decide (regValue R s.basis<
        (regValue A s.basis+fusedThresholdWordValue (s.basis b) (s.basis q) (s.basis t) (s.basis d) K P)%2^A.length)) ^^ s.basis b) := by
  have hload : ([b,q,t,d]++C).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have hadd : (cin::(C++A++addCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    have hcount := hsub.count_le w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have hcmp : (h::cin::(R++A++compareCarry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have ndCA := List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hadd).2).1
  have disCA : C.Disjoint A := ndCA.2.2
  have outside (w : Wire) (hw : w∈[b,q,t,d,h,cin]++R++addCarry++compareCarry) :
      w∉C ∧ w∉A := by
    have hmem : w∈addCarry → w∈compareCarry := fun hm => hsub.subset hm
    have hw' : w∈[b,q,t,d,h,cin]++R++compareCarry := by
      simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hw ⊢
      tauto
    have hh := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw'
    simp only [List.count_cons,List.count_append,List.count_nil] at hh ho
    constructor <;> intro hm <;> have hh' := List.count_pos_iff.mpr hm <;> omega
  have noth (w : Wire) (hw : w∈[b,q,t,d,cin]++R++addCarry++compareCarry) : w≠h := by
    have hmem : w∈addCarry → w∈compareCarry := fun hm => hsub.subset hm
    have hw' : w∈[b,q,t,d,cin]++R++compareCarry := by
      simp only [List.mem_append,List.mem_cons,List.mem_nil_iff] at hw ⊢
      tauto
    intro he
    subst w
    have hh := List.nodup_iff_count.mp hn h
    have ho := List.count_pos_iff.mpr hw'
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at hh ho
    omega
  exact fusedThresholdRecover_with_frames_correct b q t d h R A C addCarry compareCarry cin K P
    hload hadd hcmp disCA outside noth hRA hCA ha hc hK hP h1 s record hC0 ha0 hc0 hi

/-- Counts include both full arithmetic directions and the flag-cleanup comparator. -/
theorem fusedThresholdRecover_counts (b q t d h : Wire) (R A C addCarry compareCarry : List Wire)
    (cin : Wire) (K P : Nat) (hRA : R.length=A.length) (hCA : C.length=A.length)
    (ha : addCarry.length+1=A.length) (hc : compareCarry.length=A.length) :
    toffoliCount (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P)=3*A.length-2 ∧
    measurementCount (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin K P)=3*A.length-2 := by
  have hl := fusedThresholdWordLoad_counts b q t d C K P
  have hadd := addInPlace_counts C A addCarry cin hCA ha
  have hsub := subInPlace_counts C A addCarry cin hCA ha
  have hcmp := compareLt_counts none R A compareCarry cin h hRA hc
  constructor
  · simp only [fusedThresholdRecover,toffoliCount_append,hl.1,hadd.1,hsub.1,hcmp.1,
      show toffoliCount [.CX b h]=0 by rfl,Option.isSome,Bool.false_eq_true,if_false,Nat.add_zero,Nat.zero_add]
    omega
  · simp only [fusedThresholdRecover,measurementCount_append,hl.2,hadd.2,hsub.2,hcmp.2.1,
      show measurementCount [.CX b h]=0 by rfl,Nat.add_zero,Nat.zero_add]
    omega

/-- The source-dependent threshold is exact in n physical bits. The proof
keeps the complement's full machine modulus and the threshold's canonical bound. -/
theorem fusedThresholdMachine (n p Y : Nat) (b q : Bool) (hp : p%2=1)
    (hK : FusedSignedHalf.halfThreshold p%2=0) (hY : Y<p) (hwidth : p+1<2^n) :
    (signSourceValue n b (Y/2)+
      fusedThresholdWordValue b q (b&&q)
        ((!q)&&(FusedSignedHalf.parity (Y:Int)^^b))
        (FusedSignedHalf.halfThreshold p) (p+1))%2^n=
      FusedSignedHalf.threshold p b q Y := by
  let D := (!q)&&(FusedSignedHalf.parity (Y:Int)^^b)
  let F := fusedThresholdWordValue b q (b&&q) D (FusedSignedHalf.halfThreshold p) (p+1)
  let A := signSourceValue n b (Y/2)
  let M := FusedSignedHalf.threshold p b q Y
  have hf := fusedThresholdWordValue_integer b q D (FusedSignedHalf.halfThreshold p) (p+1) hK (by omega)
  change (F:Int)=_ at hf
  have ht := FusedSignedHalf.threshold_constant_identity p Y b q hp hY
  have he : ((A+F:Nat):Int)=(M:Int)+(if b then ((2^n:Nat):Int) else 0) := by
    rw [Nat.cast_add,hf]
    dsimp only [M] at ht ⊢
    rw [ht]
    cases b
    · simp [A,signSourceValue,FusedSignedHalf.thresholdConstant,D,FusedSignedHalf.bit]
    · have h1 : 1≤2^n := by omega
      have hy : Y/2≤2^n-1 := by omega
      simp only [A,signSourceValue,if_true,Nat.cast_sub hy,Nat.cast_sub h1,Nat.cast_one,
        FusedSignedHalf.thresholdConstant,D,Nat.cast_add,Nat.cast_ofNat,Int.natCast_ediv]
      ring
  have hm : M<2^n := (FusedSignedHalf.threshold_bounds p Y b q hp hY).trans_lt (by omega)
  have hcong : (((A+F)%2^n:Nat):Int)=(M:Int) := by
    rw [Int.natCast_emod,he,Int.add_emod]
    cases b <;> simp only [Bool.false_eq_true,if_false,if_true,Int.zero_emod,Int.emod_self,add_zero,Int.emod_emod] <;>
      exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast hm)
  change (A+F)%2^n=M
  omega

/-- Apply the selected full-word correction, erase every nonlinear correction
flag with phase correction, and physically rotate the proved even lift. -/
def fusedEvenHalf (b a h j l m : Wire) (C R carry : List Wire) (cin : Wire) (P : Nat) : Program :=
  fusedCorrectionApply a j l m C R carry cin P (2*P) (2^R.length-P) ++
    fusedCorrectionFlagsErase b a h j l m ++ rotateRight R

/-- The emitted correction/half capsule produces the exact canonical field
representative and clears all three selector work bits, for every record. -/
theorem fusedEvenHalf_correct (b a h j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P X Y : Nat) (hn : ([b,a,h,j,l,m,cin]++C++R++carry).Nodup)
    (hCR : C.length=R.length) (hcarry : carry.length+1=R.length)
    (hp : P%2=1) (hX : X<P) (hY : Y<P) (hwidth : 2*P<2^R.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (ha : s.basis a=FusedSignedHalf.parity (FusedSignedHalf.signedSum (s.basis b) X Y))
    (hh : s.basis h=FusedSignedHalf.reduction P (FusedSignedHalf.signedSum (s.basis b) X Y))
    (hj : s.basis j=(s.basis b && s.basis h)) (hl : s.basis l=(s.basis a && s.basis h))
    (hm : s.basis m=(s.basis a && s.basis j))
    (hR : regValue R s.basis=signedWordValue R.length (s.basis b) Y X) :
    (run (fusedEvenHalf b a h j l m C R carry cin P) record s).phase=s.phase ∧
    (∀ w,w∉R → w≠j → w≠l → w≠m →
      (run (fusedEvenHalf b a h j l m C R carry cin P) record s).basis w=s.basis w) ∧
    regValue R (run (fusedEvenHalf b a h j l m C R carry cin P) record s).basis=
      FusedSignedHalf.result P (s.basis b) X Y ∧
    (run (fusedEvenHalf b a h j l m C R carry cin P) record s).basis j=false ∧
    (run (fusedEvenHalf b a h j l m C R carry cin P) record s).basis l=false ∧
    (run (fusedEvenHalf b a h j l m C R carry cin P) record s).basis m=false := by
  have hcorr : (cin::([a,j,l,m]++C++R++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hflags : [b,a,h,j,l,m].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hnR : R.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have outside (w : Wire) (hw : w∈[b,a,h,j,l,m]) : w∉R := by
    intro hmR
    have hc := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    have hr := List.count_pos_iff.mpr hmR
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ho
    omega
  have hp0 : 0<P := by omega
  let S := FusedSignedHalf.signedSum (s.basis b) X Y
  let E := FusedSignedHalf.evenLift P (s.basis b) S
  let corr := fusedCorrectionApply a j l m C R carry cin P (2*P) (2^R.length-P)
  let st := run corr record s
  have hc := fusedCorrectionApply_correct a j l m C R carry cin P (2*P) (2^R.length-P)
    hcorr hCR hcarry (by rw [hCR]; omega) (by rw [hCR]; omega) (by rw [hCR]; omega) s record hC0 hk0 hi
  have hstR : regValue R st.basis=E.toNat := by
    rw [hc.2.2,hR,hj,hl,hm,hj,ha,hh]
    exact fusedCorrectionMachine R.length P X Y (s.basis b) hp hX hY hwidth
  let r2 := record.drop (measurementCount corr)
  let et := run (fusedCorrectionFlagsErase b a h j l m) r2 st
  have er := fusedCorrectionFlagsErase_correct b a h j l m hflags st r2
    (by rw [hc.2.1 j (outside j (by simp)),hc.2.1 b (outside b (by simp)),hc.2.1 h (outside h (by simp))]; exact hj)
    (by rw [hc.2.1 l (outside l (by simp)),hc.2.1 a (outside a (by simp)),hc.2.1 h (outside h (by simp))]; exact hl)
    (by rw [hc.2.1 m (outside m (by simp)),hc.2.1 a (outside a (by simp)),hc.2.1 j (outside j (by simp))]; exact hm)
  have hRflag (w : Wire) (hw : w∈R) : w≠j ∧ w≠l ∧ w≠m := by
    constructor
    · intro he; subst w; exact outside j (by simp) hw
    constructor
    · intro he; subst w; exact outside l (by simp) hw
    · intro he; subst w; exact outside m (by simp) hw
  have hetR : regValue R et.basis=E.toNat :=
    (regValue_congr _ _ _ (fun w hw => er.2.1 w (hRflag w hw).1 (hRflag w hw).2.1 (hRflag w hw).2.2)).trans hstR
  have he := FusedSignedHalf.evenLift_spec P (s.basis b) S hp (FusedSignedHalf.signedSum_domain P X Y (s.basis b) hX hY)
  have hnat : E.toNat%2=0 := by
    change 0≤E ∧ E<2*(P:Int) ∧ E%2=0 at he
    omega
  let r3 := record.drop (measurementCount corr+3)
  have rot := rotateRight_spec R hnR E.toNat hnat et r3 hetR
  have rf := (rotate_frame R et r3).2.1
  rw [fusedEvenHalf,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(fusedCorrectionFlags_counts b a a h j l m).2.2.2]
  change (run (rotateRight R) r3 et).phase=s.phase ∧ _
  refine ⟨rot.1.trans (er.1.trans hc.1),?_,?_,?_,?_,?_⟩
  · intro w hwR hwj hwl hwm
    exact (rf w hwR).trans ((er.2.1 w hwj hwl hwm).trans (hc.2.1 w hwR))
  · have hv : E.toNat/2=FusedSignedHalf.result P (s.basis b) X Y := by
      change E.toNat/2=(E/2).toNat
      change 0≤E ∧ E<2*(P:Int) ∧ E%2=0 at he
      omega
    exact rot.2.trans hv
  · exact (rf j (outside j (by simp))).trans er.2.2.1
  · exact (rf l (outside l (by simp))).trans er.2.2.2.1
  · exact (rf m (outside m (by simp))).trans er.2.2.2.2

/-- Physical correction/half count includes all selector erasure measurements. -/
theorem fusedEvenHalf_counts (b a h j l m : Wire) (C R carry : List Wire) (cin : Wire)
    (P : Nat) (hCR : C.length=R.length) (hcarry : carry.length+1=R.length) :
    toffoliCount (fusedEvenHalf b a h j l m C R carry cin P)=R.length-1 ∧
    measurementCount (fusedEvenHalf b a h j l m C R carry cin P)=R.length+2 := by
  have hc := fusedCorrectionApply_counts a j l m C R carry cin P (2*P) (2^R.length-P) hCR hcarry
  have hf := fusedCorrectionFlags_counts b a a h j l m
  have hr := rotate_counts R
  simp only [fusedEvenHalf,toffoliCount_append,measurementCount_append,hc.1,hc.2,hf.2.2.1,hf.2.2.2,
    hr.1,hr.2.1,Nat.add_zero]
  constructor
  · trivial
  · omega


/-- Move the two retained classical flags into cleared target guards. The early
scratch bits are cleared by physical Clifford swaps. -/
def fusedFlagsMove (a h qOut hOut : Wire) : Program :=
  [.CX h a] ++ swapBits a qOut ++ swapBits h hOut

/-- Complete flag transfer, independent of all measurement records and phase. -/
theorem fusedFlagsMove_correct (a h qOut hOut : Wire) (hn : [a,h,qOut,hOut].Nodup)
    (s : State) (record : List Bool) (hq : s.basis qOut=false) (hh : s.basis hOut=false) :
    (run (fusedFlagsMove a h qOut hOut) record s).phase=s.phase ∧
    (∀ w,w≠a → w≠h → w≠qOut → w≠hOut →
      (run (fusedFlagsMove a h qOut hOut) record s).basis w=s.basis w) ∧
    (run (fusedFlagsMove a h qOut hOut) record s).basis a=false ∧
    (run (fusedFlagsMove a h qOut hOut) record s).basis h=false ∧
    (run (fusedFlagsMove a h qOut hOut) record s).basis qOut=(s.basis a^^s.basis h) ∧
    (run (fusedFlagsMove a h qOut hOut) record s).basis hOut=s.basis h := by
  have hn' := hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at hn'
  have hah : a≠h := by tauto
  have hha : h≠a := Ne.symm hah
  have haq : a≠qOut := by tauto
  have hqa : qOut≠a := Ne.symm haq
  have hao : a≠hOut := by tauto
  have hoa : hOut≠a := Ne.symm hao
  have hhq : h≠qOut := by tauto
  have hqh : qOut≠h := Ne.symm hhq
  have hho : h≠hOut := by tauto
  have hoh : hOut≠h := Ne.symm hho
  have hqo : qOut≠hOut := by tauto
  have hoq : hOut≠qOut := Ne.symm hqo
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · intro w hwa hwh hwq hwo
    simp [fusedFlagsMove,swapBits,run,writeBit,hwa,hwh,hwq,hwo]
  all_goals cases ea : s.basis a <;> cases eh : s.basis h <;>
    simp_all [fusedFlagsMove,swapBits,run,writeBit]

/-- Flag transfer consumes no Toffoli or measurement. -/
theorem fusedFlagsMove_counts (a h qOut hOut : Wire) :
    toffoliCount (fusedFlagsMove a h qOut hOut)=0 ∧ measurementCount (fusedFlagsMove a h qOut hOut)=0 := by
  exact ⟨rfl,rfl⟩

/-- Exact low-bit read from a physical little-endian word. -/
theorem fusedWordLowBit (low : Wire) (tail : List Wire) (s : BasisState) :
    s low=decide (regValue (low::tail) s%2=1) := by
  change s low=decide (((if s low then 1 else 0)+2*regValue tail s)%2=1)
  cases s low <;> simp

/-- Exact top-bit read; the whole lower word is bounded by its physical width. -/
theorem fusedWordTopBit (loWord : List Wire) (top : Wire) (s : BasisState) :
    s top=decide (2^loWord.length≤regValue (loWord++[top]) s) := by
  rw [regValue_append]
  have hl := regValue_lt loWord s
  change s top=decide (2^loWord.length≤regValue loWord s+2^loWord.length*(if s top then 1 else 0))
  cases s top <;> simp [show ¬2^loWord.length≤regValue loWord s by omega]

/-- Candidate complete signed half stream. The target/source have two guard
bits. Early flags live in scratch A; after the canonical half they move into
zero target guards, releasing A for the full threshold cleanup. Stage-specific
layout and complete input/output composition remain to be connected. -/
def fusedSignedHalfCandidate (b cin low sign a h j l m qOut hOut t d e : Wire)
    (Y R C carry A sourceHalf : List Wire) (P : Nat) : Program :=
  let n := A.length
  let ac := carry.take (R.length-1)
  let x := R.take n
  let c := C.take n
  let kc := carry.take n
  let ka := carry.take (n-1)
  fusedRawNormalize b h Y R C ac carry cin P ++ [.CX low a] ++
    fusedCorrectionFlagsSeed sign a h j l m ++ fusedEvenHalf b a h j l m C R ac cin P ++
    fusedFlagsMove a h qOut hOut ++
    fusedThresholdFlagsSeed b qOut e t d ++
    copyRegister none sourceHalf A ++ signComplement b A ++
    fusedThresholdRecover b qOut t d hOut x A c ka kc cin
      (FusedSignedHalf.halfThreshold P) (P+1) ++
    signComplement b A ++ copyRegister none sourceHalf A ++
    fusedThresholdFlagsErase b qOut e t d ++ fusedHalfParityClear x c kc cin qOut

set_option maxHeartbeats 1000000 in
/-- Count the complete emitted candidate, including every full cleanup compare
and measured selector reset. This theorem is a program count only; it does not
assert a complete field input/output theorem for the candidate. -/
theorem fusedSignedHalfCandidate_counts (b cin low sign a h j l m qOut hOut t d e : Wire)
    (Y R C carry A sourceHalf : List Wire) (P : Nat)
    (hn : 3≤A.length) (hR : R.length=A.length+2) (hY : Y.length=R.length)
    (hC : C.length=R.length) (hk : carry.length=R.length) (hs : sourceHalf.length=A.length) :
    toffoliCount (fusedSignedHalfCandidate b cin low sign a h j l m qOut hOut t d e Y R C carry A sourceHalf P)=7*A.length+3 ∧
    measurementCount (fusedSignedHalfCandidate b cin low sign a h j l m qOut hOut t d e Y R C carry A sourceHalf P)=7*A.length+4 := by
  let n := A.length
  let ac := carry.take (R.length-1)
  let x := R.take n
  let c := C.take n
  let kc := carry.take n
  let ka := carry.take (n-1)
  have ha : ac.length+1=R.length := by simp [ac,hk,hR]
  have hx : x.length=n := by simp [x,n,hR]
  have hc : c.length=n := by simp [c,n,hC,hR]
  have hkc : kc.length=n := by simp [kc,n,hk,hR]
  have hka : ka.length+1=n := by simp [ka,n,hk,hR]; omega
  have hraw := fusedRawNormalize_counts b h Y R C ac carry cin P hY hC ha hk
  have hseed := fusedCorrectionFlags_counts b sign a h j l m
  have heven := fusedEvenHalf_counts b a h j l m C R ac cin P hC ha
  have hth := fusedThresholdFlags_counts b qOut e t d
  have hcopy := copyRegister_counts none sourceHalf A hs
  have hneg := signComplement_counts b A
  have hrecover := fusedThresholdRecover_counts b qOut t d hOut x A c ka kc cin
    (FusedSignedHalf.halfThreshold P) (P+1) hx hc hka hkc
  have hparity := fusedHalfParityClear_counts x c kc cin qOut (by omega) (by omega)
  have hswap1 : toffoliCount (swapBits a qOut)=0 ∧ measurementCount (swapBits a qOut)=0 := by exact ⟨rfl,rfl⟩
  have hswap2 : toffoliCount (swapBits h hOut)=0 ∧ measurementCount (swapBits h hOut)=0 := by exact ⟨rfl,rfl⟩
  have hcx1 : toffoliCount [.CX low a]=0 ∧ measurementCount [.CX low a]=0 := by exact ⟨rfl,rfl⟩
  have hcx2 : toffoliCount [.CX h a]=0 ∧ measurementCount [.CX h a]=0 := by exact ⟨rfl,rfl⟩
  dsimp only [ac,x,c,kc,ka,n] at hraw heven hrecover hparity
  dsimp only [x,n] at hx
  dsimp only [fusedSignedHalfCandidate]
  constructor
  · simp only [fusedFlagsMove,toffoliCount_append,hraw.1,hseed.1,heven.1,hth.1,hth.2.2.1,hcopy.1,hneg.1,
      hrecover.1,hparity.1,hswap1.1,hswap2.1,hcx1.1,hcx2.1,Option.isSome,Bool.false_eq_true,if_false]
    omega
  · simp only [fusedFlagsMove,measurementCount_append,hraw.2,hseed.2.1,heven.2,hth.2.1,hth.2.2.2,hcopy.2,hneg.2,
      hrecover.2,hparity.2,hswap1.2,hswap2.2,hcx1.2,hcx2.2]
    omega

/-- Exact raw parity, including a negative signed subtraction encoded in a full
machine word. No carry bit or low input bit is sampled or discarded. -/
theorem fusedRawParity (w P X Y : Nat) (b : Bool) (hw : 0<w)
    (hX : X<P) (hY : Y<P) (hwidth : 2*P<2^w) :
    decide (signedWordValue w b Y X%2=1)=
      FusedSignedHalf.parity (FusedSignedHalf.signedSum b X Y) := by
  have hmod : 2^w%2=0 := by
    rw [show w=(w-1)+1 by omega,pow_succ]
    omega
  cases b
  · have hsum : X+Y<2^w := by omega
    rw [show signedWordValue w false Y X=X+Y by simp [signedWordValue,Nat.mod_eq_of_lt hsum]]
    apply decide_eq_decide.mpr
    change (X+Y)%2=1 ↔ ((X:Int)+(Y:Int))%2=1
    omega
  · by_cases hxy : Y≤X
    · have hsmall : X-Y<2^w := by omega
      have hr : signedWordValue w true Y X=X-Y := by
        simp only [signedWordValue,if_true]
        rw [show X+2^w-Y=(X-Y)+2^w by omega,Nat.add_mod]
        simp [Nat.mod_eq_of_lt hsmall]
      rw [hr]
      apply decide_eq_decide.mpr
      change (X-Y)%2=1 ↔ ((X:Int)-(Y:Int))%2=1
      omega
    · have hsmall : X+2^w-Y<2^w := by omega
      rw [show signedWordValue w true Y X=X+2^w-Y by simp [signedWordValue,Nat.mod_eq_of_lt hsmall]]
      apply decide_eq_decide.mpr
      change (X+2^w-Y)%2=1 ↔ ((X:Int)-(Y:Int))%2=1
      omega

/-- Exact signed guard recovery from a full physical word. Two guards suffice
for every canonical signed field sum, including both zero boundaries. -/
theorem fusedRawSign (w P X Y : Nat) (b : Bool) (hw : 0<w)
    (hX : X<P) (hY : Y<P) (hwidth : 2*P<2^(w-1)) :
    decide (2^(w-1)≤signedWordValue w b Y X)=
      decide (FusedSignedHalf.signedSum b X Y<0) := by
  have hpow : 2^w=2*2^(w-1) := by
    calc
      2^w=2^((w-1)+1) := by congr 1; omega
      _=2^(w-1)*2 := pow_succ _ _
      _=2*2^(w-1) := Nat.mul_comm _ _
  cases b
  · have hsum : X+Y<2^w := by omega
    rw [show signedWordValue w false Y X=X+Y by simp [signedWordValue,Nat.mod_eq_of_lt hsum]]
    apply decide_eq_decide.mpr
    change 2^(w-1)≤X+Y ↔ (X:Int)+(Y:Int)<0
    omega
  · by_cases hxy : Y≤X
    · have hsmall : X-Y<2^w := by omega
      have hr : signedWordValue w true Y X=X-Y := by
        simp only [signedWordValue,if_true]
        rw [show X+2^w-Y=(X-Y)+2^w by omega,Nat.add_mod]
        simp [Nat.mod_eq_of_lt hsmall]
      rw [hr]
      apply decide_eq_decide.mpr
      change 2^(w-1)≤X-Y ↔ (X:Int)-(Y:Int)<0
      omega
    · have hsmall : X+2^w-Y<2^w := by omega
      rw [show signedWordValue w true Y X=X+2^w-Y by simp [signedWordValue,Nat.mod_eq_of_lt hsmall]]
      apply decide_eq_decide.mpr
      change 2^(w-1)≤X+2^w-Y ↔ (X:Int)-(Y:Int)<0
      omega

/-- Actual normalization cleanup, tied to the exact canonical result/source
rather than an arbitrary machine threshold. All scratch restoration remains
part of the emitted capsule's theorem. -/
theorem fusedThresholdRecover_clears (b q t d h : Wire) (R A C addCarry compareCarry : List Wire)
    (cin : Wire) (P X Y : Nat)
    (hn : ([b,q,t,d,h,cin]++R++A++C++addCarry++compareCarry).Nodup)
    (hRA : R.length=A.length) (hCA : C.length=A.length)
    (ha : addCarry.length+1=A.length) (hc : compareCarry.length=A.length)
    (hp : P%2=1) (hK : FusedSignedHalf.halfThreshold P%2=0)
    (hX : X<P) (hY : Y<P) (hwidth : P+1<2^A.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (ha0 : regValue addCarry s.basis=0) (hc0 : regValue compareCarry s.basis=0)
    (hi : s.basis cin=false)
    (hq : s.basis q=FusedSignedHalf.normalizedParity P (FusedSignedHalf.signedSum (s.basis b) X Y))
    (hh : s.basis h=FusedSignedHalf.reduction P (FusedSignedHalf.signedSum (s.basis b) X Y))
    (ht : s.basis t=(s.basis b&&s.basis q))
    (hd : s.basis d=(!s.basis q&&(FusedSignedHalf.parity (Y:Int)^^s.basis b)))
    (hR : regValue R s.basis=FusedSignedHalf.result P (s.basis b) X Y)
    (hA : regValue A s.basis=signSourceValue A.length (s.basis b) (Y/2)) :
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin
      (FusedSignedHalf.halfThreshold P) (P+1)) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin
      (FusedSignedHalf.halfThreshold P) (P+1)) record s).basis w=s.basis w) ∧
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin
      (FusedSignedHalf.halfThreshold P) (P+1)) record s).basis h=false := by
  have hsmall : FusedSignedHalf.halfThreshold P<2^C.length := by
    rw [hCA]
    unfold FusedSignedHalf.halfThreshold
    omega
  have hconstant : P+1<2^C.length := by simpa only [hCA] using hwidth
  have hbit : 1<2^C.length := by rw [hCA]; omega
  have hcircuit := fusedThresholdRecover_correct b q t d h R A C addCarry compareCarry cin
    (FusedSignedHalf.halfThreshold P) (P+1) hn hRA hCA ha hc hsmall hconstant hbit s record hC0 ha0 hc0 hi
  refine ⟨hcircuit.1,hcircuit.2.1,?_⟩
  rw [hcircuit.2.2,hA,ht,hd,
    fusedThresholdMachine A.length P Y (s.basis b) (s.basis q) hp hK hY hwidth,hR]
  let B := s.basis b
  let S := FusedSignedHalf.signedSum B X Y
  let Q := FusedSignedHalf.normalizedParity P S
  let H := FusedSignedHalf.reduction P S
  let Z := FusedSignedHalf.result P B X Y
  have he := (FusedSignedHalf.result_spec P X Y B hp hX hY).2
  have hdoubled : 2*(Z:Int)=FusedSignedHalf.signedSum B X Y+FusedSignedHalf.bit Q*(P:Int)+
      (if B then FusedSignedHalf.bit H*(P:Int) else -FusedSignedHalf.bit H*(P:Int)) := by
    rw [he]
    unfold FusedSignedHalf.evenLift FusedSignedHalf.correction
    dsimp only [Q,H,S]
    cases B <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring
  have hrec := FusedSignedHalf.reduction_recovery P X Y Z B Q H hp hX hY hdoubled
  rw [hq,hh]
  change ((H^^decide (Z<FusedSignedHalf.threshold P B Q Y))^^B)=false
  rw [hrec]
  have hxorb (V T : Bool) : ((V^^T)^^V^^T)=false := by cases V <;> cases T <;> rfl
  exact hxorb (decide (Z<FusedSignedHalf.threshold P B Q Y)) B

/-- Exact canonical normalization cleanup with the same shared full carry array. -/
theorem fusedThresholdRecover_shared_clears (b q t d h : Wire) (R A C addCarry compareCarry : List Wire)
    (cin : Wire) (P X Y : Nat)
    (hn : ([b,q,t,d,h,cin]++R++A++C++compareCarry).Nodup)
    (hsub : addCarry.Sublist compareCarry)
    (hRA : R.length=A.length) (hCA : C.length=A.length)
    (ha : addCarry.length+1=A.length) (hc : compareCarry.length=A.length)
    (hp : P%2=1) (hK : FusedSignedHalf.halfThreshold P%2=0)
    (hX : X<P) (hY : Y<P) (hwidth : P+1<2^A.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (ha0 : regValue addCarry s.basis=0) (hc0 : regValue compareCarry s.basis=0)
    (hi : s.basis cin=false)
    (hq : s.basis q=FusedSignedHalf.normalizedParity P (FusedSignedHalf.signedSum (s.basis b) X Y))
    (hh : s.basis h=FusedSignedHalf.reduction P (FusedSignedHalf.signedSum (s.basis b) X Y))
    (ht : s.basis t=(s.basis b&&s.basis q))
    (hd : s.basis d=(!s.basis q&&(FusedSignedHalf.parity (Y:Int)^^s.basis b)))
    (hR : regValue R s.basis=FusedSignedHalf.result P (s.basis b) X Y)
    (hA : regValue A s.basis=signSourceValue A.length (s.basis b) (Y/2)) :
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin
      (FusedSignedHalf.halfThreshold P) (P+1)) record s).phase=s.phase ∧
    (∀ w,w≠h → (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin
      (FusedSignedHalf.halfThreshold P) (P+1)) record s).basis w=s.basis w) ∧
    (run (fusedThresholdRecover b q t d h R A C addCarry compareCarry cin
      (FusedSignedHalf.halfThreshold P) (P+1)) record s).basis h=false := by
  have hsmall : FusedSignedHalf.halfThreshold P<2^C.length := by
    rw [hCA]
    unfold FusedSignedHalf.halfThreshold
    omega
  have hconstant : P+1<2^C.length := by simpa only [hCA] using hwidth
  have hbit : 1<2^C.length := by rw [hCA]; omega
  have hcircuit := fusedThresholdRecover_shared_correct b q t d h R A C addCarry compareCarry cin
    (FusedSignedHalf.halfThreshold P) (P+1) hn hsub hRA hCA ha hc hsmall hconstant hbit s record hC0 ha0 hc0 hi
  refine ⟨hcircuit.1,hcircuit.2.1,?_⟩
  rw [hcircuit.2.2,hA,ht,hd,
    fusedThresholdMachine A.length P Y (s.basis b) (s.basis q) hp hK hY hwidth,hR]
  let B := s.basis b
  let S := FusedSignedHalf.signedSum B X Y
  let Q := FusedSignedHalf.normalizedParity P S
  let H := FusedSignedHalf.reduction P S
  let Z := FusedSignedHalf.result P B X Y
  have he := (FusedSignedHalf.result_spec P X Y B hp hX hY).2
  have hdoubled : 2*(Z:Int)=FusedSignedHalf.signedSum B X Y+FusedSignedHalf.bit Q*(P:Int)+
      (if B then FusedSignedHalf.bit H*(P:Int) else -FusedSignedHalf.bit H*(P:Int)) := by
    rw [he]
    unfold FusedSignedHalf.evenLift FusedSignedHalf.correction
    dsimp only [Q,H,S]
    cases B <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring
  have hrec := FusedSignedHalf.reduction_recovery P X Y Z B Q H hp hX hY hdoubled
  rw [hq,hh]
  change ((H^^decide (Z<FusedSignedHalf.threshold P B Q Y))^^B)=false
  rw [hrec]
  have hxorb (V T : Bool) : ((V^^T)^^V^^T)=false := by cases V <;> cases T <;> rfl
  exact hxorb (decide (Z<FusedSignedHalf.threshold P B Q Y)) B

/-- The actual final parity cleanup is applicable to every canonical secp256k1
signed-half result, including zeros and equal inputs. -/
theorem fusedHalfParityClear_from_result (R C carry : List Wire) (cin q : Wire)
    (X Y : Nat) (B : Bool) (hn : (q::cin::(R++C++carry)).Nodup) (hR : 3≤R.length)
    (hC : C.length=R.length) (hc : carry.length=R.length) (hwidth : p<2^R.length)
    (s : State) (record : List Bool) (hC0 : regValue C s.basis=0)
    (hc0 : regValue carry s.basis=0) (hi : s.basis cin=false) (hX : X<p) (hY : Y<p)
    (hv : regValue R s.basis=FusedSignedHalf.result p B X Y)
    (hq : s.basis q=FusedSignedHalf.normalizedParity p (FusedSignedHalf.signedSum B X Y)) :
    (run (fusedHalfParityClear R C carry cin q) record s).phase=s.phase ∧
    (∀ w,w≠q → (run (fusedHalfParityClear R C carry cin q) record s).basis w=s.basis w) ∧
    (run (fusedHalfParityClear R C carry cin q) record s).basis q=false := by
  have hp : p%2=1 := by norm_num [ECDSAAdd.p]
  have hK : FusedSignedHalf.halfThreshold p<2^R.length := by
    unfold FusedSignedHalf.halfThreshold
    omega
  apply fusedHalfParityClear_correct R C carry cin q hn hR hC hc hK s record hC0 hc0 hi
  rw [hv,hq]
  exact FusedSignedHalf.normalizedParity_recovery p X Y B hp hX hY

/-- A canonical n-bit result in an n+2 physical word has both full guard bits
zero. This is the exact condition that permits later flag borrowing. -/
theorem fusedCanonicalGuards (loWord : List Wire) (g0 g1 : Wire) (s : BasisState)
    (V : Nat) (hV : V<2^loWord.length) (hv : regValue (loWord++[g0,g1]) s=V) :
    regValue loWord s=V ∧ s g0=false ∧ s g1=false := by
  have he := regValue_append loWord [g0,g1] s
  rw [hv] at he
  change V=regValue loWord s+2^loWord.length*((if s g0 then 1 else 0)+2*(if s g1 then 1 else 0)) at he
  have hp : 0<2^loWord.length := by positivity
  cases hg0 : s g0 <;> cases hg1 : s g1 <;> simp [hg0,hg1] at he ⊢ <;> omega

/-- The physical shifted source view has exactly n cells: the upper source
padding bit is retained and proved zero, rather than silently discarded. -/
theorem fusedSourceHalfValue (e : Wire) (ys : List Wire) (g0 g1 : Wire) (s : BasisState)
    (Y : Nat) (hY : Y<2^(e::ys).length) (hv : regValue ((e::ys)++[g0,g1]) s=Y) :
    regValue (ys++[g0]) s=Y/2 := by
  have hg := fusedCanonicalGuards (e::ys) g0 g1 s Y hY hv
  have hl : (if s e then 1 else 0)+2*regValue ys s=Y := hg.1
  rw [regValue_append]
  change regValue ys s+2^ys.length*(if s g0 then 1 else 0)=Y/2
  rw [hg.2.1]
  simp only [Bool.false_eq_true,if_false,mul_zero,Nat.add_zero]
  cases hb : s e <;> simp only [hb,Bool.false_eq_true,if_false,if_true] at hl <;> omega

/-- Threshold input preparation uses only Clifford copy and conditional NOT. -/
def fusedThresholdPrepare (b : Wire) (sourceHalf A : List Wire) : Program :=
  copyRegister none sourceHalf A ++ signComplement b A

/-- Restore the threshold input by a fresh forward Clifford stream. -/
def fusedThresholdUnprepare (b : Wire) (sourceHalf A : List Wire) : Program :=
  signComplement b A ++ copyRegister none sourceHalf A

/-- Exact threshold input preparation with the source/sign/phase preserved. -/
theorem fusedThresholdPrepare_correct (b : Wire) (sourceHalf A : List Wire)
    (hn : (b::(sourceHalf++A)).Nodup) (hs : sourceHalf.length=A.length)
    (s : State) (record : List Bool) (ha0 : regValue A s.basis=0) :
    (run (fusedThresholdPrepare b sourceHalf A) record s).phase=s.phase ∧
    (∀ w,w∉A → (run (fusedThresholdPrepare b sourceHalf A) record s).basis w=s.basis w) ∧
    regValue A (run (fusedThresholdPrepare b sourceHalf A) record s).basis=
      signSourceValue A.length (s.basis b) (regValue sourceHalf s.basis) := by
  have nd := List.nodup_cons.mp hn
  have na := (List.nodup_append'.mp nd.2).2.1
  have ba : b∉A := by intro hb; exact nd.1 (by simp [hb])
  let cp := copyRegister none sourceHalf A
  let st := run cp record s
  have hc := copyRegister_correct none sourceHalf A hs nd.2 (by simp) s record
  have hv : regValue A st.basis=regValue sourceHalf s.basis := by
    simpa only [copyValue,ha0,Nat.zero_xor] using hc.2.2
  let r2 := record.drop (measurementCount cp)
  have he := signComplement_correct b A na ba st r2
  rw [fusedThresholdPrepare,run_append,run_take]
  change (run (signComplement b A) r2 st).phase=s.phase ∧ _
  refine ⟨he.1.trans hc.1,fun w hw => (he.2.1 w hw).trans (hc.2.1 w hw),?_⟩
  have hb : st.basis b=s.basis b := hc.2.1 b ba
  calc
    regValue A (run (signComplement b A) r2 st).basis=signSourceValue A.length (st.basis b) (regValue A st.basis) := he.2.2
    _=signSourceValue A.length (s.basis b) (regValue sourceHalf s.basis) := by rw [hb,hv]

/-- Unpreparation clears the entire target word for every source value, including
zero, while preserving every other bit and arbitrary incoming phase. -/
theorem fusedThresholdUnprepare_correct (b : Wire) (sourceHalf A : List Wire)
    (hn : (b::(sourceHalf++A)).Nodup) (hs : sourceHalf.length=A.length)
    (s : State) (record : List Bool)
    (hA : regValue A s.basis=signSourceValue A.length (s.basis b) (regValue sourceHalf s.basis)) :
    (run (fusedThresholdUnprepare b sourceHalf A) record s).phase=s.phase ∧
    (∀ w,w∉A → (run (fusedThresholdUnprepare b sourceHalf A) record s).basis w=s.basis w) ∧
    regValue A (run (fusedThresholdUnprepare b sourceHalf A) record s).basis=0 := by
  have nd := List.nodup_cons.mp hn
  have parts := List.nodup_append'.mp nd.2
  have ba : b∉A := by intro hb; exact nd.1 (by simp [hb])
  let neg := signComplement b A
  let st := run neg record s
  have he := signComplement_correct b A parts.2.1 ba s record
  have hfit : regValue sourceHalf s.basis<2^A.length := by simpa only [hs] using regValue_lt sourceHalf s.basis
  have hcancellation : signSourceValue A.length (s.basis b)
      (signSourceValue A.length (s.basis b) (regValue sourceHalf s.basis))=regValue sourceHalf s.basis := by
    cases s.basis b <;> simp only [signSourceValue,Bool.false_eq_true,if_false,if_true]
    omega
  have hv : regValue A st.basis=regValue sourceHalf s.basis := by
    calc
      regValue A st.basis=signSourceValue A.length (s.basis b) (regValue A s.basis) := he.2.2
      _=signSourceValue A.length (s.basis b) (signSourceValue A.length (s.basis b) (regValue sourceHalf s.basis)) := congrArg (signSourceValue A.length (s.basis b)) hA
      _=regValue sourceHalf s.basis := hcancellation
  have hsource : regValue sourceHalf st.basis=regValue sourceHalf s.basis :=
    regValue_congr _ _ _ (fun w hw => he.2.1 w (List.disjoint_left.mp parts.2.2 hw))
  let r2 := record.drop (measurementCount neg)
  have hc := copyRegister_correct none sourceHalf A hs nd.2 (by simp) st r2
  rw [fusedThresholdUnprepare,run_append,run_take]
  change (run (copyRegister none sourceHalf A) r2 st).phase=s.phase ∧ _
  refine ⟨hc.1.trans he.1,fun w hw => (hc.2.1 w hw).trans (he.2.1 w hw),?_⟩
  simpa only [copyValue,hv,hsource,Nat.xor_self] using hc.2.2

/-- No nonlinear gates are hidden in threshold preparation or unpreparation. -/
theorem fusedThresholdPreparation_counts (b : Wire) (sourceHalf A : List Wire)
    (hs : sourceHalf.length=A.length) :
    toffoliCount (fusedThresholdPrepare b sourceHalf A)=0 ∧
    measurementCount (fusedThresholdPrepare b sourceHalf A)=0 ∧
    toffoliCount (fusedThresholdUnprepare b sourceHalf A)=0 ∧
    measurementCount (fusedThresholdUnprepare b sourceHalf A)=0 := by
  have hc := copyRegister_counts none sourceHalf A hs
  have hn := signComplement_counts b A
  simp only [fusedThresholdPrepare,fusedThresholdUnprepare,toffoliCount_append,measurementCount_append,
    hc.1,hc.2,hn.1,hn.2,Option.isSome,Bool.false_eq_true,if_false,Nat.add_zero]
  trivial

/-- Complete raw-to-canonical front of the fused stream, retaining only raw
parity and normalization bits for the paid output-side cleanup. -/
def fusedSignedHalfFront (b cin low sign a h j l m : Wire) (Y R C carry : List Wire)
    (P : Nat) : Program :=
  let ac := carry.take (R.length-1)
  fusedRawNormalize b h Y R C ac carry cin P ++ [.CX low a] ++
    fusedCorrectionFlagsSeed sign a h j l m ++ fusedEvenHalf b a h j l m C R ac cin P

set_option maxHeartbeats 1000000 in
/-- Exact all-record front composition. The five early flags may be borrowed
from a later scratch word; no disjoint allocation for that word is assumed. -/
theorem fusedSignedHalfFront_correct (b cin low sign a h j l m : Wire) (Y R C carry : List Wire)
    (P X V : Nat) (hn : ([b,a,h,j,l,m,cin]++Y++R++C++carry).Nodup)
    (hY : Y.length=R.length) (hC : C.length=R.length) (hk : carry.length=R.length)
    (hlo : ∃ tail,R=low::tail) (hsg : ∃ loWord,R=loWord++[sign]) (hw : 0<R.length)
    (hp : P%2=1) (hX : X<P) (hV : V<P) (hfit : 2*P<2^(R.length-1))
    (s : State) (record : List Bool) (hy : regValue Y s.basis=V) (hr : regValue R s.basis=X)
    (hc0 : regValue C s.basis=0) (hk0 : regValue carry s.basis=0) (hi : s.basis cin=false)
    (ha0 : s.basis a=false) (hh0 : s.basis h=false) (hj0 : s.basis j=false)
    (hl0 : s.basis l=false) (hm0 : s.basis m=false) :
    (run (fusedSignedHalfFront b cin low sign a h j l m Y R C carry P) record s).phase=s.phase ∧
    (∀ w,w∉R → w≠a → w≠h →
      (run (fusedSignedHalfFront b cin low sign a h j l m Y R C carry P) record s).basis w=s.basis w) ∧
    regValue R (run (fusedSignedHalfFront b cin low sign a h j l m Y R C carry P) record s).basis=
      FusedSignedHalf.result P (s.basis b) X V ∧
    (run (fusedSignedHalfFront b cin low sign a h j l m Y R C carry P) record s).basis a=
      FusedSignedHalf.parity (FusedSignedHalf.signedSum (s.basis b) X V) ∧
    (run (fusedSignedHalfFront b cin low sign a h j l m Y R C carry P) record s).basis h=
      FusedSignedHalf.reduction P (FusedSignedHalf.signedSum (s.basis b) X V) := by
  let ac := carry.take (R.length-1)
  have hsub : ac.Sublist carry := List.take_sublist _ _
  have hac : ac.length+1=R.length := by simp [ac,hk]; omega
  have hpow : 2^R.length=2*2^(R.length-1) := by
    calc
      2^R.length=2^((R.length-1)+1) := by congr 1; omega
      _=2^(R.length-1)*2 := pow_succ _ _
      _=2*2^(R.length-1) := Nat.mul_comm _ _
  have hfull : 2*P<2^R.length := by omega
  have hraw : ([b,h,cin]++Y++R++C++carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have hbits : [b,a,h,j,l,m,cin].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  have dif := hbits
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,and_true] at dif
  have ah : a≠h := by tauto
  have aj : a≠j := by tauto
  have al : a≠l := by tauto
  have am : a≠m := by tauto
  have hj : h≠j := by tauto
  have hl : h≠l := by tauto
  have hm : h≠m := by tauto
  have bj : b≠j := by tauto
  have bl : b≠l := by tauto
  have bm : b≠m := by tauto
  have outside (w : Wire) (hw : w∈[b,a,h,j,l,m,cin]++Y++C++carry) : w∉R := by
    intro hwr
    have hc := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    have hrr := List.count_pos_iff.mpr hwr
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ho
    omega
  have safe (w : Wire) (hw : w∈[b,cin]++Y++C++carry) : w∉R ∧ w∉[a,h,j,l,m] := by
    refine ⟨outside w (by simp only [List.mem_cons,List.mem_append,List.mem_nil_iff] at hw ⊢; tauto),?_⟩
    intro hf
    have hc := List.nodup_iff_count.mp hn w
    have ho := List.count_pos_iff.mpr hw
    have hh := List.count_pos_iff.mpr hf
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ho hh
    omega
  have lowR : low∈R := by rcases hlo with ⟨tail,rfl⟩; simp
  have signR : sign∈R := by rcases hsg with ⟨loWord,rfl⟩; simp
  have lowa : low≠a := by intro he; subst low; exact outside a (by simp) lowR
  have signa : sign≠a := by intro he; subst sign; exact outside a (by simp) signR
  have hseed : [b,sign,a,h,j,l,m].Nodup := by
    rcases hsg with ⟨loWord,hsign⟩
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    have hz : ([sign]).count w≤R.count w := by rw [hsign,List.count_append]; omega
    simp only [List.count_cons,List.count_append,List.count_nil] at hc hz ⊢
    omega
  have heven : ([b,a,h,j,l,m,cin]++C++R++ac).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hc := List.nodup_iff_count.mp hn w
    have hz := hsub.count_le w
    simp only [List.count_cons,List.count_append,List.count_nil] at hc ⊢
    omega
  let raw := signedWordValue R.length (s.basis b) V X
  let S := FusedSignedHalf.signedSum (s.basis b) X V
  let H := FusedSignedHalf.reduction P S
  let A := FusedSignedHalf.parity S
  let rawProg := fusedRawNormalize b h Y R C ac carry cin P
  let st1 := run rawProg record s
  have hac0 : regValue ac s.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => (regValue_zero _ _).mp hk0 w (hsub.subset hw))
  have f1 := fusedRawNormalize_shared_correct b h Y R C ac carry cin P hraw hsub hY hC hac hk
    (by omega) s record hc0 hac0 hk0 hi hh0
  have rawR : regValue R st1.basis=raw := by simpa only [hy,hr] using f1.2.2.1
  have rawH : st1.basis h=H := by
    simpa only [hy,hr,fusedRawReduction R.length P X V (s.basis b) hX hV hfull] using f1.2.2.2
  have rawa0 : st1.basis a=false := (f1.2.1 a (outside a (by simp)) ah).trans ha0
  have rawb : st1.basis b=s.basis b := f1.2.1 b (outside b (by simp)) (by tauto)
  have rawlow : st1.basis low=A := by
    rcases hlo with ⟨tail,ht⟩
    have hb := fusedWordLowBit low tail st1.basis
    rw [←ht,rawR,fusedRawParity R.length P X V (s.basis b) hw hX hV hfull] at hb
    exact hb
  have rawsign : st1.basis sign=(st1.basis b&&st1.basis h) := by
    rcases hsg with ⟨loWord,ht⟩
    have hb := fusedWordTopBit loWord sign st1.basis
    have hlen : loWord.length=R.length-1 := by rw [ht,List.length_append,List.length_singleton]; omega
    rw [←ht,rawR,hlen,fusedRawSign R.length P X V (s.basis b) hw hX hV hfit,
      FusedSignedHalf.signedGuard_copy P (s.basis b) S (FusedSignedHalf.signedSum_domain P X V (s.basis b) hX hV)] at hb
    simpa only [rawb,rawH] using hb
  let r2 := record.drop (measurementCount rawProg)
  let st2 := run [.CX low a] r2 st1
  have f2 : st2.phase=st1.phase ∧ (∀ w,w≠a → st2.basis w=st1.basis w) ∧ st2.basis a=A := by
    refine ⟨rfl,?_,?_⟩
    · intro w hw'; simp [st2,run,writeBit,hw']
    · simp [st2,run,writeBit,rawa0,rawlow]
  have hsg2 : st2.basis sign=(st2.basis b&&st2.basis h) := by
    rw [f2.2.1 sign signa,f2.2.1 b (by tauto),f2.2.1 h ah.symm]
    exact rawsign
  let st3 := run (fusedCorrectionFlagsSeed sign a h j l m) r2 st2
  have f3 := fusedCorrectionFlagsSeed_correct b sign a h j l m hseed st2 r2
    (by rw [f2.2.1 j aj.symm,f1.2.1 j (outside j (by simp)) hj.symm]; exact hj0)
    (by rw [f2.2.1 l al.symm,f1.2.1 l (outside l (by simp)) hl.symm]; exact hl0)
    (by rw [f2.2.1 m am.symm,f1.2.1 m (outside m (by simp)) hm.symm]; exact hm0) hsg2
  have fixed (w : Wire) (hwR : w∉R) (hwF : w∉[a,h,j,l,m]) : st3.basis w=s.basis w := by
    have hd : w≠a ∧ w≠h ∧ w≠j ∧ w≠l ∧ w≠m := by simpa only [List.mem_cons,List.mem_nil_iff,not_or,not_false_eq_true,and_true] using hwF
    exact (f3.2.1 w hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2).trans
      ((f2.2.1 w hd.1).trans (f1.2.1 w hwR hd.2.1))
  have b3 : st3.basis b=s.basis b := fixed b (safe b (by simp)).1 (safe b (by simp)).2
  have a3 : st3.basis a=A := (f3.2.1 a aj al am).trans f2.2.2
  have h3 : st3.basis h=H := (f3.2.1 h hj hl hm).trans ((f2.2.1 h ah.symm).trans rawH)
  have R3 : regValue R st3.basis=raw := (regValue_congr _ _ _ (fun w hwR => by
    have hnF : w≠a ∧ w≠j ∧ w≠l ∧ w≠m := by
      constructor
      · intro hh'; subst w; exact outside a (by simp) hwR
      constructor
      · intro hh'; subst w; exact outside j (by simp) hwR
      constructor
      · intro hh'; subst w; exact outside l (by simp) hwR
      · intro hh'; subst w; exact outside m (by simp) hwR
    exact (f3.2.1 w hnF.2.1 hnF.2.2.1 hnF.2.2.2).trans (f2.2.1 w hnF.1))).trans rawR
  have hj3 : st3.basis j=(st3.basis b&&st3.basis h) := by
    rw [f3.2.2.1,f3.2.1 b bj bl bm,f3.2.1 h hj hl hm]
  have hl3 : st3.basis l=(st3.basis a&&st3.basis h) := by
    rw [f3.2.2.2.1,f3.2.1 a aj al am,f3.2.1 h hj hl hm]
  have hm3 : st3.basis m=(st3.basis a&&st3.basis j) := by
    rw [f3.2.2.2.2,f3.2.1 a aj al am,f3.2.2.1]
  have c3 : regValue C st3.basis=0 := (regValue_congr _ _ _ (fun w hw' =>
    fixed w (safe w (by simp [hw'])).1 (safe w (by simp [hw'])).2)).trans hc0
  have k3 : regValue ac st3.basis=0 := (regValue_congr _ _ _ (fun w hw' =>
    fixed w (safe w (by simp [hsub.subset hw'])).1 (safe w (by simp [hsub.subset hw'])).2)).trans hac0
  have i3 : st3.basis cin=false := (fixed cin (safe cin (by simp)).1 (safe cin (by simp)).2).trans hi
  have f4 := fusedEvenHalf_correct b a h j l m C R ac cin P X V heven hC hac hp hX hV hfull st3 r2
    c3 k3 i3 (by simpa only [b3] using a3) (by simpa only [b3] using h3) hj3 hl3 hm3
    (by simpa only [b3] using R3)
  rw [fusedSignedHalfFront,run_append,run_take,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,show measurementCount [.CX low a]=0 by rfl,
    (fusedCorrectionFlags_counts b sign a h j l m).2.1,Nat.add_zero]
  change (run (fusedEvenHalf b a h j l m C R ac cin P) r2 st3).phase=s.phase ∧ _
  refine ⟨f4.1.trans (f3.1.trans (f2.1.trans f1.1)),?_,?_,?_,?_⟩
  · intro w hwR hwa hwh
    by_cases hwj : w=j
    · subst w; exact f4.2.2.2.1.trans hj0.symm
    by_cases hwl : w=l
    · subst w; exact f4.2.2.2.2.1.trans hl0.symm
    by_cases hwm : w=m
    · subst w; exact f4.2.2.2.2.2.trans hm0.symm
    exact (f4.2.1 w hwR hwj hwl hwm).trans (fixed w hwR (by simp [hwa,hwh,hwj,hwl,hwm]))
  · simpa only [b3] using f4.2.2.1
  · exact (f4.2.1 a (outside a (by simp)) aj al am).trans a3
  · exact (f4.2.1 h (outside h (by simp)) hj hl hm).trans h3

/-- Exact emitted cost of the composed canonical front, with selector cleanup. -/
theorem fusedSignedHalfFront_counts (b cin low sign a h j l m : Wire) (Y R C carry : List Wire)
    (P : Nat) (hY : Y.length=R.length) (hC : C.length=R.length) (hk : carry.length=R.length)
    (hw : 0<R.length) :
    toffoliCount (fusedSignedHalfFront b cin low sign a h j l m Y R C carry P)=3*R.length ∧
    measurementCount (fusedSignedHalfFront b cin low sign a h j l m Y R C carry P)=3*R.length+1 := by
  let ac := carry.take (R.length-1)
  have ha : ac.length+1=R.length := by simp [ac,hk]; omega
  have hr := fusedRawNormalize_counts b h Y R C ac carry cin P hY hC ha hk
  have he := fusedEvenHalf_counts b a h j l m C R ac cin P hC ha
  have hf := fusedCorrectionFlags_counts b sign a h j l m
  dsimp only [ac] at hr he
  constructor
  · simp only [fusedSignedHalfFront,toffoliCount_append,hr.1,he.1,hf.1,
      show toffoliCount [.CX low a]=0 by rfl,Nat.add_zero]
    omega
  · simp only [fusedSignedHalfFront,measurementCount_append,hr.2,he.2,hf.2.1,
      show measurementCount [.CX low a]=0 by rfl,Nat.add_zero]
    omega

end ECDSAAdd.Arithmetic
