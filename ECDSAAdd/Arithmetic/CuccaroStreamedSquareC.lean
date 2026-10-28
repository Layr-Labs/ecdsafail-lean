import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option exponentiation.threshold 512

namespace ECDSAAdd.Arithmetic
namespace CuccaroStreamedSquareWideLayout

theorem square129_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (S : Nat)
    (hS : regValue L.core.sum base=S)
    (hprod : regValue L.core.product base=0)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame L.core.product base 0) L.core.square129
      (SquareFrame L.core.product base (S^2)) := by
  let mask := L.core.work.take 129
  have nd : (L.core.cin::L.core.sum++L.core.product++L.core.pad++mask++
      ([] : List Wire)).Nodup := by
    dsimp [mask]
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hnd q
    have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
    have hm := (List.take_sublist 129 L.core.work).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have mask0 : regValue mask base=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hwork q (List.mem_of_mem_take hq))
  intro s records h
  have away (q : Wire)
      (hq : q∈L.core.sum++L.core.pad++mask++[L.core.cin]) : q∉L.core.product := by
    intro hp
    have hn := List.nodup_iff_count.mp nd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hp
    simp only [List.count_append,List.count_cons,List.count_nil] at hn h1
    omega
  have sumS : regValue L.core.sum s.basis=S := by
    rw [←hS]
    apply regValue_congr
    intro q hq
    exact h.2 q (away q (by simp [hq]))
  have padS : regValue L.core.pad s.basis=0 := by
    rw [←hpad]
    apply regValue_congr
    intro q hq
    exact h.2 q (away q (by simp [hq]))
  have maskS : regValue mask s.basis=0 := by
    rw [←mask0]
    apply regValue_congr
    intro q hq
    exact h.2 q (away q (by simp [hq]))
  have cinS : s.basis L.core.cin=false :=
    (h.2 _ (away _ (by simp))).trans hcin
  have runh := cuccaroSignedTriangularSquare_forward_correct L.core.cin
    L.core.sum L.core.product L.core.pad mask [] nd (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) (by simp [hw.core.pad])
    (by simp [mask,hw.core.work,L.core.sum_length hw.core]) s records h.1 padS maskS rfl cinS
  refine ⟨runh.1,?_,?_⟩
  · simpa [sumS] using runh.2.1
  · intro q hq
    by_cases hs : q∈L.core.sum
    · exact ((regValue_eq_iff L.core.sum _ _).mp runh.2.2.1 q hs).trans
        (h.2 q (away q (by simp [hs])))
    by_cases hp : q∈L.core.pad
    · exact ((regValue_eq_iff L.core.pad _ _).mp (runh.2.2.2.1.trans padS.symm) q hp).trans
        (h.2 q (away q (by simp [hp])))
    by_cases hm : q∈mask
    · exact ((regValue_eq_iff mask _ _).mp (runh.2.2.2.2.1.trans maskS.symm) q hm).trans
        (h.2 q (away q (by simp [hm])))
    by_cases hc : q=L.core.cin
    · subst q; exact runh.2.2.2.2.2.2.trans hcin.symm
    have hsupp := (cuccaroSignedTriangularSquare_wires_subset L.core.cin
      L.core.sum L.core.product L.core.pad mask []
      (by simp [L.core.sum_length hw.core])
      (by simp [hw.core.product,L.core.sum_length hw.core])
      (by simp [hw.core.pad]) (by simp [mask,hw.core.work,L.core.sum_length hw.core])).1
    have untouched : (run L.core.square129 records s).basis q=s.basis q := by
      apply run_preserves_outside
      intro hmemb
      have hh := List.mem_toFinset.mp (hsupp hmemb)
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh
      tauto
    exact untouched.trans (h.2 q hq)

theorem square129Clear_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (S : Nat)
    (hS : regValue L.core.sum base=S)
    (hprod : regValue L.core.product base=0)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (SquareFrame L.core.product base (S^2)) L.core.square129Clear
      (SquareFrame L.core.product base 0) := by
  let mask := L.core.work.take 129
  have nd : (L.core.cin::L.core.sum++L.core.product++L.core.pad++mask++
      ([] : List Wire)).Nodup := by
    dsimp [mask]
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hnd q
    have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
    have hm := (List.take_sublist 129 L.core.work).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have ftriple := L.square129_frame hw hnd base S hS hprod hpad hwork hcin
  intro s records hs
  let z : State := ⟨s.phase,base⟩
  have zpre : SquareFrame L.core.product base 0 z.basis :=
    ⟨hprod,fun _ _ => rfl⟩
  have f := ftriple z [] zpre
  let u := run L.core.square129 [] z
  have us : u=s := by
    have ph : u.phase=s.phase := f.1
    have bs : u.basis=s.basis := by
      funext q
      by_cases hq : q∈L.core.product
      · exact (regValue_eq_iff L.core.product u.basis s.basis).mp
          (f.2.1.trans hs.1.symm) q hq
      · exact (f.2.2 q hq).trans (hs.2 q hq).symm
    calc
      u = ⟨u.phase,u.basis⟩ := rfl
      _ = ⟨s.phase,s.basis⟩ := by rw [ph,bs]
      _ = s := rfl
  have rr := cuccaroSignedTriangularSquare_roundtrip L.core.cin L.core.sum
    L.core.product L.core.pad mask [] nd z [] records
  change run L.core.square129Clear records u=z at rr
  rw [us] at rr
  rw [rr]
  exact ⟨rfl,hprod,fun _ _ => rfl⟩

theorem square129_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (S O : Nat)
    (hS : regValue L.core.sum base=S)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (PairFrame L base 0 O) L.core.square129
      (PairFrame L base (S^2) O) := by
  have dis := L.product_out_disjoint hnd
  have sumAway (q : Wire) (hq : q∈L.core.sum) :
      q∉L.core.product ∧ q∉L.core.out := by
    constructor <;> intro hm
    all_goals
      have h := List.nodup_iff_count.mp hnd q
      have h1 := List.count_pos_iff.mpr hq
      have h2 := List.count_pos_iff.mpr hm
      have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
      have hh2 := (List.drop_sublist 128 L.core.y).count_le q
      simp only [wires,CuccaroStreamedSquareLayout.wires,
        CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
        List.count_append,List.count_cons,List.count_nil] at h h1
      omega
  intro s records h
  have sumS : regValue L.core.sum s.basis=S := by
    rw [←hS]
    apply regValue_congr
    intro q hq
    exact h.frame q (sumAway q hq).1 (sumAway q hq).2
  have padS : regValue L.core.pad s.basis=0 := by
    rw [←hpad]
    apply regValue_congr
    intro q hq
    have away := L.pairAuxAway hnd q (by simp [foldPad,hq])
    exact h.frame q away.1 away.2
  have workS : regValue L.core.work s.basis=0 := by
    rw [←hwork]
    apply regValue_congr
    intro q hq
    have away := L.pairAuxAway hnd q (by simp [hq])
    exact h.frame q away.1 away.2
  have cinS : s.basis L.core.cin=false := by
    have away := L.pairAuxAway hnd L.core.cin (by simp)
    exact (h.frame _ away.1 away.2).trans hcin
  have sq := L.square129_frame hw hnd s.basis S sumS h.product
    padS workS cinS s records
    ⟨h.product,fun _ _ => rfl⟩
  let out := run L.core.square129 records s
  have outputO : regValue L.core.out out.basis=O :=
    (regValue_congr _ _ _ (fun q hq => sq.2.2 q
      (fun hp => List.disjoint_left.mp dis hp hq))).trans h.out
  refine ⟨sq.1,sq.2.1,outputO,?_⟩
  intro q hp ho
  exact (sq.2.2 q hp).trans (h.frame q hp ho)

theorem square129Clear_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (S O : Nat)
    (hS : regValue L.core.sum base=S)
    (hprod : regValue L.core.product base=0)
    (hpad : regValue L.core.pad base=0) (hwork : regValue L.core.work base=0)
    (hcin : base L.core.cin=false) :
    Triple (PairFrame L base (S^2) O) L.core.square129Clear
      (PairFrame L base 0 O) := by
  have dis := L.product_out_disjoint hnd
  have sumAwayOut (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out := by
    intro ho
    have h := List.nodup_iff_count.mp hnd q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr ho
    have hh1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have hh2 := (List.drop_sublist 128 L.core.y).count_le q
    simp only [wires,CuccaroStreamedSquareLayout.wires,
      CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,
      List.count_append,List.count_cons,List.count_nil] at h h1
    omega
  intro s records h
  let cleanBase : BasisState := fun q => if q∈L.core.out then s.basis q else base q
  have localProd : regValue L.core.product cleanBase=0 := by
    rw [←hprod]
    apply regValue_congr
    intro q hq
    simp [cleanBase,List.disjoint_left.mp dis hq]
  have localSum : regValue L.core.sum cleanBase=S := by
    rw [←hS]
    apply regValue_congr
    intro q hq
    simp [cleanBase,sumAwayOut q hq]
  have localPad : regValue L.core.pad cleanBase=0 := by
    rw [←hpad]
    apply regValue_congr
    intro q hq
    have away : q∉L.core.out := (L.pairAuxAway hnd q (by simp [foldPad,hq])).2
    simp [cleanBase,away]
  have localWork : regValue L.core.work cleanBase=0 := by
    rw [←hwork]
    apply regValue_congr
    intro q hq
    have away : q∉L.core.out := (L.pairAuxAway hnd q (by simp [hq])).2
    simp [cleanBase,away]
  have localCin : cleanBase L.core.cin=false := by
    have away : L.core.cin∉L.core.out := (L.pairAuxAway hnd _ (by simp)).2
    simp [cleanBase,away,hcin]
  have pre : SquareFrame L.core.product cleanBase (S^2) s.basis := by
    constructor
    · exact h.product
    · intro q hp
      simp only [cleanBase]
      by_cases ho : q∈L.core.out
      · simp [ho]
      rw [if_neg ho]
      exact h.frame q hp ho
  have clear := L.square129Clear_frame hw hnd cleanBase S localSum localProd
    localPad localWork localCin s records pre
  let out := run L.core.square129Clear records s
  have outputO : regValue L.core.out out.basis=O := by
    calc
      regValue L.core.out out.basis = regValue L.core.out cleanBase :=
        regValue_congr _ _ _ (fun q hq => clear.2.2 q
          (fun hp => List.disjoint_left.mp dis hp hq))
      _ = regValue L.core.out s.basis := by
        apply regValue_congr
        intro q hq
        simp [cleanBase,hq]
      _ = O := h.out
  refine ⟨clear.1,clear.2.1,outputO,?_⟩
  intro q hp ho
  rw [clear.2.2 q hp]
  simp [cleanBase,ho,h.frame q hp ho]

def branchCMiddleValue (S O : Nat) : Nat :=
  subRotateProductValue (S^2) O true

theorem branchC_middle_pair (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (S O : Nat)
    (hS : regValue L.core.sum base=S)
    (hprod : regValue L.core.product base=0)
    (hO : O<SquareReduction.p) (hc : PairClean L base) :
    Triple (PairFrame L base 0 O)
      (L.core.square129++L.subRotate128 true++L.core.square129Clear)
      (PairFrame L base 0 (branchCMiddleValue S O)) := by
  have hp : 0<SquareReduction.p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let O1 := subRotateProductValue (S^2) O true
  have sqT := L.square129_pair hw hnd base S O hS
    (PairClean.corePad L base hc) hc.work hc.cin
  have rotT := L.subRotate128_pair hw hnd true base (S^2) O hO hc
  have clrT := L.square129Clear_pair hw hnd base S O1 hS hprod
    (PairClean.corePad L base hc) hc.work hc.cin
  intro s records hs
  let s1 := run L.core.square129 [] s
  let s2 := run (L.subRotate128 true) [] s1
  let s3 := run L.core.square129Clear records s2
  have e1 := sqT s [] hs
  have e2 := rotT s1 [] e1.2
  have e3 := clrT s2 records e2.2
  have sqm := L.core.square129_counts hw.core
  have rotm := L.rotate128_counts hw
  have exec : run
      (L.core.square129++L.subRotate128 true++L.core.square129Clear)
      records s=s3 := by
    simp [s1,s2,s3,run_append,sqm.1.2,rotm.2.2.2]
  rw [exec]
  exact ⟨e3.1.trans (e2.1.trans e1.1),e3.2⟩

end CuccaroStreamedSquareWideLayout
end ECDSAAdd.Arithmetic
