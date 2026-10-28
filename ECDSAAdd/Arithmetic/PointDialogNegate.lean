import ECDSAAdd.Arithmetic.PointRecoveryOperations

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

def pointDialogNegate (L : ControlledPointLayout) : Program := pointRecoveryNegate L

/-- Compatibility with the existing public zero-work negation interface. -/
theorem pointDialogNegate_spec (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) :
    {{ L.core.generic=B,L.dialogNegate.a=A,L.dialogNegate.z=0,L.dialogNegate.work=0 }}
      pointDialogNegate L
    {{ L.core.generic=B,L.dialogNegate.a=(if B then (p-A)%p else A),
      L.dialogNegate.z=0,L.dialogNegate.work=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have he : L.dialogNegate.a=L.point.x++[L.core.poolWire 0] := by simp only [dialogNegate]
  have hpn : p<2^256 := by norm_num [p]
  have low := (regValue_low_iff L.point.x [L.core.poolWire 0] s.basis A
    (by rw [show L.point.x.length=256 from hw.inputX];exact hA.trans hpn)).mp (he ▸ h.1.1.2)
  let K := L.recoveryNegate
  have pool : [L.core.poolWire 0]++L.dialogNegate.z++L.dialogNegate.work=L.dialogPool.take 1030 :=
    L.dialogNegate_borrow hw
  have allZero : ∀q∈L.dialogPool.take 1030,s.basis q=false := by
    rw [←pool]
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq|hq)|hq
    · exact (regValue_zero _ _).mp low.2 q hq
    · exact (regValue_zero _ _).mp h.1.2 q hq
    · exact (regValue_zero _ _).mp h.2 q hq
  have poolSubset : L.dialogPool.take 258⊆L.dialogPool.take 1030 := by
    intro q hq
    have eq : (L.dialogPool.take 1030).take 258=L.dialogPool.take 258 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←eq] at hq
    exact List.mem_of_mem_take hq
  have aux (q : Wire) (hq : q∈K.work++[K.cin,K.zero]) : s.basis q=false := by
    change q∈L.recoveryNegate.work++[L.recoveryNegate.cin,L.recoveryNegate.zero] at hq
    rw [L.recoveryNegate_pool hw] at hq
    exact allZero q (poolSubset hq)
  have work : regValue K.work s.basis=0 := (regValue_zero _ _).mpr (fun q hq => aux q (by simp [hq]))
  have sizes : K.work.length=K.word.length := by simp [K,recoveryNegate,point,hw.inputX,L.dialogPool_length hw]
  have result := K.program_correct L.core.generic (L.recoveryNegate_nodup hw hnd) sizes
    (by simp [K,recoveryNegate,point,hw.inputX]) p SquareReduction.c A
    (by simp [K,recoveryNegate,point,hw.inputX];norm_num [p,SquareReduction.c])
    (by norm_num [SquareReduction.c]) hA s m low.1 work (aux _ (by simp)) (aux _ (by simp))
  rw [h.1.1.1] at result
  change (run (pointDialogNegate L) m s).phase=s.phase ∧
    regValue L.point.x (run (pointDialogNegate L) m s).basis=(if B then (p-A)%p else A) ∧
    (∀q,q∉L.point.x → (run (pointDialogNegate L) m s).basis q=s.basis q) at result
  have same (q : Wire) (hq : q∈L.core.generic::L.core.poolWire 0::L.dialogNegate.z++L.dialogNegate.work) :
      (run (pointDialogNegate L) m s).basis q=s.basis q := by
    apply result.2.2 q
    intro bad
    have nd := List.nodup_iff_count.mp (L.dialogNegate_nodup hw hnd) q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [ModInPlaceLayout.wires,he,List.count_cons,List.count_append,List.count_nil] at nd a
    omega
  refine ⟨result.1,⟨⟨?_,?_⟩,?_⟩,?_⟩
  · exact (same _ (by simp)).trans h.1.1.1
  · rw [he,regValue_append,result.2.1]
    have z : (run (pointDialogNegate L) m s).basis (L.core.poolWire 0)=false :=
      (same _ (by simp)).trans ((regValue_zero _ _).mp low.2 _ (by simp))
    simp [regValue,z]
  · exact (regValue_congr _ _ _ (fun q hq => same q (by simp [hq]))).trans h.1.2
  · exact (regValue_congr _ _ _ (fun q hq => same q (by simp [hq]))).trans h.2

theorem pointDialogNegate_correct (L : ControlledPointLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (A : Nat) (B : Bool) (hA : A<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=A)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (pointDialogNegate L) m s).phase=s.phase ∧
      regValue L.point.x (run (pointDialogNegate L) m s).basis=(if B then (p-A)%p else A) ∧
      ∀ q∉L.point.x,(run (pointDialogNegate L) m s).basis q=s.basis q :=
  pointRecoveryNegate_correct L hw hnd A B hA s m hb hx hc

end ECDSAAdd.Arithmetic
