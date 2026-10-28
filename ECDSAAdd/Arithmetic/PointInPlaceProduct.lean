import ECDSAAdd.Arithmetic.PointInPlaceLayoutProof

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout

/-- 外部乘加/乘减只改当前y；两个扩展高位和全部借用位在边界归零。 -/
theorem pointInPlaceProduct_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (A X Y : Nat) (hA : A<p) (hX : X<p) (hY : Y<p)
    (s : State) (m : List Bool) (ha : regValue L.inPlaceSlope s.basis=A)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hz : regValue L.inPlaceBorrow s.basis=0) :
    ((run (montMulAdd L.inPlaceMultiply p) m s).phase=s.phase ∧
      regValue L.point.y (run (montMulAdd L.inPlaceMultiply p) m s).basis=(Y+(A*X)%p)%p ∧
      ∀ q∉L.point.y,(run (montMulAdd L.inPlaceMultiply p) m s).basis q=s.basis q) ∧
    ((run (montMulSub L.inPlaceMultiply p) m s).phase=s.phase ∧
      regValue L.point.y (run (montMulSub L.inPlaceMultiply p) m s).basis=(Y+p-(A*X)%p)%p ∧
      ∀ q∉L.point.y,(run (montMulSub L.inPlaceMultiply p) m s).basis q=s.basis q) := by
  letI : Fact p.Prime := ⟨Secp256k1.p_prime⟩
  have hp : p<2^256 := by norm_num [p]
  have hp0 : 0<p := by norm_num [p]
  have hs : [L.inPlaceBit 0,L.inPlaceBit 1]++L.inPlaceMultiply.work ⊆ L.inPlaceBorrow := by
    rw [L.inPlaceMultiply_borrow hw]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hz
  have h0 : s.basis (L.inPlaceBit 0)=false := clean _ (hs (by simp))
  have h1 : s.basis (L.inPlaceBit 1)=false := clean _ (hs (by simp))
  have hwork : regValue L.inPlaceMultiply.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  have hin : regValue L.inPlaceMultiply.x s.basis=A := by
    change regValue (L.inPlaceSlope++[L.inPlaceBit 0]) s.basis=A
    rw [regValue_append,ha]
    simp [regValue,h0]
  have hout : regValue L.inPlaceMultiply.out s.basis=Y := by
    change regValue (L.point.y++[L.inPlaceBit 1]) s.basis=Y
    rw [regValue_append,hy]
    simp [regValue,h1]
  have hwf := L.inPlaceMultiply_widths hw
  have hnf := L.inPlaceMultiply_nodup hw hnd
  have keep (q : Wire) (hq : q∉L.inPlaceMultiply.out) := And.intro
    (montMulAdd_frame L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
      s m hin hx hout hwork q hq)
    (montMulSub_frame L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
      s m hin hx hout hwork q hq)
  have finish (P : Program) (V : Nat) (hV : V<p)
      (hphase : (run P m s).phase=s.phase)
      (hval : regValue L.inPlaceMultiply.out (run P m s).basis=V)
      (hframe : ∀ q∉L.inPlaceMultiply.out,(run P m s).basis q=s.basis q) :
      (run P m s).phase=s.phase ∧ regValue L.point.y (run P m s).basis=V ∧
        ∀ q∉L.point.y,(run P m s).basis q=s.basis q := by
    have hlow := (regValue_low_iff L.point.y [L.inPlaceBit 1] (run P m s).basis V
      (by rw [show L.point.y.length=256 from hw.inputY]; exact hV.trans hp)).mp hval
    refine ⟨hphase,hlow.1,?_⟩
    intro q hq
    by_cases he : q=L.inPlaceBit 1
    · subst q
      exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans h1.symm
    · apply hframe q
      change q∉L.point.y++[L.inPlaceBit 1]
      simp [hq,he]
  obtain ⟨hpa,hva⟩ := montMulAdd_spec L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
    s m ⟨⟨⟨hin,hx⟩,hout⟩,hwork⟩
  obtain ⟨hps,hvs⟩ := montMulSub_spec L.inPlaceMultiply p A X Y hwf hnf hp secp256k1_mod_sixteen hA (hX.trans hp) hY
    s m ⟨⟨⟨hin,hx⟩,hout⟩,hwork⟩
  exact ⟨finish _ _ (Nat.mod_lt _ hp0) hpa hva.1.2 (fun q hq => (keep q hq).1),
    finish _ _ (Nat.mod_lt _ hp0) hps hvs.1.2 (fun q hq => (keep q hq).2)⟩

end ECDSAAdd.Arithmetic
