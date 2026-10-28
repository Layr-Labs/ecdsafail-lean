import ECDSAAdd.Arithmetic.DivideSupport
import ECDSAAdd.Math.BitcoinPrimes

namespace ECDSAAdd.Arithmetic

/-- 归还借用的输出高位后，乘积组合只修改256位acc；整个求逆历史逐线保持。 -/
theorem divideProduct_correct (L : DivideLayout) (hw : L.Widths) (hnd : L.wires.Nodup)
    (X Y Z : Nat) (B : Bool) (hX : X<p) (hY : Y<2^256) (hZ : Z<p)
    (s : State) (m : List Bool) (hb : s.basis L.control=B)
    (hx : regValue L.inner.middle.r s.basis=X) (hy : regValue L.numerator s.basis=Y)
    (hz : regValue L.acc s.basis=Z) (hc : regValue L.borrow s.basis=0) :
    ((run (montMulControlledAdd L.control L.multiply p) m s).phase=s.phase ∧
      regValue L.acc (run (montMulControlledAdd L.control L.multiply p) m s).basis=
        (if B then (Z+(X*Y)%p)%p else Z) ∧
      ∀ q∉L.acc, (run (montMulControlledAdd L.control L.multiply p) m s).basis q=s.basis q) ∧
    ((run (montMulControlledSub L.control L.multiply p) m s).phase=s.phase ∧
      regValue L.acc (run (montMulControlledSub L.control L.multiply p) m s).basis=
        (if B then (Z+p-(X*Y)%p)%p else Z) ∧
      ∀ q∉L.acc, (run (montMulControlledSub L.control L.multiply p) m s).basis q=s.basis q) := by
  letI : Fact p.Prime := ⟨Secp256k1.p_prime⟩
  have hp : p<2^256 := by norm_num [p]
  have hp0 : 0<p := by norm_num [p]
  have hs : [L.borrowedBit 0]++L.multiply.work ⊆ L.borrow := by
    rw [L.multiply_borrow hw]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have h0 : s.basis (L.borrowedBit 0)=false := clean _ (hs (by simp))
  have hwork : regValue L.multiply.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  have hout : regValue L.multiply.out s.basis=Z := by
    change regValue (L.acc++[L.borrowedBit 0]) s.basis=Z
    rw [regValue_append,hz]
    simp [regValue,h0]
  have ht := And.intro
    (montMulControlledAdd_spec L.control B L.multiply p X Y Z (L.multiply_widths hw)
      (L.multiply_nodup hw hnd) hp secp256k1_mod_sixteen hX hY hZ)
    (montMulControlledSub_spec L.control B L.multiply p X Y Z (L.multiply_widths hw)
      (L.multiply_nodup hw hnd) hp secp256k1_mod_sixteen hX hY hZ)
  have hf (q : Wire) (hq : q∉L.multiply.out) := And.intro
    (montMulControlledAdd_frame L.control B L.multiply p X Y Z (L.multiply_widths hw)
      (L.multiply_nodup hw hnd) hp secp256k1_mod_sixteen hX hY hZ s m hb hx hy hout hwork q hq)
    (montMulControlledSub_frame L.control B L.multiply p X Y Z (L.multiply_widths hw)
      (L.multiply_nodup hw hnd) hp secp256k1_mod_sixteen hX hY hZ s m hb hx hy hout hwork q hq)
  have finish (P : Program) (V : Nat) (hV : V<p)
      (hphase : (run P m s).phase=s.phase)
      (hval : regValue L.multiply.out (run P m s).basis=V)
      (hframe : ∀ q∉L.multiply.out, (run P m s).basis q=s.basis q) :
      (run P m s).phase=s.phase ∧ regValue L.acc (run P m s).basis=V ∧
        ∀ q∉L.acc, (run P m s).basis q=s.basis q := by
    have hlow := (regValue_low_iff L.acc [L.borrowedBit 0] (run P m s).basis V
      (by rw [hw.acc]; exact hV.trans hp)).mp hval
    refine ⟨hphase,hlow.1,?_⟩
    intro q hq
    by_cases he : q=L.borrowedBit 0
    · subst q
      exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans h0.symm
    · apply hframe q
      change q∉L.acc++[L.borrowedBit 0]
      simp [hq,he]
  obtain ⟨hpa,ha⟩ := ht.1 s m ⟨⟨⟨⟨hb,hx⟩,hy⟩,hout⟩,hwork⟩
  obtain ⟨hps,hsub⟩ := ht.2 s m ⟨⟨⟨⟨hb,hx⟩,hy⟩,hout⟩,hwork⟩
  exact ⟨finish _ _ (by split <;> first | exact Nat.mod_lt _ hp0 | exact hZ) hpa ha.1.2 (fun q hq => (hf q hq).1),
    finish _ _ (by split <;> first | exact Nat.mod_lt _ hp0 | exact hZ) hps hsub.1.2 (fun q hq => (hf q hq).2)⟩

end ECDSAAdd.Arithmetic
