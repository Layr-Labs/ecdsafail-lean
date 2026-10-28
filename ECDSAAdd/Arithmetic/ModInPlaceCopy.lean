import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.Reduction

namespace ECDSAAdd.Arithmetic

/-- 只复制低 n 位；规范输入与掩码的未复制高位保持零，输出仍按完整寄存器读取。 -/
theorem copyLow_correct (c : Wire) (src dst : List Wire) (n X V : Nat)
    (hs : n≤src.length) (hd : n≤dst.length) (hnd : (c::src++dst).Nodup)
    (hX : X<2^n) (hV : V<2^n) (s : State) (m : List Bool)
    (hx : regValue src s.basis=X) (hv : regValue dst s.basis=V) :
    (run (copyRegister (some c) (src.take n) (dst.take n)) m s).phase=s.phase ∧
    (∀ q, q∉dst.take n → (run (copyRegister (some c) (src.take n) (dst.take n)) m s).basis q=s.basis q) ∧
    regValue dst (run (copyRegister (some c) (src.take n) (dst.take n)) m s).basis =
      V ^^^ (if s.basis c then X else 0) := by
  have hrest := (List.nodup_cons.mp hnd).2
  have hdst := (List.nodup_append.mp hrest).2.1
  have hsub : (src.take n ++ dst.take n).Nodup :=
    ((List.take_sublist n src).append (List.take_sublist n dst)).nodup hrest
  have hc : ∀ q ∈ some c, q ∉ dst.take n := by
    intro q hq hh
    have he : q=c := by simpa [eq_comm] using hq
    subst q
    exact (List.nodup_cons.mp hnd).1 (List.mem_append_right _ ((List.take_sublist n dst).subset hh))
  have hlen : (src.take n).length=(dst.take n).length := by
    simp [List.length_take, Nat.min_eq_left hs, Nat.min_eq_left hd]
  have low (r : List Wire) (N : Nat) (hr : n≤r.length)
      (hv : regValue r s.basis=N) (hb : N<2^n) :
      regValue (r.take n) s.basis=N ∧ regValue (r.drop n) s.basis=0 := by
    have hh := regValue_append (r.take n) (r.drop n) s.basis
    rw [List.take_append_drop, List.length_take, Nat.min_eq_left hr, hv] at hh
    have hn : 0<2^n := by positivity
    have ht := regValue_lt (r.take n) s.basis
    rw [List.length_take, Nat.min_eq_left hr] at ht
    have hz : regValue (r.drop n) s.basis=0 := by
      by_contra h
      have : 1≤regValue (r.drop n) s.basis := by omega
      nlinarith
    exact ⟨by simpa [hz] using hh.symm, hz⟩
  obtain ⟨hxl,_⟩ := low src X hs hx hX
  obtain ⟨hvl,hvz⟩ := low dst V hd hv hV
  obtain ⟨hf,he,ho⟩ := copyRegister_correct (some c) (src.take n) (dst.take n) hlen hsub hc s m
  refine ⟨hf,he,?_⟩
  have htail : regValue (dst.drop n) (run (copyRegister (some c) (src.take n) (dst.take n)) m s).basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hvz
    intro q hq
    apply he q
    intro hh
    exact List.disjoint_left.mp (List.disjoint_take_drop hdst (Nat.le_refl n)) hh hq
  have hh := regValue_append (dst.take n) (dst.drop n)
    (run (copyRegister (some c) (src.take n) (dst.take n)) m s).basis
  rw [List.take_append_drop, htail, Nat.mul_zero, Nat.add_zero] at hh
  rw [hh,ho,hxl,hvl]
  rfl

end ECDSAAdd.Arithmetic
