import ECDSAAdd.Arithmetic.ControlledDoubleSteps

namespace ECDSAAdd.Arithmetic

/-- 受控规范模加倍，借位从控制与结果奇偶清除。 -/
theorem controlledDouble_spec (c : Wire) (U : ModUnaryLayout) (n p Z : Nat) (C : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hp : p%2=1) (hpn : p<2^n) (hZ : Z<p) :
    {{ c=C,U.z=Z,U.work=0 }} controlledDouble c U p
    {{ c=C,U.z=(if C then (2*Z)%p else Z),U.work=0 }} := by
  have hpos : 0<p := by omega
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  let V := if C then 2*Z else Z
  let D := (V+2^(n+1)-(if C then p else 0))%2^(n+1)
  let R := if C then (2*Z)%p else Z
  let B := C && decide (2*Z<p)
  have hsmall : Z<2^n := by omega
  have hwide : Z<2^(n+1) := by rw [Nat.pow_succ]; omega
  have hb : 2^n≤D ↔ B=true := by
    cases C with
    | false => simp [D,V,B,Nat.mod_eq_of_lt hwide,Nat.not_le.mpr hsmall]
    | true =>
      simpa only [D,V,B,if_true,Bool.true_and,decide_eq_true_eq] using
        (addReduction (2*Z) p n hpos hpn (by omega)).1
  have hr : (D%2^n+(if B then p else 0))%2^n=R := by
    cases C with
    | false => simp [D,V,B,R,Nat.mod_eq_of_lt hwide,Nat.mod_eq_of_lt hsmall]
    | true =>
      simpa only [D,V,B,R,if_true,Bool.true_and,decide_eq_true_eq] using
        modAddCore_low (2*Z) p n hpos hpn (by omega)
  have hB : B=(C && !decide (R%2=1)) := by
    cases C with
    | false => simp [B]
    | true =>
      have hh := (double_flag p Z hp hZ).2.2
      dsimp [B,R]
      simp only [Bool.true_and]
      by_cases ht : 2*Z<p
      · have ho : ¬(2*Z)%p%2=1 := by omega
        simp [ht,ho]
      · have ho : (2*Z)%p%2=1 := hh.mpr (by omega)
        simp [ht,ho]
  have h1 := UnaryValues.left c U Z C false hnd (by
    intro _; simp only [ModUnaryLayout.z,List.length_append,List.length_cons,List.length_nil,hw.low]
    rw [Nat.pow_succ]; omega)
  have h2 := UnaryValues.sub c U n p V C false hw hnd (by rw [Nat.pow_succ]; omega)
  have h3 := DoubleValues.addback c U n p D R C B hw hnd hn hpn hb hr
  have h4 := DoubleValues.finish c U n R C B hw hnd hn hB
  have hall : Triple (UnaryValues c U C Z false) (controlledDouble c U p)
      (UnaryValues c U C R false) := by
    simpa only [controlledDouble,List.append_assoc,V,D] using ((h1.seq h2).seq h3).seq h4
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero _ _).mp h.2
  have hk : regValue U.core.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.work,hq]))
  have hm : regValue U.mask s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.work,hq]))
  obtain ⟨hf,hc,hz,hk',hm',hflag⟩ := hall s m
    ⟨h.1.1,h.1.2,hk,hm,clean U.flag (by simp [ModUnaryLayout.work])⟩
  refine ⟨hf,⟨hc,hz⟩,(regValue_zero _ _).mpr ?_⟩
  intro q hq
  simp only [ModUnaryLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with (hq | hq) | hq
  · exact (regValue_zero _ _).mp hk' q hq
  · exact (regValue_zero _ _).mp hm' q hq
  · subst q; exact hflag

end ECDSAAdd.Arithmetic
