import ECDSAAdd.Arithmetic.ControlledUnaryState

namespace ECDSAAdd.Arithmetic

/-- 受控规范模减半；活动为假逐位保持，所有工作位初末为零。 -/
theorem controlledHalf_spec (c : Wire) (U : ModUnaryLayout) (n p Z : Nat) (C : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hp : p%2=1) (hpn : p<2^n) (hZ : Z<p) :
    {{ c=C,U.z=Z,U.work=0 }} controlledHalf c U p
    {{ c=C,U.z=(if C then halveMod p Z else Z),U.work=0 }} := by
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  let F := C && decide (Z%2=1)
  let V := Z+(if F then p else 0)
  let R := if C then halveMod p Z else Z
  have hv : V<2^(n+1) := by dsimp [V]; rw [Nat.pow_succ]; split <;> omega
  have he : C=true → V%2=0 := by
    intro hC
    simp only [V,F,hC,Bool.true_and,decide_eq_true_eq]
    split_ifs <;> omega
  have hr : R<p := by dsimp [R]; split; exact halve_mod_bound p Z hp hZ; exact hZ
  have hh : (if C then V/2 else V)=R := by
    cases C <;> simp [R,V,F,halveMod_eq]
  have hb : F=(C && !decide (R<(p+1)/2)) := by
    have hpar := halve_parity p Z hp hZ
    cases C with
    | false => simp [F]
    | true =>
      dsimp [F,R]
      simp only [Bool.true_and]
      by_cases ho : Z%2=1
      · have := hpar.mp ho; simp [ho,Nat.not_lt.mpr this]
      · have ht : halveMod p Z<(p+1)/2 := by omega
        simp [ho,ht]
  have h1 := UnaryValues.parity c U n Z C hw hnd hn
  have h2 := UnaryValues.add c U n p Z C F hw hnd (by rw [Nat.pow_succ]; omega)
  have h3 := UnaryValues.right c U V C F hnd he
  have h4 := UnaryValues.finish c U n R ((p+1)/2) C F hw hnd (by omega) (by omega) hb
  change Triple (UnaryValues c U C Z F) _ (UnaryValues c U C (V%2^(n+1)) F) at h2
  rw [Nat.mod_eq_of_lt hv] at h2
  rw [hh] at h3
  have hall : Triple (UnaryValues c U C Z false) (controlledHalf c U p)
      (UnaryValues c U C R false) := by
    simpa only [controlledHalf,List.append_assoc,F] using ((h1.seq h2).seq h3).seq h4
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
