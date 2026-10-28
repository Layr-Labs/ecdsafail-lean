import ECDSAAdd.Arithmetic.ModUnary

namespace ECDSAAdd.Arithmetic

private theorem half_parity (U : ModUnaryLayout) (n Z : Nat)
    (hw : U.Widths n) (hnd : U.wires.Nodup) (hn : 0<n) :
    {{ U.z=Z,U.work=0 }} [.CX U.bit U.flag]
    {{ U.z=Z,U.core.work=0,U.mask=0,U.flag=decide (Z%2=1) }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero _ _).mp h.2
  have hf := clean U.flag (by simp [ModUnaryLayout.work])
  have hb := U.bit_value n hw hn s.basis
  rw [h.1] at hb
  have hv : s.basis U.bit=decide (Z%2=1) := by
    cases hh : s.basis U.bit <;> simp [hh] at hb ⊢ <;> omega
  have away (q : Wire) (hq : q∈U.z++U.core.work++U.mask) : q≠U.flag := by
    intro he; subst q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.nodup_iff_count.mp hnd U.flag
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h1 h2
    omega
  have keep (q : Wire) (hq : q∈U.z++U.core.work++U.mask) :
      (run [.CX U.bit U.flag] m s).basis q=s.basis q := by
    simp [run,writeBit,away q hq]
  refine ⟨rfl,⟨⟨?_,?_⟩,?_⟩,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1
  · apply (regValue_zero _ _).mpr
    intro q hq
    rw [keep q (by simp [hq])]
    exact clean q (by simp [ModUnaryLayout.work,hq])
  · apply (regValue_zero _ _).mpr
    intro q hq
    rw [keep q (by simp [hq])]
    exact clean q (by simp [ModUnaryLayout.work,hq])
  · simp [run,writeBit,hf,hv]

private theorem half_add (U : ModUnaryLayout) (n p Z : Nat) (B : Bool)
    (hw : U.Widths n) (hnd : U.wires.Nodup) (hp : p<2^(n+1)) :
    {{ U.z=Z,U.core.work=0,U.mask=0,U.flag=B }}
      maskedAddConst U.flag U.constant U.z U.carry U.cin p
    {{ U.z=((Z+(if B then p else 0))%2^(n+1)),U.core.work=0,U.mask=0,U.flag=B }} := by
  have hn : (U.flag::U.cin::U.constant++U.z++U.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hz : U.z.length=n+1 := by simp [ModUnaryLayout.z,hw.low]
  have ht := hw.constant.trans hz.symm
  have hc : U.carry.length+1=U.z.length := by rw [hw.carry,hz]
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero _ _).mp h.1.1.2
  have hT : regValue U.constant s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hC : regValue U.carry s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hcin := clean U.cin (by simp [ModUnaryLayout.core,ModAddCoreLayout.work])
  obtain ⟨hf,hv⟩ := maskedAddConst_spec U.flag U.cin U.constant U.z U.carry hn ht hc p
    (by simpa only [hw.constant] using hp) B Z s m ⟨⟨⟨⟨h.2,hT⟩,h.1.1.1⟩,hcin⟩,hC⟩
  simp only [Holds.holds] at hv
  refine ⟨hf,⟨⟨?_,?_⟩,?_⟩,hv.1.1.1.1⟩
  · simpa only [hz] using hv.1.1.2
  · apply (regValue_zero _ _).mpr
    intro q hq
    simp only [ModUnaryLayout.core,ModAddCoreLayout.work,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hq
    rcases hq with (hq | hq) | hq
    · exact (regValue_zero _ _).mp hv.1.1.1.2 q hq
    · exact (regValue_zero _ _).mp hv.2 q hq
    · subst q; exact hv.1.2
  · apply Eq.trans (regValue_congr _ _ _ ?_) h.1.2
    intro q hq
    apply run_preserves_outside
    intro hh
    have hm := List.mem_toFinset.mp ((maskedConst_wires_subset U.flag U.constant U.z U.carry U.cin p ht hc).1 hh)
    have h1 := List.count_pos_iff.mpr hm
    have h2 := List.count_pos_iff.mpr hq
    have h3 := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h1 h3
    omega

private theorem half_rotate (U : ModUnaryLayout) (Z : Nat) (B : Bool)
    (hnd : U.wires.Nodup) (heven : Z%2=0) :
    {{ U.z=Z,U.core.work=0,U.mask=0,U.flag=B }} rotateRight U.z
    {{ U.z=(Z/2),U.core.work=0,U.mask=0,U.flag=B }} := by
  have hznd := (List.nodup_append.mp hnd).1
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hf,hv⟩ := rotateRight_spec U.z hznd Z heven s m h.1.1.1
  have away (q : Wire) (hq : q∈U.work) : q∉U.z :=
    fun hh => List.disjoint_left.mp (List.nodup_append'.mp hnd).2.2 hh hq
  have keep (q : Wire) (hq : q∈U.work) := (rotate_frame U.z s m).2.1 q (away q hq)
  exact ⟨hf,⟨⟨hv,(regValue_congr _ _ _ (fun q hq => keep q (by simp [ModUnaryLayout.work,hq]))).trans h.1.1.2⟩,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [ModUnaryLayout.work,hq]))).trans h.1.2⟩,
    (keep U.flag (by simp [ModUnaryLayout.work])).trans h.2⟩

/-- 常数比较恢复全部非目标位；由已证寄存器规格与精确支持集推出。 -/
private theorem constCompare_frame (x T carry : List Wire) (cin target : Wire)
    (hnd : (target::cin::x++T++carry).Nodup) (hx : x.length=T.length) (hc : carry.length=T.length)
    (K : Nat) (hK : K<2^T.length) (s : State) (m : List Bool)
    (hT : regValue T s.basis=0) (hC : regValue carry s.basis=0) (hcin : s.basis cin=false) :
    ∀ q, q≠target → (run (compareLtConst none x T carry cin target K) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := compareLtConst_spec x T carry cin target hnd hx hc K hK
    (regValue x s.basis) (s.basis target) s m ⟨⟨⟨⟨rfl,hT⟩,hC⟩,hcin⟩,rfl⟩
  simp only [Holds.holds] at h
  intro q hq
  by_cases hqx : q∈x
  · exact (regValue_eq_iff _ _ _).mp h.1.1.1.1 q hqx
  by_cases hqt : q∈T
  · exact (regValue_eq_iff _ _ _).mp (h.1.1.1.2.trans hT.symm) q hqt
  by_cases hqc : q∈carry
  · exact (regValue_eq_iff _ _ _).mp (h.1.1.2.trans hC.symm) q hqc
  by_cases hqi : q=cin
  · subst q; exact h.1.2.trans hcin.symm
  apply run_preserves_outside
  rw [(compareLt_wires none x T carry cin target hx hc).2 K]
  simp [hq,hqx,hqt,hqc,hqi]

private theorem half_finish (U : ModUnaryLayout) (n R K : Nat) (B : Bool)
    (hw : U.Widths n) (hnd : U.wires.Nodup) (hR : R<2^n) (hK : K<2^n)
    (hB : B= !decide (R<K)) :
    {{ U.z=R,U.core.work=0,U.mask=0,U.flag=B }}
      (compareLtConst none U.low (U.constant.take U.low.length) U.carry U.cin U.flag K ++ [.X U.flag])
    {{ U.z=R,U.work=0 }} := by
  let T := U.constant.take U.low.length
  have ht : T.length=n := by simp [T,hw.low,hw.constant]
  have hn : (U.flag::U.cin::U.low++T++U.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hs := (List.take_sublist U.low.length U.constant).count_le q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.z,ModUnaryLayout.work,ModUnaryLayout.core,
      ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    dsimp [T]; omega
  intro s m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero _ _).mp h.1.1.2
  have hv : regValue U.low s.basis=R := by
    rw [regValue_low U.low U.high,← ModUnaryLayout.z,h.1.1.1,hw.low,Nat.mod_eq_of_lt hR]
  have hT : regValue T s.basis=0 := (regValue_zero _ _).mpr (fun q hq => clean q
    (by have hh := (List.take_sublist U.low.length U.constant).subset hq
        simp [ModUnaryLayout.core,ModAddCoreLayout.work,hh]))
  have hC : regValue U.carry s.basis=0 := (regValue_zero _ _).mpr (fun q hq => clean q
    (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hcin := clean U.cin (by simp [ModUnaryLayout.core,ModAddCoreLayout.work])
  have hx := hw.low.trans ht.symm
  have hc := hw.carry.trans ht.symm
  have hk : K<2^T.length := by simpa only [ht] using hK
  obtain ⟨hf,hv'⟩ := compareLtConst_spec U.low T U.carry U.cin U.flag hn hx hc K hk R B
    s m ⟨⟨⟨⟨hv,hT⟩,hC⟩,hcin⟩,h.2⟩
  simp only [Holds.holds] at hv'
  have he := constCompare_frame U.low T U.carry U.cin U.flag hn hx hc K hk s m hT hC hcin
  have hb : (run (compareLtConst none U.low T U.carry U.cin U.flag K) m s).basis U.flag=true := by
    rw [hv'.2,hB]; cases decide (R<K) <;> rfl
  have away (q : Wire) (hq : q∈U.z++U.core.work++U.mask) : q≠U.flag := by
    intro hh; subst q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.nodup_iff_count.mp hnd U.flag
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h1 h2
    omega
  rw [run_append,run_take]
  simp only [run]
  have keep (q : Wire) (hq : q∈U.z++U.core.work++U.mask) :
      writeBit (run (compareLtConst none U.low T U.carry U.cin U.flag K) m s).basis
        U.flag (!(run (compareLtConst none U.low T U.carry U.cin U.flag K) m s).basis U.flag) q=s.basis q := by
    simpa only [writeBit,Function.update_of_ne (away q hq)] using he q (away q hq)
  refine ⟨hf,(regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans h.1.1.1,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  simp only [ModUnaryLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with (hq | hq) | hq
  · exact (keep q (by simp [hq])).trans (clean q hq)
  · exact (keep q (by simp [hq])).trans ((regValue_zero _ _).mp h.1.2 q hq)
  · subst q
    simp only [writeBit,Function.update_self]
    change (!(run (compareLtConst none U.low T U.carry U.cin U.flag K) m s).basis U.flag)=false
    rw [hb]; rfl

/-- 规范模减半，所有 scratch 清零；奇偶由结果大小恢复并擦除。 -/
theorem halfInPlace_spec (U : ModUnaryLayout) (n p Z : Nat)
    (hw : U.Widths n) (hnd : U.wires.Nodup) (hp : p%2=1) (hpn : p<2^n) (hZ : Z<p) :
    {{ U.z=Z,U.work=0 }} halfInPlace U p {{ U.z=halveMod p Z,U.work=0 }} := by
  have hn : 0<n := by
    by_contra hh
    have hn0 : n=0 := by omega
    rw [hn0] at hpn
    simp at hpn
    omega
  let B := decide (Z%2=1)
  let V := Z+(if B then p else 0)
  have hv : V<2^(n+1) := by dsimp [V]; rw [Nat.pow_succ]; split <;> omega
  have he : V%2=0 := by
    simp only [V,B,decide_eq_true_eq]
    split_ifs <;> omega
  have hr := halve_mod_bound p Z hp hZ
  have hh : V/2=halveMod p Z := by simp only [V,B,decide_eq_true_eq,halveMod_eq]
  have hb : B= !decide (halveMod p Z<(p+1)/2) := by
    have hpar := halve_parity p Z hp hZ
    dsimp [B]
    by_cases ho : Z%2=1
    · have := hpar.mp ho; simp [ho,Nat.not_lt.mpr this]
    · have ht : halveMod p Z<(p+1)/2 := by omega
      simp [ho,ht]
  have h1 := half_parity U n Z hw hnd hn
  have h2 := half_add U n p Z B hw hnd (by rw [Nat.pow_succ]; omega)
  have h3 := half_rotate U V B hnd he
  have h4 := half_finish U n (halveMod p Z) ((p+1)/2) B hw hnd (by omega) (by omega) hb
  change {{ U.z=Z,U.core.work=0,U.mask=0,U.flag=B }} _
    {{ U.z=(V%2^(n+1)),U.core.work=0,U.mask=0,U.flag=B }} at h2
  rw [Nat.mod_eq_of_lt hv] at h2
  rw [hh] at h3
  simpa only [halfInPlace,List.append_assoc] using ((h1.seq h2).seq h3).seq h4

end ECDSAAdd.Arithmetic
