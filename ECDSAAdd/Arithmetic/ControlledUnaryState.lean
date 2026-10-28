import ECDSAAdd.Arithmetic.ControlledModUnary

namespace ECDSAAdd.Arithmetic

/-- 单目步骤的中间断言：奇偶位可存活，其余工作位为零。 -/
def UnaryValues (c : Wire) (U : ModUnaryLayout) (C : Bool) (Z : Nat) (F : Bool)
    (s : BasisState) : Prop :=
  s c=C ∧ regValue U.z s=Z ∧ regValue U.core.work s=0 ∧ regValue U.mask s=0 ∧ s U.flag=F

namespace UnaryValues

theorem flag_away (U : ModUnaryLayout) (hn : U.wires.Nodup)
    (q : Wire) (hq : q∈U.z++U.core.work++U.mask) : q≠U.flag := by
  intro he; subst q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.nodup_iff_count.mp hn U.flag
  simp only [ModUnaryLayout.wires,ModUnaryLayout.work,List.count_append,List.count_cons,
    List.count_nil,beq_self_eq_true,if_true] at h1 h2
  omega

theorem parity (c : Wire) (U : ModUnaryLayout) (n Z : Nat) (C : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hn : 0<n) :
    Triple (UnaryValues c U C Z false) [.CCX c U.bit U.flag]
      (UnaryValues c U C Z (C && decide (Z%2=1))) := by
  intro s m h
  rcases h with ⟨hc,hz,hk,hm,hf⟩
  have hcne : c≠U.flag := fun he => (List.nodup_cons.mp hnd).1
    (he ▸ (by simp [ModUnaryLayout.wires,ModUnaryLayout.work]))
  have hb := U.bit_value n hw hn s.basis
  rw [hz] at hb
  have hv : s.basis U.bit=decide (Z%2=1) := by
    cases hh : s.basis U.bit <;> simp [hh] at hb ⊢ <;> omega
  have keep (q : Wire) (hq : q∈U.z++U.core.work++U.mask) :
      (run [.CCX c U.bit U.flag] m s).basis q=s.basis q := by
    simp [run,writeBit,flag_away U (List.nodup_cons.mp hnd).2 q hq]
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · simpa [run,writeBit,hcne] using hc
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hz
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hk
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hm
  · simp [run,writeBit,hf,hv,hc]

theorem add (c : Wire) (U : ModUnaryLayout) (n p Z : Nat) (C F : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hp : p<2^(n+1)) :
    Triple (UnaryValues c U C Z F)
      (maskedAddConst U.flag U.constant U.z U.carry U.cin p)
      (UnaryValues c U C ((Z+(if F then p else 0))%2^(n+1)) F) := by
  have hn : (U.flag::U.cin::U.constant++U.z++U.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hzlen : U.z.length=n+1 := by simp [ModUnaryLayout.z,hw.low]
  have ht := hw.constant.trans hzlen.symm
  have hcarry : U.carry.length+1=U.z.length := by rw [hw.carry,hzlen]
  intro s m h
  rcases h with ⟨hc,hz,hk,hm,hf⟩
  have clean := (regValue_zero _ _).mp hk
  have hT : regValue U.constant s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hC : regValue U.carry s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hi := clean U.cin (by simp [ModUnaryLayout.core,ModAddCoreLayout.work])
  obtain ⟨phase,v⟩ := maskedAddConst_spec U.flag U.cin U.constant U.z U.carry hn ht hcarry p
    (by simpa only [hw.constant] using hp) F Z s m ⟨⟨⟨⟨hf,hT⟩,hz⟩,hi⟩,hC⟩
  simp only [Holds.holds] at v
  have away (q : Wire) (hq : q∈c::U.mask) :
      q∉wires (maskedAddConst U.flag U.constant U.z U.carry U.cin p) := by
    intro hh
    have hmem := List.mem_toFinset.mp ((maskedConst_wires_subset U.flag U.constant U.z U.carry U.cin p ht hcarry).1 hh)
    have h1 := List.count_pos_iff.mpr hmem
    have h2 := List.count_pos_iff.mpr hq
    have h3 := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h1 h2 h3
    omega
  refine ⟨phase,(run_preserves_outside _ _ _ c (away c (by simp))).trans hc,?_,?_,?_,v.1.1.1.1⟩
  · simpa only [hzlen] using v.1.1.2
  · apply (regValue_zero _ _).mpr
    intro q hq
    simp only [ModUnaryLayout.core,ModAddCoreLayout.work,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hq
    rcases hq with (hq | hq) | hq
    · exact (regValue_zero _ _).mp v.1.1.1.2 q hq
    · exact (regValue_zero _ _).mp v.2 q hq
    · subst q; exact v.1.2
  · exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ _ _ q (away q (by simp [hq])))).trans hm

theorem right (c : Wire) (U : ModUnaryLayout) (Z : Nat) (C F : Bool)
    (hnd : (c::U.wires).Nodup) (heven : C=true → Z%2=0) :
    Triple (UnaryValues c U C Z F) (shiftRight c U.z)
      (UnaryValues c U C (if C then Z/2 else Z) F) := by
  have hn : (c::U.z).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,List.count_append,List.count_cons] at h ⊢
    omega
  intro s m h
  rcases h with ⟨hc,hz,hk,hm,hf⟩
  obtain ⟨phase,v⟩ := shiftRight_spec c U.z hn C Z heven s m ⟨hc,hz⟩
  have away (q : Wire) (hq : q∈U.work) : q∉U.z :=
    fun hh => List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.2 hh hq
  have keep (q : Wire) (hq : q∈U.work) := (shift_frame c U.z s m).2.1 q (away q hq)
  exact ⟨phase,v.1,v.2,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [ModUnaryLayout.work,hq]))).trans hk,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [ModUnaryLayout.work,hq]))).trans hm,
    (keep U.flag (by simp [ModUnaryLayout.work])).trans hf⟩


theorem compare_frame (c : Wire) (x T carry : List Wire) (cin target : Wire)
    (hnd : (c::target::cin::x++T++carry).Nodup) (hx : x.length=T.length) (hc : carry.length=T.length)
    (K : Nat) (hK : K<2^T.length) (s : State) (m : List Bool)
    (hT : regValue T s.basis=0) (hC : regValue carry s.basis=0) (hcin : s.basis cin=false) :
    ∀ q, q≠target → (run (compareLtConst (some c) x T carry cin target K) m s).basis q=s.basis q := by
  obtain ⟨_,h⟩ := maskedCompareLtConst_spec c x T carry cin target hnd hx hc K hK
    (s.basis c) (regValue x s.basis) (s.basis target) s m ⟨⟨⟨⟨⟨rfl,rfl⟩,hT⟩,hC⟩,hcin⟩,rfl⟩
  simp only [Holds.holds] at h
  intro q hq
  by_cases hqc : q=c
  · subst q; exact h.1.1.1.1.1
  by_cases hqx : q∈x
  · exact (regValue_eq_iff _ _ _).mp h.1.1.1.1.2 q hqx
  by_cases hqt : q∈T
  · exact (regValue_eq_iff _ _ _).mp (h.1.1.1.2.trans hT.symm) q hqt
  by_cases hqr : q∈carry
  · exact (regValue_eq_iff _ _ _).mp (h.1.1.2.trans hC.symm) q hqr
  by_cases hqi : q=cin
  · subst q; exact h.1.2.trans hcin.symm
  apply run_preserves_outside
  rw [(compareLt_wires (some c) x T carry cin target hx hc).2 K]
  simp [hq,hqx,hqt,hqc,hqr,hqi]

theorem finish (c : Wire) (U : ModUnaryLayout) (n R K : Nat) (C F : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hR : R<2^n) (hK : K<2^n)
    (hF : F=(C && !decide (R<K))) :
    Triple (UnaryValues c U C R F)
      (compareLtConst (some c) U.low (U.constant.take U.low.length) U.carry U.cin U.flag K ++ [.CX c U.flag])
      (UnaryValues c U C R false) := by
  let T := U.constant.take U.low.length
  have ht : T.length=n := by simp [T,hw.low,hw.constant]
  have hn : (c::U.flag::U.cin::U.low++T++U.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    have hs := (List.take_sublist U.low.length U.constant).count_le q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.z,ModUnaryLayout.work,ModUnaryLayout.core,
      ModAddCoreLayout.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    dsimp [T]; omega
  intro s m h
  rcases h with ⟨hc,hz,hk,hm,hf⟩
  have clean := (regValue_zero _ _).mp hk
  have hv : regValue U.low s.basis=R := by
    rw [regValue_low U.low U.high,← ModUnaryLayout.z,hz,hw.low,Nat.mod_eq_of_lt hR]
  have hT : regValue T s.basis=0 := (regValue_zero _ _).mpr (fun q hq => clean q
    (by have hh := (List.take_sublist U.low.length U.constant).subset hq
        simp [ModUnaryLayout.core,ModAddCoreLayout.work,hh]))
  have hC : regValue U.carry s.basis=0 := (regValue_zero _ _).mpr (fun q hq => clean q
    (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hi := clean U.cin (by simp [ModUnaryLayout.core,ModAddCoreLayout.work])
  have hx := hw.low.trans ht.symm
  have hr := hw.carry.trans ht.symm
  have hkk : K<2^T.length := by simpa only [ht] using hK
  obtain ⟨phase,v⟩ := maskedCompareLtConst_spec c U.low T U.carry U.cin U.flag hn hx hr K hkk C R F
    s m ⟨⟨⟨⟨⟨hc,hv⟩,hT⟩,hC⟩,hi⟩,hf⟩
  simp only [Holds.holds] at v
  have he := compare_frame c U.low T U.carry U.cin U.flag hn hx hr K hkk s m hT hC hi
  have hb : (run (compareLtConst (some c) U.low T U.carry U.cin U.flag K) m s).basis U.flag=C := by
    rw [v.2,hF]; cases C <;> cases decide (R<K) <;> rfl
  have hcne : c≠U.flag := fun hh => (List.nodup_cons.mp hn).1 (by simp [hh])
  rw [run_append,run_take]
  simp only [run]
  have keep (q : Wire) (hq : q∈U.z++U.core.work++U.mask) :
      writeBit (run (compareLtConst (some c) U.low T U.carry U.cin U.flag K) m s).basis
        U.flag ((run (compareLtConst (some c) U.low T U.carry U.cin U.flag K) m s).basis U.flag ^^
        (run (compareLtConst (some c) U.low T U.carry U.cin U.flag K) m s).basis c) q=s.basis q := by
    simpa only [writeBit,Function.update_of_ne (flag_away U (List.nodup_cons.mp hnd).2 q hq)] using
      he q (flag_away U (List.nodup_cons.mp hnd).2 q hq)
  refine ⟨phase,?_,?_,?_,?_,?_⟩
  · simpa only [writeBit,Function.update_of_ne hcne] using v.1.1.1.1.1
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hz
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hk
  · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hm
  · simp only [writeBit,Function.update_self]
    change ((run (compareLtConst (some c) U.low T U.carry U.cin U.flag K) m s).basis U.flag ^^
      (run (compareLtConst (some c) U.low T U.carry U.cin U.flag K) m s).basis c)=false
    rw [hb,v.1.1.1.1.1,Bool.xor_self]

theorem sub (c : Wire) (U : ModUnaryLayout) (n p Z : Nat) (C F : Bool)
    (hw : U.Widths n) (hnd : (c::U.wires).Nodup) (hp : p<2^(n+1)) :
    Triple (UnaryValues c U C Z F)
      (maskedSubConst c U.constant U.z U.carry U.cin p)
      (UnaryValues c U C ((Z+2^(n+1)-(if C then p else 0))%2^(n+1)) F) := by
  have hn : (c::U.cin::U.constant++U.z++U.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hzlen : U.z.length=n+1 := by simp [ModUnaryLayout.z,hw.low]
  have ht := hw.constant.trans hzlen.symm
  have hcarry : U.carry.length+1=U.z.length := by rw [hw.carry,hzlen]
  intro s m h
  rcases h with ⟨hc,hz,hk,hm,hf⟩
  have clean := (regValue_zero _ _).mp hk
  have hT : regValue U.constant s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hC : regValue U.carry s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (by simp [ModUnaryLayout.core,ModAddCoreLayout.work,hq]))
  have hi := clean U.cin (by simp [ModUnaryLayout.core,ModAddCoreLayout.work])
  obtain ⟨phase,v⟩ := maskedSubConst_spec c U.cin U.constant U.z U.carry hn ht hcarry p
    (by simpa only [hw.constant] using hp) C Z s m ⟨⟨⟨⟨hc,hT⟩,hz⟩,hi⟩,hC⟩
  simp only [Holds.holds] at v
  have away (q : Wire) (hq : q∈U.flag::U.mask) :
      q∉wires (maskedSubConst c U.constant U.z U.carry U.cin p) := by
    intro hh
    have hmem := List.mem_toFinset.mp ((maskedConst_wires_subset c U.constant U.z U.carry U.cin p ht hcarry).2 hh)
    have h1 := List.count_pos_iff.mpr hmem
    have h2 := List.count_pos_iff.mpr hq
    have h3 := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,ModUnaryLayout.work,ModUnaryLayout.core,ModAddCoreLayout.work,
      List.count_append,List.count_cons,List.count_nil] at h1 h2 h3
    omega
  refine ⟨phase,v.1.1.1.1,?_,?_,?_,(run_preserves_outside _ _ _ U.flag (away U.flag (by simp))).trans hf⟩
  · simpa only [hzlen] using v.1.1.2
  · apply (regValue_zero _ _).mpr
    intro q hq
    simp only [ModUnaryLayout.core,ModAddCoreLayout.work,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hq
    rcases hq with (hq | hq) | hq
    · exact (regValue_zero _ _).mp v.1.1.1.2 q hq
    · exact (regValue_zero _ _).mp v.2 q hq
    · subst q; exact v.1.2
  · exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ _ _ q (away q (by simp [hq])))).trans hm

theorem left (c : Wire) (U : ModUnaryLayout) (Z : Nat) (C F : Bool)
    (hnd : (c::U.wires).Nodup) (hfit : C=true → 2*Z<2^U.z.length) :
    Triple (UnaryValues c U C Z F) (shiftLeft c U.z)
      (UnaryValues c U C (if C then 2*Z else Z) F) := by
  have hn : (c::U.z).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hnd q
    simp only [ModUnaryLayout.wires,List.count_append,List.count_cons] at h ⊢
    omega
  intro s m h
  rcases h with ⟨hc,hz,hk,hm,hf⟩
  obtain ⟨phase,v⟩ := shiftLeft_spec c U.z hn C Z hfit s m ⟨hc,hz⟩
  have away (q : Wire) (hq : q∈U.work) : q∉U.z :=
    fun hh => List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hnd).2).2.2 hh hq
  have keep (q : Wire) (hq : q∈U.work) := (shift_frame c U.z s m).2.2.2 q (away q hq)
  exact ⟨phase,v.1,v.2,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [ModUnaryLayout.work,hq]))).trans hk,
    (regValue_congr _ _ _ (fun q hq => keep q (by simp [ModUnaryLayout.work,hq]))).trans hm,
    (keep U.flag (by simp [ModUnaryLayout.work])).trans hf⟩



end UnaryValues
end ECDSAAdd.Arithmetic
