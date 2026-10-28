import ECDSAAdd.Arithmetic.PointInPlaceProgram
import ECDSAAdd.Arithmetic.PointInPlaceLayoutProof

namespace ECDSAAdd.Arithmetic
open ControlledPointLayout Secp256k1

private theorem constant_mask (M : ModInPlaceLayout) (c : Wire) (k A Z : Nat) (B : Bool)
    (hn : (c::M.wires).Nodup) (hk : k<2^M.a.length) :
    {{ c=B,M.a=A,M.z=Z,M.work=0 }} maskedConstant c M.a k
    {{ c=B,M.a=(A ^^^ (if B then k else 0)),M.z=Z,M.work=0 }} := by
  have hc : c∉M.a := by
    intro h
    exact (List.nodup_cons.mp hn).1 (by simp [ModInPlaceLayout.wires,h])
  have hna : M.a.Nodup := by
    have h := (List.nodup_cons.mp hn).2
    exact (List.nodup_append.mp (List.nodup_append.mp h).1).1
  intro s m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hp,hframe,hvalue⟩ := maskedConstant_correct c M.a k hna hc hk s m
  have away (q : Wire) (hq : q∈M.z++M.work) : q∉M.a := by
    intro ha
    have h := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr ha
    simp only [ModInPlaceLayout.wires,List.count_append,List.count_cons] at h h1
    omega
  refine ⟨hp,⟨⟨(hframe c hc).trans h.1.1.1,?_⟩,?_⟩,?_⟩
  · simpa only [h.1.1.1,h.1.1.2] using hvalue
  · exact (regValue_congr _ _ _ (fun q hq => hframe q (away q (List.mem_append_left _ hq)))).trans h.1.2
  · exact (regValue_congr _ _ _ (fun q hq => hframe q (away q (List.mem_append_right _ hq)))).trans h.2

private theorem constant_add (M : ModInPlaceLayout) (c : Wire) (A Z : Nat) (B : Bool)
    (hw : M.Widths 256) (hn : (c::M.wires).Nodup) (hA : A≤p) (hZ : Z<p) :
    {{ c=B,M.a=A,M.z=Z,M.work=0 }} modAddInPlace M p
    {{ c=B,M.a=A,M.z=(Z+A)%p,M.work=0 }} := by
  intro s m h
  have hp : 0<p := by norm_num [p]
  have hpn : p<2^256 := by norm_num [p]
  have hnd := (List.nodup_cons.mp hn).2
  obtain ⟨hf,hv⟩ := modAddInPlace_spec M 256 p A Z hw hnd hp hpn hA hZ
    s m ⟨⟨h.1.1.2,h.1.2⟩,h.2⟩
  have hc : c∉M.z := by
    intro hh
    exact (List.nodup_cons.mp hn).1 (by simp [ModInPlaceLayout.wires,hh])
  have keep := modAddInPlace_frame M 256 p A Z hw hnd hp hpn hA hZ s m h.1.1.2 h.1.2 h.2 c hc
  exact ⟨hf,⟨⟨keep.trans h.1.1.1,hv.1.1⟩,hv.1.2⟩,hv.2⟩

/-- 掩码源在模加后仍保留，第二次CX序列将其清零。 -/
theorem constant_program_spec (M : ModInPlaceLayout) (c : Wire) (k Z : Nat) (B : Bool)
    (hw : M.Widths 256) (hn : (c::M.wires).Nodup) (hk : k<p) (hZ : Z<p) :
    {{ c=B,M.a=0,M.z=Z,M.work=0 }}
      (maskedConstant c M.a k ++ modAddInPlace M p ++ maskedConstant c M.a k)
    {{ c=B,M.a=0,M.z=(Z+(if B then k else 0))%p,M.work=0 }} := by
  have hkp : k<2^M.a.length := by
    simp only [hw.core.a,Nat.reduceAdd]
    have hp : p<2^256 := by norm_num [p]
    have hmono (n : Nat) : 2^n≤2^(n+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hm := hmono 256
    simp only [Nat.reduceAdd] at hm
    exact hk.trans (hp.trans_le hm)
  have ha := constant_mask M c k 0 Z B hn hkp
  simp only [Nat.zero_xor] at ha
  have hb := constant_add M c (if B then k else 0) Z B hw hn (by split <;> omega) hZ
  have hc := constant_mask M c k (if B then k else 0) ((Z+(if B then k else 0))%p) B hn hkp
  simpa only [Nat.xor_self] using (ha.seq hb).seq hc

theorem constant_program_frame (M : ModInPlaceLayout) (c : Wire) (k Z : Nat) (B : Bool)
    (hw : M.Widths 256) (hn : (c::M.wires).Nodup) (hk : k<p) (hZ : Z<p)
    (s : State) (m : List Bool) (hb : s.basis c=B) (ha : regValue M.a s.basis=0)
    (hz : regValue M.z s.basis=Z) (hc : regValue M.work s.basis=0)
    (q : Wire) (hq : q∉M.z) :
    (run (maskedConstant c M.a k ++ modAddInPlace M p ++ maskedConstant c M.a k) m s).basis q=s.basis q := by
  obtain ⟨_,hv⟩ := constant_program_spec M c k Z B hw hn hk hZ s m ⟨⟨⟨hb,ha⟩,hz⟩,hc⟩
  by_cases hqc : q=c
  · subst q; exact hv.1.1.1.trans hb.symm
  by_cases hqa : q∈M.a
  · exact (regValue_eq_iff _ _ _).mp (hv.1.1.2.trans ha.symm) q hqa
  by_cases hqw : q∈M.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.trans hc.symm) q hqw
  apply run_preserves_outside
  intro hh
  have hm := maskedConstant_wires_subset c M.a k
  rw [wires_append,wires_append] at hh
  have hcore : q∉M.toModAddCoreLayout.wires := by
    intro hh'
    have hw' : q∉M.toModAddCoreLayout.work := by
      intro h; exact hqw (by simp [ModInPlaceLayout.work,h])
    simp only [ModAddCoreLayout.wires,List.mem_append,ModInPlaceLayout.z] at hh' hq
    tauto
  have hmask : q∉wires (maskedConstant c M.a k) := by
    intro h; have h' := hm h
    simp [hqc,hqa] at h'
  have hmid : q∉wires (modAddInPlace M p) := by
    rw [modAddInPlace,modAddCore_wires M.toModAddCoreLayout 256 p hw.core (by omega)]
    simpa using hcore
  simp [hmask,hmid] at hh

/-- 常数加法在低256位上给出规范结果，源、目标高位及其余线路逐线恢复。 -/
theorem pointInPlaceConstantAdd_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (r : List Wire) (hr : r=L.point.x ∨ r=L.point.y)
    (k : Fp) (Z : Nat) (B : Bool) (hZ : Z<p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hz : regValue r s.basis=Z)
    (hc : regValue L.inPlaceBorrow s.basis=0) :
    (run (pointInPlaceConstantAdd L r k) m s).phase=s.phase ∧
      regValue r (run (pointInPlaceConstantAdd L r k) m s).basis=(Z+(if B then k.val else 0))%p ∧
      ∀ q∉r,(run (pointInPlaceConstantAdd L r k) m s).basis q=s.basis q := by
  let M := L.inPlaceConstant r
  have hl : r.length=256 := by rcases hr with rfl | rfl; exact hw.inputX; exact hw.inputY
  have hM := L.inPlaceConstant_widths hw r hl
  have hnm : (L.core.generic::M.wires).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.inPlace_interfaces_nodup hw hnd) q
    have ht := (List.take_sublist 1030 L.inPlaceBorrow).count_le q
    rw [← L.inPlaceConstant_borrow hw r] at ht
    have hbc := L.inPlaceBorrow_count q
    rcases hr with rfl | rfl
    all_goals
      simp only [M,inPlaceConstant,inPlaceUnary,ModInPlaceLayout.wires,ModInPlaceLayout.z,ModInPlaceLayout.work,
        ModUnaryLayout.core,ModAddCoreLayout.z,ModAddCoreLayout.work,PointAddLayout.pointWires,inPlaceFlags,
        List.count_append,List.count_cons,List.count_nil] at h ht ⊢
      omega
  have hs : L.inPlaceBorrow.take 257++[L.inPlaceBit 257]++M.work ⊆ L.inPlaceBorrow := by
    rw [L.inPlaceConstant_borrow hw r]
    exact (List.take_sublist _ _).subset
  have clean := (regValue_zero _ _).mp hc
  have hhigh : s.basis (L.inPlaceBit 257)=false := clean _ (hs (by simp))
  have ha : M.a=L.inPlaceBorrow.take 257 := by simp only [M,inPlaceConstant]
  have hsource : regValue M.a s.basis=0 := by
    rw [ha]
    exact (regValue_zero _ _).mpr
      (fun q hq => clean q (hs (List.mem_append_left _ (List.mem_append_left _ hq))))
  have hwork : regValue M.work s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hs (List.mem_append_right _ hq)))
  have hout : regValue M.z s.basis=Z := by
    simp only [M,inPlaceConstant,ModInPlaceLayout.z,ModUnaryLayout.core,inPlaceUnary,ModAddCoreLayout.z]
    rw [regValue_append,hz]
    simp [regValue,hhigh]
  obtain ⟨hp,hv⟩ := constant_program_spec M L.core.generic k.val Z B hM hnm k.isLt hZ
    s m ⟨⟨⟨hb,hsource⟩,hout⟩,hwork⟩
  have keep := constant_program_frame M L.core.generic k.val Z B hM hnm k.isLt hZ s m hb hsource hout hwork
  have hzView : M.z=r++[L.inPlaceBit 257] := by
    simp only [M,inPlaceConstant,ModInPlaceLayout.z,ModUnaryLayout.core,inPlaceUnary,ModAddCoreLayout.z]
  rw [hzView] at hv
  have hlow := (regValue_low_iff r [L.inPlaceBit 257]
    (run (pointInPlaceConstantAdd L r k) m s).basis ((Z+(if B then k.val else 0))%p)
    (by rw [hl]; exact (Nat.mod_lt _ (by norm_num [p])).trans (by norm_num [p]))).mp hv.1.2
  refine ⟨hp,hlow.1,?_⟩
  intro q hq
  by_cases he : q=L.inPlaceBit 257
  · subst q
    exact ((regValue_zero _ _).mp hlow.2 _ (by simp)).trans hhigh.symm
  · apply keep q
    simp only [M,inPlaceConstant,ModInPlaceLayout.z,ModUnaryLayout.core,inPlaceUnary,ModAddCoreLayout.z]
    simp [hq,he]

end ECDSAAdd.Arithmetic
