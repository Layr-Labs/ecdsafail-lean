import ECDSAAdd.Arithmetic.ControlledNegRaw

namespace ECDSAAdd.Arithmetic

namespace ModInPlaceLayout
/-- Copy-mask view: its source is the mask; its unused outer mask is the live original source. -/
def signedMaskView (L : ModInPlaceLayout) : ModInPlaceLayout := { L with a:=L.mask,mask:=L.a }

theorem signedMaskView_widths (L : ModInPlaceLayout) (n : Nat) (hw : L.Widths n) :
    L.signedMaskView.Widths n :=
  ⟨⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩,hw.core.a⟩

theorem signedMaskView_nodup (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) : (c::L.signedMaskView.wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hh := List.nodup_iff_count.mp hn w
  simp only [signedMaskView,wires,work,z,ModAddCoreLayout.z,ModAddCoreLayout.work,
    List.count_cons,List.count_append,List.count_nil] at hh ⊢
  omega
end ModInPlaceLayout

/-- Exact signed modular addition. Load the clean mask, conditionally negate it,
add it once, restore the mask's original value, then erase with Clifford copying.
The polarity is addition for g=true and subtraction for g=false. -/
def skywalkSignedModAdd (g : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  copyRegister none L.a L.mask ++ [.X g] ++
  controlledNegRaw g L.signedMaskView p ++ modAddCore L.maskedCore p ++
  controlledNegRaw g L.signedMaskView p ++ [.X g] ++ copyRegister none L.a L.mask

private def SignedMaskFrame (c : Wire) (L : ModInPlaceLayout) (base : BasisState)
    (C : Bool) (A Z M : Nat) (s : BasisState) : Prop :=
  s c=C ∧ regValue L.a s=A ∧ regValue L.z s=Z ∧ regValue L.mask s=M ∧
    ∀ w,w≠c → w∉L.a → w∉L.z → w∉L.mask → s w=base w

private theorem signed_control_outside (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) : c∉L.a ∧ c∉L.z ∧ c∉L.mask := by
  have hh := (List.nodup_cons.mp hn).1
  refine ⟨?_,?_,?_⟩ <;> intro hm <;>
    apply hh <;> simp [ModInPlaceLayout.wires,ModInPlaceLayout.work,hm]

private theorem signed_mask_away (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) (w : Wire) (hw : w=c ∨ w∈L.a ∨ w∈L.z) : w∉L.mask := by
  intro hm
  have hh := List.nodup_iff_count.mp hn w
  have hM := List.count_pos_iff.mpr hm
  simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_cons,List.count_append,
    List.count_nil] at hh
  rcases hw with rfl | hw | hw
  · simp only [beq_self_eq_true,if_true] at hh; omega
  · have := List.count_pos_iff.mpr hw; omega
  · have := List.count_pos_iff.mpr hw; omega

private theorem signed_target_away (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) (w : Wire) (hw : w=c ∨ w∈L.a ∨ w∈L.mask) : w∉L.z := by
  intro hm
  have hh := List.nodup_iff_count.mp hn w
  have hZ := List.count_pos_iff.mpr hm
  simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_cons,List.count_append,
    List.count_nil] at hh
  rcases hw with rfl | hw | hw
  · simp only [beq_self_eq_true,if_true] at hh; omega
  · have := List.count_pos_iff.mpr hw; omega
  · have := List.count_pos_iff.mpr hw; omega

private theorem signed_core_clean (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) (base s : BasisState) (C : Bool) (A Z M : Nat)
    (hk : regValue L.toModAddCoreLayout.work base=0)
    (h : SignedMaskFrame c L base C A Z M s) : regValue L.toModAddCoreLayout.work s=0 := by
  apply (regValue_zero _ _).mpr
  intro w hw
  have hh := List.nodup_iff_count.mp hn w
  have hK := List.count_pos_iff.mpr hw
  simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_cons,List.count_append,
    List.count_nil] at hh
  have hc : w≠c := by intro he; subst w; simp only [beq_self_eq_true,if_true] at hh; omega
  have ha : w∉L.a := by intro hm; have := List.count_pos_iff.mpr hm; omega
  have hz : w∉L.z := by intro hm; have := List.count_pos_iff.mpr hm; omega
  have hm : w∉L.mask := by intro hm; have := List.count_pos_iff.mpr hm; omega
  rw [h.2.2.2.2 w hc ha hz hm]
  exact (regValue_zero _ _).mp hk w hw

private theorem signed_update_mask (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) (base s t : BasisState) (C : Bool) (A Z M N : Nat)
    (h : SignedMaskFrame c L base C A Z M s) (hv : regValue L.mask t=N)
    (he : ∀ w,w∉L.mask → t w=s w) : SignedMaskFrame c L base C A Z N t := by
  refine ⟨(he c (signed_mask_away c L hn c (Or.inl rfl))).trans h.1,
    (regValue_congr _ _ _ (fun w hw => he w (signed_mask_away c L hn w (by tauto)))).trans h.2.1,
    (regValue_congr _ _ _ (fun w hw => he w (signed_mask_away c L hn w (by tauto)))).trans h.2.2.1,
    hv,fun w hc ha hz hm => (he w hm).trans (h.2.2.2.2 w hc ha hz hm)⟩

private theorem signed_update_target (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) (base s t : BasisState) (C : Bool) (A Z M N : Nat)
    (h : SignedMaskFrame c L base C A Z M s) (hv : regValue L.z t=N)
    (he : ∀ w,w∉L.z → t w=s w) : SignedMaskFrame c L base C A N M t := by
  refine ⟨(he c (signed_target_away c L hn c (Or.inl rfl))).trans h.1,
    (regValue_congr _ _ _ (fun w hw => he w (signed_target_away c L hn w (by tauto)))).trans h.2.1,
    hv,(regValue_congr _ _ _ (fun w hw => he w (signed_target_away c L hn w (by tauto)))).trans h.2.2.2.1,
    fun w hc ha hz hm => (he w hz).trans (h.2.2.2.2 w hc ha hz hm)⟩

private theorem signed_copy_step (c : Wire) (L : ModInPlaceLayout) (n : Nat)
    (hw : L.Widths n) (hn : (c::L.wires).Nodup) (base : BasisState)
    (C : Bool) (A Z M : Nat) :
    Triple (SignedMaskFrame c L base C A Z M) (copyRegister none L.a L.mask)
      (SignedMaskFrame c L base C A Z (M^^^A)) := by
  intro st m h
  have hnd : (L.a++L.mask).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,List.count_cons,List.count_append,
      List.count_nil] at hh ⊢
    omega
  obtain ⟨hf,he,hv⟩ := copyRegister_correct none L.a L.mask (hw.core.a.trans hw.mask.symm) hnd
    (by simp) st m
  refine ⟨hf,signed_update_mask c L hn base st.basis _ C A Z M _ h ?_ he⟩
  simpa only [copyValue,h.2.1,h.2.2.2.1] using hv

private theorem signed_flip_step (c : Wire) (L : ModInPlaceLayout)
    (hn : (c::L.wires).Nodup) (base : BasisState) (C : Bool) (A Z M : Nat) :
    Triple (SignedMaskFrame c L base C A Z M) [.X c] (SignedMaskFrame c L base (!C) A Z M) := by
  intro st m h
  have hc := signed_control_outside c L hn
  have keep (w : Wire) (hw : w≠c) : (run [.X c] m st).basis w=st.basis w := by
    simp [run,writeBit,hw]
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · simpa [run,writeBit] using congrArg Bool.not h.1
  · exact (regValue_congr _ _ _ (fun w hw => keep w (fun he => hc.1 (he ▸ hw)))).trans h.2.1
  · exact (regValue_congr _ _ _ (fun w hw => keep w (fun he => hc.2.1 (he ▸ hw)))).trans h.2.2.1
  · exact (regValue_congr _ _ _ (fun w hw => keep w (fun he => hc.2.2 (he ▸ hw)))).trans h.2.2.2.1
  · intro w hw ha hz hm
    exact (keep w hw).trans (h.2.2.2.2 w hw ha hz hm)

private theorem signed_neg_step (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : (c::L.wires).Nodup) (hp : p<2^n) (base : BasisState)
    (hk : regValue L.toModAddCoreLayout.work base=0) (C : Bool) (A Z M : Nat) (hM : M≤p) :
    Triple (SignedMaskFrame c L base C A Z M) (controlledNegRaw c L.signedMaskView p)
      (SignedMaskFrame c L base C A Z (if C then p-M else M)) := by
  intro st m h
  obtain ⟨hf,hv,he⟩ := controlledNegRaw_correct c L.signedMaskView n p M C
    (L.signedMaskView_widths n hw) (L.signedMaskView_nodup c hn) hp hM st m h.1 h.2.2.2.1
    (signed_core_clean c L hn base st.basis C A Z M hk h)
  exact ⟨hf,signed_update_mask c L hn base st.basis _ C A Z M _ h hv he⟩

private theorem signed_add_step (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : (c::L.wires).Nodup) (hp0 : 0<p) (hp : p<2^n)
    (base : BasisState) (hk : regValue L.toModAddCoreLayout.work base=0)
    (C : Bool) (A Z M : Nat) (hM : M≤p) (hZ : Z<p) :
    Triple (SignedMaskFrame c L base C A Z M) (modAddCore L.maskedCore p)
      (SignedMaskFrame c L base C A ((Z+M)%p) M) := by
  intro st m h
  have hw' : L.maskedCore.Widths n := ⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩
  have hn' : L.maskedCore.wires.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModInPlaceLayout.maskedCore,
      ModAddCoreLayout.wires,ModAddCoreLayout.work,ModAddCoreLayout.z,ModInPlaceLayout.z,
      List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have hk' := signed_core_clean c L hn base st.basis C A Z M hk h
  obtain ⟨hf,hv⟩ := modAddCore_spec L.maskedCore n p M Z hw' hn' hp0 hp hM hZ st m
    ⟨⟨h.2.2.2.1,h.2.2.1⟩,hk'⟩
  have he (q : Wire) (hq : q∉L.z) :=
    modAddCore_frame L.maskedCore n p M Z hw' hn' hp0 hp hM hZ st m h.2.2.2.1 h.2.2.1 hk' q hq
  exact ⟨hf,signed_update_target c L hn base st.basis _ C A Z M _ h
    (by simpa only [Nat.add_comm] using hv.1.2) he⟩

private theorem skywalkSignedModAdd_frame_spec (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat)
    (C : Bool) (hw : L.Widths n) (hn : (c::L.wires).Nodup) (hp0 : 0<p) (hp : p<2^n)
    (hA : A≤p) (hZ : Z<p) (base : BasisState) (hk : regValue L.toModAddCoreLayout.work base=0) :
    Triple (SignedMaskFrame c L base C A Z 0) (skywalkSignedModAdd c L p)
      (SignedMaskFrame c L base C A (if C then (Z+A)%p else (Z+p-A)%p) 0) := by
  let M := if !C then p-A else A
  have hm : M≤p := by dsimp [M]; split; exact Nat.sub_le _ _; exact hA
  have h1 := signed_copy_step c L n hw hn base C A Z 0
  have h2 := signed_flip_step c L hn base C A Z A
  have h3 := signed_neg_step c L n p hw hn hp base hk (!C) A Z A hA
  have h4 := signed_add_step c L n p hw hn hp0 hp base hk (!C) A Z M hm hZ
  have h5 := signed_neg_step c L n p hw hn hp base hk (!C) A ((Z+M)%p) M hm
  have h6 := signed_flip_step c L hn base (!C) A ((Z+M)%p) A
  have h7 := signed_copy_step c L n hw hn base C A ((Z+M)%p) A
  have hrestore : (if !C then p-M else M)=A := by
    cases C
    · change p-(p-A)=A
      omega
    · rfl
  simp only [Nat.zero_xor] at h1
  rw [hrestore] at h5
  simp only [Bool.not_not] at h6
  simp only [Nat.xor_self] at h7
  have hall := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7
  have hz : (Z+M)%p=(if C then (Z+A)%p else (Z+p-A)%p) := by
    cases C
    · dsimp [M]
      congr 1
      omega
    · rfl
  simpa only [skywalkSignedModAdd,List.append_assoc,hz] using hall

/-- Exact signed modular addition with arbitrary measurement records. Only the target changes. -/
theorem skywalkSignedModAdd_correct (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat)
    (C : Bool) (hw : L.Widths n) (hn : (c::L.wires).Nodup) (hp0 : 0<p) (hp : p<2^n)
    (hA : A≤p) (hZ : Z<p) (st : State) (m : List Bool)
    (hc : st.basis c=C) (ha : regValue L.a st.basis=A) (hz : regValue L.z st.basis=Z)
    (hk : regValue L.work st.basis=0) :
    (run (skywalkSignedModAdd c L p) m st).phase=st.phase ∧
    regValue L.z (run (skywalkSignedModAdd c L p) m st).basis=
      (if C then (Z+A)%p else (Z+p-A)%p) ∧
    (∀ w,w∉L.z → (run (skywalkSignedModAdd c L p) m st).basis w=st.basis w) := by
  have clean := (regValue_zero L.work st.basis).mp hk
  have hmask : regValue L.mask st.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => clean w (by simp [ModInPlaceLayout.work,hw]))
  have hcore : regValue L.toModAddCoreLayout.work st.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => clean w (by simp [ModInPlaceLayout.work,hw]))
  obtain ⟨hf,hv⟩ := skywalkSignedModAdd_frame_spec c L n p A Z C hw hn hp0 hp hA hZ st.basis hcore st m
    ⟨hc,ha,hz,hmask,fun _ _ _ _ _ => rfl⟩
  refine ⟨hf,hv.2.2.1,?_⟩
  intro w hwz
  by_cases hwc : w=c
  · subst w; exact hv.1.trans hc.symm
  by_cases hwa : w∈L.a
  · exact (regValue_eq_iff _ _ _).mp (hv.2.1.trans ha.symm) w hwa
  by_cases hwm : w∈L.mask
  · exact (regValue_eq_iff _ _ _).mp (hv.2.2.2.1.trans hmask.symm) w hwm
  exact hv.2.2.2.2 w hwc hwa hwz hwm

/-- Compatible modular-add interface: source/control unchanged and the whole outer work pool clean. -/
theorem skywalkSignedModAdd_spec (c : Wire) (L : ModInPlaceLayout) (n p A Z : Nat)
    (C : Bool) (hw : L.Widths n) (hn : (c::L.wires).Nodup) (hp0 : 0<p) (hp : p<2^n)
    (hA : A≤p) (hZ : Z<p) :
    {{ c=C,L.a=A,L.z=Z,L.work=0 }} skywalkSignedModAdd c L p
    {{ c=C,L.a=A,L.z=(if C then (Z+A)%p else (Z+p-A)%p),L.work=0 }} := by
  intro st m h
  simp only [Holds.holds] at h ⊢
  obtain ⟨hf,hz,he⟩ := skywalkSignedModAdd_correct c L n p A Z C hw hn hp0 hp hA hZ st m
    h.1.1.1 h.1.1.2 h.1.2 h.2
  have hc := (signed_control_outside c L hn).2.1
  have ha (w : Wire) (hwa : w∈L.a) : w∉L.z := signed_target_away c L hn w (by tauto)
  have hwork (w : Wire) (hww : w∈L.work) : w∉L.z := by
    intro hwz
    have hh := List.nodup_iff_count.mp hn w
    have hW := List.count_pos_iff.mpr hww
    have hZ := List.count_pos_iff.mpr hwz
    simp only [ModInPlaceLayout.wires,List.count_cons,List.count_append] at hh
    omega
  exact ⟨hf,⟨⟨(he c hc).trans h.1.1.1,
    (regValue_congr _ _ _ (fun w hw => he w (ha w hw))).trans h.1.1.2⟩,hz⟩,
    (regValue_congr _ _ _ (fun w hw => he w (hwork w hw))).trans h.2⟩

/-- Exact count for the same source-copy, negation, modular-add and cleanup stream. -/
theorem skywalkSignedModAdd_counts (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    toffoliCount (skywalkSignedModAdd c L p)=6*n-1 ∧
    measurementCount (skywalkSignedModAdd c L p)=6*n-1 := by
  have hc := copyRegister_counts none L.a L.mask (hw.core.a.trans hw.mask.symm)
  have hn' := controlledNegRaw_counts c L.signedMaskView n p (L.signedMaskView_widths n hw)
  have hm := modAddCore_counts L.maskedCore n p
    ⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩ hn
  have hf : toffoliCount [.X c]=0 ∧ measurementCount [.X c]=0 := ⟨rfl,rfl⟩
  simp only [skywalkSignedModAdd,toffoliCount_append,measurementCount_append,
    hc.1,hc.2,hn'.1,hn'.2,hm.1,hm.2,hf.1,hf.2,Option.isSome_none,
    Bool.false_eq_true,if_false]
  omega
/-- Actual gate support excludes the outer flag and borrows no additional wires. -/
theorem skywalkSignedModAdd_wires_subset (c : Wire) (L : ModInPlaceLayout) (n p : Nat)
    (hw : L.Widths n) (hn : 0<n) :
    wires (skywalkSignedModAdd c L p) ⊆
      (c::L.a++L.mask++L.z++L.toModAddCoreLayout.work).toFinset := by
  let own := (c::L.a++L.mask++L.z++L.toModAddCoreLayout.work).toFinset
  have hc := copyRegister_wires none L.a L.mask (hw.core.a.trans hw.mask.symm)
  have hne : L.a.isEmpty=false := by
    cases h : L.a with
    | nil => have hh := hw.core.a; simp [h] at hh
    | cons a as => rfl
  rw [hne] at hc
  simp only [Bool.false_eq_true,if_false,Option.toList_none,List.nil_append] at hc
  have hcopy : wires (copyRegister none L.a L.mask) ⊆ own := by
    rw [hc]
    intro w hw
    simp only [own,List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
    tauto
  have hneg : wires (controlledNegRaw c L.signedMaskView p) ⊆ own := by
    intro w hq
    have hh := controlledNegRaw_wires_subset c L.signedMaskView n p (L.signedMaskView_widths n hw) hq
    simp only [ModInPlaceLayout.signedMaskView,ModAddCoreLayout.work,own,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hh ⊢
    tauto
  have hcore : wires (modAddCore L.maskedCore p) ⊆ own := by
    rw [modAddCore_wires L.maskedCore n p ⟨hw.mask,hw.core.low,hw.core.constant,hw.core.carry⟩ hn]
    intro w hw
    simp only [ModInPlaceLayout.maskedCore,ModAddCoreLayout.wires,ModAddCoreLayout.z,
      ModAddCoreLayout.work,ModInPlaceLayout.z,own,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false] at hw ⊢
    tauto
  have hflip : wires [.X c] ⊆ own := by simp [own,wires,Instr.wires]
  simp only [skywalkSignedModAdd,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨hcopy,hflip⟩,hneg⟩,hcore⟩,hneg⟩,hflip⟩,hcopy⟩


end ECDSAAdd.Arithmetic
