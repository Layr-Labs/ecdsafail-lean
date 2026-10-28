import ECDSAAdd.Arithmetic.ModInPlaceWrappers
import ECDSAAdd.Arithmetic.SignedWord

namespace ECDSAAdd.Arithmetic

/-- Conditional expanded raw negation. Zero maps to p in the active branch;
that temporary source value is legal for the exact modular-add core. -/
def controlledNegRaw (c : Wire) (L : ModInPlaceLayout) (p : Nat) : Program :=
  signComplement c L.a ++ maskedAddConst c L.constant L.a L.carry L.cin (p+1)

private theorem controlledNegRaw_core_nodup (c : Wire) (L : ModInPlaceLayout)
    (hnd : (c::L.wires).Nodup) : (c::L.cin::(L.constant++L.a++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hh := List.nodup_iff_count.mp hnd w
  simp only [ModInPlaceLayout.wires,ModInPlaceLayout.work,ModAddCoreLayout.work,
    List.count_cons,List.count_append,List.count_nil] at hh ⊢
  omega

private theorem controlledNegRaw_complement_spec (c : Wire) (L : ModInPlaceLayout)
    (hnd : (c::L.wires).Nodup) (C : Bool) (A : Nat) :
    {{ c=C,L.constant=0,L.a=A,L.cin=false,L.carry=0 }} signComplement c L.a
    {{ c=C,L.constant=0,L.a=(if C then 2^L.a.length-1-A else A),L.cin=false,L.carry=0 }} := by
  intro st m h
  simp only [Holds.holds] at h ⊢
  have hn := controlledNegRaw_core_nodup c L hnd
  have ha : L.a.Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at hh
    omega
  have outside (w : Wire) (hw : w=c ∨ w=L.cin ∨ w∈L.constant ∨ w∈L.carry) : w∉L.a := by
    intro hwa
    have hh := List.nodup_iff_count.mp hn w
    have hA := List.count_pos_iff.mpr hwa
    simp only [List.count_cons,List.count_append] at hh
    rcases hw with rfl | rfl | hw | hw
    · simp only [beq_self_eq_true,if_true] at hh; omega
    · simp only [beq_self_eq_true,if_true] at hh; omega
    · have := List.count_pos_iff.mpr hw; omega
    · have := List.count_pos_iff.mpr hw; omega
  obtain ⟨hf,he,hv⟩ := signComplement_correct c L.a ha (outside c (Or.inl rfl)) st m
  refine ⟨hf,⟨⟨⟨⟨(he c (outside c (Or.inl rfl))).trans h.1.1.1.1,
    (regValue_congr _ _ _ (fun w hw => he w (outside w (by tauto)))).trans h.1.1.1.2⟩,?_⟩,
    (he L.cin (outside L.cin (by tauto))).trans h.1.2⟩,
    (regValue_congr _ _ _ (fun w hw => he w (outside w (by tauto)))).trans h.2⟩⟩
  simpa only [h.1.1.1.1,h.1.1.2] using hv

private theorem controlledNegRaw_value (n p A : Nat) (C : Bool) (hp : p<2^n) (hA : A≤p) :
    ((if C then 2^(n+1)-1-A else A)+(if C then p+1 else 0))%2^(n+1)=
      (if C then p-A else A) := by
  have hfit : A<2^(n+1) := by rw [Nat.pow_succ]; omega
  cases C
  · simp [Nat.mod_eq_of_lt hfit]
  · have he : 2^(n+1)-1-A+(p+1)=2^(n+1)+(p-A) := by
      rw [Nat.pow_succ]
      omega
    have hb : p-A<2^(n+1) := by rw [Nat.pow_succ]; omega
    simp only [if_true]
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt hb]

/-- No zero assumption on the outer mask or flag: only the core scratch must be clean.
This permits applying the primitive to a copied source mask while the original source is live. -/
theorem controlledNegRaw_spec (c : Wire) (L : ModInPlaceLayout) (n p A : Nat) (C : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : p<2^n) (hA : A≤p) :
    {{ c=C,L.a=A,L.toModAddCoreLayout.work=0 }} controlledNegRaw c L p
    {{ c=C,L.a=(if C then p-A else A),L.toModAddCoreLayout.work=0 }} := by
  have hn := controlledNegRaw_core_nodup c L hnd
  have hc : L.carry.length+1=L.a.length := by rw [hw.core.carry,hw.core.a]
  have hk : p+1<2^L.constant.length := by rw [hw.core.constant,Nat.pow_succ]; omega
  have h1 := controlledNegRaw_complement_spec c L hnd C A
  have h2 := maskedAddConst_spec c L.cin L.constant L.a L.carry hn
    (hw.core.constant.trans hw.core.a.symm) hc (p+1) hk C
    (if C then 2^L.a.length-1-A else A)
  have hall := h1.seq h2
  have he := controlledNegRaw_value n p A C hp hA
  rw [hw.core.a,he] at hall
  intro st m h
  simp only [Holds.holds] at h ⊢
  have clean := (regValue_zero L.toModAddCoreLayout.work st.basis).mp h.2
  have ht : regValue L.constant st.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => clean w (by simp [ModAddCoreLayout.work,hw]))
  have hcarry : regValue L.carry st.basis=0 := (regValue_zero _ _).mpr
    (fun w hw => clean w (by simp [ModAddCoreLayout.work,hw]))
  have hcin : st.basis L.cin=false := clean L.cin (by simp [ModAddCoreLayout.work])
  obtain ⟨hf,hv⟩ := hall st m ⟨⟨⟨⟨h.1.1,ht⟩,h.1.2⟩,hcin⟩,hcarry⟩
  simp only [Holds.holds] at hv
  refine ⟨hf,⟨hv.1.1.1.1,hv.1.1.2⟩,(regValue_zero _ _).mpr ?_⟩
  intro w hw
  simp only [ModAddCoreLayout.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with (hw | hw) | hw
  · exact (regValue_zero _ _).mp hv.1.1.1.2 w hw
  · exact (regValue_zero _ _).mp hv.2 w hw
  · subst w; exact hv.1.2

/-- The only nonlinear gates are the n carries of one full-width exact addition. -/
theorem controlledNegRaw_counts (c : Wire) (L : ModInPlaceLayout) (n p : Nat) (hw : L.Widths n) :
    toffoliCount (controlledNegRaw c L p)=n ∧ measurementCount (controlledNegRaw c L p)=n := by
  have hs := signComplement_counts c L.a
  have ha := addInPlace_counts L.constant L.a L.carry L.cin
    (hw.core.constant.trans hw.core.a.symm) (by rw [hw.core.carry,hw.core.a])
  have hm := maskedConstant_counts c L.constant (p+1)
  simp only [controlledNegRaw,maskedAddConst,toffoliCount_append,measurementCount_append,
    hs.1,hs.2,ha.1,ha.2,hm.1,hm.2,hw.core.a]
  omega

/-- Exact support containment, with the unused outer mask and flag excluded. -/
theorem controlledNegRaw_wires_subset (c : Wire) (L : ModInPlaceLayout) (n p : Nat) (hw : L.Widths n) :
    wires (controlledNegRaw c L p) ⊆ (c::L.a++L.toModAddCoreLayout.work).toFinset := by
  have hs := signComplement_wires_subset c L.a
  have hm := (maskedConst_wires_subset c L.constant L.a L.carry L.cin (p+1)
    (hw.core.constant.trans hw.core.a.symm) (by rw [hw.core.carry,hw.core.a])).1
  rw [controlledNegRaw,wires_append]
  apply Finset.union_subset
  · intro w hw
    have hh := hs hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
    tauto
  · intro w hw
    have hh := hm hw
    simp only [ModAddCoreLayout.work,List.mem_toFinset,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false] at hh ⊢
    tauto

/-- Every outside wire, control and scratch wire is restored for every measurement record. -/
theorem controlledNegRaw_correct (c : Wire) (L : ModInPlaceLayout) (n p A : Nat) (C : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : p<2^n) (hA : A≤p)
    (st : State) (m : List Bool) (hc : st.basis c=C) (ha : regValue L.a st.basis=A)
    (hk : regValue L.toModAddCoreLayout.work st.basis=0) :
    (run (controlledNegRaw c L p) m st).phase=st.phase ∧
    regValue L.a (run (controlledNegRaw c L p) m st).basis=(if C then p-A else A) ∧
    (∀ w,w∉L.a → (run (controlledNegRaw c L p) m st).basis w=st.basis w) := by
  obtain ⟨hf,hv⟩ := controlledNegRaw_spec c L n p A C hw hnd hp hA st m ⟨⟨hc,ha⟩,hk⟩
  simp only [Holds.holds] at hv
  refine ⟨hf,hv.1.2,?_⟩
  intro w hwa
  by_cases he : w=c
  · subst w; exact hv.1.1.trans hc.symm
  by_cases hwork : w∈L.toModAddCoreLayout.work
  · exact (regValue_eq_iff _ _ _).mp (hv.2.trans hk.symm) w hwork
  apply run_preserves_outside
  intro hh
  have hs := controlledNegRaw_wires_subset c L n p hw hh
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hs
  tauto

/-- Exact involution on all A≤p, including the zero/p pair, for independent record streams. -/
theorem controlledNegRaw_involution (c : Wire) (L : ModInPlaceLayout) (n p A : Nat) (C : Bool)
    (hw : L.Widths n) (hnd : (c::L.wires).Nodup) (hp : p<2^n) (hA : A≤p)
    (st : State) (m₁ m₂ : List Bool) (hc : st.basis c=C) (ha : regValue L.a st.basis=A)
    (hk : regValue L.toModAddCoreLayout.work st.basis=0) :
    run (controlledNegRaw c L p) m₂ (run (controlledNegRaw c L p) m₁ st)=st := by
  let t := run (controlledNegRaw c L p) m₁ st
  have hs := controlledNegRaw_spec c L n p A C hw hnd hp hA st m₁ ⟨⟨hc,ha⟩,hk⟩
  have hB : (if C then p-A else A)≤p := by
    cases C
    · exact hA
    · exact Nat.sub_le p A
  have hrestore : (if C then p-(if C then p-A else A) else (if C then p-A else A))=A := by
    cases C
    · rfl
    · change p-(p-A)=A
      omega
  have first := controlledNegRaw_correct c L n p A C hw hnd hp hA st m₁ hc ha hk
  have second := controlledNegRaw_correct c L n p (if C then p-A else A) C hw hnd hp hB
    t m₂ hs.2.1.1 hs.2.1.2 hs.2.2
  apply congrArg₂ State.mk
  · exact second.1.trans first.1
  · funext w
    by_cases hw : w∈L.a
    · apply (regValue_eq_iff L.a _ _).mp
        (by rw [second.2.1,hrestore,ha]) w hw
    · exact (second.2.2 w hw).trans (first.2.2 w hw)

end ECDSAAdd.Arithmetic
