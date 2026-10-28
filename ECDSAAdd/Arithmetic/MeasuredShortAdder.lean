import ECDSAAdd.Arithmetic.MeasuredMaskedAdder
import ECDSAAdd.Arithmetic.ModInPlaceCopy

namespace ECDSAAdd.Arithmetic

/-- Exact masked addition of a shorter source, zero-extended in the clean mask.
Only the occupied low source bits are copied and measured. -/
def measuredShortAddInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src (t.take src.length) ++
    addInPlace t y carry cin ++ eraseMask c src (t.take src.length)

/-- Exact masked subtraction with the same short-source mask construction. -/
def measuredShortSubInPlace (c : Wire) (src t y carry : List Wire) (cin : Wire) : Program :=
  copyRegister (some c) src (t.take src.length) ++
    subInPlace t y carry cin ++ eraseMask c src (t.take src.length)

private theorem short_low_value (r : List Wire) (n V : Nat) (hr : n≤r.length)
    (s : BasisState) (hv : regValue r s=V) (hb : V<2^n) :
    regValue (r.take n) s=V := by
  have hh := regValue_append (r.take n) (r.drop n) s
  rw [List.take_append_drop,List.length_take,Nat.min_eq_left hr,hv] at hh
  have ht := regValue_lt (r.take n) s
  rw [List.length_take,Nat.min_eq_left hr] at ht
  have hn : 0<2^n := by positivity
  have hz : regValue (r.drop n) s=0 := by
    by_contra h
    have : 1≤regValue (r.drop n) s := by omega
    nlinarith
  simpa [hz] using hh.symm

private theorem shortCopyWithFrame_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c::cin::(src++t++y++carry)).Nodup) (hs : src.length≤t.length)
    (C : Bool) (S V Y : Nat) (hS : S<2^src.length) (hV : V<2^src.length) :
    {{ c=C, src=S, t=V, y=Y, cin=false, carry=0 }}
      copyRegister (some c) src (t.take src.length)
    {{ c=C, src=S, t=(V ^^^ (if C then S else 0)), y=Y, cin=false, carry=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hcnt := List.nodup_iff_count.mp hnd
  have hst : (c::(src++t)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have hh := hcnt w
    simp only [List.count_cons,List.count_append] at hh ⊢; omega
  have outside (w : Wire) (hw : w=c ∨ w=cin ∨ w∈src ∨ w∈y ∨ w∈carry) : w∉t := by
    intro ht
    have hh := hcnt w
    have hn := List.count_pos_iff.mpr ht
    simp only [List.count_cons,List.count_append] at hh
    rcases hw with rfl | rfl | hw | hw | hw
    · simp only [beq_self_eq_true,if_true] at hh; omega
    · simp only [beq_self_eq_true,if_true] at hh; omega
    · have := List.count_pos_iff.mpr hw; omega
    · have := List.count_pos_iff.mpr hw; omega
    · have := List.count_pos_iff.mpr hw; omega
  obtain ⟨hp,he,hv⟩ := copyLow_correct c src t src.length S V
    (Nat.le_refl _) hs hst hS hV s m h.1.1.1.1.2 h.1.1.1.2
  simp only [List.take_length] at hp he hv
  have keep (w : Wire) (hw : w=c ∨ w=cin ∨ w∈src ∨ w∈y ∨ w∈carry) :
      (run (copyRegister (some c) src (t.take src.length)) m s).basis w=s.basis w :=
    he w (fun hh => outside w hw (List.mem_of_mem_take hh))
  refine ⟨hp,⟨⟨⟨⟨(keep c (Or.inl rfl)).trans h.1.1.1.1.1,
    (regValue_congr _ _ _ (fun w hw => keep w (by tauto))).trans h.1.1.1.1.2⟩,?_⟩,
    (regValue_congr _ _ _ (fun w hw => keep w (by tauto))).trans h.1.1.2⟩,
    (keep cin (by tauto)).trans h.1.2⟩,
    (regValue_congr _ _ _ (fun w hw => keep w (by tauto))).trans h.2⟩
  simpa only [h.1.1.1.1.1] using hv

private theorem shortEraseWithFrame_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c::cin::(src++t++y++carry)).Nodup) (hs : src.length≤t.length)
    (C : Bool) (S Y : Nat) (hS : S<2^src.length) :
    {{ c=C, src=S, t=(if C then S else 0), y=Y, cin=false, carry=0 }}
      eraseMask c src (t.take src.length)
    {{ c=C, src=S, t=0, y=Y, cin=false, carry=0 }} := by
  have hlen : src.length=(t.take src.length).length := by
    simp only [List.length_take,Nat.min_eq_left hs]
  have hst : (c::(src++t.take src.length)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hnd w
    have ht := (List.take_sublist src.length t).count_le w
    simp only [List.count_cons,List.count_append] at hh ⊢; omega
  have hV : (if C then S else 0)<2^src.length := by
    cases C with
    | false => simp
    | true => simpa using hS
  intro s m h
  have hv : regValue (t.take src.length) s.basis=if C then S else 0 :=
    short_low_value t src.length _ hs s.basis h.1.1.1.2 hV
  have rel : regValue (t.take src.length) s.basis=
      if s.basis c then regValue src s.basis else 0 := by
    rw [hv,h.1.1.1.1.1,h.1.1.1.1.2]
  rw [eraseMask_eq_copy c src _ hlen hst s m rel]
  have hh := shortCopyWithFrame_spec c cin src t y carry hnd hs C S
    (if C then S else 0) Y hS hV s m h
  simpa only [Nat.xor_self] using hh

/-- All input states and all measurement records: exact addition, source/control
preservation, complete mask/carry cleanup, and phase restoration. -/
theorem measuredShortAddInPlace_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c::cin::(src++t++y++carry)).Nodup) (hs : src.length≤t.length)
    (ht : t.length=y.length) (hc : carry.length+1=y.length)
    (C : Bool) (S Y : Nat) (hS : S<2^src.length) :
    {{ c=C, src=S, t=0, y=Y, cin=false, carry=0 }} measuredShortAddInPlace c src t y carry cin
    {{ c=C, src=S, t=0, y=((Y+(if C then S else 0))%2^y.length), cin=false, carry=0 }} := by
  have h1 := shortCopyWithFrame_spec c cin src t y carry hnd hs C S 0 Y hS (by positivity)
  have h2 := addInPlaceWithSource_spec c cin src t y carry hnd ht hc C S (if C then S else 0) Y
  have h3 := shortEraseWithFrame_spec c cin src t y carry hnd hs C S
    ((Y+(if C then S else 0))%2^y.length) hS
  simp only [Nat.zero_xor] at h1
  simpa only [measuredShortAddInPlace,List.append_assoc] using h1.seq (h2.seq h3)

/-- The same universal guarantees for exact subtraction modulo the destination width. -/
theorem measuredShortSubInPlace_spec (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c::cin::(src++t++y++carry)).Nodup) (hs : src.length≤t.length)
    (ht : t.length=y.length) (hc : carry.length+1=y.length)
    (C : Bool) (S Y : Nat) (hS : S<2^src.length) :
    {{ c=C, src=S, t=0, y=Y, cin=false, carry=0 }} measuredShortSubInPlace c src t y carry cin
    {{ c=C, src=S, t=0, y=((Y+2^y.length-(if C then S else 0))%2^y.length), cin=false, carry=0 }} := by
  have h1 := shortCopyWithFrame_spec c cin src t y carry hnd hs C S 0 Y hS (by positivity)
  have h2 := subInPlaceWithSource_spec c cin src t y carry hnd ht hc C S (if C then S else 0) Y
  have h3 := shortEraseWithFrame_spec c cin src t y carry hnd hs C S
    ((Y+2^y.length-(if C then S else 0))%2^y.length) hS
  simp only [Nat.zero_xor] at h1
  simpa only [measuredShortSubInPlace,List.append_assoc] using h1.seq (h2.seq h3)

/-- Exact static counts, including every measurement-conditioned correction. -/
theorem measuredShortInPlace_counts (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length≤t.length) (ht : t.length=y.length) (hc : carry.length+1=y.length) :
    (toffoliCount (measuredShortAddInPlace c src t y carry cin)=src.length+y.length-1 ∧
      measurementCount (measuredShortAddInPlace c src t y carry cin)=src.length+y.length-1) ∧
    (toffoliCount (measuredShortSubInPlace c src t y carry cin)=src.length+y.length-1 ∧
      measurementCount (measuredShortSubInPlace c src t y carry cin)=src.length+y.length-1) := by
  have hlen : src.length=(t.take src.length).length := by
    simp only [List.length_take,Nat.min_eq_left hs]
  have cp := copyRegister_counts (some c) src (t.take src.length) hlen
  have ep := eraseMask_counts c src (t.take src.length) hlen
  have ap := addInPlace_counts t y carry cin ht hc
  have sp := subInPlace_counts t y carry cin ht hc
  simp only [measuredShortAddInPlace,measuredShortSubInPlace,toffoliCount_append,
    measurementCount_append,cp.1,cp.2,ep.1,ep.2,ap.1,ap.2,sp.1,sp.2,
    List.length_take,Nat.min_eq_left hs,Option.isSome_some,if_true]
  omega

/-- The optimized program uses only the caller's existing register pool. -/
theorem measuredShortInPlace_wires_subset (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hs : src.length≤t.length) (ht : t.length=y.length) (hc : carry.length+1=y.length) :
    wires (measuredShortAddInPlace c src t y carry cin) ⊆ (c::cin::(src++t++y++carry)).toFinset ∧
    wires (measuredShortSubInPlace c src t y carry cin) ⊆ (c::cin::(src++t++y++carry)).toFinset := by
  have hlen : src.length=(t.take src.length).length := by
    simp only [List.length_take,Nat.min_eq_left hs]
  have cp := copyRegister_wires (some c) src (t.take src.length) hlen
  have ep := eraseMask_wires_subset c src (t.take src.length)
  have ct : wires (copyRegister (some c) src (t.take src.length)) ⊆
      (c::cin::(src++t++y++carry)).toFinset := by
    rw [cp]; split_ifs
    · exact Finset.empty_subset _
    · intro w hw
      have hm : w∈t.take src.length → w∈t := List.mem_of_mem_take
      simp only [Option.toList_some,List.cons_append,List.nil_append,
        List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
      tauto
  have et : wires (eraseMask c src (t.take src.length)) ⊆
      (c::cin::(src++t++y++carry)).toFinset := by
    intro w hw
    have he := ep hw
    have hm : w∈t.take src.length → w∈t := List.mem_of_mem_take
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at he ⊢
    tauto
  constructor
  · simp only [measuredShortAddInPlace,wires_append]
    apply Finset.union_subset
    · apply Finset.union_subset ct
      rw [addInPlace_wires t y carry cin ht hc]
      intro w hw
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
      tauto
    · exact et
  · simp only [measuredShortSubInPlace,wires_append]
    apply Finset.union_subset
    · apply Finset.union_subset ct
      rw [subInPlace_wires t y carry cin ht hc]
      intro w hw
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hw ⊢
      tauto
    · exact et

set_option maxHeartbeats 1000000 in
/-- With a nonempty source, the exact support omits all former padding wires. -/
theorem measuredShortInPlace_wires (c : Wire) (src t y carry : List Wire) (cin : Wire)
    (hn : src≠[]) (hs : src.length≤t.length) (ht : t.length=y.length)
    (hc : carry.length+1=y.length) :
    wires (measuredShortAddInPlace c src t y carry cin)=(c::cin::(src++t++y++carry)).toFinset ∧
    wires (measuredShortSubInPlace c src t y carry cin)=(c::cin::(src++t++y++carry)).toFinset := by
  have hlen : src.length=(t.take src.length).length := by
    simp only [List.length_take,Nat.min_eq_left hs]
  have cp := copyRegister_wires (some c) src (t.take src.length) hlen
  simp only [List.isEmpty_iff,hn,if_false,Option.toList_some,List.cons_append,List.nil_append] at cp
  have ep := eraseMask_wires_subset c src (t.take src.length)
  have hm (w : Wire) : w∈t.take src.length → w∈t := List.mem_of_mem_take
  constructor
  · rw [measuredShortAddInPlace,wires_append,wires_append,cp,addInPlace_wires t y carry cin ht hc]
    ext w
    have he := @ep w
    have ht' := hm w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append] at he ⊢
    tauto
  · rw [measuredShortSubInPlace,wires_append,wires_append,cp,subInPlace_wires t y carry cin ht hc]
    ext w
    have he := @ep w
    have ht' := hm w
    simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append] at he ⊢
    tauto

private theorem short_mask_frame (c cin : Wire) (src t y carry : List Wire) (s u : BasisState)
    (hc : u c=s c) (hi : u cin=s cin)
    (hs : regValue src u=regValue src s) (ht : regValue t u=regValue t s)
    (hk : regValue carry u=regValue carry s)
    (he : ∀ w, w∉c::cin::(src++t++y++carry) → u w=s w) :
    ∀ w, w∉y → u w=s w := by
  intro w hy
  by_cases hw : w∈c::cin::(src++t++y++carry)
  · simp only [List.mem_cons,List.mem_append] at hw
    rcases hw with rfl | rfl | ((hw | hw) | hw) | hw
    · exact hc
    · exact hi
    · exact (regValue_eq_iff src u s).mp hs w hw
    · exact (regValue_eq_iff t u s).mp ht w hw
    · exact False.elim (hy hw)
    · exact (regValue_eq_iff carry u s).mp hk w hw
  · exact he w hw

theorem measuredShortAddInPlace_frame (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c::cin::(src++t++y++carry)).Nodup) (hs : src.length≤t.length)
    (ht : t.length=y.length) (hc : carry.length+1=y.length)
    (s : State) (m : List Bool) (vt : regValue t s.basis=0)
    (vi : s.basis cin=false) (vk : regValue carry s.basis=0) :
    ∀ w, w∉y → (run (measuredShortAddInPlace c src t y carry cin) m s).basis w=s.basis w := by
  obtain ⟨_,h⟩ := measuredShortAddInPlace_spec c cin src t y carry hnd hs ht hc
    (s.basis c) (regValue src s.basis) (regValue y s.basis) (regValue_lt src s.basis)
    s m ⟨⟨⟨⟨⟨rfl,rfl⟩,vt⟩,rfl⟩,vi⟩,vk⟩
  apply short_mask_frame c cin src t y carry s.basis _ h.1.1.1.1.1 (h.1.2.trans vi.symm)
    h.1.1.1.1.2 (h.1.1.1.2.trans vt.symm) (h.2.trans vk.symm)
  intro w hw
  apply run_preserves_outside
  intro hh
  have he := (measuredShortInPlace_wires_subset c src t y carry cin hs ht hc).1 hh
  exact hw (List.mem_toFinset.mp he)

theorem measuredShortSubInPlace_frame (c cin : Wire) (src t y carry : List Wire)
    (hnd : (c::cin::(src++t++y++carry)).Nodup) (hs : src.length≤t.length)
    (ht : t.length=y.length) (hc : carry.length+1=y.length)
    (s : State) (m : List Bool) (vt : regValue t s.basis=0)
    (vi : s.basis cin=false) (vk : regValue carry s.basis=0) :
    ∀ w, w∉y → (run (measuredShortSubInPlace c src t y carry cin) m s).basis w=s.basis w := by
  obtain ⟨_,h⟩ := measuredShortSubInPlace_spec c cin src t y carry hnd hs ht hc
    (s.basis c) (regValue src s.basis) (regValue y s.basis) (regValue_lt src s.basis)
    s m ⟨⟨⟨⟨⟨rfl,rfl⟩,vt⟩,rfl⟩,vi⟩,vk⟩
  apply short_mask_frame c cin src t y carry s.basis _ h.1.1.1.1.1 (h.1.2.trans vi.symm)
    h.1.1.1.1.2 (h.1.1.1.2.trans vt.symm) (h.2.trans vk.symm)
  intro w hw
  apply run_preserves_outside
  intro hh
  have he := (measuredShortInPlace_wires_subset c src t y carry cin hs ht hc).2 hh
  exact hw (List.mem_toFinset.mp he)

end ECDSAAdd.Arithmetic
