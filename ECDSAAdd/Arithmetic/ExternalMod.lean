import ECDSAAdd.Arithmetic.Copy
import ECDSAAdd.Arithmetic.ModularFrame

namespace ECDSAAdd.Arithmetic.ExternalMod

def Values (L : ModLayout) (src dst : List Wire) (X O : Nat)
    (v : ModField → Nat) (st : BasisState) : Prop :=
  regValue src st = X ∧ regValue dst st = O ∧ ModValues L v st

theorem external_disjoint (src dst : List Wire) (L : ModLayout)
    (hnd : (src ++ dst ++ L.wires).Nodup) : src.Disjoint L.wires ∧ dst.Disjoint L.wires := by
  have h := (List.nodup_append'.mp hnd).2.2
  exact ⟨List.disjoint_left.mpr (fun _ hs hl => List.disjoint_left.mp h (List.mem_append_left dst hs) hl),
    List.disjoint_left.mpr (fun _ hd hl => List.disjoint_left.mp h (List.mem_append_right src hd) hl)⟩

theorem field_subset (L : ModLayout) (f : ModField) : L.reg f ⊆ L.wires :=
  fun _ hw => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (L.reg_mem f hw))

theorem copy_into (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (hlen : src.length = L.width+1)
    (X O : Nat) (v : ModField → Nat) (f : ModField) :
    Triple (Values L src dst X O v) (copyRegister none src (L.reg f))
      (Values L src dst X O (Function.update v f (v f ^^^ X))) := by
  intro s m hv
  obtain ⟨hs, hd⟩ := external_disjoint src dst L hnd
  have hl : L.wires.Nodup := (List.nodup_append'.mp hnd).2.1
  have hsr : src.Disjoint (L.reg f) :=
    List.disjoint_left.mpr (fun _ h₁ h₂ => List.disjoint_left.mp hs h₁ (field_subset L f h₂))
  have hc : (src ++ L.reg f).Nodup := List.nodup_append'.mpr
    ⟨(List.nodup_append'.mp (List.nodup_append'.mp hnd).1).1, L.reg_nodup hl f, hsr⟩
  obtain ⟨hp, he, hz⟩ := copyRegister_correct none src (L.reg f)
    (by rw [L.reg_length]; exact hlen) hc (by simp) s m
  refine ⟨hp, ?_, ?_, ModValues.update L hl v f _ s.basis _ hv.2.2 he ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp hsr hw))).trans hv.1
  · exact (regValue_congr _ _ _ (fun w hw => he w (fun h => List.disjoint_left.mp hd hw
      (field_subset L f h)))).trans hv.2.1
  · simpa only [copyValue, hv.1, hv.2.2.1 f] using hz

theorem copy_out (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (hlen : dst.length = L.width+1)
    (X O : Nat) (v : ModField → Nat) :
    Triple (Values L src dst X O v) (copyRegister none L.out dst)
      (Values L src dst X (O ^^^ v .out) v) := by
  intro s m hv
  obtain ⟨_, hd⟩ := external_disjoint src dst L hnd
  have hl : L.wires.Nodup := (List.nodup_append'.mp hnd).2.1
  have hsd : src.Disjoint dst := (List.nodup_append'.mp (List.nodup_append'.mp hnd).1).2.2
  have ho : L.out.Disjoint dst := List.disjoint_left.mpr
    (fun _ h₁ h₂ => List.disjoint_left.mp hd h₂ (field_subset L .out h₁))
  have hc : (L.out ++ dst).Nodup := List.nodup_append'.mpr
    ⟨L.reg_nodup hl .out, (List.nodup_append'.mp (List.nodup_append'.mp hnd).1).2.1, ho⟩
  obtain ⟨hp, he, hz⟩ := copyRegister_correct none L.out dst
    (by change (L.reg .out).length = _; rw [L.reg_length]; exact hlen.symm) hc (by simp) s m
  have hlwire (w : Wire) (hw : w ∈ L.wires) :
      (run (copyRegister none L.out dst) m s).basis w = s.basis w :=
    he w (fun h => List.disjoint_left.mp hd h hw)
  refine ⟨hp, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp hsd hw))).trans hv.1
  · simpa only [copyValue, hv.2.1, show regValue L.out s.basis = v .out from hv.2.2.1 .out] using hz
  · refine ⟨fun f => (regValue_congr _ _ _ (fun w hw => hlwire w (field_subset L f hw))).trans
      (hv.2.2.1 f), ?_, ?_⟩
    · exact (hlwire L.cinSum (by simp [ModLayout.wires])).trans hv.2.2.2.1
    · exact (hlwire L.cinDiff (by simp [ModLayout.wires])).trans hv.2.2.2.2

theorem work_zero (L : ModLayout) (v : ModField → Nat) (st : BasisState)
    (hv : ModValues L v st)
    (hc : ∀ f, f ≠ .x → f ≠ .y → f ≠ .out → v f = 0) : regValue L.work st = 0 := by
  apply (regValue_zero _ _).mpr
  intro w hw
  simp only [ModLayout.work, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with ((((ht | hm) | hd) | hcs) | hcd) | hci | hci
  · exact (regValue_zero _ _).mp ((hv.1 .total).trans (hc .total (by decide) (by decide) (by decide))) w ht
  · exact (regValue_zero _ _).mp ((hv.1 .modulus).trans (hc .modulus (by decide) (by decide) (by decide))) w hm
  · exact (regValue_zero _ _).mp ((hv.1 .diff).trans (hc .diff (by decide) (by decide) (by decide))) w hd
  · exact (regValue_zero _ _).mp ((hv.1 .carrySum).trans (hc .carrySum (by decide) (by decide) (by decide))) w hcs
  · exact (regValue_zero _ _).mp ((hv.1 .carryDiff).trans (hc .carryDiff (by decide) (by decide) (by decide))) w hcd
  · subst w; exact hv.2.1
  · subst w; exact hv.2.2

theorem zeros_iff (L : ModLayout) (st : BasisState) :
    ModValues L (fun _ => 0) st ↔ regValue L.wires st = 0 := by
  constructor
  · intro hv
    have hw := work_zero L (fun _ => 0) st hv (by intros; rfl)
    apply (regValue_zero _ _).mpr
    intro w hm
    have h := L.interface_perm.mem_iff.mpr hm
    simp only [List.mem_append] at h
    rcases h with ((hx | hy) | ho) | hwork
    · exact (regValue_zero _ _).mp (hv.1 .x) w hx
    · exact (regValue_zero _ _).mp (hv.1 .y) w hy
    · exact (regValue_zero _ _).mp (hv.1 .out) w ho
    · exact (regValue_zero _ _).mp hw w hwork
  · intro hw
    have hz := (regValue_zero _ _).mp hw
    refine ⟨fun f => (regValue_zero _ _).mpr (fun w hw => hz w (field_subset L f hw)), ?_, ?_⟩
    · exact hz L.cinSum (by simp [ModLayout.wires])
    · exact hz L.cinDiff (by simp [ModLayout.wires])

end ECDSAAdd.Arithmetic.ExternalMod
