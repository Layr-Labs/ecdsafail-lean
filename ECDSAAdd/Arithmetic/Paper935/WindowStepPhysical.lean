import ECDSAAdd.Arithmetic.Paper935.WindowStep
import ECDSAAdd.Arithmetic.Paper935.WindowRoutedPhysical

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic.Divsteps ECDSAAdd.RecordedQuantum

private theorem complement_physical (c : Wire) (r : List Wire) (h : c∉r) :
    GatePhysical (signComplement c r) := by
  intro i hi
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
  exact fun e => h (e ▸ hw)

/-- Counter legality needs only address separation, not arithmetic success. -/
theorem counter_both_physical (active swap : Wire) (zero z carry : List Wire)
    (hn : (active::swap::(zero++z++carry)).Nodup) :
    GatePhysical (counterUpdate active swap zero z carry) ∧
    GatePhysical (counterUpdateInverse active swap zero z carry) := by
  have ha : active∉z := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have hs : swap∉z := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 (by simp [h])
  have ht : (active::(zero++z++carry)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have a := complement_physical active z ha
  have s := complement_physical swap z hs
  have add := addInPlace_physical zero z carry active ht
  simp only [counterUpdate,counterUpdateInverse,negateSigned,gatePhysical_append]
  exact ⟨⟨s,add⟩,⟨⟨⟨a,add⟩,a⟩,s⟩⟩

/-- Planned resizing and legal counter addresses suffice for both streams. -/
theorem RoutedBankLayout.windowStep_physical (L : RoutedBankLayout) (hv : L.Valid)
    (out : WindowBank) (w : RowWindow) (A C : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (zero z carry : List Wire)
    (hn : (L.active::L.q::(zero++z++carry)).Nodup) :
    GatePhysical (L.windowStep resize zero z carry) ∧
    GatePhysical (L.windowStepInverse resize zero z carry) := by
  have r := (L.after.resize_resources out w A C resize hp).1
  have rp := (physical_embed _).mp (physical_of_proper _ r)
  have ri := (physical_embed _).mp (physical_of_proper _ (properProgram_reverse _ r))
  have c := counter_both_physical L.active L.q zero z carry hn
  simp only [windowStep,windowStepInverse,gatePhysical_append]
  exact ⟨⟨(L.physical hv).1,⟨rp,c.1⟩⟩,⟨⟨c.2,ri⟩,(L.physical hv).2⟩⟩

/-- The full step and its inverse stay inside the physical arena, including
all resize and counter work wires. This is local support, not a whole-walk peak. -/
theorem RoutedBankLayout.windowStep_support (L : RoutedBankLayout)
    (out : WindowBank) (w : RowWindow) (A C : Arena) (resize : Program)
    (hp : L.after.Planned out w A C resize) (zero z carry : List Wire)
    (hr : wires L.program⊆arenaWires)
    (hc : (L.active::L.q::(zero++z++carry)).toFinset⊆arenaWires)
    (hz : zero.length=z.length) (hk : carry.length+1=z.length) :
    wires (L.windowStep resize zero z carry)⊆arenaWires ∧
    wires (L.windowStepInverse resize zero z carry)⊆arenaWires := by
  have resizeBound := (L.after.resize_resources out w A C resize hp).2.2.2
  have forward := (counterUpdate_wires_subset L.active L.q zero z carry hz hk).trans hc
  have backward := (counterUpdateInverse_wires_subset L.active L.q zero z carry hz hk).trans hc
  simp only [windowStep,windowStepInverse,wires_append,wires_reverse,L.inverse_wires,
    Finset.union_subset_iff]
  exact ⟨⟨hr,⟨resizeBound,forward⟩⟩,⟨⟨backward,resizeBound⟩,hr⟩⟩

end ECDSAAdd.Arithmetic.Paper935
