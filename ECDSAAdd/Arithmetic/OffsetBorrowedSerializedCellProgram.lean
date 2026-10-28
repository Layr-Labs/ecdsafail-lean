import ECDSAAdd.Arithmetic.CompressedFieldActiveSupport
import ECDSAAdd.Arithmetic.TranscriptSelectFlag
import ECDSAAdd.Arithmetic.SwapRegisters

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic.OffsetBorrowedSerialized

attribute [local irreducible] OffsetBorrowedField.program OffsetBorrowedInverse.program
  swapRegisters wires

/-- Each window restores flag=false before the next selection. The real field
kernel is surrounded by its existing control-polarity correction. -/
def forward (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag]) ++
  transcriptSelectWindow b swap flag is
    (swapRegisters flag (balancedSharedPorts w flag).r (balancedSharedPorts w flag).y)

/-- Swap selection is retired before selecting the inverse field control.
This uses the independently measured inverse kernel, never reversed MX. -/
def inverse (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b swap flag is
    (swapRegisters flag (balancedSharedPorts w flag).r (balancedSharedPorts w flag).y) ++
  transcriptSelectWindow b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])

def sites (w : Nat → Wire) (b g swap flag : Wire) : List Wire :=
  [b,g,swap]++CompressedFieldSupport.sharedSites w flag

theorem counts (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool)
    (hn : (flag::(balancedSharedPorts w flag).r++
      (balancedSharedPorts w flag).y).Nodup) :
    toffoliCount (forward w b g swap flag ig is)=1280 ∧
    measurementCount (forward w b g swap flag ig is)=1025 ∧
    toffoliCount (inverse w b g swap flag ig is)=1281 ∧
    measurementCount (inverse w b g swap flag ig is)=1025 := by
  have width := BalancedCleanup.widths (balancedSharedPorts w flag).toLayout
    (balancedSharedPorts_widths w flag)
  have sw := swapRegisters_resources flag _ _ (width.2.1.trans width.2.2.1.symm) hn
  have fw := OffsetBorrowedField.counts w flag
  have iv := OffsetBorrowedInverse.counts w flag
  have fsel := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])
  have isel := transcriptSelectWindow_counts b g flag ig
    ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])
  have ssel := transcriptSelectWindow_counts b swap flag is
    (swapRegisters flag (balancedSharedPorts w flag).r (balancedSharedPorts w flag).y)
  simp only [forward,inverse,toffoliCount_append,measurementCount_append,
    fsel.1,fsel.2,isel.1,isel.2,ssel.1,ssel.2,
    fw.1,fw.2,iv.1,iv.2,sw.1,sw.2.1,width.2.1]
  norm_num [toffoliCount,measurementCount]

theorem forward_counts (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool)
    (hn : (flag::(balancedSharedPorts w flag).r++(balancedSharedPorts w flag).y).Nodup) :
    toffoliCount (forward w b g swap flag ig is)=1280 ∧
    measurementCount (forward w b g swap flag ig is)=1025 := by
  have h := counts w b g swap flag ig is hn
  exact ⟨h.1,h.2.1⟩

theorem inverse_counts (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool)
    (hn : (flag::(balancedSharedPorts w flag).r++(balancedSharedPorts w flag).y).Nodup) :
    toffoliCount (inverse w b g swap flag ig is)=1281 ∧
    measurementCount (inverse w b g swap flag ig is)=1025 := by
  have h := counts w b g swap flag ig is hn
  exact ⟨h.2.2.1,h.2.2.2⟩

private theorem window_support (b src flag : Wire) (constant : Bool)
    (body : Program) (W : Finset Wire) (hb : b∈W) (hs : src∈W)
    (hf : flag∈W) (hbody : wires body⊆W) :
    wires (transcriptSelectWindow b src flag constant body)⊆W := by
  have select : wires (transcriptSelectCompute b src flag constant)⊆W ∧
      wires (transcriptSelectExpose flag constant)⊆W ∧
      wires (transcriptSelectErase b src flag constant)⊆W := by
    cases constant <;>
      simp [transcriptSelectCompute,transcriptSelectExpose,transcriptSelectErase,
        wires,Instr.wires,correctionWires,Finset.subset_iff,hb,hs,hf]
  simp only [transcriptSelectWindow,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨select.1,select.2.1,hbody,select.2.1,select.2.2⟩

private theorem swap_layout_support (L : BalancedCircuit.Layout)
    (hw : L.r.length=L.y.length) :
    wires (swapRegisters L.sign L.r L.y)⊆L.wires.toFinset := by
  intro q hq
  have member := (swapRegisters_wires L.sign L.r L.y hw) hq
  simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
    BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
    List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member ⊢
  tauto

/-- Only one effective-control site occurs in either actual instruction list.
All measured Z/CZ correction support is included. -/
theorem support (w : Nat → Wire) (b g swap flag : Wire) (ig is : Bool) :
    wires (forward w b g swap flag ig is)⊆(sites w b g swap flag).toFinset ∧
    wires (inverse w b g swap flag ig is)⊆(sites w b g swap flag).toFinset := by
  let L := balancedSharedPorts w flag
  let W := (sites w b g swap flag).toFinset
  have own : L.wires.toFinset⊆W := by
    intro q hq
    simp only [W,sites,CompressedFieldSupport.sharedSites,List.mem_toFinset,
      List.mem_append] at ⊢
    exact Or.inr (Or.inl (Or.inr (List.mem_toFinset.mp hq)))
  have kernelOwn : (CompressedFieldSupport.sharedSites w flag).toFinset⊆W := by
    intro q hq
    simp only [W,sites,List.mem_toFinset,List.mem_append]
    exact Or.inr (List.mem_toFinset.mp hq)
  have controls : b∈W ∧ g∈W ∧ swap∈W ∧ flag∈W := by
    simp [W,sites,CompressedFieldSupport.sharedSites]
  have kernels := CompressedFieldSupport.kernels_support w flag
  have flagSupport : wires [.X flag]⊆W := by
    simp [wires,Instr.wires,Finset.subset_iff,controls.2.2.2]
  have fw : wires ([.X flag]++OffsetBorrowedField.program w flag++[.X flag])⊆W := by
    simp only [wires_append,Finset.union_subset_iff]
    exact ⟨⟨flagSupport,kernels.1.trans kernelOwn⟩,flagSupport⟩
  have iv : wires ([.X flag]++OffsetBorrowedInverse.program w flag++[.X flag])⊆W := by
    simp only [wires_append,Finset.union_subset_iff]
    exact ⟨⟨flagSupport,kernels.2.trans kernelOwn⟩,flagSupport⟩
  have width := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w flag)
  have sw : wires (swapRegisters flag L.r L.y)⊆W :=
    (swap_layout_support L (width.2.1.trans width.2.2.1.symm)).trans own
  have fwin := window_support b g flag ig _ W controls.1 controls.2.1 controls.2.2.2 fw
  have iwin := window_support b g flag ig _ W controls.1 controls.2.1 controls.2.2.2 iv
  have swin := window_support b swap flag is _ W controls.1 controls.2.2.1 controls.2.2.2 sw
  simp only [forward,inverse,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fwin,swin⟩,⟨swin,iwin⟩⟩

theorem omitted_effS_away (w : Nat → Wire) (b g swap flag oldEffS : Wire)
    (ig is : Bool) (ha : oldEffS∉sites w b g swap flag) :
    oldEffS∉wires (forward w b g swap flag ig is) ∧
    oldEffS∉wires (inverse w b g swap flag ig is) := by
  have h := support w b g swap flag ig is
  exact ⟨fun hm => ha (List.mem_toFinset.mp (h.1 hm)),
    fun hm => ha (List.mem_toFinset.mp (h.2 hm))⟩

end ECDSAAdd.Arithmetic.OffsetBorrowedSerialized
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSerialized.counts
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSerialized.forward_counts
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSerialized.inverse_counts
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSerialized.support
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSerialized.omitted_effS_away
