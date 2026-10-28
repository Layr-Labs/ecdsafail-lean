import ECDSAAdd.Arithmetic.BalancedInverseTranscriptKernelSupport
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptBoundary
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic
private theorem inverse_select_support (b source flag : Wire) (v : Bool) (p : Program) :
    wires (transcriptSelectWindow b source flag v p)⊆
      [b,source,flag].toFinset ∪ wires p := by
  intro q hq
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil] at hq ⊢ <;> tauto

theorem balancedInverseTranscriptBody_support (L : BalancedCircuit.Layout) (effS : Wire)
    (hw : L.Widths) : wires (balancedInverseTranscriptBody L effS)⊆(effS::L.wires).toFinset := by
  have k := BalancedInverse.support L hw
  have sw := swapRegisters_wires effS L.r L.y
    ((BalancedCleanup.widths L.toLayout hw).2.1.trans
      (BalancedCleanup.widths L.toLayout hw).2.2.1.symm)
  intro q hq
  simp only [balancedInverseTranscriptBody,wires_append,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq
  · have h := sw hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.not_mem_nil,or_false] at h ⊢
    tauto
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp [hq,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  · simpa only [List.mem_toFinset,List.mem_cons] using Or.inr (List.mem_toFinset.mp (k hq))
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp [hq,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]

theorem balancedInverseTranscriptCell_support (L : BalancedCircuit.Layout)
    (b g swap effS : Wire) (ig is : Bool) (hw : L.Widths) :
    wires (balancedInverseTranscriptCell L b g swap effS ig is)⊆
      ([b,g,swap,effS]++L.wires).toFinset := by
  have outer := inverse_select_support b g L.sign ig
    (transcriptSelectWindow b swap effS is (balancedInverseTranscriptBody L effS))
  have inner := inverse_select_support b swap effS is (balancedInverseTranscriptBody L effS)
  have body := balancedInverseTranscriptBody_support L effS hw
  intro q hq
  have h := outer hq
  simp only [Finset.mem_union] at h
  rcases h with h|h
  · simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    rcases h with h|h|h
    · simp [h]
    · simp [h]
    · right; simp [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,h]
  · have h := inner h
    simp only [Finset.mem_union] at h
    rcases h with h|h
    · simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      tauto
    · have hb := body h
      simp only [List.mem_toFinset,List.mem_cons] at hb
      rcases hb with e|member
      · subst q
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil]
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl True.intro))))
      · simp only [List.mem_toFinset,List.mem_append]
        exact Or.inr member

def balancedInverseTranscriptSupport (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) : List Wire :=
  [b,effS]++L.wires++ls.flatMap (fun l => [l.1.1,l.1.2])

theorem balancedInverseTranscriptReplay_support (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) (hw : L.Widths) :
    wires (balancedInverseTranscriptReplay L b effS ls)⊆(balancedInverseTranscriptSupport L b effS ls).toFinset := by
  induction ls with
  | nil => simp [balancedInverseTranscriptReplay,wires]
  | cons l ls ih =>
    have c := balancedInverseTranscriptCell_support L b l.1.1 l.1.2 effS l.2.1 l.2.2 hw
    intro q hq
    simp only [balancedInverseTranscriptReplay,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · have h := ih hq
      simp only [balancedInverseTranscriptSupport,List.flatMap_cons,List.mem_toFinset,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
    · have h := c hq
      simp only [balancedInverseTranscriptSupport,List.flatMap_cons,List.mem_toFinset,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto

/-- Endpoint converter support is counted only at the two replay boundaries. -/
def balancedInverseTranscriptCanonicalSupport (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter) :
    List Wire := balancedInverseTranscriptSupport L b effS ls ++ D.target.wires ++ D.source.wires

theorem balancedInverseTranscriptCanonicalReplay_support (L : BalancedCircuit.Layout)
    (D : BalancedTranscriptBoundary L) (b effS : Wire) (ls : List MixedTranscriptLetter)
    (hw : L.Widths) : wires (balancedInverseTranscriptCanonicalReplay L D b effS ls) ⊆
      (balancedInverseTranscriptCanonicalSupport L D b effS ls).toFinset := by
  have t := BalancedConvert.support D.target
  have s := BalancedConvert.support D.source
  have r := balancedInverseTranscriptReplay_support L b effS ls hw
  intro q hq
  simp only [balancedInverseTranscriptCanonicalReplay,balancedTranscriptCenterPair,
    balancedTranscriptCanonicalPair,wires_append,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq|hq
  · have h := t.1 hq
    simp only [balancedInverseTranscriptCanonicalSupport,List.mem_toFinset,List.mem_append] at h ⊢
    tauto
  · have h := s.1 hq
    simp only [balancedInverseTranscriptCanonicalSupport,List.mem_toFinset,List.mem_append] at h ⊢
    tauto
  · have h := r hq
    simp only [balancedInverseTranscriptCanonicalSupport,List.mem_toFinset,List.mem_append] at h ⊢
    tauto
  · have h := t.2 hq
    simp only [balancedInverseTranscriptCanonicalSupport,List.mem_toFinset,List.mem_append] at h ⊢
    tauto
  · have h := s.2 hq
    simp only [balancedInverseTranscriptCanonicalSupport,List.mem_toFinset,List.mem_append] at h ⊢
    tauto
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedInverseTranscriptReplay_support

#print axioms ECDSAAdd.Arithmetic.balancedInverseTranscriptCanonicalReplay_support
