import ECDSAAdd.Arithmetic.BalancedTranscriptBoundary
import ECDSAAdd.Arithmetic.MeasuredGateSupport
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
namespace ECDSAAdd.Arithmetic

namespace BalancedConvert
/-- Includes phase-correction controls of every measurement instruction. -/
theorem support (L : Layout) :
    wires (center L)⊆L.wires.toFinset ∧ wires (canonical L)⊆L.wires.toFinset := by
  have a := literalConstAdd_wires L.word L.carry L.cin L.one bias
  have b := literalConstAdd_wires L.word L.carry L.cin L.one inverseBias
  have c := mappedAdd_wires_subset (correction L) L.word L.carry L.cin
  have d := mappedSub_wires_subset (correction L) L.word L.carry L.cin
  have lit (q : Wire) (hq : q∈(L.one::L.cin::(L.word++L.carry)).toFinset) :
      q∈L.wires.toFinset := by
    simp only [Layout.wires,Layout.word,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have mapped (q : Wire) (hq : q∈(mappedWires (correction L)++L.word++L.carry++[L.cin]).toFinset) :
      q∈L.wires.toFinset := by
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hq
    rcases hq with hq|hq|hq|hq
    · have e := correction_sources L q hq
      simp [Layout.wires,e]
    · simp only [Layout.wires,Layout.word,List.mem_toFinset,List.mem_cons,
        List.mem_append,List.not_mem_nil,or_false] at hq ⊢
      tauto
    · simp [Layout.wires,hq]
    · simp [Layout.wires,hq]
  have cx : wires [.CX L.msb L.flag]⊆L.wires.toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false,Layout.wires,List.mem_toFinset,List.mem_cons,
      List.mem_append,List.not_mem_nil] at hq ⊢
    tauto
  have pred : wires (predicate L)⊆L.wires.toFinset := by
    intro q hq
    simp only [predicate,wires_append,Finset.mem_union] at hq
    rcases hq with (hq|hq)|hq
    · exact lit q (a hq)
    · exact cx hq
    · exact lit q (b hq)
  constructor <;> intro q hq
  · simp only [center,wires_append,Finset.mem_union] at hq
    rcases hq with (hq|hq)|hq
    · exact pred hq
    · exact mapped q (c hq)
    · exact cx hq
  · simp only [canonical,wires_append,Finset.mem_union] at hq
    rcases hq with (hq|hq)|hq
    · exact cx hq
    · exact mapped q (d hq)
    · exact pred hq
end BalancedConvert

private theorem balanced_select_support (b source flag : Wire) (v : Bool) (p : Program) :
    wires (transcriptSelectWindow b source flag v p)⊆
      [b,source,flag].toFinset ∪ wires p := by
  intro q hq
  cases v <;>
    simp only [transcriptSelectWindow,transcriptSelectCompute,transcriptSelectExpose,
      transcriptSelectErase,Bool.false_eq_true,if_false,if_true,List.nil_append,
      wires_append,Finset.mem_union,wires,Instr.wires,correctionWires,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,List.mem_toFinset,
      List.mem_cons,List.not_mem_nil] at hq ⊢ <;> tauto

theorem balancedTranscriptBody_support (L : BalancedCircuit.Layout) (effS : Wire)
    (hw : L.Widths) : wires (balancedTranscriptBody L effS)⊆(effS::L.wires).toFinset := by
  have k := BalancedCircuit.support L hw
  have sw := swapRegisters_wires effS L.r L.y
    ((BalancedCleanup.widths L.toLayout hw).2.1.trans
      (BalancedCleanup.widths L.toLayout hw).2.2.1.symm)
  intro q hq
  simp only [balancedTranscriptBody,wires_append,Finset.mem_union,or_assoc] at hq
  rcases hq with hq|hq|hq|hq
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp [hq,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  · simpa only [List.mem_toFinset,List.mem_cons] using Or.inr (List.mem_toFinset.mp (k hq))
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp [hq,BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires]
  · have h := sw hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem balancedTranscriptCell_support (L : BalancedCircuit.Layout)
    (b g swap effS : Wire) (ig is : Bool) (hw : L.Widths) :
    wires (balancedTranscriptCell L b g swap effS ig is)⊆
      ([b,g,swap,effS]++L.wires).toFinset := by
  have outer := balanced_select_support b g L.sign ig
    (transcriptSelectWindow b swap effS is (balancedTranscriptBody L effS))
  have inner := balanced_select_support b swap effS is (balancedTranscriptBody L effS)
  have body := balancedTranscriptBody_support L effS hw
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

def balancedTranscriptSupport (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) : List Wire :=
  [b,effS]++L.wires++ls.flatMap (fun l => [l.1.1,l.1.2])

theorem balancedTranscriptReplay_support (L : BalancedCircuit.Layout) (b effS : Wire)
    (ls : List MixedTranscriptLetter) (hw : L.Widths) :
    wires (balancedTranscriptReplay L b effS ls)⊆(balancedTranscriptSupport L b effS ls).toFinset := by
  induction ls with
  | nil => simp [balancedTranscriptReplay,wires]
  | cons l ls ih =>
    have c := balancedTranscriptCell_support L b l.1.1 l.1.2 effS l.2.1 l.2.2 hw
    intro q hq
    simp only [balancedTranscriptReplay,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · have h := c hq
      simp only [balancedTranscriptSupport,List.flatMap_cons,List.mem_toFinset,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
    · have h := ih hq
      simp only [balancedTranscriptSupport,List.flatMap_cons,List.mem_toFinset,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.BalancedConvert.support
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptReplay_support
