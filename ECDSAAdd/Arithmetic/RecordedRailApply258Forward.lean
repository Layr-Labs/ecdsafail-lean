import ECDSAAdd.Arithmetic.RecordedRailApply258Finish

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApply258
open RecordedRailDefer

private theorem segment_m (a b bank : List Wire) (cin even odd : Wire)
    (original : BasisState) (ready : Ready a b bank cin even odd original)
    (j : Nat) (hj : j<7) :
    recordedMeasurementCount (segment a b (bank.take 31) cin even odd j)=(if j=0 then 31 else 32) := by
  have al : RecordedRailVented.Aligned (chunk a j) (chunk b j) (bank.take 31) := by
    simp [RecordedRailVented.Aligned,chunk_length a ready.1 j hj,
      chunk_length b ready.2.1 j hj,ready.2.2.1]
  have shape := RecordedRailVented.aligned_shape _ _ _ al
  by_cases zero : j=0
  · subst j
    have costs := RecordedRailVented.counts _ _ _ shape (some cin) even
    simpa only [segment,if_pos rfl,chunk_length a ready.1 0 (by decide)] using costs.2
  · have last : j≠7 := by omega
    have costs := advance_counts _ _ _ shape (boundary even odd (j-1)) (boundary even odd j)
    simpa only [segment,if_neg zero,if_neg last,chunk_length a ready.1 j hj] using costs.2

/-- Actual eight-word Defer gate proof. The seven old outcomes remain phase
weights until Apply; the source, control, bank, and both real headers restore. -/
theorem correct_forward (a b bank : List Wire) (cin even odd : Wire) :
    ForwardContract a b bank cin even odd := by
  intro original phase m cursor ready
  let s1 := runWithTape (segment a b (bank.take 31) cin even odd 0) m cursor ⟨phase,original⟩
  let s2 := runWithTape (segment a b (bank.take 31) cin even odd 1) m (cursor+31) s1
  let s3 := runWithTape (segment a b (bank.take 31) cin even odd 2) m (cursor+63) s2
  let s4 := runWithTape (segment a b (bank.take 31) cin even odd 3) m (cursor+95) s3
  let s5 := runWithTape (segment a b (bank.take 31) cin even odd 4) m (cursor+127) s4
  let s6 := runWithTape (segment a b (bank.take 31) cin even odd 5) m (cursor+159) s5
  let s7 := runWithTape (segment a b (bank.take 31) cin even odd 6) m (cursor+191) s6
  let s8 := runWithTape (finish (a.drop 224) (b.drop 224) bank even) m (cursor+223) s7
  have h1 := initial_prefix a b bank cin even odd original phase m cursor ready
  change s1.phase=phase ∧ PrefixState a b (bank.take 31) cin even odd original s1 1 at h1
  have h2 := step_prefix a b bank cin even odd even odd original s1 m (cursor+31) 1 (by decide)
    ready (Or.inl ⟨rfl,rfl⟩) h1.2
  change s2.phase=(s1.phase ^^ (m.getD (cursor+62) false && prefixCarry a b cin original 32)) ∧
    PrefixState a b (bank.take 31) cin odd even original s2 2 at h2
  have h3 := step_prefix a b bank cin even odd odd even original s2 m (cursor+63) 2 (by decide)
    ready (Or.inr ⟨rfl,rfl⟩) h2.2
  change s3.phase=(s2.phase ^^ (m.getD (cursor+94) false && prefixCarry a b cin original 64)) ∧
    PrefixState a b (bank.take 31) cin even odd original s3 3 at h3
  have h4 := step_prefix a b bank cin even odd even odd original s3 m (cursor+95) 3 (by decide)
    ready (Or.inl ⟨rfl,rfl⟩) h3.2
  change s4.phase=(s3.phase ^^ (m.getD (cursor+126) false && prefixCarry a b cin original 96)) ∧
    PrefixState a b (bank.take 31) cin odd even original s4 4 at h4
  have h5 := step_prefix a b bank cin even odd odd even original s4 m (cursor+127) 4 (by decide)
    ready (Or.inr ⟨rfl,rfl⟩) h4.2
  change s5.phase=(s4.phase ^^ (m.getD (cursor+158) false && prefixCarry a b cin original 128)) ∧
    PrefixState a b (bank.take 31) cin even odd original s5 5 at h5
  have h6 := step_prefix a b bank cin even odd even odd original s5 m (cursor+159) 5 (by decide)
    ready (Or.inl ⟨rfl,rfl⟩) h5.2
  change s6.phase=(s5.phase ^^ (m.getD (cursor+190) false && prefixCarry a b cin original 160)) ∧
    PrefixState a b (bank.take 31) cin odd even original s6 6 at h6
  have h7 := step_prefix a b bank cin even odd odd even original s6 m (cursor+191) 6 (by decide)
    ready (Or.inr ⟨rfl,rfl⟩) h6.2
  change s7.phase=(s6.phase ^^ (m.getD (cursor+222) false && prefixCarry a b cin original 192)) ∧
    PrefixState a b (bank.take 31) cin even odd original s7 7 at h7
  have h8 := last_prefix a b bank cin even odd original s7 m (cursor+223) ready h7.2
  change s8.phase=(s7.phase ^^ (m.getD (cursor+255) false && prefixCarry a b cin original 224)) ∧
    regValue b s8.basis=(regValue a original+regValue b original+(original cin).toNat)%2^258 ∧
    (∀q,q∉b → s8.basis q=original q) ∧ (∀q∈bank,s8.basis q=false) ∧
    s8.basis even=false ∧ s8.basis odd=false at h8
  have c0 := (segment_m a b bank cin even odd original ready 0 (by decide))
  have c1 := (segment_m a b bank cin even odd original ready 1 (by decide))
  have c2 := (segment_m a b bank cin even odd original ready 2 (by decide))
  have c3 := (segment_m a b bank cin even odd original ready 3 (by decide))
  have c4 := (segment_m a b bank cin even odd original ready 4 (by decide))
  have c5 := (segment_m a b bank cin even odd original ready 5 (by decide))
  have c6 := (segment_m a b bank cin even odd original ready 6 (by decide))
  norm_num at c0 c1 c2 c3 c4 c5 c6
  have runAll : runWithTape (forward a b bank cin even odd) m cursor ⟨phase,original⟩=s8 := by
    simp only [forward,runWithTape_append,recordedMeasurementCount_append,c0,c1,c2,c3,c4,c5,c6,
      Nat.add_assoc,Nat.reduceAdd]
    rfl
  dsimp only
  rw [runAll]
  refine ⟨?_,h8.2⟩
  rw [h8.1,h7.1,h6.1,h5.1,h4.1,h3.1,h2.1,h1.1]
  simp only [debt,ordinals,RecordedRailDefer.positions,List.zip,List.zipWith,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,Nat.reduceAdd,Bool.xor_false,Bool.xor_assoc]

end ECDSAAdd.Arithmetic.RecordedRailApply258
#print axioms ECDSAAdd.Arithmetic.RecordedRailApply258.correct_forward
