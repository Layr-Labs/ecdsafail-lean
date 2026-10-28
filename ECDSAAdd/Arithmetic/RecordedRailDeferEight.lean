import ECDSAAdd.Arithmetic.RecordedRailDeferPrefixStep

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

private theorem odd_outside (a b bank : List Wire) (cin even odd : Wire)
    (nd : ([cin]++a++b++bank++[even,odd]).Nodup) : odd∉b := by
  intro hb
  have h := List.nodup_iff_count.mp nd odd
  have positive := List.count_pos_iff.mpr hb
  simp only [List.count_cons,List.count_append,List.count_nil] at h
  simp only [beq_self_eq_true,if_true] at h
  omega

private theorem last_prefix (a b bank : List Wire) (cin even odd : Wire)
    (original : BasisState) (s : State) (m : List Bool) (cursor : Nat)
    (ready : Ready32 a b bank cin even odd original)
    (state : PrefixState a b bank cin even odd original s 7) :
    let out := runWithTape (segment a b bank cin even odd 7) m cursor s
    out.phase=(s.phase ^^ (m.getD (cursor+30) false && prefixCarry a b cin original 224)) ∧
    regValue b out.basis=(regValue a original+regValue b original+(original cin).toNat)%2^256 ∧
    (∀q,q∉b → out.basis q=original q) ∧
    (∀q∈bank,out.basis q=false) ∧ out.basis even=false ∧ out.basis odd=false := by
  have internalReady := prepare_prefix a b bank cin even odd even odd original s 7 (by decide)
    ready (Or.inl ⟨rfl,rfl⟩) state
  have result := finish_prefix (a.take (32*7)) (b.take (32*7)) (chunk a 7) (chunk b 7)
    bank cin even odd original s m cursor internalReady
  obtain ⟨hp,hvalue,houtside,hbank,heven⟩ := result
  have aw := ready.1
  have bw := ready.2.1
  rw [chunk_length32 a aw 7 (by decide),carry_prefix a b cin original 7 bw (by decide)] at hp
  rw [prefix_chunk a 7,prefix_chunk b 7] at hvalue
  rw [prefix_chunk b 7] at houtside
  simp only [prefix_length b bw 7 (by decide),chunk_length32 b bw 7 (by decide)] at hvalue
  simp only [show 32*(7+1)=256 from by decide,←aw,←bw,List.take_length] at hvalue houtside
  have bt : b.take a.length=b := by
    rw [ready.1,←ready.2.1,List.take_length]
  rw [bt] at hvalue houtside
  have hodd := houtside odd (odd_outside a b bank cin even odd ready.2.2.2.1)
  dsimp only
  simp only [segment,show (7:Nat)≠0 from by decide,if_neg,if_pos rfl,if_false,if_true]
  refine ⟨hp,hvalue,houtside,hbank,heven,?_⟩
  exact hodd.trans ready.2.2.2.2.2.2

/-- Actual eight-word Defer gate proof. The seven old outcomes remain phase
weights until Apply; the source, control, bank, and both real headers restore. -/
theorem correct32 (a b bank : List Wire) (cin even odd : Wire) :
    Contract32 a b bank cin even odd := by
  intro original phase m cursor ready
  let s1 := runWithTape (segment a b bank cin even odd 0) m cursor ⟨phase,original⟩
  let s2 := runWithTape (segment a b bank cin even odd 1) m (cursor+31) s1
  let s3 := runWithTape (segment a b bank cin even odd 2) m (cursor+63) s2
  let s4 := runWithTape (segment a b bank cin even odd 3) m (cursor+95) s3
  let s5 := runWithTape (segment a b bank cin even odd 4) m (cursor+127) s4
  let s6 := runWithTape (segment a b bank cin even odd 5) m (cursor+159) s5
  let s7 := runWithTape (segment a b bank cin even odd 6) m (cursor+191) s6
  let s8 := runWithTape (segment a b bank cin even odd 7) m (cursor+223) s7
  have h1 := initial_prefix a b bank cin even odd original phase m cursor ready
  change s1.phase=phase ∧ PrefixState a b bank cin even odd original s1 1 at h1
  have h2 := step_prefix a b bank cin even odd even odd original s1 m (cursor+31) 1 (by decide)
    ready (Or.inl ⟨rfl,rfl⟩) h1.2
  change s2.phase=(s1.phase ^^ (m.getD (cursor+62) false && prefixCarry a b cin original 32)) ∧
    PrefixState a b bank cin odd even original s2 2 at h2
  have h3 := step_prefix a b bank cin even odd odd even original s2 m (cursor+63) 2 (by decide)
    ready (Or.inr ⟨rfl,rfl⟩) h2.2
  change s3.phase=(s2.phase ^^ (m.getD (cursor+94) false && prefixCarry a b cin original 64)) ∧
    PrefixState a b bank cin even odd original s3 3 at h3
  have h4 := step_prefix a b bank cin even odd even odd original s3 m (cursor+95) 3 (by decide)
    ready (Or.inl ⟨rfl,rfl⟩) h3.2
  change s4.phase=(s3.phase ^^ (m.getD (cursor+126) false && prefixCarry a b cin original 96)) ∧
    PrefixState a b bank cin odd even original s4 4 at h4
  have h5 := step_prefix a b bank cin even odd odd even original s4 m (cursor+127) 4 (by decide)
    ready (Or.inr ⟨rfl,rfl⟩) h4.2
  change s5.phase=(s4.phase ^^ (m.getD (cursor+158) false && prefixCarry a b cin original 128)) ∧
    PrefixState a b bank cin even odd original s5 5 at h5
  have h6 := step_prefix a b bank cin even odd even odd original s5 m (cursor+159) 5 (by decide)
    ready (Or.inl ⟨rfl,rfl⟩) h5.2
  change s6.phase=(s5.phase ^^ (m.getD (cursor+190) false && prefixCarry a b cin original 160)) ∧
    PrefixState a b bank cin odd even original s6 6 at h6
  have h7 := step_prefix a b bank cin even odd odd even original s6 m (cursor+191) 6 (by decide)
    ready (Or.inr ⟨rfl,rfl⟩) h6.2
  change s7.phase=(s6.phase ^^ (m.getD (cursor+222) false && prefixCarry a b cin original 192)) ∧
    PrefixState a b bank cin even odd original s7 7 at h7
  have h8 := last_prefix a b bank cin even odd original s7 m (cursor+223) ready h7.2
  change s8.phase=(s7.phase ^^ (m.getD (cursor+253) false && prefixCarry a b cin original 224)) ∧
    regValue b s8.basis=(regValue a original+regValue b original+(original cin).toNat)%2^256 ∧
    (∀q,q∉b → s8.basis q=original q) ∧ (∀q∈bank,s8.basis q=false) ∧
    s8.basis even=false ∧ s8.basis odd=false at h8
  have c0 := (segment_counts a b bank cin even odd ready.1 ready.2.1 ready.2.2.1 0 (by decide)).2
  have c1 := (segment_counts a b bank cin even odd ready.1 ready.2.1 ready.2.2.1 1 (by decide)).2
  have c2 := (segment_counts a b bank cin even odd ready.1 ready.2.1 ready.2.2.1 2 (by decide)).2
  have c3 := (segment_counts a b bank cin even odd ready.1 ready.2.1 ready.2.2.1 3 (by decide)).2
  have c4 := (segment_counts a b bank cin even odd ready.1 ready.2.1 ready.2.2.1 4 (by decide)).2
  have c5 := (segment_counts a b bank cin even odd ready.1 ready.2.1 ready.2.2.1 5 (by decide)).2
  have c6 := (segment_counts a b bank cin even odd ready.1 ready.2.1 ready.2.2.1 6 (by decide)).2
  norm_num at c0 c1 c2 c3 c4 c5 c6
  have runAll : runWithTape (forward32 a b bank cin even odd) m cursor ⟨phase,original⟩=s8 := by
    simp only [forward32,runWithTape_append,recordedMeasurementCount_append,c0,c1,c2,c3,c4,c5,c6,
      Nat.add_assoc,Nat.reduceAdd]
    rfl
  dsimp only
  rw [runAll]
  refine ⟨?_,h8.2⟩
  rw [h8.1,h7.1,h6.1,h5.1,h4.1,h3.1,h2.1,h1.1]
  simp only [debt32,ordinals,positions,List.zip,List.zipWith,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,Nat.reduceAdd,Bool.xor_false,Bool.xor_assoc]

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.correct32
