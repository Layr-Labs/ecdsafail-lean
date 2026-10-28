import ECDSAAdd.Arithmetic.Paper935.BlockedPostPhysical

namespace ECDSAAdd.Arithmetic.Paper935.BlockedPost
open ECDSAAdd.Arithmetic.Paper935

private theorem shared_ports (bs : List BlockedZero.Block) (scratch : List Wire)
    (hw : ∀ b∈bs,∀ x∈b.bits,x.work∈scratch) :
    ∀ q∈BlockedZero.ports bs,q∈BlockedZero.inputs bs ++ bs.map BlockedZero.Block.flag ++ scratch := by
  intro q hq
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  simp only [BlockedZero.Block.ports,List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨b,hb,rfl⟩))
  · obtain ⟨x,hx,hq⟩ := List.mem_flatMap.mp hq
    simp only [ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨x,hx,rfl⟩⟩))
    · exact List.mem_append_right _ (hw b hb x hx)

/-- Shared-work support for both directions, including all comparison work and
record wires. The record input list is not counted twice. -/
theorem shared_post_support (armed : Bool) (one zf frozen fire active witness : Wire)
    (xs : List (Wire × List Wire)) (scratch : List Wire) (rb : List ZeroBit) (k : Nat)
    (hf : BlockedZero.Fits xs scratch) :
    let W := (one::zf::frozen::fire::active::witness::
      (xs.flatMap Prod.snd ++ xs.map Prod.fst ++ scratch ++ rb.flatMap ZeroBit.wires)).toFinset
    wires (publicPost armed one zf frozen fire active witness (BlockedZero.chunks xs scratch) rb k) ⊆ W ∧
    wires (publicPostInverse armed one zf frozen fire active (BlockedZero.chunks xs scratch) rb k) ⊆ W := by
  have hp := shared_ports (BlockedZero.chunks xs scratch) scratch (BlockedZero.chunks_work xs scratch)
  rw [BlockedZero.chunks_inputs xs scratch hf] at hp
  simp only [BlockedZero.chunks,List.map_map,Function.comp_def] at hp
  have hr : ∀ q∈rb.map ZeroBit.input,q∈rb.flatMap ZeroBit.wires := by
    intro q hq
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
    exact List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
  have hs : (one::zf::frozen::fire::active::witness::
      (rb.map ZeroBit.input++BlockedZero.ports (BlockedZero.chunks xs scratch)++rb.flatMap ZeroBit.wires)).toFinset ⊆
      (one::zf::frozen::fire::active::witness::
      (xs.flatMap Prod.snd ++ xs.map Prod.fst ++ scratch ++ rb.flatMap ZeroBit.wires)).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hh := hp q
    simp only [List.mem_append] at hh
    tauto
  exact ⟨(publicPost_support armed one zf frozen fire active witness _ rb k).trans hs,
    (inverse_support armed one zf frozen fire active witness _ rb k).trans hs⟩

theorem shared_post_qubits (armed : Bool) (one zf frozen fire active witness : Wire)
    (xs : List (Wire × List Wire)) (scratch : List Wire) (rb : List ZeroBit) (k : Nat)
    (hf : BlockedZero.Fits xs scratch) :
    let bound := (xs.flatMap Prod.snd).length + xs.length + scratch.length + 2*rb.length + 6
    qubitCount (publicPost armed one zf frozen fire active witness (BlockedZero.chunks xs scratch) rb k) ≤ bound ∧
    qubitCount (publicPostInverse armed one zf frozen fire active (BlockedZero.chunks xs scratch) rb k) ≤ bound := by
  have h := shared_post_support armed one zf frozen fire active witness xs scratch rb k hf
  have hr : (rb.flatMap ZeroBit.wires).length = 2*rb.length := by
    induction rb with
    | nil => rfl
    | cons b bs ih => simp [ZeroBit.wires]; omega
  have hl : (one::zf::frozen::fire::active::witness::
      (xs.flatMap Prod.snd ++ xs.map Prod.fst ++ scratch ++ rb.flatMap ZeroBit.wires)).toFinset.card ≤
      (xs.flatMap Prod.snd).length + xs.length + scratch.length + 2*rb.length + 6 := by
    apply (List.toFinset_card_le _).trans
    simp only [List.length_cons,List.length_append,List.length_map,hr]
    omega
  exact ⟨(Finset.card_le_card h.1).trans hl,(Finset.card_le_card h.2).trans hl⟩

end ECDSAAdd.Arithmetic.Paper935.BlockedPost
