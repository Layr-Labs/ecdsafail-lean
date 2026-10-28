import ECDSAAdd.Arithmetic.BlockedZero

namespace ECDSAAdd.Arithmetic.BlockedZero

/-- Public layout: a flag and an input list for each block; a single independent
scratch list is shared by all blocks. No truncation is permitted by the API. -/
def chunks (xs : List (Wire × List Wire)) (scratch : List Wire) : List Block :=
  xs.map (fun p => ⟨p.1,List.zipWith ZeroBit.mk p.2 scratch⟩)

def Fits (xs : List (Wire × List Wire)) (scratch : List Wire) : Prop :=
  ∀ p ∈ xs, p.2.length ≤ scratch.length

private theorem zip_inputs (xs scratch : List Wire) (h : xs.length ≤ scratch.length) :
    (List.zipWith ZeroBit.mk xs scratch).map ZeroBit.input = xs := by
  induction xs generalizing scratch with
  | nil => simp
  | cons x xs ih =>
    cases scratch with
    | nil => simp at h
    | cons w ws => simpa using congrArg (List.cons x) (ih ws (by simpa using h))

private theorem zip_work (xs scratch : List Wire) :
    ∀ b ∈ List.zipWith ZeroBit.mk xs scratch, b.work ∈ scratch := by
  induction xs generalizing scratch with
  | nil => simp
  | cons x xs ih =>
    cases scratch with
    | nil => simp
    | cons w ws =>
      intro b hb
      simp only [List.zipWith_cons_cons,List.mem_cons] at hb
      rcases hb with rfl | hb
      · simp
      · exact List.mem_cons_of_mem _ (ih ws b hb)

theorem chunks_inputs (xs : List (Wire × List Wire)) (scratch : List Wire)
    (hf : Fits xs scratch) : inputs (chunks xs scratch) = xs.flatMap Prod.snd := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    simp only [chunks,List.map_cons,inputs,List.flatMap_cons]
    rw [zip_inputs p.2 scratch (hf p (by simp))]
    exact congrArg (List.append p.2) (ih (fun q hq => hf q (by simp [hq])))

theorem chunks_work (xs : List (Wire × List Wire)) (scratch : List Wire) :
    ∀ b ∈ chunks xs scratch, ∀ x ∈ b.bits, x.work ∈ scratch := by
  intro b hb
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hb
  exact zip_work p.2 scratch

theorem chunks_clean (xs : List (Wire × List Wire)) (scratch : List Wire) (s : BasisState)
    (hf : ∀ p ∈ xs, s p.1 = false) (hw : ∀ w ∈ scratch, s w = false) :
    clean (chunks xs scratch) s := by
  intro b hb
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  exact ⟨hf p hp,fun x hx => hw x.work (zip_work p.2 scratch x hx)⟩

/-- External contract uses independent input lists and shared work, and accepts
arbitrary output, control, and measurement tape. -/
theorem chunks_run (c target : Wire) (xs : List (Wire × List Wire)) (scratch : List Wire)
    (hf : Fits xs scratch) (hv : Valid c target (chunks xs scratch))
    (s : State) (m : List Bool) (hflags : ∀ p ∈ xs, s.basis p.1 = false)
    (hw : ∀ w ∈ scratch, s.basis w = false) :
    run (program c target (chunks xs scratch)) m s =
      ⟨s.phase,writeBit s.basis target
        (s.basis target ^^ (s.basis c && decide (regValue (xs.flatMap Prod.snd) s.basis = 0)))⟩ := by
  rw [run_eq c target _ hv s m (chunks_clean xs scratch s.basis hflags hw),
    test_eq_zero,chunks_inputs xs scratch hf]

theorem chunks_counts (c target : Wire) (xs : List (Wire × List Wire)) (scratch : List Wire)
    (hf : Fits xs scratch) :
    toffoliCount (program c target (chunks xs scratch)) = 2 * (xs.flatMap Prod.snd).length ∧
    measurementCount (program c target (chunks xs scratch)) = 2 * (xs.flatMap Prod.snd).length := by
  simpa only [chunks_inputs xs scratch hf] using counts c target (chunks xs scratch)

theorem chunks_qubits_le (c target : Wire) (xs : List (Wire × List Wire)) (scratch : List Wire)
    (hf : Fits xs scratch) :
    qubitCount (program c target (chunks xs scratch)) ≤
      (xs.flatMap Prod.snd).length + xs.length + scratch.length + 2 := by
  have h := qubits_le c target (chunks xs scratch) scratch (chunks_work xs scratch)
  rw [chunks_inputs xs scratch hf] at h
  simpa only [chunks,List.length_map] using h

theorem chunks_support (c target : Wire) (xs : List (Wire × List Wire)) (scratch : List Wire)
    (hf : Fits xs scratch) :
    wires (program c target (chunks xs scratch)) ⊆
      (c::target::(xs.flatMap Prod.snd ++ xs.map Prod.fst ++ scratch)).toFinset := by
  have h := shared_support c target (chunks xs scratch) scratch (chunks_work xs scratch)
  rw [chunks_inputs xs scratch hf] at h
  simpa only [chunks,List.map_map,Function.comp_def] using h

theorem chunks_physical (c target : Wire) (xs : List (Wire × List Wire)) (scratch : List Wire)
    (hv : Valid c target (chunks xs scratch)) :
    GatePhysical (program c target (chunks xs scratch)) :=
  physical c target _ hv

/-- With at most 43 blocks of at most six bits, a 256-bit row uses no more
than 307 wires total: 256 inputs, 43 flags, six shared scratch, and two ports. -/
theorem six_bit_qubits_le (c target : Wire) (xs : List (Wire × List Wire)) (scratch : List Wire)
    (hf : Fits xs scratch) (hi : (xs.flatMap Prod.snd).length ≤ 256)
    (hb : xs.length ≤ 43) (hw : scratch.length ≤ 6) :
    qubitCount (program c target (chunks xs scratch)) ≤ 307 := by
  have h := chunks_qubits_le c target xs scratch hf
  omega

end ECDSAAdd.Arithmetic.BlockedZero
