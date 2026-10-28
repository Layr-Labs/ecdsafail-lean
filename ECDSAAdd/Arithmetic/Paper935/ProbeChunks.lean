import ECDSAAdd.Arithmetic.Paper935.ProbeGeometry

namespace ECDSAAdd.Arithmetic.Paper935

private theorem chunksGo_flatten {α : Type} (n : Nat) (xs : List α) (part : Array α) (done : Array (List α)) :
    (List.toChunks.go n xs part done).flatten=done.toList.flatten++part.toList++xs := by
  induction xs generalizing part done with
  | nil => simp [List.toChunks.go]
  | cons x xs ih =>
    simp only [List.toChunks.go]
    split <;> rw [ih] <;> simp [List.append_assoc]

private theorem chunksGo_lengths {α : Type} (n : Nat) (xs : List α) (part : Array α) (done : Array (List α))
    (positive : 0<n) (partBound : part.size≤n) (doneBound : ∀ c∈done.toList,c.length≤n) :
    ∀ c∈List.toChunks.go n xs part done,c.length≤n := by
  induction xs generalizing part done with
  | nil => simpa [List.toChunks.go] using
      (show ∀ c∈done.toList++[part.toList],c.length≤n from by
        intro c hc
        rcases List.mem_append.mp hc with hc|hc
        · exact doneBound c hc
        · obtain rfl := List.mem_singleton.mp hc
          simpa using partBound)
  | cons x xs ih =>
    simp only [List.toChunks.go]
    split
    · apply ih _ _ (by simpa using positive)
      intro c hc
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at hc
      rcases hc with hc|rfl
      · exact doneBound c hc
      · simpa using partBound
    · apply ih _ _ (by simp only [Array.size_push]; simp_all only [beq_iff_eq]; omega) doneBound

/-- The actual tail-recursive public chunker preserves all physical inputs. -/
theorem probeChunks_flatten (inputs : List Wire) (width : Nat) :
    (inputs.toChunks width).flatten=inputs := by
  cases inputs with
  | nil => simp [List.toChunks]
  | cons x xs =>
    cases width with
    | zero => simp [List.toChunks]
    | succ n => simpa only [List.toChunks] using chunksGo_flatten (n+1) xs #[x] #[]

/-- Every actual public chunk fits the shared width, provided it is positive. -/
theorem probeChunks_lengths (inputs : List Wire) (width : Nat) (positive : 0<width) :
    ∀ c∈inputs.toChunks width,c.length≤width := by
  cases inputs with
  | nil => simp [List.toChunks]
  | cons x xs =>
    cases width with
    | zero => omega
    | succ n =>
      exact chunksGo_lengths (n+1) xs #[x] #[] positive (by simp) (by simp)

end ECDSAAdd.Arithmetic.Paper935
