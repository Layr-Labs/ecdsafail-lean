import ECDSAAdd.Arithmetic.Paper935.ProbeChunks
import ECDSAAdd.Arithmetic.Paper935.PostCompiler

namespace ECDSAAdd.Arithmetic.Paper935

private theorem chunksGo_count {α : Type} (n : Nat) (xs : List α) (part : Array α) (done : Array (List α))
    (positive : 0<n) (partPositive : 0<part.size) (partBound : part.size≤n) :
    (List.toChunks.go n xs part done).length = done.size + (part.size+xs.length-1)/n+1 := by
  induction xs generalizing part done with
  | nil =>
    have hz : (part.size-1)/n=0 := Nat.div_eq_of_lt (by omega)
    simp [List.toChunks.go,hz]
  | cons x xs ih =>
    simp only [List.toChunks.go]
    split
    · rename_i h
      have he : part.size=n := by simpa using h
      rw [ih _ _ (by simp) (by simp; omega)]
      simp only [Array.size_push,List.length_cons]
      change done.size+1+(1+xs.length-1)/n+1 = _
      rw [show 1+xs.length-1=xs.length by omega]
      have hnum : part.size+(xs.length+1)-1=xs.length+n := by omega
      rw [hnum,Nat.add_div_right _ positive]
      omega
    · rw [ih _ _ (by simp) (by simp only [Array.size_push]; simp_all only [beq_iff_eq]; omega)]
      simp only [Array.size_push,List.length_cons]
      rw [show part.size+1+xs.length-1=part.size+(xs.length+1)-1 by omega]

/-- Public chunk count for the actual tail-recursive probe partition. -/
def probeChunkCount (length width : Nat) : Nat :=
  if length=0 then 0 else (length-1)/width+1

theorem probeChunks_count (inputs : List Wire) (width : Nat) (positive : 0<width) :
    (inputs.toChunks width).length = probeChunkCount inputs.length width := by
  cases inputs with
  | nil => simp [List.toChunks,probeChunkCount]
  | cons x xs =>
    cases width with
    | zero => omega
    | succ n =>
      simpa [List.toChunks,probeChunkCount,Nat.add_comm] using
        chunksGo_count (n+1) xs #[x] #[] positive (by simp) (by simp)

/-- Shared post work depends only on public input and record lengths. -/
theorem postPoolSize_public (inputs record : List Wire) (width : Nat) (positive : 0<width) :
    postPoolSize inputs record width = max (width+probeChunkCount inputs.length width) (record.length+1) := by
  rw [postPoolSize,probeChunks_count inputs width positive]

end ECDSAAdd.Arithmetic.Paper935
