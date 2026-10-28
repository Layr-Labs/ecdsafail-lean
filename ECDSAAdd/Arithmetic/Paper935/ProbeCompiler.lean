import ECDSAAdd.Arithmetic.Paper935.BlockedPostShared
import ECDSAAdd.Arithmetic.Paper935.HistoryAllocation

namespace ECDSAAdd.Arithmetic.Paper935

instance blockedValidDecidable (c target : Wire) (bs : List BlockedZero.Block) :
    Decidable (BlockedZero.Valid c target bs) := by
  induction bs generalizing c with
  | nil => unfold BlockedZero.Valid; infer_instance
  | cons b bs ih =>
    letI := ih b.flag
    unfold BlockedZero.Valid
    infer_instance

instance (xs : List (Wire × List Wire)) (scratch : List Wire) :
    Decidable (BlockedZero.Fits xs scratch) := by
  unfold BlockedZero.Fits
  infer_instance

/-- Public chunking assigns one flag per block and reuses the remaining
scratch across blocks. The checked input equality forbids truncation. -/
def probeCandidate (inputs work : List Wire) (width : Nat) : List (Wire × List Wire) × List Wire :=
  let chunks := inputs.toChunks width
  (List.zip (work.take chunks.length) chunks,work.drop chunks.length)

def compileProbe (one target : Wire) (inputs work : List Wire) (width : Nat) :
    Option (List BlockedZero.Block) :=
  let (xs,scratch) := probeCandidate inputs work width
  let bs := BlockedZero.chunks xs scratch
  if BlockedZero.Valid one target bs ∧ xs.flatMap Prod.snd=inputs ∧
      BlockedZero.Fits xs scratch then some bs else none

theorem compileProbe_contract (one target : Wire) (inputs work : List Wire) (width : Nat)
    (bs : List BlockedZero.Block) (h : compileProbe one target inputs work width=some bs) :
    BlockedZero.Valid one target bs ∧ BlockedZero.inputs bs=inputs := by
  unfold compileProbe at h
  dsimp only at h
  split at h
  next valid =>
    cases h
    exact ⟨valid.1,(BlockedZero.chunks_inputs _ _ valid.2.2).trans valid.2.1⟩
  next invalid => simp at h

def compileBorrowedProbe (A : Arena) (one target : Wire) (inputs : List Wire) (width : Nat) :
    Option (Arena × List Wire × List BlockedZero.Block) := do
  let (D,work) ← A.borrowMany (width+(inputs.toChunks width).length)
  let bs ← compileProbe one target inputs work width
  pure (D,work,bs)

theorem compileBorrowedProbe_contract (A D : Arena) (one target : Wire)
    (inputs work : List Wire) (width : Nat) (bs : List BlockedZero.Block)
    (h : compileBorrowedProbe A one target inputs width=some (D,work,bs)) :
    A.borrowMany (width+(inputs.toChunks width).length)=some (D,work) ∧
    compileProbe one target inputs work width=some bs := by
  unfold compileBorrowedProbe at h
  cases hb : A.borrowMany (width+(inputs.toChunks width).length) with
  | none => simp [hb] at h
  | some result =>
    rcases result with ⟨B,ws⟩
    simp only [hb] at h
    dsimp only [Bind.bind,Option.bind,Prod.fst,Prod.snd] at h
    cases hc : compileProbe one target inputs ws width with
    | none => simp [hc] at h
    | some ks =>
      simp only [hc] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      exact ⟨rfl,hc⟩

end ECDSAAdd.Arithmetic.Paper935
