import ECDSAAdd.Arithmetic.CompactSkywalkSignReleaseProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Exact signed padding identity, including the negative endpoint. -/
theorem compactSkywalkSignRelease_expanded_value (L : CompactSkywalkSignReleaseLayout)
    (s : BasisState) (hc : L.Copies s) :
    signedRegValue L.expanded s = signedRegValue L.retained s := by
  apply narrow_signed_extend L.retained L.released s (signedRegValue L.retained s)
    (by simp [CompactSkywalkSignReleaseLayout.retained]) rfl
  intro q hq
  exact (hc q hq).trans (signedRegValue_sign L.low L.sign s)

/-- A proved strict signed fit supplies every physical high sign copy. -/
theorem compactSkywalkSignRelease_copies_of_fit (L : CompactSkywalkSignReleaseLayout)
    (s : BasisState) (A : Int) (ha : signedRegValue L.expanded s = A)
    (ha0 : -((2^(L.retained.length-1):Nat):Int) ≤ A)
    (ha1 : A < ((2^(L.retained.length-1):Nat):Int)) : L.Copies s := by
  have hp := narrow_signed_prefix L.retained L.released s A
    (by simp [CompactSkywalkSignReleaseLayout.retained]) ha ha0 ha1
  have hs := signedRegValue_sign L.low L.sign s
  change s L.sign = SkywalkRails.neg (signedRegValue L.retained s) at hs
  rw [hp.1] at hs
  intro q hq
  exact (hp.2 q hq).trans hs.symm

private theorem retained_congr (L : CompactSkywalkSignReleaseLayout) (s t : BasisState)
    (he : ∀q ∈ L.retained,t q = s q) : signedRegValue L.retained t = signedRegValue L.retained s := by
  unfold signedRegValue
  rw [regValue_congr L.retained t s he]

/-- Clearing the physical tail preserves the retained signed value. The old
expanded word must subsequently be interpreted through reconstruction. -/
theorem compactSkywalkSignRelease_signed (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Copies s.basis) :
    signedRegValue L.retained (run (compactSkywalkSignRelease L) m s).basis = 
      signedRegValue L.expanded s.basis := by
  have h := (compactSkywalkSignRelease_phase_frame L hv s m).2.1
  have hp := retained_congr L s.basis (run (compactSkywalkSignRelease L) m s).basis
    (fun q hq => h q (L.retainedAway hv q hq))
  exact hp.trans (compactSkywalkSignRelease_expanded_value L s.basis hc).symm

/-- Virtual high sign extension depends only on the current retained word,
so released sites may carry other data between certified clean boundaries. -/
theorem compactSkywalkSignRelease_virtual_signed (L : CompactSkywalkSignReleaseLayout)
    (hv : L.Valid) (s : BasisState) :
    signedRegValue L.expanded (L.reconstructed s) = signedRegValue L.retained s := by
  have hc : L.Copies (L.reconstructed s) := by
    intro q hq
    simp [CompactSkywalkSignReleaseLayout.reconstructed,hq,L.signAway hv]
  have hp := retained_congr L s (L.reconstructed s) (by
    intro q hq
    simp [CompactSkywalkSignReleaseLayout.reconstructed,L.retainedAway hv q hq])
  exact (compactSkywalkSignRelease_expanded_value L (L.reconstructed s) hc).trans hp

/-- Actual CX expansion realizes the virtual signed interpretation once all
loaned sites have been returned clean; the retained sign may have changed. -/
theorem compactSkywalkSignExpand_signed (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hc : L.Clean s.basis) :
    signedRegValue L.expanded (run (compactSkywalkSignExpand L) m s).basis = 
      signedRegValue L.retained s.basis := by
  rw [compactSkywalkSignExpand_correct L hv s m hc]
  exact compactSkywalkSignRelease_virtual_signed L hv s.basis

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignRelease_signed
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignRelease_copies_of_fit
#print axioms ECDSAAdd.Arithmetic.compactSkywalkSignExpand_signed
