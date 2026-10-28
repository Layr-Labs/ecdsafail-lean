import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
import ECDSAAdd.Arithmetic.SignedSquarePhysical
import ECDSAAdd.Arithmetic.MappedSignedSquare

namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem mappedDiag_physical (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin :: xs ++ dst ++ carry).Nodup) :
    GatePhysical (mappedDiagAdd xs dst carry cin) ∧
    GatePhysical (mappedDiagSub xs dst carry cin) := by
  have nd : (cin :: dst ++ carry.take (dst.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    have ht := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have ha : ∀ b ∈ mappedDiagonal xs, ∀ q ∈ b.wire,
      q ∉ cin :: dst ++ carry.take (dst.length-1) := by
    intro b hb q hq hm
    have hs : q ∈ mappedWires (mappedDiagonal xs) :=
      List.mem_flatMap.mpr ⟨b,hb,by simpa using hq⟩
    rw [mappedDiagonal_wires] at hs
    have hx : q ∈ xs := by
      rcases List.mem_append.mp hs with h|h
      · exact h
      · exact List.mem_of_mem_take h
    have h := List.nodup_iff_count.mp hn q
    have hc := List.count_pos_iff.mpr hx
    have hh := List.count_pos_iff.mpr hm
    have ht := (List.take_sublist (dst.length-1) carry).count_le q
    simp only [List.count_cons,List.count_append] at h hh; omega
  have hadd := mappedAdd_physical (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin nd ha
  refine ⟨hadd,?_⟩
  simp only [mappedDiagSub,mappedSub,gatePhysical_append]
  exact ⟨⟨notRegister_physical _,hadd⟩,notRegister_physical _⟩

theorem mappedSignedSquare_physical (xs dst pad carry : List Wire) (cin : Wire)
    (hn : (cin :: xs ++ dst ++ pad ++ carry).Nodup) :
    GatePhysical (mappedSignedSquare xs dst pad carry cin) ∧
    GatePhysical (mappedSignedSquareClear xs dst pad carry cin) := by
  have nr : (xs ++ dst ++ pad ++ carry).Nodup := (List.nodup_cons.mp hn).2
  have nt : (xs ++ dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have nd : (cin :: xs ++ dst ++ carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have rows := signedSquareRows_physical xs dst pad carry nr
  have top := signedSquareTop_physical xs dst nt
  have diag := mappedDiag_physical xs dst carry cin nd
  simp only [mappedSignedSquare,mappedSignedSquareClear,gatePhysical_append]
  exact ⟨⟨⟨rows.1,top⟩,diag.2⟩,⟨diag.1,top⟩,rows.2⟩

end ECDSAAdd.Arithmetic
