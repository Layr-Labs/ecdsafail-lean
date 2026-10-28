import ECDSAAdd.Arithmetic.Paper935.HmrRowMulPrefixEquivalence
import ECDSAAdd.Arithmetic.Paper935.HmrSourceCallPorts

namespace ECDSAAdd.Arithmetic.Paper935

attribute [local irreducible] placedRowFold placedMagnitude

private theorem legacyPrefix_ports (ports : Array Wire) (L : HmrRowMulLayout)
    (hm : (0 :: List.range' 1 280 ++ List.range' 793 24).map (rowMulPort ports 0) =
      L.row.sign :: L.row.payload ++ L.anc)
    (hr : (List.range' 1 280).map (rowMulPort ports 0) = L.row.payload)
    (ho : (List.range' 537 256).map (rowMulPort ports 0) = L.out)
    (ha : (List.range' 793 24).map (rowMulPort ports 0) = L.anc) :
    rowMulLegacyPrefix ports = embedRecorded (L.lift ++ L.fold) := by
  dsimp only [rowMulLegacyPrefix]
  rw [hm, hr, ho, ha]
  rfl

private theorem ports2_m : (0 :: List.range' 1 280 ++ List.range' 793 24).map (rowMulPort s2ForwardPorts 0) =
    s2HmrSourceLayout.row.sign :: s2HmrSourceLayout.row.payload ++ s2HmrSourceLayout.anc := by decide +kernel

private theorem ports2_r : (List.range' 1 280).map (rowMulPort s2ForwardPorts 0) =
    s2HmrSourceLayout.row.payload := by decide +kernel

private theorem ports2_o : (List.range' 537 256).map (rowMulPort s2ForwardPorts 0) =
    s2HmrSourceLayout.out := by decide +kernel

private theorem ports2_a : (List.range' 793 24).map (rowMulPort s2ForwardPorts 0) =
    s2HmrSourceLayout.anc := by decide +kernel

theorem s2ForwardPrefix_layout : rowMulLegacyPrefix s2ForwardPorts =
    embedRecorded (s2HmrSourceLayout.lift ++ s2HmrSourceLayout.fold) :=
  legacyPrefix_ports s2ForwardPorts s2HmrSourceLayout ports2_m ports2_r ports2_o ports2_a

private theorem ports6_m : (0 :: List.range' 1 280 ++ List.range' 793 24).map (rowMulPort s6ForwardPorts 0) =
    s6HmrSourceLayout.row.sign :: s6HmrSourceLayout.row.payload ++ s6HmrSourceLayout.anc := by decide +kernel

private theorem ports6_r : (List.range' 1 280).map (rowMulPort s6ForwardPorts 0) =
    s6HmrSourceLayout.row.payload := by decide +kernel

private theorem ports6_o : (List.range' 537 256).map (rowMulPort s6ForwardPorts 0) =
    s6HmrSourceLayout.out := by decide +kernel

private theorem ports6_a : (List.range' 793 24).map (rowMulPort s6ForwardPorts 0) =
    s6HmrSourceLayout.anc := by decide +kernel

theorem s6ForwardPrefix_layout : rowMulLegacyPrefix s6ForwardPorts =
    embedRecorded (s6HmrSourceLayout.lift ++ s6HmrSourceLayout.fold) :=
  legacyPrefix_ports s6ForwardPorts s6HmrSourceLayout ports6_m ports6_r ports6_o ports6_a

end ECDSAAdd.Arithmetic.Paper935
