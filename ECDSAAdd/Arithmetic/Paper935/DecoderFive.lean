import ECDSAAdd.Arithmetic.Paper935.SlotDecoderReady

namespace ECDSAAdd.Arithmetic.Paper935

theorem compileSlotDecoder_five (F : SlotRegisters) (Q : HistoricalSlot) (D : SlotDecoder)
    (compiled : compileSlotDecoder F Q=some D) :
    ∃ a b c d e,D.layouts=[a,b,c,d,e] ∧ a.low.length=2 ∧ b.low.length=3 ∧
      c.low.length=4 ∧ d.low.length=5 ∧ e.low.length=6 := by
  have lens := (compileSlotDecoder_pool F Q D compiled).2.2
  cases h : D.layouts with
  | nil => simp [h] at lens
  | cons a rest =>
    cases rest with
    | nil => simp [h] at lens
    | cons b rest =>
      cases rest with
      | nil => simp [h] at lens
      | cons c rest =>
        cases rest with
        | nil => simp [h] at lens
        | cons d rest =>
          cases rest with
          | nil => simp [h] at lens
          | cons e rest =>
            cases rest with
            | nil => exact ⟨a,b,c,d,e,rfl,by simpa [h] using lens⟩
            | cons x xs => simp [h] at lens

theorem WindowRow.asStep_views (r : WindowRow) (h : 2≤r.payload.length) :
    r.asStep.wires=r.wires ∧ r.asStep.second=r.wires.getD 1 0 := by
  cases r with
  | mk payload sign =>
    cases payload with
    | nil => simp at h
    | cons x rest =>
      cases rest with
      | nil => simp at h
      | cons y ys => exact ⟨rfl,rfl⟩

end ECDSAAdd.Arithmetic.Paper935
