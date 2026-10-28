import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler

namespace ECDSAAdd.Arithmetic.Paper935

/-- Physical widening for history remains inside the same public row-count
bounds. This finite table check is kernel reduction, not native evaluation,
and says nothing about failure probabilities. -/
theorem author_history_window_bounds : ∀ w∈authorWindows,
    (historyWindow w).payload≤582 ∧ (historyWindow w).addPad.payload≤588 := by decide +kernel

theorem historyWindow_covers (w : RowWindow) : w.Le (historyWindow w) := by
  exact ⟨le_rfl,le_rfl,Nat.le_max_right _ _,le_rfl⟩

theorem historyWindow_fits (w : RowWindow) (s : ECDSAAdd.Divsteps.ZState) (h : w.Fits s) :
    (historyWindow w).Fits s := by
  exact ⟨h.1,h.2.1,h.2.2.1.mono (Nat.le_max_right _ _),h.2.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
