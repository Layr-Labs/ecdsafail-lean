import ECDSAAdd.Arithmetic.MontLookupPhysical
import ECDSAAdd.Arithmetic.MontAdapterLayout

namespace ECDSAAdd.Arithmetic

theorem montRounds_physical (L : MontStageLayout) (x y : List Wire) (p k : Nat)
    (hw : L.Widths) (hn : (x++y++L.wires).Nodup)
    (hk : k ≤ 64) (hy : 256 ≤ y.length) :
    GatePhysical (montPrepareRounds L x y p k) ∧ GatePhysical (montRestoreRounds L x y p k) := by
  induction k with
  | zero => simp [montPrepareRounds,montRestoreRounds,GatePhysical]
  | succ k ih =>
    have prev := ih (by omega)
    have step := montWindow_physical L x y p k hw hn (by omega) hy
    simp only [montPrepareRounds,montRestoreRounds,gatePhysical_append]
    exact ⟨⟨prev.1,step.1⟩,⟨step.2,prev.2⟩⟩

theorem constRounds_physical (L : MontStageLayout) (y : List Wire) (p K k : Nat)
    (hw : L.Widths) (hn : (y++L.wires).Nodup)
    (hk : k ≤ 64) (hy : 256 ≤ y.length) :
    GatePhysical (constPrepareRounds L y p K k) ∧ GatePhysical (constRestoreRounds L y p K k) := by
  induction k with
  | zero => simp [constPrepareRounds,constRestoreRounds,GatePhysical]
  | succ k ih =>
    have prev := ih (by omega)
    have step := constMontWindow_physical L y p K k hw hn (by omega) hy
    simp only [constPrepareRounds,constRestoreRounds,gatePhysical_append]
    exact ⟨⟨prev.1,step.1⟩,⟨step.2,prev.2⟩⟩

theorem montStage_physical (L : MontStageLayout) (x y : List Wire) (p : Nat)
    (hw : L.Widths) (hn : (x++y++L.wires).Nodup) (hy : 256 ≤ y.length) :
    GatePhysical (montPrepare L x y p) ∧ GatePhysical (montRestore L x y p) := by
  have nd : L.wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append] at h; omega
  have rounds := montRounds_physical L x y p 64 hw hn (by omega) hy
  have norm := montNormalize_physical L p hw nd
  simp only [montPrepare,montRestore,gatePhysical_append]
  exact ⟨⟨rounds.1,norm.1⟩,⟨norm.2,rounds.2⟩⟩

theorem constStage_physical (L : MontStageLayout) (y : List Wire) (p K : Nat)
    (hw : L.Widths) (hn : (y++L.wires).Nodup) (hy : 256 ≤ y.length) :
    GatePhysical (constPrepare L y p K) ∧ GatePhysical (constRestore L y p K) := by
  have nd : L.wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append] at h; omega
  have rounds := constRounds_physical L y p K 64 hw hn (by omega) hy
  have norm := montNormalize_physical L p hw nd
  simp only [constPrepare,constRestore,gatePhysical_append]
  exact ⟨⟨rounds.1,norm.1⟩,⟨norm.2,rounds.2⟩⟩

theorem montPQ_physical (M : MontLayout) (p : Nat) (hw : M.Widths) (hn : M.wires.Nodup) :
    GatePhysical (montP M p) ∧ GatePhysical (montQ M p) := by
  have first := montStage_physical M.first M.x M.y p hw.first (M.first_nodup hn) (by rw [hw.y])
  have second := constStage_physical M.second M.a p (montgomeryConversion p)
    (M.second_widths hw) (M.second_nodup hn) (by change 256 ≤ M.first.acc.length; rw [hw.first.acc]; omega)
  simp only [montP,montQ,gatePhysical_append]
  exact ⟨⟨first.1,second.1⟩,⟨second.2,first.2⟩⟩

theorem montControlled_physical (c : Wire) (M : MontLayout) (p : Nat)
    (hw : M.Widths) (hn : (c :: M.wires).Nodup) :
    GatePhysical (montMulControlledAdd c M p) ∧ GatePhysical (montMulControlledSub c M p) := by
  have pq := montPQ_physical M p hw hn.tail
  have nd := M.controlled_add_nodup c hw hn
  simp only [montMulControlledAdd,montMulControlledSub,gatePhysical_append]
  exact ⟨⟨⟨pq.1,controlledModAdd_physical _ _ _ nd⟩,pq.2⟩,
    ⟨⟨pq.1,controlledModSub_physical _ _ _ nd⟩,pq.2⟩⟩

end ECDSAAdd.Arithmetic
