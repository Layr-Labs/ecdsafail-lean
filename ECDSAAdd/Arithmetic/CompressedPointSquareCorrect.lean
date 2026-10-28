import ECDSAAdd.Arithmetic.CompressedPointSquarePool
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace ECDSAAdd.Arithmetic.CompressedPointSquare
open ControlledPointLayout Secp256k1
attribute [local irreducible] run wires computableProgram program pointMeasuredSquareCandidate

private theorem pool_bit (L : ControlledPointLayout) (hw : L.Widths)
    (i : Nat) (hi : i < 945) : L.core.poolWire i∈L.dialogPool := by
  change L.core.poolWire i∈L.core.pool.take 2613
  rw [←L.core.pool_prefix hw 2613 (by omega)]
  exact List.mem_map.mpr ⟨i,by simp [List.mem_range'_1]; omega,rfl⟩

private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

/-- Only declared pool wires move. Their zero basis bits make the complete
State invariant under the public permutation, including incoming phase. -/
theorem zero_pool_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (clean : ∀q∈L.dialogPool,s.basis q=false) :
    pullState (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) s=s := by
  classical
  let inj := layout_bounded_injective L hw hn
  let e := poolPermutation L.core.poolWire inj
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (e q)=s.basis q
    by_cases left : LeftSite L.core.poolWire q
    · obtain ⟨i,lo,hi,rfl⟩ := left
      have eq : e (L.core.poolWire i)=L.core.poolWire (indexPermutation i) :=
        wire_apply L.core.poolWire inj i (by omega)
      rw [eq]
      exact (clean _ (pool_bit L hw _ (index_bounded i (by omega)))).trans
        (clean _ (pool_bit L hw i (by omega))).symm
    · by_cases right : RightSite L.core.poolWire q
      · obtain ⟨i,lo,hi,rfl⟩ := right
        have eq : e (L.core.poolWire i)=L.core.poolWire (indexPermutation i) :=
          wire_apply L.core.poolWire inj i hi
        rw [eq]
        exact (clean _ (pool_bit L hw _ (index_bounded i hi))).trans
          (clean _ (pool_bit L hw i hi)).symm
      · rw [outside_fixed L.core.poolWire inj q left right]

private theorem pull_injective (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

/-- Exact complete-State equivalence for the actual computable emission.
All original square inputs, independent records, and the full pool contract
are retained; the permutation is confined to clean declared sites. -/
theorem state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (computableProgram L) m s=run (pointMeasuredSquareCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := pointMeasuredSquareCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (pointMeasuredSquareCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (pool_away_x L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (pointMeasuredSquareCandidate L) m s) cleanOut
  rw [computableProgram_eq L hw hn,program]
  apply pull_injective e
  have semantic := run_rename e e.injective (pointMeasuredSquareCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

/-- Existing phase, numeric, clean-work, and every outsider guarantees are
inherited as properties of the actual computable renamed square. -/
theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (computableProgram L) m s).phase=s.phase ∧
    regValue L.point.x (run (computableProgram L) m s).basis=
      (X+p-(if B then Y*Y else 0)%p)%p ∧
    ∀q,q∉L.point.x → (run (computableProgram L) m s).basis q=s.basis q := by
  rw [state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact pointMeasuredSquareCandidate_correct L hw hn X Y B hX s m hb hx hy hc

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (computableProgram L)=99902 ∧ measurementCount (computableProgram L)=99382 := by
  rw [computableProgram]
  have renamed := renameProgram_counts (labelFn L.core.poolWire) (pointMeasuredSquareCandidate L)
  have old := pointMeasuredSquareCandidate_counts L hw
  exact ⟨renamed.1.trans old.1,renamed.2.trans old.2⟩

theorem residents_length (L : ControlledPointLayout) (hw : L.Widths) : (residents L).length=521 := by
  simp only [residents,PointAddLayout.pointWires,inPlaceFlags,List.length_append,List.length_cons,
    List.length_nil,show L.point.x.length=256 from hw.inputX,
    show L.point.y.length=256 from hw.inputY]

/-- The actual square fits the shared candidate inventory. Cardinality is
bounded by the1899 explicit sites; no whole-point allocation claim is made. -/
theorem shared_support_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (residents L++sharedPool L).length=1899 ∧
    wires (computableProgram L)⊆(residents L++sharedPool L).toFinset ∧
    qubitCount (computableProgram L) ≤ 1899 := by
  have length : (residents L++sharedPool L).length=1899 := by
    rw [List.length_append,residents_length L hw,sharedPool_length]
  have support := computable_support L hw hn
  refine ⟨length,support,?_⟩
  change (wires (computableProgram L)).card ≤ 1899
  calc
    _ ≤ (residents L++sharedPool L).toFinset.card := Finset.card_le_card support
    _ ≤ (residents L++sharedPool L).length := List.toFinset_card_le _
    _ = 1899 := length

end ECDSAAdd.Arithmetic.CompressedPointSquare
#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.state_eq
#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.correct
#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.counts
#print axioms ECDSAAdd.Arithmetic.CompressedPointSquare.shared_support_sites
