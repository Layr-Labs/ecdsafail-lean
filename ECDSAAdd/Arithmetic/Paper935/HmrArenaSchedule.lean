import ECDSAAdd.Arithmetic.Paper935.HmrRowMulSpec

namespace ECDSAAdd.Arithmetic.Paper935

/-- Ownership of a pool for an entire caller lifecycle. Reservation is at the
lease boundary, not again at each use of the already-owned pool or output. -/
structure HmrArenaLease (A B : Arena) (pool : List Wire) (P : RecordedProgram) : Prop where
  reserved : A.borrowMany 24=some (B,pool)
  support : recordedWires P⊆B.live

/-- A full lifecycle's proved cleanup suffices to return exactly the original
arena. This theorem does not assume a release or readiness postcondition. -/
theorem HmrArenaLease.release (A B : Arena) (pool : List Wire) (P : RecordedProgram)
    (lease : HmrArenaLease A B pool P) (s : State) (tape : List Bool) (cursor : Nat)
    (ready : A.Ready s.basis)
    (clean : ∀q∈pool,(runWithTape P tape cursor s).basis q=false) :
    B.release pool.toFinset (runWithTape P tape cursor s).basis=some A ∧
    A.Ready (runWithTape P tape cursor s).basis ∧ B.live.card=A.live.card+24 := by
  have hc := A.borrowMany_contract B 24 pool lease.reserved
  have live := (A.borrowMany_live B 24 pool lease.reserved).1
  have disjoint := ((A.reserve_success pool.toFinset).mp ⟨B,hc.2.2⟩).2
  have owned : pool.toFinset⊆B.live := by rw [live]; exact Finset.subset_union_right
  have zero : ∀q∈pool.toFinset,(runWithTape P tape cursor s).basis q=false := by
    simpa only [List.mem_toFinset] using clean
  have difference : B.live\pool.toFinset=A.live := by
    rw [live]
    ext q
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨ha|hp,hn⟩
      · exact ha
      · exact False.elim (hn hp)
    · intro ha
      exact ⟨Or.inl ha,fun hp => Finset.disjoint_left.mp disjoint ha hp⟩
  have released : B.release pool.toFinset (runWithTape P tape cursor s).basis=some A := by
    unfold Arena.release
    rw [if_pos ⟨owned,zero⟩]
    congr 1
    cases A
    simp only [Arena.mk.injEq]
    exact difference
  have during := (A.reserve_ready B pool.toFinset s.basis ready hc.2.2).1
  have after : B.Ready (runWithTape P tape cursor s).basis := by
    intro q hq hn
    rw [runWithTape_preserves_outside P tape cursor s q (fun h => hn (lease.support h))]
    exact during q hq hn
  exact ⟨released,B.release_ready A _ _ after released,
    (A.borrowMany_live B 24 pool lease.reserved).2⟩

/-- s2 retains its lease through the intervening HMR/correction segment and
unpark. Cleanup is supplied by the unpark producer, not by early lift cleanup. -/
theorem hmr_s2_release (L : HmrRowMulLayout) (H K U : RecordedProgram)
    (spec : HmrRowUnparkSpec L U) (A B : Arena)
    (lease : HmrArenaLease A B L.anc (H++K++U))
    (call : FusedCall) (original s : State) (tape : List Bool) (cursor : Nat)
    (ready : A.Ready s.basis)
    (unparkInput : spec.pre call original tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    B.release L.anc.toFinset (runWithTape (H++K++U) tape cursor s).basis=some A ∧
    A.Ready (runWithTape (H++K++U) tape cursor s).basis ∧ B.live.card=A.live.card+24 := by
  apply lease.release A B L.anc (H++K++U) s tape cursor ready
  intro q hq
  rw [runWithTape_append]
  exact (spec.run call original _ tape _ unparkInput).2.2.2.1 q
    (Finset.mem_union_left _ (List.mem_toFinset.mpr hq))

/-- s6 keeps the same pool live across apply, corrections and erase. Only the
inverse-call cleanup authorizes release; no second reservation of anc or out. -/
theorem hmr_s6_release (L : HmrRowMulLayout) (H K R : RecordedProgram)
    (spec : HmrRowMulInvSpec L R) (A B : Arena)
    (lease : HmrArenaLease A B L.anc (H++K++R))
    (call : FusedCall) (original s : State) (tape : List Bool) (cursor : Nat)
    (ready : A.Ready s.basis)
    (eraseInput : spec.pre call original tape (cursor+recordedMeasurementCount (H++K))
      (runWithTape (H++K) tape cursor s)) :
    B.release L.anc.toFinset (runWithTape (H++K++R) tape cursor s).basis=some A ∧
    A.Ready (runWithTape (H++K++R) tape cursor s).basis ∧ B.live.card=A.live.card+24 := by
  apply lease.release A B L.anc (H++K++R) s tape cursor ready
  intro q hq
  rw [runWithTape_append]
  exact (spec.run call original _ tape _ eraseInput).2.2.2.1 q
    (Finset.mem_union_left _ (List.mem_toFinset.mpr hq))

/-- The intervening caller segment changes ownership from the s2 boundary to
the s6 boundary. Its precondition and readiness proof are a separate producer
obligation, not inferred from equal capacities or numerical row values. -/
structure HmrArenaTransfer (A C : Arena) (J : RecordedProgram) where
  pre : List Bool → Nat → State → Prop
  ready : ∀tape cursor s,pre tape cursor s → A.Ready s.basis →
    C.Ready (runWithTape J tape cursor s).basis

/-- Two leases cover the three row-multiply invocations: s2 forward followed
by unpark, then s6 apply/erase sharing one retained lease. The intermediate
states and absolute tape cursors are computed from the actual concatenation. -/
theorem hmr_three_call_schedule
    (L2 L6 : HmrRowMulLayout) (H2 K2 U2 J H6 K6 R6 : RecordedProgram)
    (unpark : HmrRowUnparkSpec L2 U2) (erase : HmrRowMulInvSpec L6 R6)
    (A2 B2 A6 B6 : Arena)
    (lease2 : HmrArenaLease A2 B2 L2.anc (H2++K2++U2))
    (lease6 : HmrArenaLease A6 B6 L6.anc (H6++K6++R6))
    (transfer : HmrArenaTransfer A2 A6 J)
    (call2 call6 : FusedCall) (original2 original6 s : State)
    (tape : List Bool) (cursor : Nat) (ready : A2.Ready s.basis)
    (unparkInput : unpark.pre call2 original2 tape
      (cursor+recordedMeasurementCount (H2++K2)) (runWithTape (H2++K2) tape cursor s))
    (transferInput : transfer.pre tape (cursor+recordedMeasurementCount (H2++K2++U2))
      (runWithTape (H2++K2++U2) tape cursor s))
    (eraseInput : erase.pre call6 original6 tape
      (cursor+recordedMeasurementCount ((H2++K2++U2)++J)+recordedMeasurementCount (H6++K6))
      (runWithTape (H6++K6) tape (cursor+recordedMeasurementCount ((H2++K2++U2)++J))
        (runWithTape ((H2++K2++U2)++J) tape cursor s))) :
    B2.release L2.anc.toFinset (runWithTape (H2++K2++U2) tape cursor s).basis=some A2 ∧
    B6.release L6.anc.toFinset
      (runWithTape (((H2++K2++U2)++J)++(H6++K6++R6)) tape cursor s).basis=some A6 ∧
    A6.Ready (runWithTape (((H2++K2++U2)++J)++(H6++K6++R6)) tape cursor s).basis ∧
    B2.live.card=A2.live.card+24 ∧ B6.live.card=A6.live.card+24 := by
  have first := hmr_s2_release L2 H2 K2 U2 unpark A2 B2 lease2 call2 original2 s
    tape cursor ready unparkInput
  have next : A6.Ready (runWithTape ((H2++K2++U2)++J) tape cursor s).basis := by
    rw [runWithTape_append]
    exact transfer.ready tape _ _ transferInput first.2.1
  have last := hmr_s6_release L6 H6 K6 R6 erase A6 B6 lease6 call6 original6
    (runWithTape ((H2++K2++U2)++J) tape cursor s) tape
    (cursor+recordedMeasurementCount ((H2++K2++U2)++J)) next eraseInput
  rw [runWithTape_append ((H2++K2++U2)++J) (H6++K6++R6) tape cursor s]
  exact ⟨first.1,last.1,last.2.1,first.2.2,last.2.2⟩

end ECDSAAdd.Arithmetic.Paper935
