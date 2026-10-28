import ECDSAAdd.Arithmetic.RecordedRailDeferPrefixLayout

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailDefer

theorem initial_prefix (a b bank : List Wire) (cin even odd : Wire)
    (original : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : Ready32 a b bank cin even odd original) :
    let s := runWithTape (segment a b bank cin even odd 0) m cursor ⟨phase,original⟩
    s.phase=phase ∧ PrefixState a b bank cin even odd original s 1 := by
  obtain ⟨aw,bw,bankWidth,nd,clean,evenZero,oddZero⟩ := ready
  have al : RecordedRailVented.Aligned (chunk a 0) (chunk b 0) bank := by
    simp [RecordedRailVented.Aligned,chunk_length32 a aw 0 (by decide),
      chunk_length32 b bw 0 (by decide),bankWidth]
  have nd0 : ([cin]++chunk a 0++chunk b 0++bank++[even]).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    have ac := count_take_bound a 32 q
    have bc := count_take_bound b 32 q
    simp only [chunk,Nat.mul_zero,List.drop_zero,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have currentReady : RecordedRailVented.Ready (chunk a 0) (chunk b 0) (some cin) bank even original :=
    ⟨al,nd0,clean,evenZero⟩
  let s := runWithTape (RecordedRailVented.vented (chunk a 0) (chunk b 0) (some cin) bank even)
    m cursor ⟨phase,original⟩
  have result := RecordedRailVented.correct (chunk a 0) (chunk b 0) (some cin) bank even original phase m cursor currentReady
  obtain ⟨hp,ha,wide,low,quotient,hcin,outside,work⟩ := result
  have oddAway : odd∉chunk b 0++[even] := by
    intro hmem
    have h := List.nodup_iff_count.mp nd odd
    have positive := List.count_pos_iff.mpr hmem
    have bc := count_take_bound b 32 odd
    simp only [chunk,Nat.mul_zero,List.drop_zero,List.count_cons,List.count_append,List.count_nil] at h positive
    simp only [beq_self_eq_true,if_true] at h
    omega
  have oddClean : s.basis odd=false := (outside odd oddAway).trans oddZero
  dsimp only
  simp only [segment,if_pos rfl]
  refine ⟨hp,?_,?_,work,oddClean⟩
  · simpa only [PrefixState,chunk,Nat.mul_zero,Nat.mul_one,List.drop_zero,
      RecordedRailRipple.incomingValue] using wide
  · intro q hq
    exact outside q (by simpa only [chunk,Nat.mul_zero,Nat.mul_one,List.drop_zero] using hq)

/-- One actual advance supplies the next prefix invariant and the precise new
original-prefix phase factor. The retired header becomes the clean spare. -/
theorem step_prefix (a b bank : List Wire) (cin even odd old next : Wire)
    (original : BasisState) (s : State) (m : List Bool) (cursor : Nat) (j : Nat)
    (hj : j<7) (ready : Ready32 a b bank cin even odd original)
    (roles : old=even ∧ next=odd ∨ old=odd ∧ next=even)
    (state : PrefixState a b bank cin old next original s j) :
    let out := runWithTape (advance (chunk a j) (chunk b j) bank old next) m cursor s
    out.phase=(s.phase ^^ (m.getD (cursor+31) false && prefixCarry a b cin original (32*j))) ∧
    PrefixState a b bank cin next old original out (j+1) := by
  have internalReady := prepare_prefix a b bank cin even odd old next original s j (by omega) ready roles state
  have result := advance_prefix (a.take (32*j)) (b.take (32*j)) (chunk a j) (chunk b j)
    bank cin old next original s m cursor internalReady
  obtain ⟨hp,wide,outside,work,oldClean⟩ := result
  have aw := chunk_length32 a ready.1 j (by omega)
  have bw := ready.2.1
  rw [aw,show cursor+32-1=cursor+31 from by omega,
    carry_prefix a b cin original j bw (by omega)] at hp
  rw [prefix_chunk a j,prefix_chunk b j] at wide
  rw [prefix_chunk b j] at outside
  dsimp only
  refine ⟨hp,wide,outside,work,oldClean⟩

end ECDSAAdd.Arithmetic.RecordedRailDefer
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.initial_prefix
#print axioms ECDSAAdd.Arithmetic.RecordedRailDefer.step_prefix
