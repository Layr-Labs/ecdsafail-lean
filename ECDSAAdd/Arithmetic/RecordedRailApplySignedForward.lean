import ECDSAAdd.Arithmetic.RecordedRailApplySignedFrame

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.RecordedRailApplySigned

def forward (a b bank : List Wire) (aTop bTop tau even odd : Wire) : RecordedProgram :=
  prepare a aTop bTop tau ++ RecordedRailDefer.forward32 a b bank tau even odd ++ restore a aTop bTop tau

/-- Actual individual donor signed forward word, with its coherent saved tau.
No promise makes tau zero at this boundary. The phase is the prepared-word
Defer debt, and the exact full-width unsigned formula states its signed choice. -/
theorem forward_contract (a b bank mirrorBank : List Wire) (aTop bTop tau even odd : Wire)
    (original : BasisState) (phase : Bool) (m : List Bool) (cursor : Nat)
    (ready : RecordedRailApply.Ready a b bank mirrorBank tau even odd original)
    (haTop : aTop∈a) (bt : bTop∈b) (zero : original tau=false) :
    let pb := preparedBits a aTop bTop tau original
    let out := runWithTape (forward a b bank aTop bTop tau even odd) m cursor ⟨phase,original⟩
    out.phase=(phase ^^ RecordedRailDefer.debt32 a b tau pb m cursor) ∧
    regValue b out.basis=(regValue a pb+regValue b original+(signValue aTop bTop tau original).toNat)%2^256 ∧
    (∀q∈a,out.basis q=original q) ∧
    out.basis tau=(original bTop ^^ out.basis bTop) ∧
    (∀q,q∉a → q∉b → q≠tau → out.basis q=original q) := by
  have layout := ready.1
  obtain ⟨aw,bw,fw,mw,nd,smallND,subset⟩ := layout
  obtain ⟨bND,tauAway,sourceAway,bankAway⟩ := RecordedRailApply.data_separation a b mirrorBank tau nd
  have parts := List.nodup_append'.mp nd
  have data := List.nodup_append'.mp parts.1
  have left := List.nodup_append'.mp data.1
  have aND := left.2.1
  have ht : tau∉a := by
    intro h
    exact List.disjoint_left.mp left.2.2 (by simp) h
  have hat : aTop≠tau := by intro he; exact ht (he ▸ haTop)
  have hbt : bTop≠tau := by intro he; exact tauAway (he ▸ bt)
  have bta : bTop∉a := by intro h; exact sourceAway bTop h bt
  let pb := preparedBits a aTop bTop tau original
  have protectedBank : ∀q∈mirrorBank,q≠tau ∧ q∉a := by
    intro q hq
    refine ⟨?_,?_⟩
    · intro he
      exact List.disjoint_left.mp parts.2.2 (by simp [he]) hq
    · intro ha
      exact List.disjoint_left.mp parts.2.2 (by simp [ha]) hq
  have pbclean : ∀q∈mirrorBank,pb q=false := by
    intro q hq
    obtain ⟨hqt,hqa⟩ := protectedBank q hq
    simp only [pb,preparedBits,if_neg hqt,if_neg hqa]
    exact ready.2 q hq
  have preparedReady : RecordedRailApply.Ready a b bank mirrorBank tau even odd pb := ⟨ready.1,pbclean⟩
  have fwdReady := RecordedRailApply.forward_ready a b bank mirrorBank tau even odd pb preparedReady
  let f := runWithTape (RecordedRailDefer.forward32 a b bank tau even odd) m cursor ⟨phase,pb⟩
  have fwd := RecordedRailDefer.correct32 a b bank tau even odd pb phase m cursor fwdReady
  obtain ⟨hp,hvalue,houtside,hbank,heven,hodd⟩ := fwd
  have fsource : ∀q∈a,f.basis q=(original q ^^ signValue aTop bTop tau original) := by
    intro q hq
    rw [houtside q (sourceAway q hq)]
    have hqt : q≠tau := by intro he; exact ht (he ▸ hq)
    simp [pb,preparedBits,hqt,hq]
  have ftau : f.basis tau=signValue aTop bTop tau original := by
    rw [houtside tau tauAway]
    simp [pb,preparedBits]
  have bOrig : regValue b pb=regValue b original := by
    apply regValue_congr
    intro q hq
    have hqt : q≠tau := by intro he; exact tauAway (he ▸ hq)
    have hqa : q∉a := fun ha => sourceAway q ha hq
    simp [pb,preparedBits,hqt,hqa]
  have post := restore_after_word a aTop bTop tau aND ht haTop bta hbt original f zero fsource ftau m (cursor+254)
  let out := runWithTape (restore a aTop bTop tau) m (cursor+254) f
  obtain ⟨postPhase,postSource,postTau,postOutside⟩ := post
  have targetSame : ∀q∈b,out.basis q=f.basis q := by
    intro q hq
    exact postOutside q (fun ha => sourceAway q ha hq) (by intro he; exact tauAway (he ▸ hq))
  have targetValue : regValue b out.basis=regValue b f.basis := regValue_congr b out.basis f.basis targetSame
  have counts := RecordedRailDefer.forward32_counts a b bank tau even odd aw bw fw
  have hrun : runWithTape (forward a b bank aTop bTop tau even odd) m cursor ⟨phase,original⟩=out := by
    rw [forward,runWithTape_append,runWithTape_append]
    simp only [recordedMeasurementCount_append,(zero_measurements a aTop bTop tau).1,counts.2,
      Nat.add_zero,Nat.zero_add]
    rw [prepare_state a aTop bTop tau aND ht hat hbt]
  dsimp only
  rw [hrun]
  refine ⟨postPhase.trans hp,?_,postSource,?_,?_⟩
  · rw [targetValue,hvalue,bOrig]
    simp only [RecordedRailRipple.incomingValue,pb,preparedBits,if_pos rfl,if_true]
  · rw [postTau,targetSame bTop bt]
  · intro q hqa hqb hqt
    rw [postOutside q hqa hqt,houtside q hqb]
    simp [pb,preparedBits,hqa,hqt]

end ECDSAAdd.Arithmetic.RecordedRailApplySigned
#print axioms ECDSAAdd.Arithmetic.RecordedRailApplySigned.forward_contract
