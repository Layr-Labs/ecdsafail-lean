import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeStair44PointMap486a9e3
import ECDSAAdd.Submission.Entrant.PrizeTail10d9efffc
import ECDSAAdd.Submission.Entrant.PrizeTail2024ba497
import ECDSAAdd.Submission.Entrant.PrizeTail227303371
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires measurementCount Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

abbrev Z1 : Program :=
  renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8)

abbrev Z2 : Program := renameProgram (sig 507) (W.ReverseCarry.compactReceiverTick base 507)

abbrev Y : Program :=
  (renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++
      W.ReverseCarry.compactReceiverTick base 510) ++
    renameProgram (sig 509) (W.ReverseCarry.compactReceiverTick base 509)) ++
    renameProgram (sig 508) (W.ReverseCarry.compactReceiverTick base 508)

theorem stage_after (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (k : Nat) (hk : 1 + k ≤ 512) (m : List Bool) :
    Rolling1588.Integer.Stage base false x p (1 + k)
      (run (Rolling1588.Integer.regularForward base false 1 k) m s1).basis := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32 ≤ 2^256 := by norm_num [p]
  exact ((Rolling1588.Integer.regularForward_spec base false base_pool_nodup StackOB5.historyAbove
    x p 1 k hp0 hx0 hpo hp gap hx cop hk) s1 m (Rolling1588.Integer.stage_one base false x p s1 first)).2

abbrev Q2 : Program := renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)

theorem run_congr_append (A A' B : Program) (s : State)
    (h : ∀ r, run A r s = run A' r s) (hc : measurementCount A = measurementCount A')
    (r : List Bool) : run (A ++ B) r s = run (A' ++ B) r s := by
  rw [run_append, run_append, hc, h]

theorem cZ : measurementCount Z1 = measurementCount Y := by
  decide +kernel

theorem agree_split (u s1 : State) (M : List Bool) (A B : Program)
    (h : Rolling1588.Integer.regularForward base false 1 510 = A ++ B)
    (hu : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run (Rolling1588.Integer.regularForward base false 1 510) M s1).basis q) :
    ∀ q ∈ skywalkPoolWires base, u.basis q =
      (run B (M.drop (measurementCount A)) (run A (M.take (measurementCount A)) s1)).basis q := by
  intro q hq
  rw [hu q hq, h, run_append]

abbrev Q1 : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFour15.candidate15)

theorem PE2 :
    renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFour15.old15) =
      Z1 ++ Z2 := by
  rw [InverseFour15.unpack51015]
  simp only [Z1, Z2, InverseFour15.same50715, InverseFour15.old15, Six505.rename_append,
    List.append_assoc]

theorem cQ : measurementCount Q1 = measurementCount (Y ++ Z2) := by
  decide +kernel

theorem split507 : Rolling1588.Integer.regularForward base false 1 510 =
    Rolling1588.Integer.regularForward base false 1 506 ++
      ((MorningFour.tick507 ++ tripF) ++ Rolling1588.Integer.packAfter base false 510) := by
  rw [Rolling1588.Integer.regularForward_snoc base false 1 509,show (1:Nat)+509=510 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 508,show (1:Nat)+508=509 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 507,show (1:Nat)+507=508 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 506,show (1:Nat)+506=507 by rfl,
    MorningPlacement.pack507,Rolling1588.Integer.pack508,Rolling1588.Integer.pack509,
    MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
  simp only [tripF,List.append_assoc,List.append_nil]

abbrev P1 : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)

theorem PE1 :
    renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ TerminalFivePlacement.old) =
      Q1 ++ Q2 := by
  rw [Six505.rename_append, TerminalFivePlacement.old_placed]
  simp only [Q1, Q2, Six505.rename_append, List.append_assoc]
  rfl

theorem split506 : Rolling1588.Integer.regularForward base false 1 510 =
    Rolling1588.Integer.regularForward base false 1 505 ++
      (TerminalFiveBridge.forward ++ Rolling1588.Integer.packAfter base false 510) := by
  rw [Rolling1588.Integer.regularForward_snoc base false 1 509,show (1:Nat)+509=510 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 508,show (1:Nat)+508=509 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 507,show (1:Nat)+507=508 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 506,show (1:Nat)+506=507 by rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 505,show (1:Nat)+505=506 by rfl,
    InverseFive23.pack506,MorningPlacement.pack507,Rolling1588.Integer.pack508,
    Rolling1588.Integer.pack509,
    MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
  simp only [TerminalFiveBridge.forward,tripF,List.append_assoc,List.append_nil]

theorem split508 : Rolling1588.Integer.regularForward base false 1 510 =
    Rolling1588.Integer.regularForward base false 1 507 ++
      (((W.repairedTick base 508 ++ W.repairedTick base 509) ++ W.repairedTick base 510) ++
        Rolling1588.Integer.packAfter base false 510) := by
  rw [Rolling1588.Integer.regularForward_snoc base false 1 509,show (1:Nat)+509=510 from rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 508,show (1:Nat)+508=509 from rfl,
    Rolling1588.Integer.regularForward_snoc base false 1 507,show (1:Nat)+507=508 from rfl,
    Rolling1588.Integer.pack508 false,Rolling1588.Integer.pack509 false]
  simp only [List.append_assoc,List.append_nil]

theorem PE4 : (Y ++ Z2) ++ Q2 = Rolling1588.Integer.reverse false 506 5 := by
  decide +kernel

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.Stair44HostedCut
open ECDSAAdd Arithmetic StairField13V3 StairConcreteAssembly
set_option maxRecDepth 30000
attribute [local irreducible] run wires

private theorem takeCuts (pre : State → Prop) (j : Nat) :
    ∀ ps : List Piece, ∀ X : Program, Cuts pre X ps → Cuts pre X (ps.take j) := by
  induction j with
  | zero => intro ps X _; trivial
  | succ j ih =>
    intro ps X hc
    cases ps with
    | nil => trivial
    | cons p ps => exact ⟨hc.1,hc.2.1,ih ps (X ++ p.L) hc.2.2⟩

theorem runPrefix (pre : State → Prop) (ps : List Piece) (j : Nat)
    (loc : ∀ p∈ps,p.Local)
    (cuts : ∀ i (hi : i<ps.length),
      CutClean pre (((ps.take i).map Piece.L).flatten) (ps[i]).moved ∧
      CutClean pre (((ps.take (i+1)).map Piece.L).flatten) (ps[i]).moved)
    (s : State) (hs : pre s) (m : List Bool) :
    run (((ps.take j).map Piece.H).flatten) m s=run (((ps.take j).map Piece.L).flatten) m s := by
  have all := cuts_of_index pre ps [] (fun i hi => by simpa only [List.nil_append] using cuts i hi)
  exact run_eq_of_cuts pre (ps.take j) [] (fun pc h => loc pc (List.mem_of_mem_take h))
    (takeCuts pre j ps [] all) s hs m

theorem entry (j : Nat) (s : State) (hs : EntryPre s) (m : List Bool) :
    let ps := entryPieces checkpointPrimitives hostPlan
    run (((ps.take j).map Piece.H).flatten) m s=run (((ps.take j).map Piece.L).flatten) m s := by
  have c := StairField13V3Clean.entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760
  have cuts := entrySlotsClean_of _ _ _ (entrySlots_of_v3 (entrySlotsV3_of_parts
    (StairField13V3Fresh.entryParts_of_clean c)))
  exact runPrefix _ _ _ (entryPieces_local _ _) cuts s hs m

theorem exit (k j : Nat) (s : State) (hs : ExitPre k s) (m : List Bool) :
    let ps := exitPieces checkpointPrimitives hostPlan k
    run (((ps.take j).map Piece.H).flatten) m s=run (((ps.take j).map Piece.L).flatten) m s := by
  have c := StairField13V3Clean.exitClean_of_planR StairOpenWiring.exitPlans StairOpenWiring.half760 k
  have cuts := exitSlotsClean_of _ _ _ _ (exitSlots_of_v3 k (exitSlotsV3_of_parts k
    (StairField13V3Fresh.exitParts_of_clean k c)))
  exact runPrefix _ _ _ (exitPieces_local _ _ k) cuts s hs m

end ECDSAAdd.Entrant.Stair44HostedCut

end

section

namespace ECDSAAdd.Entrant.Stair44OuterX
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement Baselines
  ParityXEntry FlagEntry ParityEven Stair44PointMap
set_option maxRecDepth 30000
set_option maxHeartbeats 1800000
attribute [local irreducible] run wires layout pmapR
def cleanIndex (i : Nat) : Prop := i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722

private theorem pool (i : Nat) (hi : cleanIndex i) : pmapR layout (base i) ∈ layout.dialogPool := by
  apply pmap_pool _ layout_widths layout_nodup
  · exact List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by unfold cleanIndex at hi; omega))
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold cleanIndex at hi
    omega
  · intro e; have := base_injective e; unfold cleanIndex at hi; omega

private def exitIndices : List Nat := [1542,1541,721,722,500,501,502,503,504,514]

private theorem direct (s : State) (m : List Bool) (X : Nat) (hx : regValue layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue layout.dialogPool s.basis=0) (i : Nat) (hi : i∈exitIndices) :
    (run (E1QubitPlacement.tickF layout) m s).basis (pmapR layout (base i)) = false := by
  let f := pmapR layout
  let t := pullState f s
  have cl (j : Nat) (hj : cleanIndex j) : t.basis (base j) = false :=
    (regValue_zero _ _).mp hc _ (pool j hj)
  have blk (a n : Nat) (h : a+n ≤ 515 ∨ (1026 ≤ a ∧ a+n ≤ 1285) ∨ (1540≤a ∧ a+n≤1798)) :
      regValue (wireBlock base a n) t.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact cl j (by unfold cleanIndex; omega)
  have Hx : regValue (wireBlock base 770 256) t.basis = X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (f q)) = X
    rw [regValue_pull,pmap_x layout layout_widths layout_nodup,hx]
  have kv : regValue (E1Merge.kR base) t.basis = X := by
    rw [E1Merge.kR_x base base_pool_nodup, show E1Merge.xR base=wireBlock base 770 256 from rfl,
      Hx,blk 1026 2 (by decide)]
    simp
  have seed : LiteralSkywalkSeedValues (literalSkywalkPoolSeed base) 0 X t.basis :=
    ⟨blk 0 258 (by decide), kv, blk 1540 257 (by decide), cl 1797 (by unfold cleanIndex; decide),
      cl 1028 (by unfold cleanIndex; decide),cl 1797 (by unfold cleanIndex; decide)⟩
  have range : cleanIndex i := by simp [exitIndices] at hi; unfold cleanIndex; omega
  have isS : base i∈S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i
    (by unfold cleanIndex at range; omega))
  have phys := run_rename_pool f S (pmap_inj _ layout_widths layout_nodup) _
    forward_S m t s rfl (fun _ _ => rfl)
  rw [E1QubitPlacement.tickF,phys.2 _ isS]
  have out := NativeFirstDirect.forward_spec base base_pool_nodup X hX t m seed
  have cold : base i∉NativeFirstDirect.mutable base :=
    (by decide +kernel : ∀ i ∈ exitIndices,base i∉NativeFirstDirect.mutable base) i hi
  exact (out.2.2.2.2.2 _ cold).trans (cl i range)

theorem tickZero (s : State) (m : List Bool) (X : Nat) (hx : regValue layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue layout.dialogPool s.basis=0) :
    ∀q∈firstClean,(run (E1QubitPlacement.tickF layout) m s).basis q=false := by
  have tab : ∀ q∈firstClean, ∃i∈exitIndices, pmapR layout (base i)=q := by decide +kernel
  intro q hq
  obtain ⟨i,hi,rfl⟩ := tab q hq
  exact direct s m X hx hX hc i hi

private theorem afterAdd (k : Fp) (s : State) (m : List Bool) (X : Fp)
    (hx : regValue layout.point.x s.basis=X.val) (hc : regValue layout.dialogPool s.basis=0)
    (i : Nat) (hi : i∈exitIndices) :
    (run (entryM layout k) m s).basis (pmapR layout (base i)) = false := by
  rw [entry_eq layout layout_widths layout_nodup k s X.val X.isLt _ hx rfl hc m m,run_append]
  let cmd := fastConstAdd layout layout.point.x k
  let s1 := run cmd (m.take (measurementCount cmd)) s
  have facts := fastConstAdd_correct layout layout_widths layout_nodup layout.point.x (Or.inl rfl)
    k X.val _ X.isLt s (m.take (measurementCount cmd)) rfl hx hc
  have fresh : regValue layout.dialogPool s1.basis=0 := by
    exact (regValue_congr _ _ _ (fun q hq => facts.2.2 q
      ((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).1)).trans hc
  apply direct s1 _ _ facts.2.1 _ fresh i hi
  exact Nat.mod_lt _ (by decide)

theorem stockExit (X k : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hc : regValue layout.dialogPool s.basis=0) :
    ∀ q∈firstClean, (run (entryXNew layout (pkW layout) k) m
      (put s (pkW layout) (if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+k.val) else false))).basis q=false := by
  rw [entryXNew_run layout layout_widths layout_nodup _ X k s hx hc (pk_pool layout layout_widths)
    (pk_ne_flag layout layout_widths layout_nodup) (pk_ne_high layout layout_widths layout_nodup)
    (pk_ne_x layout layout_widths layout_nodup) (by rw [pmap_g layout layout_widths layout_nodup]; decide +kernel),
    entryXAll_eq layout layout_widths layout_nodup X k s _ hx hc]
  have mapTable : ∀ q∈firstClean, ∃i∈exitIndices, pmapR layout (base i)=q := by decide +kernel
  intro q hq
  obtain ⟨i,hi,rfl⟩ := mapTable q hq
  exact afterAdd k s _ X hx hc i hi

theorem execute (X k : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hc : regValue layout.dialogPool s.basis=0) :
    let P := entryXNew layout (pkW layout) k
    let logical := put s (pkW layout)
      (if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+k.val) else false)
    run (switchX P) m (pullState outer.symm logical) = pullState integerFirst.symm (run P m logical) := by
  intro P logical
  have prep : ∀q∈([4836,4629]:List Wire), logical.basis q=false := by
    have table : ∀q∈([4836,4629]:List Wire),q∈layout.dialogPool ∧ q≠pkW layout := by decide +kernel
    intro q hq
    have ⟨member,notFlag⟩ := table q hq
    change (put s (pkW layout) _).basis q = false
    simpa [put,writeBit,Function.update_apply,notFlag] using (regValue_zero _ _).mp hc q member
  have full (e : Equiv.Perm Wire) (a : State) : pullState e (pullState e.symm a) = a := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg a.basis (e.symm_apply_apply q)
  rw [at_x_input logical prep, ← at_x_output _ (stockExit X k s m hx hc)]
  have r := run_rename duringX duringX.injective P m (pullState duringX.symm logical)
  rw [full] at r
  have e := congrArg (pullState duringX.symm) r
  have back (a : State) : pullState duringX.symm (pullState duringX a)=a := by
    simpa only [Equiv.symm_symm] using full duringX.symm a
  rw [back] at e
  exact e

end ECDSAAdd.Entrant.Stair44OuterX

end

section

namespace ECDSAAdd.Entrant.Stair44WalkCuts
open Arithmetic MappedCompressed Stair44WalkMap
set_option maxRecDepth 8000
attribute [local irreducible] run wires Rolling1588TickGap.forward Rolling1588.Integer.regularForward

theorem release (s : State) (hp : ∀q∈Stair44WalkExit.atExit,s.basis q=false)
    (h : s.basis (base 514)=false) : pullState rest s=s := by
  have a := cleanWireRebind id s s _ _ rfl (hp _ (by decide : base 1026∈Stair44WalkExit.atExit)) h
  have b := cleanWireRebind _ s s _ _ a (hp _ (by decide : base 1541∈Stair44WalkExit.atExit))
    (hp _ (by decide : base (Placement5.H 1)∈Stair44WalkExit.atExit))
  exact cleanWireRebind _ s s _ _ b (hp _ (by decide : base 1542∈Stair44WalkExit.atExit))
    (hp _ (by decide : base (Placement5.H 0)∈Stair44WalkExit.atExit))

private theorem cancel (e : Equiv.Perm Wire) {s t : State}
    (h : pullState e s = pullState e t) : s=t := by
  apply State.extensionality
  · have r := congrArg State.phase h
    exact r
  · funext q; simpa only [pullState, Equiv.apply_symm_apply] using congrFun (congrArg State.basis h) (e.symm q)

theorem forward_done (d : Bool) (a x : Nat) (atCut : 1+(15+a) ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s actual : State) (m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 1 s.basis) (input : pullState first actual=s) :
    run (Stair44WalkRun.forward d a) m actual = run (Rolling1588TickGap.forward d 1 (15+a)) m s := by
  let n := 15+a
  have bounds : 1+n ≤ 506 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut; dsimp [n]; omega
  let stock := run (Rolling1588TickGap.forward d 1 n) m s
  let raw := run (Rolling1588.Integer.regularForward base d 1 n) m s
  have zero : pullState (OB5.sig 0) s=s := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg s.basis (OB5.sig_zero q)
  have eqn := Rolling1588TickGap.forward_gen d x hx0 hx n 1 (by decide) (by omega) s m hs
  rw [show 1-1=0 by decide,zero] at eqn
  have eq' : stock = pullState (OB5.sig (1+n-1)) raw := eqn
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have stage := (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p
    1 n hp0 hx0 hpo hp (by norm_num [p]) hx cop (by omega) s m hs).2
  have flags : ∀q∈Stair44WalkExit.atExit,stock.basis q=false := by
    rw [eq']
    exact Stair44WalkExit.ready d _ x p atCut hp0 hpo raw stage
  have bit := run_preserves_outside _ m s _ (Stair44WalkSites.idle514 d 1 n (by decide) bounds).1
  have fixed := release stock flags (bit.trans (Stair44WalkExit.first_ready d x p s hs 514 (by decide)))
  have out := Stair44WalkRun.forward_run d a x hx0 hx s actual m hs input
  change pullState rest _ = stock at out
  rw [←fixed] at out
  exact cancel rest out

end ECDSAAdd.Entrant.Stair44WalkCuts

end

section

namespace ECDSAAdd.Entrant.StairArchiveNativeRows
open CodecBitSliceVerify StairArchiveGates
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 100000

def chronological (high : Bool) := (List.range 10).map
  (fun q => get integer_load0Trace0In ((if high then 10 else 0)+q))

/-- The literal incumbent's complete encoding program acts on the unmodified chronological
G/S pairs. The byte uses the same eight physical slots for both A and B. -/
theorem stock_code (isA high : Bool) :
    eval ones (Rolling1588.codeEncode isA) (chronological high) = (true, storage (native isA high)) := by
  cases isA <;> cases high <;> decide +kernel

end ECDSAAdd.Entrant.StairArchiveNativeRows

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
attribute [local irreducible] run routed measurementCount body
namespace NativePack240
open ArchiveBoundary240
def fourHoles : List Wire := [1276,1278,1281,1283]
theorem blank_slots : ∀q∈fourHoles,∃i:Fin 157,16 ≤ i.val ∧ codePorts i=q := by decide +kernel
theorem cleared_holes (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^136)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    ∀q∈fourHoles,(run (nextWindow d) m s).basis q=false := by
  let pre:=run Partial.enter240 m s
  let tape:=m.drop (measurementCount Partial.enter240)
  let T:=Shadow.reduced 136 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 136 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter240.ready_pending raw s z G S m small cut input hist 
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have final:=archive_result d row limit _ _ frame
  intro q hq
  obtain ⟨i,hi,slot⟩:=blank_slots q hq
  have absent:∀q∈fourHoles,¬MayTouch idx (windowNet idx q):=by decide +kernel
  rw [nextWindow,run_append,run_take]
  exact after_encoded idx (withArchive d) codePorts d row pre tape final i hi q slot (absent q hq)
end NativePack240
namespace NativePack255
open ArchiveBoundary255
def fourHoles : List Wire := [1291,1293,1296,1298]
theorem blank_slots : ∀q∈fourHoles,∃i:Fin 157,16 ≤ i.val ∧ codePorts i=q := by decide +kernel
theorem cleared_holes (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^129)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    ∀q∈fourHoles,(run (nextWindow d) m s).basis q=false := by
  let pre:=run Partial.enter255 m s
  let tape:=m.drop (measurementCount Partial.enter255)
  let T:=Shadow.reduced 129 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 129 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter255.ready_pending raw s z G S m small cut input hist endScratch
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have final:=archive_result d row limit _ _ frame
  intro q hq
  obtain ⟨i,hi,slot⟩:=blank_slots q hq
  have absent:∀q∈fourHoles,¬MayTouch idx (windowNet idx q):=by decide +kernel
  rw [nextWindow,run_append,run_take]
  exact after_encoded idx (withArchive d) codePorts d row pre tape final i hi q slot (absent q hq)
end NativePack255
namespace NativePack270
open ArchiveBoundary270
def fourHoles : List Wire := [1807,1805,1802,1800]
theorem blank_slots : ∀q∈fourHoles,∃i:Fin 157,16 ≤ i.val ∧ codePorts i=q := by decide +kernel
theorem cleared_holes (d:Bool) (row:Nat) (s:State) (frame:Frame codePorts (code d) row s) :
    ∀q∈fourHoles,s.basis q=false := by
  intro q hq
  obtain ⟨i,hi,rfl⟩:=blank_slots q hq
  rw [frame,archive_blank d i hi,Nat.zero_testBit]
end NativePack270
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.WideReference
open Arithmetic MappedCompressed
attribute [local irreducible] run W.compactSkywalkTick

theorem pastOffSpan (i n q:Nat) (bound:i+n≤512) (early:Earlier i q) : q∉wires (span i n) := by
  induction n generalizing i with
  | zero => simp [span,wires]
  | succ n ih =>
    rw [span,wires_append,Finset.mem_union]
    rintro (head|tail)
    · have sub:=W.compactSkywalkTick_support base i (by omega) base_pool_nodup
      exact away (by omega) early (List.mem_toFinset.mp (sub head))
    · exact ih (i+1) (by omega) (earlier_mono (by omega) early) tail

theorem preservePast (i n x p r:Nat) (bound:i+n≤512) (good:Bounds x p) (raw:State)
    (dom:Domain i x p raw) (rOld:r < i) (m:List Bool) :
    let out:=run (span i n) m raw
    out.basis (base r)=raw.basis (base r) ∧ out.basis (base (1028+r))=raw.basis (base (1028+r)) := by
  by_cases old:r+2 ≤ i
  · exact ⟨run_preserves_outside _ _ _ _ (pastOffSpan _ _ _ bound ⟨r,old,Or.inl rfl⟩),
      run_preserves_outside _ _ _ _ (pastOffSpan _ _ _ bound ⟨r,old,Or.inr rfl⟩)⟩
  obtain ⟨ref,same,stage⟩:=dom
  have h1:¬Earlier i (base r) := by
    rintro ⟨k,prev,h|h⟩ <;> simp only [base,Wire] at * <;> omega
  have h2:¬Earlier i (base (1028+r)) := by
    rintro ⟨k,prev,h|h⟩ <;> simp only [base,Wire] at * <;> omega
  have link:=fixed_span i i n (Nat.le_refl _) bound raw ref m same
  have endStage:=full_span i n x p bound good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime ref m stage
  have before:=(W.compactSkywalkStage_fields_iff base _ i (by omega) base_pool_nodup _).mp stage
  have after:=(W.compactSkywalkStage_fields_iff base _ (i+n) bound base_pool_nodup _).mp endStage
  have a:=before.2.2.2.1 r rOld
  have b:=after.2.2.2.1 r (by omega)
  exact ⟨(link.2 _ h1).trans (b.1.trans (a.1.symm.trans (same.2 _ h1).symm)),
    (link.2 _ h2).trans (b.2.trans (a.2.symm.trans (same.2 _ h2).symm))⟩

theorem endRaw_inside (i:Nat) (raw history:State) (fix:Fixed i) (q:Wire) (member:q∈sites i) :
    (endRaw i raw history).basis q=history.basis q := by
  change (origin i raw history).basis (OB5.sig (i+14) q)=_
  rw [fix q member,inside _ _ _ q member]

theorem endRaw_outside (i:Nat) (bound:i+14≤511) (raw history:State) (fix:Fixed i) (q:Wire) (off:q∉sites i) :
    (endRaw i raw history).basis q=(run (span i 15) [] raw).basis q := by
  have invol:=OB5.sig_invol (i+14) bound q
  have out:OB5.sig (i+14) q∉sites i:=by
    intro h
    have eq:=fix _ h
    rw [invol] at eq
    exact off (eq.symm ▸ h)
  change (origin i raw history).basis (OB5.sig (i+14) q)=_
  rw [outside _ _ _ _ out,invol]

end ECDSAAdd.Entrant.StairPacket.WideReference

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3200000
attribute [local irreducible] run body measurementCount leave225 leave225Inv NativePack225.firstWindow NativePack225.firstUnwind

theorem pinned225 (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool) (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    let s:=pullState (OB5.sig 224) raw
    let v:=run (NativePack225.firstWindow d) m s
    ∃a b c e,At240 d x p (endRaw 225 raw v) (run leave225 n v) a b c e := by
  let s:=pullState (OB5.sig 224) raw
  let v:=run (NativePack225.firstWindow d) m s
  let out:=run leave225 n v
  let raw':=endRaw 225 raw v
  obtain ⟨g,sg,input,h,cut,facts⟩:=NativePack225.stock_endpoint d x p good raw m n stage
  let flags:=Leave225Admission.flags (unsigned 225 x p) g sg
  have dom:=initial 225 x p (by decide) d raw stage
  have carried:=stepInput 225 144 x p (by decide) (by decide) fixed225 good raw v g sg dom input h.small
  exact ⟨flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,unique_input input (fixed_input 225 x p (by decide) good raw dom)⟩
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed ArchivePortAction ArchiveStockRows
set_option maxRecDepth 30000
set_option maxHeartbeats 3300000
attribute [local irreducible] run body measurementCount leave240 leave240Inv NativePack240.nextWindow NativePack240.nextUnwind

theorem pinned240 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m n:List Bool) (pre:At240 d x p raw s g sg pg ps) :
    let v:=run (NativePack240.nextWindow d) m s
    ∃a b c e,At255 d x p (endRaw 240 raw v) (run leave240 n v) a b c e := by
  let v:=run (NativePack240.nextWindow d) m s
  let out:=run leave240 n v
  let raw':=endRaw 240 raw v
  let flags:=Leave240Admission.flags (unsigned 240 x p) g sg
  have curr:=readInput 240 x p raw g sg pre.input
  have native:=NativePack240.from_domain_matched d x p good raw s m pre.domain g sg pre.cut curr pg ps _ pre.facts
  obtain ⟨h,cut,facts⟩:=NativePack240.stock_endpoint d x p good raw s m n pre.domain g sg pre.cut curr pg ps _ pre.facts
  have carried:=stepInput 240 136 x p (by decide) (by decide) fixed240 good raw v g sg pre.domain pre.input h.small
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology 225 x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  have accepted:Saved 225 x p ArchiveBoundary240.codePorts d out:=by
    refine ⟨row,bound,chr,ArchiveWindowPreserve.keep kept ?_⟩
    intro q hq
    exact ArchiveWindowPreserve.after240 v n q hq
  have same:=unique_input pre.input (fixed_input _ _ _ (by decide) good raw pre.domain)
  exact ⟨flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,same,accepted⟩
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic IntegerPacket WideReference SkywalkRails Partial MappedCompressed ArchivePortAction ArchiveStockRows
set_option maxRecDepth 30000
set_option maxHeartbeats 3300000
attribute [local irreducible] run body measurementCount leave255 leave255Inv NativePack255.nextWindow NativePack255.nextUnwind

theorem pinned255 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m n:List Bool) (pre:At255 d x p raw s g sg pg ps) :
    let v:=run (NativePack255.nextWindow d) m s
    ∃a b c e,At270 d x p (endRaw 255 raw v) (run leave255 n v) a b c e := by
  let v:=run (NativePack255.nextWindow d) m s
  let out:=run leave255 n v
  let raw':=endRaw 255 raw v
  let flags:=Leave255Admission.flags (unsigned 255 x p) g sg
  have curr:=readInput 255 x p raw g sg pre.input
  have native:=NativePack255.from_domain_matched d x p good raw s m pre.domain g sg pre.cut curr pg ps _ pre.facts
  obtain ⟨h,cut,facts⟩:=NativePack255.stock_endpoint d x p good raw s m n pre.domain g sg pre.cut curr pg ps _ pre.facts
  have carried:=stepInput 255 129 x p (by decide) (by decide) fixed255 good raw v g sg pre.domain pre.input h.small
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology 240 x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  have accepted:Saved 240 x p ArchiveBoundary255.codePorts d out:=by
    refine ⟨row,bound,chr,ArchiveWindowPreserve.keep kept ?_⟩
    intro q hq
    exact ArchiveWindowPreserve.after255 v n q (List.mem_append.mpr (Or.inr hq))
  have same:=unique_input pre.input (fixed_input _ _ _ (by decide) good raw pre.domain)
  have older:Saved 225 x p ArchiveBoundary240.codePorts d out:=by
    obtain ⟨r,lim,yes,old⟩:=pre.saved225
    refine ⟨r,lim,yes,ArchiveWindowPreserve.keep old ?_⟩
    intro q hq
    exact (ArchiveWindowPreserve.after255 v n q (List.mem_append.mpr (Or.inl hq))).trans
      (ArchiveWindowPreserve.entering255 d s m q hq)
  exact ⟨flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts.1,facts.2.1,facts.2.2.1,facts.2.2.2,same,older,accepted⟩
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockCanonicalRow
open Arithmetic ArchivePortAction SkywalkRails IntegerPacket StairArchiveRaw CodecBitSliceVerify StairArchiveTrace
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

def key (b:Nat) (z:SkywalkNat.State) (cross:Bool) (trace:List (Bool×Bool)) (q:Nat):Bool:=
  let f:=decide (Shadow.far b 15 z)
  rawBit (read (trace.drop 5)) f (f && afterFlags (decide (z.v<z.u)) (trace.take 5)) (f && cross) q

def Encodes (v:Nat→Bool) (r:Nat):Prop:=∀q:Fin 23,(rawCol q).testBit r=v q
noncomputable def select (v:Nat→Bool):Nat:=by
  classical
  exact if h:∃r<63145,Encodes v r then h.choose else 0
theorem select_spec {v} (h:∃r<63145,Encodes v r):select v<63145 ∧ Encodes v (select v):=by
  classical
  simpa only [select,dif_pos h] using h.choose_spec

theorem frame_key (j:Fin 23) (ps:Ports) (chron:∀i:Fin 20,ps ⟨i,by omega⟩=nativeRawPort j i)
    (r:Nat) (b:Nat) (z:SkywalkNat.State) (g sg cross:Bool) (before out:State)
    (prior:PastFacts j ps b z g sg cross before)
    (kept:∀i:Fin 23,out.basis (ps ⟨i,by omega⟩)=before.basis (ps ⟨i,by omega⟩))
    (frame:Frame ps raw r out):
    Encodes (key b z cross (SkywalkTrace.trace 15 (encode g sg z.u z.v))) r:=by
  intro q
  have same:(rawCol q).testBit r=before.basis (ps ⟨q,by omega⟩):=
    ((congrArg (fun n:Nat=>n.testBit r) (io true true ⟨q,by omega⟩).1).trans (frame ⟨q,by omega⟩).symm).trans (kept q)
  by_cases h:q.val<20
  · have eq:=row_truth j ps chron r z g sg before out prior.records kept frame ⟨q,h⟩
    simpa only [key,rawBit,if_pos h] using eq
  · rcases q with ⟨q,bound⟩
    change ¬q<20 at h
    have cases:q=20 ∨ q=21 ∨ q=22:=by omega
    rcases cases with rfl|rfl|rfl
    · exact same.trans prior.far
    · simpa only [←prior.records] using same.trans prior.suffix
    · exact same.trans prior.crossed

theorem reframe {v r} (limit:r<63145) (eq:Encodes v r) (ps:Ports) (out:State)
    (frame:Frame ps raw r out):Frame ps raw (select v) out:=by
  have ⟨_,selected⟩:=select_spec ⟨r,limit,eq⟩
  intro i
  rw [frame i]
  by_cases old:i.val<23
  · have read:get raw i=rawCol i:=(io true true i).1.symm
    rw [read,eq ⟨i,old⟩,selected ⟨i,old⟩]
  · have empty:get raw i=0:=(blank true true i (by omega)).1
    rw [empty,Nat.zero_testBit,Nat.zero_testBit]
end ECDSAAdd.Entrant.StairPacket.StockCanonicalRow

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockDelayed
open Arithmetic MappedCompressed WideReference Rolling1588.Integer Secp256k1
attribute [local irreducible] run W.compactSkywalkTick
def packs (d:Bool) (i:Nat):Nat→Program
  | 0=>[]
  | n+1=>packAfter base d i ++ packs d (i+1) n

private theorem off (d:Bool) (k i n:Nat) (lo:k < i) (hi:i+n≤512):
    Disjoint (wires (packAfter base d k)) (wires (span i n)):=by
  induction n generalizing i with
  | zero=>simp [span,wires]
  | succ n ih=>
    have offPre:=prefix_disjoint_tick base d base_pool_nodup (k+1) i lo (by omega)
    rw [encodePrefix,wires_append] at offPre
    have step:=Disjoint.mono_left (Finset.subset_union_right (s₁:=wires (encodePrefix base d k))) offPre
    have tail:=ih (i+1) (by omega) (by omega)
    rw [span,wires_append,Finset.disjoint_union_right];exact ⟨step,tail⟩

theorem deferred (d:Bool) (i n:Nat) (hi:i+n≤512) (s:State):
    run (compactForward base d i n) [] s=run (packs d i n) [] (run (span i n) [] s):=by
  induction n generalizing i s with
  | zero=>simp only [compactForward,packs,span,run]
  | succ n ih=>
    simp only [compactForward,packs,span,run_append,run_take,List.drop_nil]
    rw [ih (i+1) (by omega),run_disjoint_commute _ _ (off d i (i+1) n (by omega) (by omega))]

theorem window (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (i n:Nat) (lo:0 < i) (hi:i+n≤512)
    (s:State) (m:List Bool) (stage:Stage base d x p i s.basis):
    run (Rolling1588TickGap.forward d i n) m (pullState (OB5.sig (i-1)) s)=
      pullState (OB5.sig (i+n-1)) (run (packs d i n) [] (run (span i n) [] s)):=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x hx0 hx
  rw [Rolling1588TickGap.forward_gen d x hx0 hx n i lo hi s m stage,
    regularForward_eq base d base_pool_nodup StackOB5.historyAbove x p hp0 hx0 odd cap
      (by norm_num [p]) hx cop n i hi s m [] stage,deferred d i n hi]
end ECDSAAdd.Entrant.StairPacket.StockDelayed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open WindowFieldMask WindowFieldCosts ArchiveFieldScratch StairArchiveInactive
attribute [local irreducible] run measurementCount StairArchiveInactive.packet fieldHook
def joinTapes (P : Program) (m n : List Bool) : List Bool :=
  (m++List.replicate (measurementCount P) false).take (measurementCount P) ++ n
theorem joined (P Q : Program) (m n : List Bool) (s : State) :
    run (P++Q) (joinTapes P m n) s=run Q n (run P m s) := by
  let padded := (m++List.replicate (measurementCount P) false).take (measurementCount P)
  have len : padded.length = measurementCount P := by simp [padded]
  rw [run_append]
  change run Q ((padded++n).drop _) (run P ((padded++n).take _) s)=_
  rw [←len,List.take_left,List.drop_left]
  exact congrArg (run Q n) (TrimSquare.run_padTake P m _ s rfl)
def referenceLeg (d : Bool) : Leg→ Program
  | .native j n => group d j n
  | .paired j => first j (!d) ++ second j (!d)
def legTape (d : Bool) (m : List Bool) : Leg → List Bool
  | .native _ _ => m
  | .paired j => joinTapes (first j (!d)) (tapeA j (!d) m) (tapeB j (!d) m)
theorem localTape (d : Bool) (m : List Bool) (s : State) (l : Leg) :
    stock d m s l = run (referenceLeg d l) (legTape d m l) s := by
  cases l with
  | native j n => rfl
  | paired j => exact (joined _ _ _ _ _).symm
def referenceProgram (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => referenceLeg d l ++ referenceProgram d ls
def referenceTape (d : Bool) : List Leg → List Bool → List Bool
  | [],_ => []
  | l::ls,m => joinTapes (referenceLeg d l) (legTape d m l) (referenceTape d ls (nextTape d l m))
theorem ref_run (d : Bool) (ls : List Leg) (m : List Bool) (r : State) :
    destination d ls m r = run (referenceProgram d ls) (referenceTape d ls m) r := by
  induction ls generalizing m r with
  | nil => simp only [destination,referenceProgram,referenceTape,run]
  | cons l ls ih => rw [destination,referenceProgram,referenceTape,joined,←localTape,←ih]

set_option maxRecDepth 8000
set_option maxHeartbeats 900000
private theorem shape' (d : Bool) (p : Nat→Program) : PacketSequence.program d p 1 84 =
  let seq := PacketSequence.program d p
  if d then seq 1 45 ++ ((p 46 ++ p 47) ++ (seq 48 1 ++ ((p 49 ++ p 50) ++ (seq 51 1 ++ ((p 52 ++ p 53) ++ (seq 54 31 ++ []))))))
  else seq 54 31 ++ ((p 53 ++ p 52) ++ (seq 51 1 ++ ((p 50 ++ p 49) ++ (seq 48 1 ++ ((p 47 ++ p 46) ++ (seq 1 45 ++ [])))))) := by
  cases d <;> simp [PacketSequence.program,List.append_assoc]
theorem reference_eq (d : Bool) : referenceProgram d (plan d)=group d 1 84 := by
  simp only [group, distribute, distributed]
  rw [shape' d (packet d)]
  cases d <;> simp only [referenceProgram,plan,referenceLeg,first,second,group,distribute,distributed,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false]
end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
abbrev Hops := List (Wire×Wire)
/-- Each step adds previous carry times a control into a borrowed bit.
The identical gate on exit restores its original value. -/
def chain (src last target : Wire) : Hops→Program
  | [] => [.CCX src last target]
  | (c,b)::xs => [.CCX src c b] ++ chain b last target xs ++ [.CCX src c b]
def mcx (a b src last t : Wire) (xs : Hops) :=
  chain src last t xs ++ ([Instr.CCX a b src] ++ (chain src last t xs ++ [Instr.CCX a b src]))
inductive Aff where
  | x (dst : Wire)
  | cx (src dst : Wire)
  deriving DecidableEq
def gate : Aff→Instr
  | .x w => .X w
  | .cx c w => .CX c w
def affine (p : List Aff) := p.map gate
structure Clause where
  prep : List Aff
  a : Wire
  b : Wire
  last : Wire
  xs : Hops

def guarded (labels neg : List Wire) (pivot : Option Wire) : Clause :=
  let ph := match pivot with
    | none => []
    | some z => ((List.range 16).erase z).map (fun i=>Aff.cx i z)
  let mid := (labels.drop 2).dropLast
  ⟨ph++neg.map Aff.x,labels[0]!,labels[1]!,labels.getLast!, mid.zipIdx.map (fun ⟨c,i⟩=>(c,18+i))⟩

def clauses : List Clause :=
  [guarded [0,1,2,3,4,5] [4] (some 5),
   guarded [0,3,4,5,6,7,1] [] (some 1),
   guarded [0,8,9,10,11,12,1] [0,12] (some 1),
   guarded [0,1,2,3,4,12] [4,12] none,
   guarded [0,8,9,10,11,12] [0,12] none,
   guarded (List.range 16) (List.range' 4 12) none,
   guarded (List.range 16) (List.range 8++List.range' 12 4) none]

def body (c : Clause) := affine c.prep ++ (mcx c.a c.b 17 c.last 16 c.xs ++ affine c.prep.reverse)
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed WindowParityDirty
def region : Program := clauses.flatMap ECDSAAdd.Entrant.StairPacket.WindowParityDirty.body
def site (j i : Nat) := OB5.sig 511 (NewHistory5.payloadWire base (8*j+i))
def other (j : Nat) := if j=46 then 49 else 46
def port (j q : Nat) : Wire :=
  if q<16 then site j q else if q=16 then FrontierEntry1591Field.host else site (other j) (q-17)
def bankCorrection (j : Nat) := renameProgram (port j) region
def correction := bankCorrection 46 ++ (bankCorrection 49 ++ bankCorrection 52)
def setup := StairSchedule.paritySetup ++ correction
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires measurementCount Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

theorem key510 (x : Nat) (hx0 : 0 < x) (hx : x < p) (a u : State)
    (stage : Rolling1588.Integer.Stage base false x p 508 a.basis) (r2 : List Bool)
    (hu : ∀ q ∈ skywalkPoolWires base, u.basis q =
      (run (((W.repairedTick base 508 ++ W.repairedTick base 509) ++ W.repairedTick base 510) ++
        Rolling1588.Integer.packAfter base false 510) r2 a).basis q)
    (r : List Bool) :
    run Z1 r (pullState (sig 510) u) = run Y r (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32 ≤ 2^256 := by norm_num [p]
  have pool : ∀ q∈sitesT8,q∈(skywalkPoolWires base).toFinset :=
    fun q hq => List.mem_toFinset.mpr (sitesT8_pool q hq)
  have dec : wires (Rolling1588.Integer.decodeBefore base false 510)⊆(skywalkPoolWires base).toFinset := by
    have d := (History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←Rolling1588.Integer.decodeBefore_support_eq base false 510] at d
    exact d
  have hB : wires (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8)⊆(skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,fun q hq => pool q (List.mem_toFinset.mp (tickMR8_wires hq))⟩
  have u10 := Rolling1588.Integer.untick_pool base false base_pool_nodup 510 (by omega)
  have u9 := Rolling1588.Integer.untick_pool base false base_pool_nodup 509 (by omega)
  rw [Rolling1588.Integer.decode509 false,List.nil_append] at u9
  have u8 := Rolling1588.Integer.untick_pool base false base_pool_nodup 508 (by omega)
  rw [Rolling1588.Integer.decode508 false,List.nil_append] at u8
  have hO : wires (Rolling1588.Integer.decodeBefore base false 510 ++ ((W.ReverseCarry.compactReceiverTick base 510 ++
      W.ReverseCarry.compactReceiverTick base 509) ++
      W.ReverseCarry.compactReceiverTick base 508))⊆(skywalkPoolWires base).toFinset := by
    rw [←List.append_assoc,←List.append_assoc,wires_append,wires_append,Finset.union_subset_iff,
      Finset.union_subset_iff]
    exact ⟨⟨u10,u9⟩,u8⟩
  have inner (r : List Bool) :
      run (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8) r u=
        run (Rolling1588.Integer.decodeBefore base false 510 ++ ((W.ReverseCarry.compactReceiverTick base 510 ++
          W.ReverseCarry.compactReceiverTick base 509) ++
          W.ReverseCarry.compactReceiverTick base 508)) r u :=
    Stack5.local_replace _ _ _ hB hO u _ r r
      (fun q hq => hu q (List.mem_toFinset.mp hq))
      (Rolling1588.Integer.blockN_eq_new false x hx0 hx a stage r2 r)
  have s9 := (Rolling1588.Integer.step_spec base false base_pool_nodup StackOB5.historyAbove x p 508 hp0 hx0 hpo hp hgap hx
    cop (by omega) a [] stage).2
  simp only [Rolling1588.Integer.pack508 false,List.append_nil] at s9
  obtain ⟨b8,hb8⟩ : ∃ b8 : State,run (W.repairedTick base 508) [] a=b8 := ⟨_,rfl⟩
  rw [hb8] at s9
  have s10 := (Rolling1588.Integer.step_spec base false base_pool_nodup StackOB5.historyAbove x p 509 hp0 hx0 hpo hp hgap hx
    cop (by omega) b8 [] s9).2
  simp only [Rolling1588.Integer.pack509 false,List.append_nil] at s10
  obtain ⟨b9,hb9⟩ : ∃ b9 : State,run (W.repairedTick base 509) [] b8=b9 := ⟨_,rfl⟩
  rw [hb9] at s10
  have rawE : run (((W.repairedTick base 508 ++ W.repairedTick base 509) ++ W.repairedTick base 510) ++
      Rolling1588.Integer.packAfter base false 510) [] a=
        run (W.repairedTick base 510 ++ Rolling1588.Integer.packAfter base false 510) [] b9 := by
    rw [←hb9,←hb8]
    simp only [List.append_assoc,run_append,List.take_nil,List.drop_nil]
  have hu' : ∀ q∈skywalkPoolWires base,
      u.basis q=(run (W.repairedTick base 510 ++ Rolling1588.Integer.packAfter base false 510) [] b9).basis q := by
    intro q hq
    rw [hu q hq,←rawE]
    exact congrFun (run_basis_records _ a a r2 [] rfl) q
  have z10 := Rolling1588.Integer.stage_zero false x 510 (by omega) b9.basis s10
  have z9 := Rolling1588.Integer.stage_zero false x 509 (by omega) b8.basis s9
  have c9 := Rolling1588.Integer.stage_zero_gen false x 508 509 (by omega) (by omega) a.basis stage
  have c10 := Rolling1588.Integer.stage_zero_gen false x 508 510 (by omega) (by omega) a.basis stage
  have rt10 (r1 : List Bool) := Rolling1588.Integer.oneStep_roundtrip base false base_pool_nodup x p 510 hp0 hx0 hpo hp hgap hx
    cop (by omega) b9 s10 [] r1
  have rt9 (r1 : List Bool) := Rolling1588.Integer.oneStep_roundtrip base false base_pool_nodup x p 509 hp0 hx0 hpo hp hgap hx
    cop (by omega) b8 s9 [] r1
  simp only [Rolling1588.Integer.decode509 false,Rolling1588.Integer.pack509 false,List.nil_append,List.append_nil,hb9] at rt9
  have rt8 (r1 : List Bool) := Rolling1588.Integer.oneStep_roundtrip base false base_pool_nodup x p 508 hp0 hx0 hpo hp hgap hx
    cop (by omega) a stage [] r1
  simp only [Rolling1588.Integer.decode508 false,Rolling1588.Integer.pack508 false,List.nil_append,List.append_nil,hb8] at rt8
  have rn10 := (renameProgram_counts (sig 510)
    (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510)).2
  have rn9 := (renameProgram_counts (sig 509) (W.ReverseCarry.compactReceiverTick base 509)).2
  show run (renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++ tickMR8)) r (pullState (sig 510) u)=
        run ((renameProgram (sig 510) (Rolling1588.Integer.decodeBefore base false 510 ++
            W.ReverseCarry.compactReceiverTick base 510) ++
          renameProgram (sig 509) (W.ReverseCarry.compactReceiverTick base 509)) ++
          renameProgram (sig 508) (W.ReverseCarry.compactReceiverTick base 508)) r
          (pullState (sig 510) u)
  rw [OB5.run_rename 510 (by omega),inner r]
  have e : Rolling1588.Integer.decodeBefore base false 510 ++ ((W.ReverseCarry.compactReceiverTick base 510 ++
      W.ReverseCarry.compactReceiverTick base 509) ++ W.ReverseCarry.compactReceiverTick base 508)=
      ((Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) ++
        W.ReverseCarry.compactReceiverTick base 509) ++ W.ReverseCarry.compactReceiverTick base 508 := by
    simp only [List.append_assoc]
  rw [e,Rolling1588.Integer.run_append3,Rolling1588.Integer.run_append3,rn10,rn9]
  obtain ⟨r1,hr1⟩ : ∃ r1 : List Bool,r.take (measurementCount (Rolling1588.Integer.decodeBefore base false 510 ++
    W.ReverseCarry.compactReceiverTick base 510))=r1 := ⟨_,rfl⟩
  obtain ⟨r3,hr3⟩ : ∃ r3 : List Bool,(r.drop (measurementCount (Rolling1588.Integer.decodeBefore base false 510 ++
    W.ReverseCarry.compactReceiverTick base 510))).take
      (measurementCount (W.ReverseCarry.compactReceiverTick base 509))=r3 := ⟨_,rfl⟩
  obtain ⟨r5,hr5⟩ : ∃ r5 : List Bool,r.drop (measurementCount (Rolling1588.Integer.decodeBefore base false 510 ++
    W.ReverseCarry.compactReceiverTick base 510)+
      measurementCount (W.ReverseCarry.compactReceiverTick base 509))=r5 := ⟨_,rfl⟩
  rw [hr1,hr3,hr5,OB5.run_rename 510 (by omega)]
  have a1 := OB5.pool_agree _ u10 r1 u _ hu'
  rw [rt10 r1] at a1
  have a2 := OB5.pool_agree _ u9 r3 _ _ a1
  rw [rt9 r3] at a2
  have a3 := OB5.pool_agree _ u8 r5 _ _ a2
  rw [rt8 r5] at a3
  have v1c : (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u).basis
      (base (1028+510))=false :=
    (a1 _ (OB5.base_pool _ (by omega))).trans z10.1
  have v1d : 257 ≤ 510 → (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u).basis
      (base (2053-510))=false :=
    fun big => (a1 _ (OB5.base_pool _ (by omega))).trans (z10.2 big)
  rw [←OB5.pull_step 510 (by omega) _ v1c v1d,OB5.run_rename 509 (by omega)]
  have v2c : (run (W.ReverseCarry.compactReceiverTick base 509) r3
      (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u)).basis
      (base (1028+509))=false :=
    (a2 _ (OB5.base_pool _ (by omega))).trans z9.1
  have v2d : 257 ≤ 509 → (run (W.ReverseCarry.compactReceiverTick base 509) r3
      (run (Rolling1588.Integer.decodeBefore base false 510 ++ W.ReverseCarry.compactReceiverTick base 510) r1 u)).basis
      (base (2053-509))=false :=
    fun big => (a2 _ (OB5.base_pool _ (by omega))).trans (z9.2 big)
  rw [←OB5.pull_step 509 (by omega) _ v2c v2d,OB5.run_rename 508 (by omega)]
  have p9 := OB5.pull_step 509 (by omega) _
    ((a3 _ (OB5.base_pool _ (by omega))).trans c9.1)
    (fun big => (a3 _ (OB5.base_pool _ (by omega))).trans (c9.2 big))
  have p10 := OB5.pull_step 510 (by omega) _
    ((a3 _ (OB5.base_pool _ (by omega))).trans c10.1)
    (fun big => (a3 _ (OB5.base_pool _ (by omega))).trans (c10.2 big))
  exact (p9.trans p10).symm

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.Stair44DivisionCut
open ECDSAAdd Arithmetic MappedCompressed Secp256k1
open StairField13V3 StairConcreteAssembly
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires renameProgram

def beforeClose (pr : StairSchedule.StairPrimitives) (h : StairHostsSchedule.HostPlan) :=
  renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase pr) ++
    StairHostsSchedule.entryFieldHosted pr h

theorem selected (pr : StairSchedule.StairPrimitives) (h : StairHostsSchedule.HostPlan) :
    (((entryPieces pr h).take 24).map Piece.H).flatten = beforeClose pr h := by
  simp only [entryPieces,List.take_succ_cons,List.take_zero,groupSlot,firstSlot,lowCommon,common,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,beforeClose,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.entryLowPrefix,StairHostsSchedule.entryTailPrefix,
    StairHostsSchedule.entryLowSuffix,StairHostsSchedule.entryTailSuffix,fieldRename_append,rename_append,List.append_assoc]

theorem logical (h : StairHostsSchedule.HostPlan) :
    (((entryPieces checkpointPrimitives h).take 24).map Piece.L).flatten =
      StairLoanField7Cores.entrySelectedArithmeticFor StairConcrete.bestLoans := by
  simp only [entryPieces,List.take_succ_cons,List.take_zero,groupSlot,firstSlot,lowCommon,common,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    StairLoanField7Cores.entrySelectedArithmeticFor,StairSchedule.entryFieldHosted,
    StairSchedule.entryLowPrefix,StairSchedule.entryTailPrefix,StairSchedule.entryLowSuffix,
    StairSchedule.entryTailSuffix,fieldRename_append,rename_append,List.append_assoc]

theorem reference {t : State} (F : EntryFrame t) (m : List Bool) :
    run (beforeClose checkpointPrimitives hostPlan) m t =
      run (StairLoanRecordSupport.entryFieldHostedShape StairConcrete.bestLoans) []
        (run (Rolling1588.firstPhase true) [] t) := by
  have bridge := Stair44HostedCut.entry 24 t ⟨F⟩ m
  change run (((entryPieces checkpointPrimitives hostPlan).take 24).map Piece.H).flatten m t =
    run (((entryPieces checkpointPrimitives hostPlan).take 24).map Piece.L).flatten m t at bridge
  rw [selected,logical] at bridge
  have core := StairLoanField7RR.entryCoreR_best StairOpenWiring.half760 StairOpenWiring.entryPlans t ⟨F⟩ m []
  rw [bridge,core,StairLoanField7Cores.entryReferenceArithmeticFor,run_append]
  simp only [List.take_nil,List.drop_nil]
  rw [StairLoanField7Values.first_phase_hosted true F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt
    t [] (StairField13V3Clean.entryInput F)]

theorem pool {t : State} (F : EntryFrame t) (m : List Bool) :
    let z := run (beforeClose checkpointPrimitives hostPlan) m t
    let y := run (Rolling1588.firstPhase false) [] t
    z.phase=y.phase ∧ ∀q∈skywalkPoolWires base,z.basis q=y.basis q := by
  rw [reference F]
  have r := StairLoanRecordKernel.shape_entry_boundary StairOpenWiring.half760 F.sharedNodup F.historyAbove
    F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt F.source t [] [] F.input F.selectorG_zero
    F.selectorS_zero F.phase F.outsideNumerator F.numerator
  refine ⟨r.1,fun q hq => r.2.2 q (FrontierEntry1591Kernel.pool_away_numerator q hq)⟩

end ECDSAAdd.Entrant.Stair44DivisionCut

end

section

namespace ECDSAAdd.Entrant.Stair44MultiplyCut
open Arithmetic MappedCompressed Secp256k1
open StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairField2V3Delta StairField2V3Couple StairField2V3Entry
open StairField2V3ExitPlan StairField2V3ExitPlanR StairField2V3Final
open StairLoanField7Transport StairLoanField7R StairLoanExitReachX
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires renameProgram

def lastRows := (XS21 ++ grpFL StairConcrete.bestLoans 0 1 84) ++ lowTail

private theorem reached (k x : Nat) :
    ∃ Q, CRel (XPreX k x) (RowRelL k x 87 (YFL StairConcrete.bestLoans)) lastRows Q := by
  obtain ⟨Q,h⟩ := rch21 k x (StairOpenWiring.exitPlans k x) StairOpenWiring.half760
  have next := sharedL k x 87 (grpFL StairConcrete.bestLoans 0 1 84) ZE
    (away_of_sub _ _ _ exitGroupSub_best.2.2.2.2.2 (grpF_away 87 (by decide) 1 84 (by decide)))
  exact ⟨_,crel_append (crel_append h next)
    (sharedL k x 87 lowTail (ZE ++ grpFL StairConcrete.bestLoans 0 1 84) low_away)⟩

theorem recover (k x : Nat) (u : State) (hp : ExitMiddleX k x u) (rows unpack : List Bool) :
    let a := run (closeSel cp) unpack (run lastRows rows u)
    ∃ (s1 : State) (enc : List Bool),
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis ∧
      pullState Rolling1588Lifetime.phaseHost a = run (Rolling1588TickGap.forward true 1 424) enc s1 := by
  obtain ⟨Q,h⟩ := reached k x
  obtain ⟨old,rel,ref⟩ := h u u ⟨hp,rfl⟩ rows
  have ordinary := (exitReachTransportR_best StairOpenWiring.half760 k x).f _ ref
  obtain ⟨t0,c,adm,eq⟩ := StairField2V3ExitRecClose.closeRec_of
    StairField2V3JuncSel2.ExtraSel StairField2V3JuncSel2.extraSel_genuine k x _ ordinary
  rw [eq] at rel
  have before := relX_unique x 87 _ _ _ rel (StairField2V3JuncSel2.junc x t0 adm [] c)
  have back := StairField2V3JuncSel2.firstTrip_sel x t0 adm [] unpack
  dsimp only
  rw [before,back]
  exact adm.2.2.2

def beforeClose (h : StairHostsSchedule.HostPlan) :=
  exitReferenceOpening ++ StairHostsSchedule.exitFieldHosted cp h

theorem selected (k : Nat) (h : StairHostsSchedule.HostPlan) :
    (((exitPieces cp h k).take 24).map Piece.H).flatten = beforeClose h := by
  simp only [exitPieces,List.take_succ_cons,List.take_zero,groupSlot,firstSlot,lowCommon,common,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,beforeClose,
    exitReferenceOpening,StairHostsSchedule.exitFieldHosted,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.exitHeadPrefix,StairHostsSchedule.exitLowSuffix,StairHostsSchedule.exitHeadSuffix,
    StairHostsSchedule.hostedEndpoint,fieldRename_append,rename_append,List.append_assoc]

theorem logical (k : Nat) :
    (((exitPieces cp hostPlan k).take 24).map Piece.L).flatten = exitReferenceOpening ++ lastRows := by
  change cut (xps k) 24=_
  rw [cut_succ (xps k) 23 (xL k 23 (by decide)),xcut23]
  change (exitReferenceOpening ++ XS23) ++ StairSchedule.fieldRename (Rolling1588.placedFirstPacket false)=_
  simp only [XS23,lastRows,lowTail,fieldRename_append,List.append_assoc]

theorem pool (k : Nat) {t : State} (F : ExitFrame k t) (m tail : List Bool) :
    let a := run (closeSel cp) tail (run (beforeClose hostPlan) m t)
    ∃ (s1 : State) (enc : List Bool),
      W.CompactSkywalkStage base (SkywalkRails.encode false false (F.x:Int) (p:Int)) 1 s1.basis ∧
      pullState Rolling1588Lifetime.phaseHost a = run (Rolling1588TickGap.forward true 1 424) enc s1 := by
  have bridge := Stair44HostedCut.exit k 24 t ⟨F⟩ m
  change run (((exitPieces cp hostPlan k).take 24).map Piece.H).flatten m t =
    run (((exitPieces cp hostPlan k).take 24).map Piece.L).flatten m t at bridge
  rw [selected,logical,run_append exitReferenceOpening lastRows] at bridge
  dsimp only
  rw [bridge]
  exact recover k F.x _ ⟨t,F,rfl,_,rfl⟩ _ tail
end ECDSAAdd.Entrant.Stair44MultiplyCut

end

section

namespace ECDSAAdd.Entrant.Stair44PlacedHead
open Arithmetic MappedCompressed Secp256k1 Baselines ControlledPointLayout CompressedPointDialog
  CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry ParityUniform ParityEven Stair44PointMap
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
attribute [local irreducible] run measurementCount

def plain (kx ky : Fp) := entryYAll layout ky ++ entryXNew layout (pkW layout) kx
def routed (kx ky : Fp) := encodeY (entryYAll layout ky) ++ switchX (entryXNew layout (pkW layout) kx)

theorem unpull (f : Equiv.Perm Wire) (s : State) : pullState f.symm (pullState f s)=s := by
  apply State.extensionality
  · rfl
  · funext q; exact congrArg s.basis (f.apply_symm_apply q)

theorem encoded_head (X Y kx ky : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hy : regValue layout.point.y s.basis=Y.val)
    (clean : regValue layout.dialogPool s.basis=0) :
    let flag := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+kx.val) else false
    let initial := put s (pkW layout) flag
    run (routed kx ky) m (pullState outer.symm initial)=pullState integerFirst.symm (run (plain kx ky) m initial) := by
  intro flag initial
  let YP := entryYAll layout ky
  let tape := m.take (measurementCount YP)
  let sY := run (fusedY layout ky) tape s
  have fy := fusedY_correct layout layout_widths layout_nodup Y ky s tape hy clean
  have same (q : Wire) (hq : q∉layout.point.y) : sY.basis q=s.basis q := fy.2.2 q hq
  have xc : regValue layout.point.x sY.basis=X.val :=
    (regValue_congr _ _ s.basis (fun q hq => same q ((E1QubitPlacement.lay layout layout_widths layout_nodup q).1 hq))).trans hx
  have pc : regValue layout.dialogPool sY.basis=0 :=
    (regValue_congr _ _ s.basis (fun q hq => same q (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2))).trans clean
  have gc := same _ (((E1QubitPlacement.lay layout layout_widths layout_nodup _).2.2 rfl).2)
  have yactual := Stair44OuterY.entry Y ky s (pullState outer.symm initial) tape flag hy clean
    (unpull outer.symm initial)
  have ystock : run YP tape initial=put sY (pkW layout) flag := by
    rw [show YP=entryYAll layout ky from rfl, show initial=put s (pkW layout) flag from rfl,
      run_put _ _ _ _ _ (pk_not_Y layout layout_widths layout_nodup _ (by decide +kernel)),
      entryYAll_eq layout layout_widths layout_nodup Y ky s tape hy clean]
  have ey := congrArg (pullState outer.symm) yactual
  rw [unpull,ystock] at ey
  have ex := Stair44OuterX.execute X kx sY (m.drop (measurementCount YP)) xc pc
  dsimp only at ex
  rw [gc] at ex
  rw [routed,plain,run_append,run_append,show measurementCount (encodeY YP)=measurementCount YP from
    (renameProgram_counts _ _).2]
  change run _ _ (run (encodeY YP) tape _) = pullState integerFirst.symm (run _ _ (run YP tape initial))
  rw [ey,ystock]
  exact ex

theorem cleanInteger (s : State) (hc : regValue layout.dialogPool s.basis=0) : pullState integerFirst s=s := by
  let pairs : List (Wire × Wire) := [(4835,4615),(4837,4616),(4836,4629)]
  have members : ∀ab∈pairs,ab.1∈layout.dialogPool ∧ ab.2∈layout.dialogPool := by decide +kernel
  apply (clean_chain pairs id s s (fun ab hab => ⟨(regValue_zero _ _).mp hc _ (members ab hab).1,
    (regValue_zero _ _).mp hc _ (members ab hab).2⟩)).mpr
  rfl

theorem encodedTick (s : State) (m : List Bool) (hc : regValue layout.dialogPool s.basis=0) :
    run (renameProgram integerFirst (E1QubitPlacement.tickF layout)) m s=
    pullState integerFirst.symm (run (E1QubitPlacement.tickF layout) m s) := by
  have e := congrArg (pullState integerFirst.symm)
    (run_rename integerFirst integerFirst.injective (E1QubitPlacement.tickF layout) m s)
  rw [unpull,cleanInteger s hc] at e
  exact e

end ECDSAAdd.Entrant.Stair44PlacedHead

end

section

namespace ECDSAAdd.Entrant.Stair44WalkCuts
open Arithmetic MappedCompressed Stair44WalkMap
set_option maxRecDepth 8000
attribute [local irreducible] run wires Rolling1588.reverse Rolling1588TickGap.forward
  Rolling1588.Integer.regularForward Rolling1588.Integer.regularReverse measurementCount
  Rolling1588.Integer.reverse Stair44WalkRun.backward

theorem early514 (d : Bool) (x p : Nat) (s : State)
    (hs : Rolling1588.Integer.Stage base d x p 16 s.basis) : s.basis (base 514)=false := by
  obtain ⟨raw,hraw,bits⟩ := hs
  rw [congrFun bits _, Rolling1588.Integer.encodePrefix_index base d 3]
  have far : base 514 ∉ wires (Rolling1588.allEncode base d 3) := by
    intro used
    have h := List.mem_toFinset.mp (Rolling1588.allEncode_history_support base d 3 (by decide) used)
    rcases List.mem_append.mp h with a|a
    all_goals obtain ⟨t,ht,et⟩ := List.mem_map.mp a
    all_goals have r := List.mem_range'_1.mp ht
    all_goals have e := Nat.add_right_cancel et
    all_goals omega
  rw [run_preserves_outside _ [] raw _ far]
  have exp := (W.compactSkywalkStage_fields_iff base _ 16 (by decide) base_pool_nodup raw.basis).mp hraw
  exact (exp.2.2.2.2.1 256 (by decide) (by decide)).1

theorem backward_start (d : Bool) (a x : Nat) (atCut : 16+a ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s v : State) (enc m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 16 s.basis)
    (agree : ∀q ∈ skywalkPoolWires base,v.basis q=(run (Rolling1588.Integer.regularForward base d 16 a) enc s).basis q) :
    let t := pullState (OB5.sig (16+a-1)) v
    pullState first (run (Stair44WalkRun.backward d a) m t) = run (Rolling1588.reverse d 1 (15+a)) m t := by
  let i := 16+a
  have bound : 16+a ≤ 506 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut; omega
  let raw := run (Rolling1588.Integer.regularForward base d 16 a) enc s
  let t := pullState (OB5.sig (i-1)) v
  let ref := pullState (OB5.sig (i-1)) raw
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have stage := (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p
    16 a hp0 hx0 hpo hp (by norm_num [p]) hx cop (by omega) s enc hs).2
  have flags := Stair44WalkExit.ready d i x p atCut hp0 hpo raw stage
  have inpool : ∀ j∈[425,505,506], ∀ q∈base 514 :: Stair44WalkExit.atExit,
      OB5.sig (j-1) q ∈ skywalkPoolWires base := by decide +kernel
  have same (q : Wire) (hq : q∈base 514 :: Stair44WalkExit.atExit) : t.basis q=ref.basis q :=
    agree _ (inpool _ atCut _ hq)
  have stock := Rolling1588TickGap.forward_gen d x hx0 hx a 16 (by decide) (by omega) s enc hs
  have eqn : run (Rolling1588TickGap.forward d 16 a) enc (pullState (OB5.sig 15) s) = ref := stock
  have bit := run_preserves_outside _ enc (pullState (OB5.sig 15) s) _ (Stair44WalkSites.idle514 d 16 a (by decide) bound).1
  rw [eqn] at bit
  have sig : OB5.sig 15 (base 514)=base 514 := by decide
  have t514 : t.basis (base 514)=false := (same _ (List.mem_cons_self)).trans (bit.trans (by simpa only [pullState,sig] using early514 d x p s hs))
  have fix := release t (fun q hq => (same q (List.mem_cons_of_mem _ hq)).trans (flags q hq)) t514
  exact Stair44WalkRun.backward_run d a x (by omega) hx0 hx s v t enc m hs agree fix

private theorem fsplit (d : Bool) (i n m : Nat) :
    Rolling1588.Integer.regularForward base d i (n+m) =
    Rolling1588.Integer.regularForward base d i n ++ Rolling1588.Integer.regularForward base d (i+n) m := by
  induction n generalizing i with
  | zero => simp [Rolling1588.Integer.regularForward]
  | succ n ih =>
    simp only [Nat.succ_add,Rolling1588.Integer.regularForward,List.append_assoc]
    rw [ih]
    rw [show i+(n+1)=i+1+n by omega]

theorem start16 (d : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (enc : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 1 s.basis) :
    Rolling1588.Integer.Stage base d x p 16 (run (Rolling1588.Integer.regularForward base d 1 15) enc s).basis := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  exact (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p
    1 15 hp0 hx0 hpo hp (by norm_num [p]) hx cop (by decide) s enc hs).2

theorem decompose (d : Bool) (i n a : Nat) (s : State) (enc : List Bool) :
    let pr := Rolling1588.Integer.regularForward base d i n
    let late := Rolling1588.Integer.regularForward base d (i+n) a
    run (Rolling1588.Integer.regularForward base d i (n+a)) enc s =
      run late (enc.drop (measurementCount pr)) (run pr (enc.take (measurementCount pr)) s) := by
  rw [fsplit d i n a]
  exact run_append _ _ _ _

theorem restore_raw (d : Bool) (a x : Nat) (atCut : 16+a ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s v : State) (enc m : List Bool)
    (hs : Rolling1588.Integer.Stage base d x p 1 s.basis)
    (agree : ∀q ∈ skywalkPoolWires base,v.basis q=(run (Rolling1588.Integer.regularForward base d 1 (15+a)) enc s).basis q) :
    let t := pullState (OB5.sig (16+a-1)) v
    ∀q∈skywalkPoolWires base,(run (Rolling1588.reverse d 1 (15+a)) m t).basis q=s.basis q := by
  have bound : 1+(15+a)≤512 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut; omega
  have r := Rolling1588.Integer.reverse_gen d x hx0 hx (15+a) 1 (by decide) bound s enc v m hs agree
  rw [Rolling1588.Integer.reverse_eq_packets] at r
  change ∀q∈skywalkPoolWires base,(run (Rolling1588.reverse d 1 (15+a)) m (pullState (OB5.sig (16+a-1)) v)).basis q=s.basis q
  rw [show 16+a-1=1+(15+a)-1 by omega,r.1]
  intro q hq
  change (run _ _ _).basis (OB5.sig 0 q)=_
  rw [OB5.sig_zero]
  exact r.2 q hq

end ECDSAAdd.Entrant.Stair44WalkCuts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveByte
open Arithmetic Rolling1588 StairArchiveRows StairArchiveHandoff StairArchiveNativeRows StairArchiveRaw CodecBitSliceVerify ArchiveFieldScratch
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 100000
private theorem geom (d:Bool):wires (codeEncode d)=Finset.range 10:=by cases d <;> decide +kernel
private theorem cols (hi:Bool):∀q:Fin 10,get (chronological hi) q=rawCol ((if hi then 10 else 0)+q.val):=by
  cases hi <;> decide +kernel
theorem run_byte (d hi:Bool) (row:Nat) (hr:row<63145) (f:Fin 10→Wire) (inj:Function.Injective f)
    (s:State) (m:List Bool)
    (data:∀q:Fin 10,s.basis (f q)=(rawCol ((if hi then 10 else 0)+q.val)).testBit row):
    (run (codeEncodeAt d f) m s).phase=s.phase ∧ ∀q:Fin 10,
      (run (codeEncodeAt d f) m s).basis (f q)=(get (storage (native d hi)) q).testBit row:=by
  let map:=MeasuredCodec5.label f
  let t:=pullState map s
  let x:=value (chronological hi) row
  have rel:Rel (chronological hi) x row:=value_rel _ _
  have checked:=stock_code d hi
  have active:ones.testBit row=true:=by
    rw [ones,Nat.testBit_two_pow_sub_one];exact decide_eq_true hr
  have bounds:∀a∈codeEncode d,target a<(chronological hi).length:=by cases d <;> cases hi <;> decide +kernel
  have eqs(q:Nat)(hq:q∈wires (codeEncode d)):t.basis q=x.testBit q:=by
    have lt:q<10:=Finset.mem_range.mp ((geom d) ▸ hq)
    let i:Fin 10:=⟨q,lt⟩
    have h:map q=f i:=by simp [map,MeasuredCodec5.label,lt,i]
    exact (congrArg s.basis h).trans ((data i).trans ((congrArg (fun n:Nat=>n.testBit row) (cols hi i)).symm.trans (rel q).symm))
  have result:=run_row (codeEncode d) ones row x m t _ _ active bounds rel checked eqs
  have placed:=run_rename_pool map (Finset.range 10) (FirstNonzeroCodec.label_inj' f inj) (codeEncode d)
    (by rw [geom]) m t s rfl (fun _ _=>rfl)
  refine ⟨placed.1.trans result.1,?_⟩
  intro j
  have ge:j.val∈wires (codeEncode d):=(geom d).symm ▸ Finset.mem_range.mpr j.isLt
  have lay:map j.val=f j:=by simp [map,MeasuredCodec5.label,j.isLt]
  exact (congrArg (run (codeEncodeAt d f) m s).basis lay).symm.trans ((placed.2 j.val (Finset.mem_range.mpr j.isLt)).trans (result.2.1 j.val ge))
end ECDSAAdd.Entrant.StairPacket.StockArchiveByte

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveReference
open Arithmetic MappedCompressed WideReference
def ordinary (d:Bool):Program:=
  Rolling1588.encodeAt base d 220 ++ Rolling1588.encodeAt base d 225 ++
  Rolling1588.encodeAt base d 240 ++ Rolling1588.encodeAt base d 255
def starts:List Nat:=[230,235,245,250,260,265]
def holes:List Wire:=starts.flatMap (fun t=>[base (1028+t+2),base (1028+t+4)])
def common (d:Bool) (raw:State):State:=
  pullState (OB5.sig 270) (eraseSites holes (run (ordinary d) [] (run (span 225 46) [] raw)))
end ECDSAAdd.Entrant.StairPacket.StockArchiveReference

end

section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction StairArchiveTrace StockCanonicalRow
attribute [local irreducible] run onRails routed measurementCount body
namespace NativePack240
open ArchiveBoundary240
theorem selected_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^136)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 (PortalValues.negative S z.u)
      (decide (Shadow.far 136 15 z)) (decide (Shadow.far 136 15 z ∧ 2^136≤z.u))
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 240) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+240+r))=false) 
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^144)
    (prior:PastFacts sourceIdx rawPorts 144 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    let v:=key 144 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    select v<63145 ∧ Encodes v (select v) ∧ Kept codePorts d (select v) out:=by
  let pre:=run Partial.enter240 m s
  let tape:=m.drop (measurementCount Partial.enter240)
  let T:=Shadow.reduced 136 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 136 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter240.ready_pending raw s z G S m small cut input hist 
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have held:=bank_kept d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1
  have all:=frame_key sourceIdx rawPorts chronological row 144 past pg ps cross s _ prior held frame
  have spec:=select_spec ⟨row,limit,all⟩
  have final:=receipt d pre tape _ spec.1 (reframe limit all rawPorts _ frame)
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨spec.1,spec.2,final.1⟩
end NativePack240
namespace NativePack255
open ArchiveBoundary255
theorem selected_receipt (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^129)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 (PortalValues.negative S z.u)
      (decide (Shadow.far 129 15 z)) (decide (Shadow.far 129 15 z ∧ 2^129≤z.u))
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 255) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (base (1028+255+r))=false) (endScratch:raw.basis 1812=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^136)
    (prior:PastFacts sourceIdx rawPorts 136 past pg ps cross s) :
    let out:=run (nextWindow d) m s
    let v:=key 136 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    select v<63145 ∧ Encodes v (select v) ∧ Kept codePorts d (select v) out:=by
  let pre:=run Partial.enter255 m s
  let tape:=m.drop (measurementCount Partial.enter255)
  let T:=Shadow.reduced 129 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd 129 z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=Enter255.ready_pending raw s z G S m small cut input hist endScratch
  obtain ⟨_,row,limit,frame⟩:=admits d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1 past pg ps cross po pm prior
  have held:=bank_kept d s m tape (tape.drop (measurementCount (routed idx 0 1))) Z parity ready.2.1
  have all:=frame_key sourceIdx rawPorts chronological row 136 past pg ps cross s _ prior held frame
  have spec:=select_spec ⟨row,limit,all⟩
  have final:=receipt d pre tape _ spec.1 (reframe limit all rawPorts _ frame)
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨spec.1,spec.2,final.1⟩
end NativePack255
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open StockCanonicalRow ArchiveBoundary270 ParkEndpoint Portal270Flag Secp256k1 SkywalkRails StairArchiveTrace
theorem selected_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (p ++ (program d ++ Partial.archiveLoad270 d)) m s
    out.phase=s.phase ∧ (let v:=key 129 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run (Partial.archiveRestore270 d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=frame_key sourceIdx rawPorts chronological row 129 past G S cross s pre prior
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have spec:=select_spec ⟨row,limit,truth⟩
  have fresh:=reframe limit truth rawPorts pre frame
  have enc:=source_law d tick e legal
  have act:=load_run d _ spec.1 pre f fresh
  exact sequence_law p (program d) (Partial.archiveLoad270 d) (Partial.archiveRestore270 d)
    (reverse d) q s m (fun out=>let v:=key 129 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run (Partial.archiveLoad270 d) f pre) rfl act.1
    ⟨spec.1,spec.2,act.2.1⟩ (fun n=>roundtrip d _ spec.1 pre f n fresh)

theorem selected_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^129)
    (prior:PastFacts sourceIdx rawPorts 129 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (let v:=key 129 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run (endUndo d) n out=s :=
  selected_generic EndTick.physP EndTick.physQ d s m step past G S cross odd small prior
theorem selected_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 270 original.basis)
    (hist:raw.basis (base (1028+270))=false) (swapSlot:raw.basis (base (2053-270))=false)
    (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 129 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount Partial.park270)
  let one:=run Partial.portal270Inv n (run Partial.park270 m s)
  let tape:=n.drop (measurementCount Partial.portal270Inv)
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot tape
  have eqOne:one=stash s (pullState (OB5.sig 269) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 129 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick.physP tape one):=by rw [eqOne];exact tick
  have body:=selected_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem selected_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 270 x p raw) (z:SkywalkNat.State) (small:min z.u z.v<2^121) (G S:Bool)
    (input:SkywalkIntegerInput EndTick.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 285 1700 1698 1699 (PortalValues.negative S z.u)
      (decide (3*2^137≤z.u+z.v)) (decide (3*2^137≤z.u+z.v ∧ 2^121≤z.u)) (pullState (OB5.sig 269) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^129)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1701=decide (Shadow.far 129 15 past))
    (angle:s.basis 1702=(decide (Shadow.far 129 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1703=(decide (Shadow.far 129 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 129 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩:=WideReference.terminal d x raw domain
  exact selected_last d x hx0 hx raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack270

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
def entryFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.fieldRename (WindowCallerCosts.entryLowPrefix p) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (entryLowSuffix hostPlan) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowPrefix hostPlan) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (WindowCallerCosts.exitLowSuffix p)

open Stair44Outer

def divide : Program :=
  phasePlace (WindowWalkCosts.forward true 154) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace (entryFieldHosted checkpointPrimitives) ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 235) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 234) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 154) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

def generic (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (ParityUniform.entryYAll layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (ParityUniform.exitYAll layout cy)

def borrowGeneric (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (generic cx cy))

def finite (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGeneric cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def program (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finite (.some hc) cx cy)

end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
def flip (q : Wire) (v : Bool) (s : State) : State :=
  ⟨s.phase, writeBit s.basis q (s.basis q ^^ v)⟩
@[simp] theorem at_flip (s : State) (q : Wire) (v : Bool) : (flip q v s).basis q = (s.basis q ^^ v) := by simp [flip,writeBit]
theorem at_other (s : State) (q t : Wire) (v : Bool) (ne : q≠t) : (flip t v s).basis q=s.basis q := by simp [flip,writeBit,ne]
theorem flip_twice (s : State) (t : Wire) (a b : Bool) : flip t b (flip t a s) = flip t (a^^b) s := by
  apply congrArg₂ State.mk rfl; funext q
  by_cases e : q=t
  · subst q; simp [flip,writeBit,Bool.xor_assoc]
  · simp [flip,writeBit,e]
@[simp] theorem flip_zero (s : State) (t : Wire) : flip t false s=s := by
  apply congrArg₂ State.mk rfl; funext q
  by_cases e : q=t <;> simp [flip,writeBit,e]
theorem flip_comm (s : State) (i j : Wire) (a b : Bool) (ne : i≠j) :
    flip i a (flip j b s)=flip j b (flip i a s) := by
  apply congrArg₂ State.mk rfl; funext q
  by_cases x : q=i
  · subst q; simp [flip,writeBit,ne,ne.symm]
  by_cases y : q=j
  · subst q; simp [flip,writeBit,ne,ne.symm]
  · simp [flip,writeBit,x,y]
theorem ccx (a b t : Wire) (P : Program) (m : List Bool) (s : State) :
    run (.CCX a b t::P) m s = run P m (flip t (s.basis a && s.basis b) s) := rfl

def value (last : Wire) (s : BasisState) : Hops→Bool→Bool
  | [],v => v && s last
  | (c,b)::xs,v => value last s xs (s b ^^ (v && s c))
def product (last : Wire) (s : BasisState) : Hops→Bool
  | [] => s last
  | (c,_)::xs => s c && product last s xs
def outside (q last : Wire) (xs : Hops) := q≠last ∧ ∀ e∈xs,q≠e.1 ∧ q≠e.2
def safe (last target : Wire) : Wire→Hops→Prop
  | src,[] => src≠target ∧ last≠target
  | src,(c,b)::xs => src≠target ∧ c≠target ∧ b≠target ∧ src≠b ∧ c≠b ∧ outside b last xs ∧ safe last target b xs

theorem value_away (xs : Hops) (last q : Wire) (s : State) (u v : Bool) (h : outside q last xs) :
    value last (flip q u s).basis xs v=value last s.basis xs v := by
  induction xs generalizing v with
  | nil => simp only [value,at_other _ _ _ _ h.1.symm]
  | cons a xs ih =>
    rcases a with ⟨c,b⟩
    have hcb := h.2 (c,b) (by simp)
    have rest : outside q last xs := ⟨h.1,fun e he=>h.2 e (List.mem_cons_of_mem _ he)⟩
    simp only [value,at_other _ _ _ _ hcb.1.symm,at_other _ _ _ _ hcb.2.symm,ih _ rest]
theorem value_xor (xs : Hops) (last : Wire) (s : BasisState) (v u : Bool) :
    value last s xs (v^^u)=(value last s xs v ^^ (u && product last s xs)) := by
  induction xs generalizing v u with
  | nil => simp only [value,product]; cases v <;> cases u <;> cases s last <;> rfl
  | cons term xs ih =>
    rcases term with ⟨c,b⟩
    have e : (s b ^^ ((v^^u) && s c)) = ((s b ^^ (v && s c)) ^^ (u && s c)) := by
      cases v <;> cases u <;> cases s c <;> cases s b <;> rfl
    rw [value,e,ih,value,product,Bool.and_assoc]

theorem chain_run (src last t : Wire) (xs : Hops) (m : List Bool) (s : State) (hp : safe last t src xs) :
    run (chain src last t xs) m s = flip t (value last s.basis xs (s.basis src)) s := by
  induction xs generalizing src s m with
  | nil => rfl
  | cons term xs ih =>
    rcases term with ⟨c,b⟩
    obtain ⟨st,ct,bt,sb,cb,away,small⟩ := hp
    let e := s.basis src && s.basis c
    let mid := flip b e s
    let z := value last mid.basis xs (mid.basis b)
    have rest : run (chain b last t xs) m mid=flip t z mid := ih b m mid small
    rw [chain,List.singleton_append,List.cons_append,ccx,run_append,run_take]
    change run [.CCX src c b] _ (run (chain b last t xs) m mid) = _
    rw [rest]
    change flip b ((flip t z mid).basis src && (flip t z mid).basis c) (flip t z mid)=_
    simp only [at_other _ _ _ _ st,at_other _ _ _ _ ct]
    change flip b ((flip b e s).basis src && (flip b e s).basis c) (flip t z (flip b e s))=_
    rw [at_other _ _ _ _ sb,at_other _ _ _ _ cb,flip_comm _ b t _ _ bt,flip_twice]
    have same : (e^^e)=false := by cases e <;> rfl
    change flip t z (flip b (e^^e) s) = _
    rw [same,flip_zero]
    unfold z mid
    rw [at_flip,value_away _ _ _ _ _ _ away]; rfl
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires measurementCount Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

theorem head_chain (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (M : List Bool) (u : State)
    (hu : ∀ q ∈ skywalkPoolWires base,
      u.basis q = (run (Rolling1588.Integer.regularForward base false 1 510) M s1).basis q)
    (mD : List Bool) :
    run P1 mD (pullState (sig 510) u) =
      run (Rolling1588.Integer.reverse false 506 5) mD (pullState (sig 510) u) := by
  have st6 := stage_after x hx0 hx s1 first 505 (by omega)
    (M.take (measurementCount (Rolling1588.Integer.regularForward base false 1 505)))
  have ag6 := agree_split u s1 M _ _ split506 hu
  have st7 := stage_after x hx0 hx s1 first 506 (by omega)
    (M.take (measurementCount (Rolling1588.Integer.regularForward base false 1 506)))
  have ag7 := agree_split u s1 M _ _ split507 hu
  have st8 := stage_after x hx0 hx s1 first 507 (by omega)
    (M.take (measurementCount (Rolling1588.Integer.regularForward base false 1 507)))
  have ag8 := agree_split u s1 M _ _ split508 hu
  have hb : ∀ r, run P1 r (pullState (sig 510) u) = run (Q1 ++ Q2) r (pullState (sig 510) u) := by
    intro r
    rw [← PE1]
    show run (renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)) r
      (pullState (sig 510) u) = _
    rw [InverseFour15.unpack51015, OB5.run_rename 510 (by omega), OB5.run_rename 510 (by omega),
      InverseFive23.decoded_replace_pool15 false x hx0 hx _ u st6 _ r ag6]
  have hc : ∀ r, run Q1 r (pullState (sig 510) u) = run (Z1 ++ Z2) r (pullState (sig 510) u) := by
    intro r
    rw [← PE2]
    exact InverseFour15.placed_block15 false x hx0 hx _ u st7 _ r ag7
  have hd : ∀ r, run Z1 r (pullState (sig 510) u) = run Y r (pullState (sig 510) u) :=
    key510 x hx0 hx _ u st8 _ ag8
  have hQ : ∀ r, run Q1 r (pullState (sig 510) u) = run (Y ++ Z2) r (pullState (sig 510) u) :=
    fun r => (hc r).trans (run_congr_append Z1 Y Z2 _ hd cZ r)
  have hP : ∀ r, run P1 r (pullState (sig 510) u) =
      run ((Y ++ Z2) ++ Q2) r (pullState (sig 510) u) :=
    fun r => (hb r).trans (run_congr_append Q1 (Y ++ Z2) Q2 _ hQ cQ r)
  rw [hP mD, PE4]

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.Stair44WalkCuts
open Arithmetic MappedCompressed Stair44WalkMap Rolling1588.Integer
set_option maxRecDepth 12000
attribute [local irreducible] run wires measurementCount Rolling1588.reverse
  Rolling1588TickGap.forward regularForward Stair44WalkRun.backward

theorem backward_record (d : Bool) (a x : Nat) (atCut : 16+a ∈ [425,505,506])
    (hx0 : 0<x) (hx : x<p) (s v : State) (enc m : List Bool)
    (hs : Stage base d x p 1 s.basis)
    (agree : ∀q ∈ skywalkPoolWires base,v.basis q=(run (regularForward base d 1 (15+a)) enc s).basis q) :
    let t := pullState (OB5.sig (16+a-1)) v
    pullState first (run (Stair44WalkRun.backward d a) m t) = run (Rolling1588.reverse d 1 (15+a)) m t := by
  obtain ⟨mid,hm⟩ : ∃ u : State,run (regularForward base d 1 15)
    (enc.take (measurementCount (regularForward base d 1 15))) s=u := ⟨_,rfl⟩
  have st := start16 d x hx0 hx s (enc.take (measurementCount (regularForward base d 1 15))) hs
  rw [hm] at st
  have cut := decompose d 1 15 a s enc
  dsimp only at cut
  rw [hm,show (1:Nat)+15=16 by decide] at cut
  obtain ⟨post,he⟩ : ∃ z : List Bool,enc.drop (measurementCount (regularForward base d 1 15))=z := ⟨_,rfl⟩
  rw [he] at cut
  have pool (q : Wire) (hq : q∈skywalkPoolWires base) : v.basis q=(run (regularForward base d 16 a) post mid).basis q :=
    (agree q hq).trans (congrArg (fun w : State => w.basis q) cut)
  exact backward_start d a x atCut hx0 hx mid v post m st pool
end ECDSAAdd.Entrant.Stair44WalkCuts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveHistoryCompare
open Arithmetic MappedCompressed WideReference
attribute [local irreducible] run W.compactSkywalkTick

def Except (qs:List Wire) (s t:State) := ∀q∉qs,s.basis q=t.basis q

theorem runEq {qs:List Wire} (P:Program) (s t:State) (m n:List Bool) (initial:Except qs s t)
    (off:∀q∈qs,q∉wires P) : Except qs (run P m s) (run P n t) := by
  let aligned:State:=⟨s.phase,t.basis⟩
  have localEq:=run_measured_locality P (wires P) (Finset.Subset.refl _) s aligned m rfl
    (fun q used=>initial q (fun mem=>off q mem used))
  have records:=StairDivLoanTop.run_basis_records P m n aligned t rfl
  intro q hq
  by_cases used:q∈wires P
  · exact (localEq.2 q used).trans (congrFun records q)
  · rw [run_preserves_outside _ _ _ _ used,run_preserves_outside _ _ _ _ used]
    exact initial q hq

theorem spanAppend (i n k:Nat) : span i (n+k)=span i n++span (i+n) k := by
  induction n generalizing i with
  | zero=>simp [span]
  | succ n ih=>rw [Nat.succ_add,span,span,ih (i+1),List.append_assoc];simp [Nat.succ_add,Nat.add_assoc]

theorem moveEarlier (i n:Nat) (lim:i+n≤512) (P:Program) (old:∀q∈wires P,Earlier i q) (s:State) :
    run (span i n) [] (run P [] s)=run P [] (run (span i n) [] s) := by
  have disjoint:Disjoint (wires P) (wires (span i n)) :=
    Finset.disjoint_left.mpr (fun _ h=>pastOffSpan _ _ _ lim (old _ h))
  exact (run_disjoint_commute _ _ disjoint [] [] s).symm

theorem join {old added:List Wire} {s a b:State} (h:Except added s a) (k:Except old a b):
    Except (old++added) s b := by
  intro q off
  exact (h q (fun hit=>off (List.mem_append.mpr (Or.inr hit)))).trans (k q (fun hit=>off (List.mem_append.mpr (Or.inl hit))))

/-- Move earlier encoders past the untouched tick span and then add this window's encoder. -/
theorem extend (i n:Nat) (lim:i+n≤512) (old added:List Wire) (prefixProgram nextProgram:Program)
    (raw reference out:State) (pre:Except old raw (run prefixProgram [] reference))
    (window:Except added out (run nextProgram [] (run (span i n) [] raw)))
    (priorOld:∀q∈old,Earlier i q) (opsOld:∀q∈wires prefixProgram,Earlier i q)
    (avoid:∀q∈old,q∉wires nextProgram) :
    Except (old++added) out (run (prefixProgram++nextProgram) [] (run (span i n) [] reference)) := by
  have stable:=runEq (span i n) raw (run prefixProgram [] reference) [] [] pre
    (fun q mem=>pastOffSpan _ _ _ lim (priorOld q mem))
  rw [moveEarlier _ _ lim _ opsOld reference] at stable
  have next:=runEq nextProgram _ _ [] [] stable avoid
  rw [run_append,run_take,List.drop_nil]
  exact join window next

end ECDSAAdd.Entrant.StairPacket.ArchiveHistoryCompare

end

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveOrdinaryFive
open Arithmetic MappedCompressed Rolling1588
set_option maxRecDepth 25000
set_option maxHeartbeats 2400000
attribute [local irreducible] run

theorem stock_relocated (d:Bool) (f g:Fin 10→Wire) (inj:Function.Injective f) (inj':Function.Injective g)
    (s t:State) (m n:List Bool) (initial:∀i,s.basis (f i)=t.basis (g i)) (i:Fin 10) :
    (run (codeEncodeAt d f) m s).basis (f i)=(run (codeEncodeAt d g) n t).basis (g i) := by
  let a:=MeasuredCodec5.label f
  let b:=MeasuredCodec5.label g
  let src:=pullState a s
  let dst:State:=⟨t.phase,src.basis⟩
  have footprint:wires (codeEncode d)⊆Finset.range 10:=by cases d <;> decide +kernel
  have input (q:Nat) (hq:q∈Finset.range 10) : dst.basis q=t.basis (b q) := by
    have lt:=Finset.mem_range.mp hq
    simpa [dst,src,pullState,a,b,MeasuredCodec5.label,lt] using initial ⟨q,lt⟩
  have srcStep:=run_rename_pool a _ (FirstNonzeroCodec.label_inj' _ inj) _ footprint m src s rfl (fun _ _=>rfl)
  have dstStep:=run_rename_pool b _ (FirstNonzeroCodec.label_inj' _ inj') _ footprint n dst t rfl input
  have basis:=StairDivLoanTop.run_basis_records (codeEncode d) m n src dst rfl
  have h: i.val∈Finset.range 10:=Finset.mem_range.mpr i.isLt
  have srcBit:=srcStep.2 _ h
  have dstBit:=dstStep.2 _ h
  change (run (codeEncodeAt d f) m s).basis (a i.val)=_ at srcBit
  change (run (codeEncodeAt d g) n t).basis (b i.val)=_ at dstBit
  simpa only [a,b,MeasuredCodec5.label,dif_pos i.isLt] using
    srcBit.trans ((congrFun basis i.val).trans dstBit.symm)
end ECDSAAdd.Entrant.StairPacket.ArchiveOrdinaryFive

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveTruth
open Arithmetic MappedCompressed WideReference SkywalkRails StairArchiveTrace StairArchiveRaw StairArchiveNativeRows CodecBitSliceVerify
attribute [local irreducible] run SkywalkNat.step span WideReference.canonical StairArchiveRaw.rawCol SkywalkTrace.trace
def tile (k:Nat) (hi:Bool):Nat:=k+5+(if hi then 5 else 0)
private theorem nextCanon (k j x p:Nat):SkywalkTrace.next^[j] (WideReference.canonical k x p)=WideReference.canonical (k+j) x p:=by
  unfold WideReference.canonical
  rw [Nat.add_comm k j]
  exact (Function.iterate_add_apply _ j k _).symm

theorem observedLabel (k x p row:Nat) (truth:ArchiveStockRows.Chronology k x p row) (e:Fin 20):
    (rawCol e).testBit row=letterBit (SkywalkTrace.code (WideReference.canonical (k+(5+e.val/2)) x p)) e:=by
  have h:=truth e
  have drop (cs:List (Bool×Bool)):read (cs.drop 5) (e.val/2)=read cs (5+e.val/2):=by simp only [StairArchiveRaw.read,List.getElem?_drop]
  rw [drop,read_trace _ _ (by omega),nextCanon] at h
  exact h

private theorem observeSite (b:BasisState) (t:Nat) (q:Fin 10) (v:Bool×Bool)
    (a:b (base (t+q.val/2))=v.1) (c:b (base (1028+(t+q.val/2)))=v.2):
    b (History5.historyMap base t q)=letterBit v q:=by
  unfold History5.historyMap History5.historyId letterBit
  by_cases h:q.val%2=0
  · simpa only [if_pos h] using a
  · simpa only [if_neg h,Nat.add_assoc] using c

theorem raw_for (x p:Nat) (good:Bounds x p) (s:State) (dom:Domain 225 x p s)
    (k:Nat) (start:225≤k) (stop:k+15≤271)
    (row:Nat) (truth:ArchiveStockRows.Chronology k x p row) (hi:Bool) (q:Fin 10):
    (run (span 225 46) [] s).basis (History5.historyMap base (tile k hi) q)=
      (rawCol ((if hi then 10 else 0)+q.val)).testBit row:=by
  let e:Nat:=(if hi then 10 else 0)+q.val
  have bound:e<20:=by cases hi <;> simp [e] <;> omega
  have lo:225≤tile k hi+q.val/2:=by unfold tile;omega
  have lim:tile k hi+q.val/2<225+46:=by cases hi <;> simp [tile] <;> omega
  have obs:=trace_sites 225 46 x p (by decide) good s [] dom (tile k hi+q.val/2) lo lim
  have exactBit:=observeSite (run (span 225 46) [] s).basis (tile k hi) q _ obs.1 obs.2
  have label:=observedLabel k x p row truth ⟨e,bound⟩
  change (rawCol e).testBit row=letterBit (SkywalkTrace.code (WideReference.canonical (k+(5+e/2)) x p)) e at label
  have shift : k+(5+e/2)=tile k hi+q.val/2:=by cases hi <;> simp [tile,e] <;> omega
  have parity:e%2=q.val%2:=by
    cases hi <;> simp [e]
    omega
  rw [shift] at label
  have bit (v:Bool×Bool):letterBit v e=letterBit v q:=by simp only [letterBit,parity]
  exact exactBit.trans ((bit _).symm.trans label.symm)

theorem native_byte (x p:Nat) (good:Bounds x p) (s:State) (dom:Domain 225 x p s)
    (k:Nat) (start:225≤k) (stop:k+15≤271) 
    (row:Nat) (lim:row<63145) (truth:ArchiveStockRows.Chronology k x p row) (d hi:Bool) (m:List Bool):
    let raw:=run (span 225 46) [] s
    let f:=History5.historyMap base (tile k hi)
    let out:=run (Rolling1588.codeEncodeAt d f) m raw
    out.phase=raw.phase ∧ ∀q:Fin 10,out.basis (f q)=(get (storage (native d hi)) q).testBit row:=by
  exact StockArchiveByte.run_byte d hi row lim _ (History5.historyMap_injective base base_pool_nodup _ (by cases hi <;> simp [tile] <;> omega)) _ m
    (raw_for x p good s dom k start stop row truth hi)
end ECDSAAdd.Entrant.StairPacket.StockArchiveTruth

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockGroups
open Arithmetic MappedCompressed ArchiveStockSuffix StockArchiveReference
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
abbrev Group:=Fin 10
def start (i:Group):Nat:=220+5*i.val
def slot (i:Group):Fin 10→Wire:=History5.historyMap base (start i)
def ports (i:Group):Finset Wire:=Finset.univ.image (slot i)
def one (d:Bool) (i:Group):Program:=Rolling1588.encodeAt base d (start i)
def batch (d:Bool) (seq:List Group):Program:=seq.flatMap (one d)
def all:List Group:=List.finRange 10
def plain:List Group:=[0,1,4,7]
def packed:List Group:=[2,3,5,6,8,9]
theorem stockEq (d:Bool):StockDelayed.packs d 225 46=batch d all:=by rfl
theorem ordinaryEq (d:Bool):ordinary d=batch d plain:=by
  simp [ordinary,batch,plain,one,start,List.append_assoc]
theorem distinct:∀i j:Group,i≠j→Disjoint (ports i) (ports j):=by decide +kernel
theorem sparse:∀i∈packed,∀j:Fin 10,
    (j=5 ∨ j=9) ∧ slot i j∈holes ∨ OB5.sig 270 (slot i j)∈archives:=by decide +kernel
theorem holeSlot:∀q∈holes,∃i∈packed,∃j:Fin 10,q=slot i j:=by decide +kernel
theorem split(i:Group):i∈plain ∨ i∈packed:=by revert i;decide
theorem inAll (i:Group):i∈all:=List.mem_finRange _
theorem allNodup:all.Nodup:=by decide
theorem plainNodup:plain.Nodup:=by decide
theorem cover (d:Bool)(i:Group):wires (one d i)⊆ports i:=by
  intro q h
  change q∈wires (renameProgram (MeasuredCodec5.label (slot i)) (Rolling1588.codeEncode d)) at h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
  rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
  exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,by simp [MeasuredCodec5.label,ha]⟩
private theorem distant {i h:Group} (ne:i≠h) {q:Wire} (mem:q∈ports i):
    q∉ports h:=fun hit=>Finset.disjoint_left.mp (distinct i h ne) mem hit
theorem batch_cover (d:Bool) (seq:List Group) (q:Wire) (hit:q∈wires (batch d seq)):
    ∃i∈seq,q∈ports i:=by
  induction seq with
  | nil=>simp [batch,wires] at hit
  | cons h t ih=>
    change q∈wires (one d h++batch d t) at hit
    rw [wires_append,Finset.mem_union] at hit
    rcases hit with a|b
    · exact ⟨h,by simp,cover _ _ a⟩
    · obtain ⟨i,ii,v⟩:=ih b
      exact ⟨i,by simp [ii],v⟩
theorem outside (d:Bool) (seq:List Group) (s:State) (q:Wire) (off:∀i∈seq,q∉ports i):
    (run (batch d seq) [] s).basis q=s.basis q:=by
  apply run_preserves_outside
  intro hit;obtain ⟨i,mem,h⟩:=batch_cover d seq q hit;exact off i mem h
theorem isolated (d:Bool) (seq:List Group) (nd:seq.Nodup) (s:State) (i:Group) (mem:i∈seq)
    (q:Wire) (hq:q∈ports i):(run (batch d seq) [] s).basis q=(run (one d i) [] s).basis q:=by
  induction seq generalizing s with
  | nil=>simp at mem
  | cons h t ih=>
    change (run (one d h++batch d t) [] s).basis q=_
    rw [run_append,run_take,List.drop_nil]
    obtain ⟨not,unique⟩:=List.nodup_cons.mp nd
    rcases List.mem_cons.mp mem with rfl|im
    · exact outside d t _ q (fun j jj=>distant (i:=i) (h:=j) (fun eq=>not (eq.symm ▸ jj)) hq)
    · have ne:i≠h:=fun eq=>not (eq ▸ im)
      have hd:Disjoint (wires (one d i)) (wires (one d h)):=(distinct i h ne).mono (cover _ _) (cover _ _)
      rw [ih unique (run (one d h) [] s) im,run_disjoint_commute _ _ hd]
      exact run_preserves_outside _ _ _ _ (fun bad=>distant ne hq (cover _ _ bad))
end ECDSAAdd.Entrant.StairPacket.StockGroups

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockStrongChain
open Arithmetic MappedCompressed Secp256k1 IntegerPacket WideReference StockWindowTicket StockCanonicalRow Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 16000
set_option maxHeartbeats 4500000
attribute [local irreducible] run measurementCount Partial.leave225 Partial.leave240 Partial.leave255
  NativePack240.nextWindow NativePack255.nextWindow NativePack270.lastWindow
noncomputable def value (x p i b:Nat) (c:SkywalkNat.State→Bool):Nat→Bool:=
  key b (unsigned i x p) (c (unsigned i x p)) (SkywalkTrace.trace 15 (WideReference.canonical i x p))
def cross225 (z:SkywalkNat.State):Bool:=HighBankSum.cross (Leave225TrueMiddle.d z)
def cross240 (z:SkywalkNat.State):Bool:=HighBankSum.cross (Leave240TrueMiddle.d z)
def cross255 (z:SkywalkNat.State):Bool:=HighBankSum.cross (Leave255TrueMiddle.d z)
def SavedKey (v:Nat→Bool) (ps:Ports) (d:Bool) (s:State):Prop:= select v<63145 ∧ Encodes v (select v) ∧ Kept ps d (select v) s

theorem selected240 (d:Bool) (x p:Nat) (good:Bounds x p):
    Checked (NativePack240.nextWindow d++leave240) (leave240Inv++NativePack240.nextUnwind d)
      (fun s=>Ready240 d x p s)
      (fun s=>Ready255 d x p s ∧ SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s):=by
  intro s m h
  have h0:=step240 d x p good s m h
  obtain ⟨raw,g,sg,pg,ps,pre⟩:=h
  let v:=run (NativePack240.nextWindow d) m s
  let tape:=m.drop (measurementCount (NativePack240.nextWindow d))
  have nums:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) pre.domain
  have cert:=NativePack240.selected_receipt d raw s m (unsigned 240 x p) g sg nums.odd nums.small pre.cut
    (readInput 240 x p raw g sg pre.input) hist (unsigned 225 x p) pg ps _ old.odd old.small pre.facts
  have canon:=pre.pastCanonical
  unfold signedAt at canon
  dsimp only at cert
  rw [canon] at cert
  refine ⟨h0.1,⟨h0.2.1,?_⟩,h0.2.2⟩
  simp only [run_append,run_take]
  exact ⟨cert.1,cert.2.1,ArchiveWindowPreserve.keep cert.2.2 (fun q hq=>ArchiveWindowPreserve.after240 v tape q hq)⟩

theorem selected255 (d:Bool) (x p:Nat) (good:Bounds x p):
    Checked (NativePack255.nextWindow d++leave255) (leave255Inv++NativePack255.nextUnwind d)
      (fun s=>Ready255 d x p s ∧ SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s)
      (fun s=>Ready270 d x p s ∧ SavedKey (value x p 240 136 cross240) ArchiveBoundary255.codePorts d s ∧ SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s):=by
  intro s m h
  have h0:=step255 d x p good s m h.1
  obtain ⟨raw,g,sg,pg,ps,pre⟩:=h.1
  let v:=run (NativePack255.nextWindow d) m s
  let tape:=m.drop (measurementCount (NativePack255.nextWindow d))
  have nums:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have old:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using WideReference.future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) pre.domain
  have cert:=NativePack255.selected_receipt d raw s m (unsigned 255 x p) g sg nums.odd nums.small pre.cut
    (readInput 255 x p raw g sg pre.input) hist (WideReference.carry (by decide) pre.domain) (unsigned 240 x p) pg ps _ old.odd old.small pre.facts
  have canon:=pre.pastCanonical
  unfold signedAt at canon
  dsimp only at cert
  rw [canon] at cert
  refine ⟨h0.1,⟨h0.2.1,?_⟩,h0.2.2⟩
  simp only [run_append,run_take]
  refine ⟨⟨cert.1,cert.2.1,ArchiveWindowPreserve.keep cert.2.2 (fun q hq=>ArchiveWindowPreserve.after255 v tape q (List.mem_append.mpr (Or.inr hq)))⟩,h.2.1,h.2.2.1,?_⟩
  exact ArchiveWindowPreserve.keep h.2.2.2 (fun q hq=>(ArchiveWindowPreserve.after255 v tape q (List.mem_append.mpr (Or.inl hq))).trans (ArchiveWindowPreserve.entering255 d s m q hq))

def final (d:Bool) (x p:Nat) (s:State):Prop:=
  SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s ∧
  SavedKey (value x p 240 136 cross240) ArchiveBoundary255.codePorts d s ∧
  SavedKey (value x p 255 129 cross255) ArchiveBoundary270.codePorts d s

attribute [local irreducible] key select WideReference.canonical
theorem kept_frame (ps:Ports) (d:Bool) (r:Nat) (s:State) (h:Frame ps (code d) r s):
    Kept ps d r s:=fun j=>h ⟨j,by omega⟩
theorem finalBank (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (m:List Bool) (ready:Ready270 d x p s):
    SavedKey (value x p 255 129 cross255) ArchiveBoundary270.codePorts d (run (NativePack270.lastWindow d) m s):=by
  obtain ⟨raw,g,sg,pg,ps,pre⟩:=ready
  let z:=unsigned 270 x p
  have short:min z.u z.v<2^121:=true_small x p 270 (lt_trans good.small good.cap) good.cap (by decide)
  have old:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have eq:farAt 121 270 x p=(3*2^137≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have last:=NativePack270.selected_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 270 x p raw g sg pre.input) (by simpa only [eq] using pre.cut) (unsigned 255 x p) pg ps _
    old.odd old.small pre.records pre.mode pre.side pre.cross
  have canon:=pre.pastCanonical
  unfold signedAt at canon
  have cert:=last.2.1
  dsimp only at cert
  rw [canon] at cert
  exact ⟨cert.1,cert.2.1,kept_frame _ _ _ _ cert.2.2⟩

theorem selected270 (d:Bool) (x:Nat) (good:Bounds x p):
    Checked (NativePack270.lastWindow d) (NativePack270.lastUnwind d)
      (fun s=>Ready270 d x p s ∧ SavedKey (value x p 240 136 cross240) ArchiveBoundary255.codePorts d s ∧
        SavedKey (value x p 225 144 cross225) ArchiveBoundary240.codePorts d s) (final d x p):=by
  intro s m h
  have previous:=step270 d x good s m h.1
  refine ⟨previous.1,⟨⟨h.2.2.1,h.2.2.2.1,?_⟩,⟨h.2.1.1,h.2.1.2.1,?_⟩,finalBank d x good s m h.1⟩,previous.2.2⟩
  · exact ArchiveWindowPreserve.keep h.2.2.2.2 (fun q mem=>ArchiveWindowPreserve.last d s m q (List.mem_append.mpr (Or.inl mem)))
  · exact ArchiveWindowPreserve.keep h.2.1.2.2 (fun q mem=>ArchiveWindowPreserve.last d s m q (List.mem_append.mpr (Or.inr mem)))

theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis):
    let start:=pullState (OB5.sig 224) raw
    let out:=run (forward45plus1 d) m start
    out.phase=raw.phase ∧ final d x p out ∧ ∀n,run (reverse45plus1 d) n out=start:=by
  have room:Checked (forward45plus1 d) (reverse45plus1 d) (Before d x p) (final d x p):=by
    rw [assembly,unwind_assembly]
    simpa only [List.append_assoc] using
      composition (step225 d x p good) (composition (selected240 d x p good) (composition (selected255 d x p good) (selected270 d x good)))
  exact room _ m ⟨raw,stage,rfl⟩
end ECDSAAdd.Entrant.StairPacket.StockStrongChain

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44Resources Stair44Outer
open StairConcreteAssembly WindowFieldParity
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
private theorem leaf : toffoliCount region=200 ∧ measurementCount region=0 ∧ gateSlots region=352 := by
  decide +kernel
private theorem correction_eq (c : Cost) : c.measure correction=3*c.measure region := by
  simp only [correction,bankCorrection,c.append,c.rename]; omega
private theorem df (c : Cost) (p : StairSchedule.StairPrimitives) :
    c.measure (entryFieldHosted p)=c.measure (WindowCallerCosts.entryFieldHosted p)+2*c.measure correction := by
  simp only [entryFieldHosted,WindowCallerCosts.entryFieldHosted,setup,c.append]; omega
private theorem mf (c : Cost) (p : StairSchedule.StairPrimitives) :
    c.measure (exitFieldHosted p)=c.measure (WindowCallerCosts.exitFieldHosted p)+2*c.measure correction := by
  simp only [exitFieldHosted,WindowCallerCosts.exitFieldHosted,setup,c.append]; omega
private theorem div (c : Cost) : c.measure divide=c.measure WindowCallerCosts.divide+2*c.measure correction := by
  simp only [divide,WindowCallerCosts.divide,kernelPlace,c.append,c.rename,df]; omega
private theorem mul (c : Cost) (k : Nat) :
    c.measure (multiply k)=c.measure (WindowCallerCosts.multiply k)+2*c.measure correction := by
  simp only [multiply,WindowCallerCosts.multiply,kernelPlace,c.append,c.rename,mf]; omega
private theorem all (c : Cost) (C : Point) (cx cy : Fp) :
    c.measure (finite C cx cy)=c.measure (WindowCallerCosts.finite C cx cy)+12*c.measure region := by
  simp only [finite,WindowCallerCosts.finite,borrowGeneric,WindowCallerCosts.borrowGeneric,generic,
    WindowCallerCosts.generic,c.append,c.rename,div,mul,correction_eq]; omega
theorem metrics (C : Point) : toffoliCount (program C) ≤ 2153619 ∧
    measurementCount (program C) ≤ 1512390 ∧ gateSlots (program C) ≤ 51930861 := by
  have old := WindowCallerCosts.totals C
  have sl := WindowSlots.slotBound C
  cases C with
  | zero => change toffoliCount [] ≤ _ ∧ measurementCount [] ≤ _ ∧ gateSlots [] ≤ _; decide
  | @some cx cy hc =>
    have ht := all tc (.some hc) cx cy
    have hm := all mc (.some hc) cx cy
    have hs := all slots (.some hc) cx cy
    rw [show tc.measure=toffoliCount from rfl,leaf.1] at ht
    rw [show mc.measure=measurementCount from rfl,leaf.2.1] at hm
    rw [show slots.measure=gateSlots from rfl,leaf.2.2] at hs
    simp only [program,WindowCallerCosts.program,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,rename_gateSlots] at old sl ⊢
    exact ⟨by omega,by omega,by omega⟩
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
attribute [local irreducible] run chain

structure Good (a b src last t : Wire) (xs : Hops) : Prop where
  chained : safe last t src xs
  source : outside src last xs
  target : outside t last xs
  st : src≠t
  at_ : a≠t
  bt : b≠t
  as_ : a≠src
  bs : b≠src

theorem single (a b t : Wire) (m : List Bool) (s : State) :
  run [.CCX a b t] m s=flip t (s.basis a && s.basis b) s := by rw [ccx,run]
theorem mcx_run (a b src last t : Wire) (xs : Hops) (m : List Bool) (s : State) (h : Good a b src last t xs) :
    run (mcx a b src last t xs) m s =
      flip t ((s.basis a && s.basis b) && product last s.basis xs) s := by
  let d := s.basis a && s.basis b
  let first := value last s.basis xs (s.basis src)
  let u := flip src d (flip t first s)
  have readSrc : u.basis src=(s.basis src^^d) := by
    simp only [u,at_flip,at_other _ _ _ _ h.st]
  have next : value last u.basis xs (u.basis src) =
      (first ^^ (d && product last s.basis xs)) := by
    rw [readSrc]
    unfold u
    rw [value_away _ _ _ _ _ _ h.source,value_away _ _ _ _ _ _ h.target,value_xor]
  let second := first ^^ (d && product last s.basis xs)
  have x1 : (flip t first s).basis a=s.basis a := at_other _ _ _ _ h.at_
  have y1 : (flip t first s).basis b=s.basis b := at_other _ _ _ _ h.bt
  have x2 : (flip t second u).basis a=s.basis a := by
    simp only [u,at_other _ _ _ _ h.at_,at_other _ _ _ _ h.as_]
  have y2 : (flip t second u).basis b=s.basis b := by
    simp only [u,at_other _ _ _ _ h.bt,at_other _ _ _ _ h.bs]
  simp only [mcx,run_append,run_take,chain_run _ _ _ _ _ _ h.chained,single,x1,y1]
  simp only [at_other _ _ _ _ h.at_,at_other _ _ _ _ h.bt,at_other _ _ _ _ h.as_,at_other _ _ _ _ h.bs]
  change flip src d (flip t (value last u.basis xs (u.basis src)) u)=_
  rw [next]
  change flip src d (flip t second u)=_
  rw [flip_comm _ src t _ _ h.st]
  change flip t second (flip src d (flip src d (flip t first s)))=_
  rw [flip_twice]
  have remove : (d^^d)=false := by cases d <;> rfl
  rw [remove,flip_zero,flip_twice]
  have finish : (first^^second)=(d && product last s.basis xs) := by
    unfold second; cases first <;> cases (d && product last s.basis xs) <;> rfl
  rw [finish]
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Baselines Stair44Outer StairConcreteAssembly WindowFieldParity
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
private theorem extra : GatePhysical (kernelPlace correction) :=
  CodecBitSliceVerify.physical_of_check _ (by decide +kernel)
private theorem kapp (a b : Program) : kernelPlace (a++b)=kernelPlace a++kernelPlace b := List.map_append
private theorem ef (p : StairSchedule.StairPrimitives)
    (h : GatePhysical (kernelPlace (WindowCallerCosts.entryFieldHosted p))) :
    GatePhysical (kernelPlace (entryFieldHosted p)) := by
  simp only [WindowCallerCosts.entryFieldHosted,kapp,gatePhysical_append] at h
  simp only [entryFieldHosted,setup,kapp,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨h.1.1.1.1.1,⟨h.1.1.1.1.2,extra⟩⟩,h.1.1.1.2⟩,h.1.1.2⟩,h.1.2⟩,⟨h.2,extra⟩⟩
private theorem mfP (p : StairSchedule.StairPrimitives)
    (h : GatePhysical (kernelPlace (WindowCallerCosts.exitFieldHosted p))) :
    GatePhysical (kernelPlace (exitFieldHosted p)) := by
  simp only [WindowCallerCosts.exitFieldHosted,kapp,gatePhysical_append] at h
  simp only [exitFieldHosted,setup,kapp,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨h.1.1.1.1.1,extra⟩,h.1.1.1.1.2⟩,h.1.1.1.2⟩,⟨h.1.1.2,extra⟩⟩,h.1.2⟩,h.2⟩
private theorem dp : GatePhysical divide := by
  have h := WindowPhysical.dividePhysical PartialPhysical.forward45plus1_physical PartialPhysical.reverse45plus1_physical
  simp only [WindowCallerCosts.divide,gatePhysical_append] at h
  simp only [divide,gatePhysical_append]
  exact ⟨⟨⟨⟨h.1.1.1.1,ef _ h.1.1.1.2⟩,h.1.1.2⟩,h.1.2⟩,h.2⟩
private theorem mp (k : Nat) : GatePhysical (multiply k) := by
  have h := WindowPhysical.multiplyPhysical PartialPhysical.forward45plus1_physical PartialPhysical.reverse45plus1_physical k
  simp only [WindowCallerCosts.multiply,gatePhysical_append] at h
  simp only [multiply,gatePhysical_append]
  exact ⟨⟨⟨⟨h.1.1.1.1,mfP _ h.1.1.1.2⟩,h.1.1.2⟩,h.1.2⟩,h.2⟩
theorem genericPhysical (cx cy : Fp) : GatePhysical (generic cx cy) := by
  have g := FlagTop2.genericN_physical cx cy
  simp only [FlagExit.genericN,FlagExit.secondStageN,gatePhysical_append] at g
  simp only [generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.1.1.1,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ g.1.1.2⟩,dp⟩,
    Stair44Square.physical _⟩,mp _⟩,
    gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.2.2⟩

theorem physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    let C : Point := .some hc
    have m := AboveFieldPointDevelop.middle_physical C cx cy
    simp only [AboveFieldPointDevelop.middle,gatePhysical_append] at m
    apply gatePhysical_rename _ (Wrapper5.U layout).injective
    simp only [finite,gatePhysical_append]
    refine ⟨⟨gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_,?_⟩,
      gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_⟩
    · simp only [gatePhysical_append]
      exact ⟨⟨FlagTop.stageNew_physical hc,m.1.1.1.1⟩,m.1.1.1.2⟩
    · exact gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ FlagTop.rho_injective _ (genericPhysical cx cy))
    · simp only [gatePhysical_append]
      exact ⟨⟨m.1.2,m.2⟩,ControlPointEncodingDevelop.borrowOut_physical hc⟩
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Challenge Baselines Stair44Outer WindowFieldParity
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
abbrev Sub (a b : Program) := wires a⊆wires b
private theorem ap {a b x y : Program} (l : Sub a x) (r : Sub b y) : Sub (a++b) (x++y) := by
  unfold Sub at *; simpa only [wires_append] using Finset.union_subset_union l r
private theorem rn {a b : Program} (f : Wire→Wire) (l : Sub a b) :
    Sub (renameProgram f a) (renameProgram f b) := by
  unfold Sub at *; simpa only [renameProgram_support] using Finset.image_mono l (f:=f)
private theorem controlsG {q : Wire} {cs : List Wire} {h : Wire} (mem : q∈cs) :
    q∈wires (ParityHost5.setup cs h) := by
  induction cs with
  | nil => simp at mem
  | cons x xs ih =>
    simp only [ParityHost5.setup,List.map_cons,wires,Finset.mem_union]
    rcases List.mem_cons.mp mem with rfl|later
    · left; simp [Instr.wires]
    · exact Or.inr (ih later)
private def payload (q : Nat) := OB5.sig 511 (NewHistory5.payloadWire base q)
private theorem hostused : FrontierEntry1591Field.host∈wires StairSchedule.paritySetup := by
  apply Finset.mem_union_left
  simp [Instr.wires]
private theorem regionSites : wires region⊆Finset.range 31 := by decide +kernel
private theorem subpart {j : Nat} (hj : j=46 ∨ j=49 ∨ j=52) : Sub (bankCorrection j) StairSchedule.paritySetup := by
  intro q h
  rw [bankCorrection,renameProgram_support] at h
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
  have ii := Finset.mem_range.mp (regionSites hi)
  unfold port
  split_ifs with low host
  · apply controlsG
    exact List.mem_map.mpr ⟨8*j+i,List.mem_range.mpr (by rcases hj with h|h|h <;> omega),rfl⟩
  · exact hostused
  · apply controlsG
    exact List.mem_map.mpr ⟨8*(other j)+(i-17),List.mem_range.mpr (by
      rcases hj with h|h|h <;> subst j <;> simp [other] <;> omega),rfl⟩
private theorem repair : Sub setup StairSchedule.paritySetup := by
  intro q h; simp only [setup,correction,wires_append,Finset.mem_union] at h
  rcases h with h|h|h|h
  · exact h
  · exact subpart (Or.inl rfl) h
  · exact subpart (Or.inr (Or.inl rfl)) h
  · exact subpart (Or.inr (Or.inr rfl)) h

private theorem repaired_eq : wires setup = wires StairSchedule.paritySetup :=
  Finset.Subset.antisymm repair (by rw [setup,wires_append]; exact Finset.subset_union_left)
private theorem E (p : StairSchedule.StairPrimitives) :
    wires (entryFieldHosted p)=wires (WindowCallerCosts.entryFieldHosted p) := by
  simp only [entryFieldHosted,WindowCallerCosts.entryFieldHosted,wires_append,repaired_eq]
private theorem M (p : StairSchedule.StairPrimitives) :
    wires (exitFieldHosted p)=wires (WindowCallerCosts.exitFieldHosted p) := by
  simp only [exitFieldHosted,WindowCallerCosts.exitFieldHosted,wires_append,repaired_eq]
private theorem D : wires divide=wires WindowCallerCosts.divide := by
  simp only [divide,WindowCallerCosts.divide,wires_append,kernelPlace,renameProgram_support,E]
private theorem X (k : Nat) : wires (multiply k)=wires (WindowCallerCosts.multiply k) := by
  simp only [multiply,WindowCallerCosts.multiply,wires_append,kernelPlace,renameProgram_support,M]
private theorem G (cx cy : Fp) : wires (generic cx cy)=wires (WindowCallerCosts.generic cx cy) := by
  simp only [generic,WindowCallerCosts.generic,wires_append,D,X]
theorem support_eq (C : Point) : wires (program C)=wires (WindowCallerCosts.program C) := by
  cases C with
  | zero => rfl
  | @some cx cy hc =>
    simp only [program,WindowCallerCosts.program,finite,WindowCallerCosts.finite,
      borrowGeneric,WindowCallerCosts.borrowGeneric,wires_append,renameProgram_support,G]
theorem width (C : Point) : qubits (program C) ≤1543 := by
  unfold qubits; rw [support_eq]; exact WindowCallerCosts.qubitBound C
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open Arithmetic MappedCompressed Secp256k1 OB5 Rolling1588.Integer
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588.reverse
def head := renameProgram (sig 511) tickR ++ P1

theorem after_head (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (M : List Bool) (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base false 1 511) M s1).basis q) (mD : List Bool) :
    ∃ raw : State, run head mD (pullState (sig 511) t5)=pullState (sig 505) raw ∧
      ∀q∈skywalkPoolWires base,raw.basis q=(run (regularForward base false 1 505) M s1).basis q := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base false x p 511
      (run (regularForward base false 1 510)
        (M.take (measurementCount (regularForward base false 1 510))) s1).basis :=
    ((regularForward_spec base false base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base false x p s1 first)).2
  have whole : run (regularForward base false 1 510)
      (M.take (measurementCount (regularForward base false 1 510))) s1=
        run (regularForward base false 1 510) M s1 := run_take _ M s1
  have last : run (regularForward base false 1 511) M s1=
      run (W.repairedTick base 511) (M.drop (measurementCount (regularForward base false 1 510)))
        (run (regularForward base false 1 510)
          (M.take (measurementCount (regularForward base false 1 510))) s1) := by
    rw [regularForward_snoc base false 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base false 1 510)
    (M.take (measurementCount (regularForward base false 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits false x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero false x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have hu (q : Wire) (hq : q∈skywalkPoolWires base) : (run tickR [] t5).basis q =
      (run (regularForward base false 1 510) M s1).basis q :=
    (uAgree q hq).trans (congrArg (fun w : State => w.basis q) whole)
  let pr := regularForward base false 1 505
  obtain ⟨s6,e6⟩ : ∃ u : State,run pr (M.take (measurementCount pr)) s1=u := ⟨_,rfl⟩
  have stage6 := stage_after x hx0 hx s1 first 505 (by decide) (M.take (measurementCount pr))
  change Stage base false x p 506 (run pr (M.take (measurementCount pr)) s1).basis at stage6
  rw [e6] at stage6
  have split := Stair44WalkCuts.decompose false 1 505 5 s1 M
  change run (regularForward base false 1 510) M s1 =
    run (regularForward base false 506 5) (M.drop (measurementCount pr)) (run pr (M.take (measurementCount pr)) s1) at split
  rw [e6] at split
  have hb (q : Wire) (hq : q∈skywalkPoolWires base) :=
    (hu q hq).trans (congrArg (fun w : State => w.basis q) split)
  have rg := reverse_gen false x hx0 hx 5 506 (by decide) (by decide) s6 (M.drop (measurementCount pr))
    (run tickR [] t5) mD stage6 hb
  refine ⟨run (regularReverse base false 506 5) mD (run tickR [] t5),?_,?_⟩
  · have cn := (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
    rw [head,run_append,cn]
    simp only [List.take_zero,List.drop_zero]
    rw [OB5.run_rename 511 (by decide),tickR_run,move,head_chain x hx0 hx s1 first M _ hu mD]
    simpa only [Rolling1588.Integer.reverse_eq_packets] using rg.1
  · intro q hq
    exact (rg.2 q hq).trans (congrArg (fun w : State => w.basis q) (e6.symm.trans (run_take pr M s1)))

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary225Exit
open Arithmetic MappedCompressed IntegerPacket Partial WideReference NativePack225
set_option maxRecDepth 25000
set_option maxHeartbeats 2800000
attribute [local irreducible] run body routed measurementCount

private theorem bins:∀i:Fin 10,∃r:Fin 225,(History5.historyMap base 220) i=base r.val ∨ (History5.historyMap base 220) i=base (1028+r.val) := by decide +kernel

private theorem old:∀i:Fin 10,oldRange (start idx+1) (windowNet idx (history i)) := by decide +kernel

private theorem injected:Function.Injective (History5.historyMap base 220):=by decide +kernel

private theorem kept (j:Fin 23) (admin:Program) (m:List Bool) (s:State) (q:Wire)
    (early:oldRange (start j+1) (windowNet j q)) :
    (run (body j admin) m s).basis q=
      (run admin (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m s)).basis q := by
  simp only [body,run_append,run_take]
  exact route_outside j 1 14 (by decide) q (old_clear (by decide) early) _ _

private theorem pastInput (x p:Nat) (good:Bounds x p) (raw:State) (dom:Domain 225 x p raw) (i:Fin 10) :
    raw.basis (History5.historyMap base 220 i)=(run (span 225 15) [] raw).basis (History5.historyMap base 220 i) := by
  obtain ⟨r,h|h⟩:=bins i
  · rw [h];exact (preservePast 225 15 x p r.val (by decide) good raw dom r.isLt []).1.symm
  · rw [h];exact (preservePast 225 15 x p r.val (by decide) good raw dom r.isLt []).2.symm

private theorem encode (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (history i)=b.basis (History5.historyMap base 220 i)) (i:Fin 10) :
    (run (program d) tape a).basis (history i)=(run (Rolling1588.encodeAt base d 220) [] b).basis (History5.historyMap base 220 i) := by
  rw [(equals d).1]
  exact ArchiveOrdinaryFive.stock_relocated d history _ histInj injected a b tape [] agree i

private theorem readback (d:Bool) (raw pre wide out:State) (tape:List Bool)
    (input:∀i,pre.basis (history i)=raw.basis (History5.historyMap base 220 i))
    (stable:∀i,raw.basis (History5.historyMap base 220 i)=wide.basis (History5.historyMap base 220 i))
    (last:∀i,out.basis (history i)=(run (program d) tape pre).basis (history i)) (i:Fin 10) :
    out.basis (history i)=(run (Rolling1588.encodeAt base d 220) [] wide).basis (History5.historyMap base 220 i) := by
  apply (last i).trans
  exact encode d pre wide tape (fun j=>(input j).trans (stable j)) i

theorem result (d:Bool) (raw s:State) (m:List Bool) (x p:Nat) (good:Bounds x p) (dom:Domain 225 x p raw)
    (input:∀i,(run (routed idx 0 1) m s).basis (history i)=raw.basis (History5.historyMap base 220 i)) :
    ∀i,(run (body idx (program d)) m s).basis (history i)=
      (run (Rolling1588.encodeAt base d 220) [] (run (span 225 15) [] raw)).basis (History5.historyMap base 220 i) := by
  exact readback d raw (run (routed idx 0 1) m s) (run (span 225 15) [] raw)
    _ _ input (pastInput x p good raw dom) (fun i=>kept idx _ m s _ (old i))
end ECDSAAdd.Entrant.StairPacket.Ordinary225Exit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary240Exit
open Arithmetic MappedCompressed IntegerPacket Partial WideReference NativePack240
set_option maxRecDepth 25000
set_option maxHeartbeats 2800000
attribute [local irreducible] run body routed measurementCount

private theorem bins:∀i:Fin 10,∃r:Fin 240,(History5.historyMap base 225) i=base r.val ∨ (History5.historyMap base 225) i=base (1028+r.val) := by decide +kernel

private theorem old:∀i:Fin 10,oldRange (start idx+1) (windowNet idx (history i)) := by decide +kernel

private theorem injected:Function.Injective (History5.historyMap base 225):=by decide +kernel

private theorem kept (j:Fin 23) (admin:Program) (m:List Bool) (s:State) (q:Wire)
    (early:oldRange (start j+1) (windowNet j q)) :
    (run (body j admin) m s).basis q=
      (run admin (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m s)).basis q := by
  simp only [body,run_append,run_take]
  exact route_outside j 1 14 (by decide) q (old_clear (by decide) early) _ _

private theorem pastInput (x p:Nat) (good:Bounds x p) (raw:State) (dom:Domain 240 x p raw) (i:Fin 10) :
    raw.basis (History5.historyMap base 225 i)=(run (span 240 15) [] raw).basis (History5.historyMap base 225 i) := by
  obtain ⟨r,h|h⟩:=bins i
  · rw [h];exact (preservePast 240 15 x p r.val (by decide) good raw dom r.isLt []).1.symm
  · rw [h];exact (preservePast 240 15 x p r.val (by decide) good raw dom r.isLt []).2.symm

private theorem encode (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (history i)=b.basis (History5.historyMap base 225 i)) (i:Fin 10) :
    (run (program d) tape a).basis (history i)=(run (Rolling1588.encodeAt base d 225) [] b).basis (History5.historyMap base 225 i) := by
  rw [(equals d).1]
  exact ArchiveOrdinaryFive.stock_relocated d history _ histInj injected a b tape [] agree i

private theorem readback (d:Bool) (raw pre wide out:State) (tape:List Bool)
    (input:∀i,pre.basis (history i)=raw.basis (History5.historyMap base 225 i))
    (stable:∀i,raw.basis (History5.historyMap base 225 i)=wide.basis (History5.historyMap base 225 i))
    (last:∀i,out.basis (history i)=(run (withArchive d) tape pre).basis (history i)) (i:Fin 10) :
    out.basis (history i)=(run (Rolling1588.encodeAt base d 225) [] wide).basis (History5.historyMap base 225 i) := by
  apply (last i).trans
  rw [withArchive,run_append,run_take]
  have off:∀q:Fin 10,history q∉ArchiveBoundary240.rawPortsList:=by decide +kernel
  rw [run_preserves_outside (archiveLoad240 d) _ _ _ (fun h=>(off i) (List.mem_toFinset.mp (ArchiveBoundary240.load_cover d h)))]
  exact encode d pre wide tape (fun j=>(input j).trans (stable j)) i

theorem result (d:Bool) (raw s:State) (m:List Bool) (x p:Nat) (good:Bounds x p) (dom:Domain 240 x p raw)
    (input:∀i,(run (routed idx 0 1) m s).basis (history i)=raw.basis (History5.historyMap base 225 i)) :
    ∀i,(run (body idx (withArchive d)) m s).basis (history i)=
      (run (Rolling1588.encodeAt base d 225) [] (run (span 240 15) [] raw)).basis (History5.historyMap base 225 i) := by
  exact readback d raw (run (routed idx 0 1) m s) (run (span 240 15) [] raw)
    _ _ input (pastInput x p good raw dom) (fun i=>kept idx _ m s _ (old i))
end ECDSAAdd.Entrant.StairPacket.Ordinary240Exit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary255Exit
open Arithmetic MappedCompressed IntegerPacket Partial WideReference NativePack255
set_option maxRecDepth 25000
set_option maxHeartbeats 2800000
attribute [local irreducible] run body routed measurementCount

private theorem bins:∀i:Fin 10,∃r:Fin 255,(History5.historyMap base 240) i=base r.val ∨ (History5.historyMap base 240) i=base (1028+r.val) := by decide +kernel

private theorem old:∀i:Fin 10,oldRange (start idx+1) (windowNet idx (history i)) := by decide +kernel

private theorem injected:Function.Injective (History5.historyMap base 240):=by decide +kernel

private theorem kept (j:Fin 23) (admin:Program) (m:List Bool) (s:State) (q:Wire)
    (early:oldRange (start j+1) (windowNet j q)) :
    (run (body j admin) m s).basis q=
      (run admin (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m s)).basis q := by
  simp only [body,run_append,run_take]
  exact route_outside j 1 14 (by decide) q (old_clear (by decide) early) _ _

private theorem pastInput (x p:Nat) (good:Bounds x p) (raw:State) (dom:Domain 255 x p raw) (i:Fin 10) :
    raw.basis (History5.historyMap base 240 i)=(run (span 255 15) [] raw).basis (History5.historyMap base 240 i) := by
  obtain ⟨r,h|h⟩:=bins i
  · rw [h];exact (preservePast 255 15 x p r.val (by decide) good raw dom r.isLt []).1.symm
  · rw [h];exact (preservePast 255 15 x p r.val (by decide) good raw dom r.isLt []).2.symm

private theorem encode (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (history i)=b.basis (History5.historyMap base 240 i)) (i:Fin 10) :
    (run (program d) tape a).basis (history i)=(run (Rolling1588.encodeAt base d 240) [] b).basis (History5.historyMap base 240 i) := by
  rw [(equals d).1]
  exact ArchiveOrdinaryFive.stock_relocated d history _ histInj injected a b tape [] agree i

private theorem readback (d:Bool) (raw pre wide out:State) (tape:List Bool)
    (input:∀i,pre.basis (history i)=raw.basis (History5.historyMap base 240 i))
    (stable:∀i,raw.basis (History5.historyMap base 240 i)=wide.basis (History5.historyMap base 240 i))
    (last:∀i,out.basis (history i)=(run (withArchive d) tape pre).basis (history i)) (i:Fin 10) :
    out.basis (history i)=(run (Rolling1588.encodeAt base d 240) [] wide).basis (History5.historyMap base 240 i) := by
  apply (last i).trans
  rw [withArchive,run_append,run_take]
  have off:∀q:Fin 10,history q∉ArchiveBoundary255.rawPortsList:=by decide +kernel
  rw [run_preserves_outside (archiveLoad255 d) _ _ _ (fun h=>(off i) (List.mem_toFinset.mp (ArchiveBoundary255.load_cover d h)))]
  exact encode d pre wide tape (fun j=>(input j).trans (stable j)) i

theorem result (d:Bool) (raw s:State) (m:List Bool) (x p:Nat) (good:Bounds x p) (dom:Domain 255 x p raw)
    (input:∀i,(run (routed idx 0 1) m s).basis (history i)=raw.basis (History5.historyMap base 240 i)) :
    ∀i,(run (body idx (withArchive d)) m s).basis (history i)=
      (run (Rolling1588.encodeAt base d 240) [] (run (span 255 15) [] raw)).basis (History5.historyMap base 240 i) := by
  exact readback d raw (run (routed idx 0 1) m s) (run (span 255 15) [] raw)
    _ _ input (pastInput x p good raw dom) (fun i=>kept idx _ m s _ (old i))
end ECDSAAdd.Entrant.StairPacket.Ordinary255Exit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary270Terminal
open Arithmetic MappedCompressed NativePack270 ArchivePortAction ArchiveBoundary270 ParkEndpoint CodecBitSliceVerify
set_option maxRecDepth 40000
set_option maxHeartbeats 3800000
attribute [local irreducible] run
def newBank := (List.range' 260 10).flatMap (fun r=>[OB5.sig 270 (base r), OB5.sig 270 (base (1028+r))])
def ordinary := (List.finRange 10).map history
def zeros:=List.range' 1556 134++dst

theorem basis (d:Bool) (raw payload:State) (m n:List Bool)
    (row:Nat)
    (clear:∀q∈zeros,raw.basis (OB5.sig 270 q)=false)
    (frame:Frame codePorts (code d) row (run (Partial.archiveLoad270 d) n
      (run (program d) m (stash payload (pullState (OB5.sig 270) raw))))) :
    let out:=run (Partial.archiveLoad270 d) n (run (program d) m (stash payload (pullState (OB5.sig 270) raw)))
    let wide:=run (Rolling1588.encodeAt base d 255) [] raw
    ∀q∉newBank,out.basis q=wide.basis (OB5.sig 270 q) := by
  let inp:=stash payload (pullState (OB5.sig 270) raw)
  let mid:=run (program d) m inp
  let wide:=run (Rolling1588.encodeAt base d 255) [] raw
  let coords:=History5.historyMap base 255
  have geom:∀i:Fin 10,history i∉dst ∧ OB5.sig 270 (history i)=coords i ∧ history i∉rawPortsList := by dsimp only [coords];decide +kernel
  have agree (i:Fin 10):inp.basis (history i)=raw.basis (coords i):=by
    simp only [inp,stash,if_neg (geom i).1,pullState,(geom i).2.1]
  have injected:Function.Injective coords:=by dsimp only [coords];decide +kernel
  have keep (q:Wire) (no:q∉ordinary) : wide.basis (OB5.sig 270 q)=raw.basis (OB5.sig 270 q) := by
    have cover:wires (Rolling1588.encodeAt base d 255) ⊆ ((List.finRange 10).map coords).toFinset:=by dsimp only [coords];cases d <;> decide +kernel
    apply run_preserves_outside
    intro h
    obtain ⟨i,_,e⟩:=List.mem_map.mp (List.mem_toFinset.mp (cover h))
    have e':OB5.sig 270 (history i)=OB5.sig 270 q:=(geom i).2.1.trans e
    have unique:history i=q:=by simpa only [OB5.sig_invol 270 (by decide)] using congrArg (OB5.sig 270) e'
    exact no (List.mem_map.mpr ⟨i,List.mem_finRange i,unique⟩)
  dsimp only
  intro q outside
  by_cases normal:q∈ordinary
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp normal
    rw [run_preserves_outside (Partial.archiveLoad270 d) _ _ _ (fun h=>(geom i).2.2 (List.mem_toFinset.mp (load_cover d h))), (geom i).2.1]
    have encoded:=ArchiveOrdinaryFive.stock_relocated d history coords histInj injected inp raw m [] agree i
    rw [←(equals d).1] at encoded
    exact encoded
  rw [keep q normal]
  by_cases touched:q∈rawPortsList
  · have mask:∀q∈rawPortsList,q∈newBank ∨ (q∈zeros ∧ ∃i:Fin 157,16≤ i.val ∧ codePorts i=q) := by decide +kernel
    obtain ⟨blank,i,hi,slot⟩:=(mask q touched).resolve_left outside
    rw [clear q blank,←slot,frame,archive_blank _ _ hi,Nat.zero_testBit]
  · have no:q∉wires (Partial.archiveLoad270 d):=fun h=>touched (List.mem_toFinset.mp (load_cover d h))
    have mask:∀q∈dst,q∈rawPortsList:=by decide +kernel
    have notDst:q∉dst:=fun h=>touched (mask q h)
    rw [run_preserves_outside _ _ _ _ no]
    exact (NativePack270.outside d q (fun i e=>normal (List.mem_map.mpr ⟨i,List.mem_finRange i,e.symm⟩)) _ _).trans
      (by simp only [stash,if_neg notDst,pullState])
end ECDSAAdd.Entrant.StairPacket.Ordinary270Terminal

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockBaseline
open Arithmetic MappedCompressed Secp256k1 WideReference StockGroups StockArchiveReference
open StairArchiveNativeRows CodecBitSliceVerify ArchiveStockSuffix
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
attribute [local irreducible] run span WideReference.canonical
def packet (i:StockGroups.Group):Nat:=225+15*((i.val-2)/3)
def high (i:StockGroups.Group):Bool:=decide ((i.val-2)%3=1)
theorem chart:∀i∈StockGroups.packed,StockGroups.start i=StockArchiveTruth.tile (packet i) (high i) ∧
    packet i∈[225,240,255] ∧ 225≤packet i ∧ packet i+15≤271:=by decide +kernel
theorem phase_batch (d:Bool) (seq:List StockGroups.Group) (s:State):(run (StockGroups.batch d seq) [] s).phase=s.phase:=by
  induction seq generalizing s with
  | nil=>simp only [StockGroups.batch,List.flatMap_nil,run]
  | cons h t ih=>
    change (run (StockGroups.one d h++StockGroups.batch d t) [] s).phase=_
    rw [run_append,run_take,List.drop_nil,ih]
    exact Rolling1588.codeEncodeAt_zero_phase d (StockGroups.slot h)
      (History5.historyMap_injective base base_pool_nodup (StockGroups.start h) (by unfold StockGroups.start;omega)) s
theorem receipt (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (dom:Domain 225 x p s)
    (i:StockGroups.Group) (active:i∈StockGroups.packed) (row:Nat) (lim:row<63145) (truth:ArchiveStockRows.Chronology (packet i) x p row) (j:Fin 10):
    let raw:=run (span 225 46) [] s
    (run (StockGroups.batch d StockGroups.all) [] raw).basis (StockGroups.slot i j)=(get (storage (native d (high i))) j).testBit row:=by
  have ⟨shape,_,lo,hi⟩:=chart i active
  let raw:=run (span 225 46) [] s
  have obs:=StockArchiveTruth.native_byte x p good s dom (packet i) lo hi row lim truth d (high i) []
  have bit:=obs.2 j
  change (run (StockGroups.batch d StockGroups.all) [] raw).basis (StockGroups.slot i j)=_
  rw [isolated d StockGroups.all allNodup raw i (inAll i) (StockGroups.slot i j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)]
  change (run (Rolling1588.codeEncodeAt d (History5.historyMap base (StockGroups.start i))) [] raw).basis (History5.historyMap base (StockGroups.start i) j)=_
  rwa [shape]

theorem from_final (d:Bool) (x:Nat) (a:State) (results:ArchiveStockRows.Final d x p a)
    (i:StockGroups.Group) (active:i∈StockGroups.packed):∃row<63145,ArchiveStockRows.Chronology (packet i) x p row:=by
  have which:=(chart i active).2.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at which
  rcases which with h|h|h
  · obtain ⟨r,l,t,_⟩:=results.first;exact ⟨r,l,h ▸ t⟩
  · obtain ⟨r,l,t,_⟩:=results.middle;exact ⟨r,l,h ▸ t⟩
  · obtain ⟨r,l,t,_⟩:=results.last;exact ⟨r,l,h ▸ t⟩

theorem comparison (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 s.basis) (results:ArchiveStockRows.Final d x p a):
    Same (run (Rolling1588TickGap.forward d 225 46) m (pullState (OB5.sig 224) s)) (common d s):=by
  let raw:=run (span 225 46) [] s
  have stock:=StockDelayed.window d x good.nonzero good.small 225 46 (by decide) (by decide) s m stage
  change run (Rolling1588TickGap.forward d 225 46) m (pullState (OB5.sig 224) s)=pullState (OB5.sig 270) (run (StockDelayed.packs d 225 46) [] raw) at stock
  rw [stock,stockEq,common,ordinaryEq]
  refine ⟨(phase_batch d StockGroups.all raw).trans (phase_batch d StockGroups.plain raw).symm,?_⟩
  intro q safe
  let y:=OB5.sig 270 q
  change (run (StockGroups.batch d StockGroups.all) [] raw).basis y=(if y∈holes then false else (run (StockGroups.batch d StockGroups.plain) [] raw).basis y)
  have away:OB5.sig 270 y∉archives:=by simpa only [y,OB5.sig_invol 270 (by decide)] using safe
  by_cases old:∃i∈StockGroups.packed,y∈StockGroups.ports i
  · obtain ⟨i,used,inside⟩:=old
    obtain ⟨j,_,atSite⟩:=Finset.mem_image.mp inside
    have hs:=StockGroups.sparse i used j
    rcases hs with ⟨blank,hit⟩|covered
    · rw [←atSite,if_pos hit]
      obtain ⟨row,lim,history⟩:=from_final d x a results i used
      have dom:=WideReference.initial 225 x p (by decide) d s stage
      have bit:=receipt d x good s dom i used row lim history j
      have cleared (n:Nat) (ok:n=5 ∨ n=9):CodecBitSliceVerify.get (storage (native d (high i))) n=0:=by rcases ok with rfl|rfl <;> rfl
      exact bit.trans ((congrArg (fun a:Nat=>a.testBit row) (cleared j (by rcases blank with rfl|rfl <;> decide))).trans (Nat.zero_testBit row))
    · exact (away (atSite ▸ covered)).elim
  · have nh:y∉holes:=by
      intro h;obtain ⟨i,used,j,e⟩:=StockGroups.holeSlot y h
      exact old ⟨i,used,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm⟩⟩
    rw [if_neg nh]
    by_cases saved:∃i∈StockGroups.plain,y∈StockGroups.ports i
    · obtain ⟨i,mem,h⟩:=saved
      exact (isolated d StockGroups.all allNodup raw i (inAll i) y h).trans (isolated d StockGroups.plain plainNodup raw i mem y h).symm
    · have off(i:StockGroups.Group):y∉StockGroups.ports i:=by
        intro h;rcases StockGroups.split i with m|m
        · exact saved ⟨i,m,h⟩
        · exact old ⟨i,m,h⟩
      exact (StockGroups.outside d StockGroups.all raw y (fun i _=>off i)).trans (StockGroups.outside d StockGroups.plain raw y (fun i _=>off i)).symm
end ECDSAAdd.Entrant.StairPacket.StockBaseline

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldHistory
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairField2V3Seg
attribute [local irreducible] run wires rawCol CodecBitSliceVerify.get SkywalkTrace.next
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1400
set_option maxHeartbeats 400000

/-- Identify the 20 row columns with real raw field history at a ten-cell suffix. -/
theorem originBits (j x row : Nat) (jb : 5*j+10≤512) (lb : 5≤5*j) (origin : BasisState)
    (tr : TraceOK x origin) (record : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (hi : Bool) (q : Fin 10) :
    origin (History5.historyMap base (5*(j+(if hi then 1 else 0))) q) =
      (rawCol ((if hi then 10 else 0)+q.val)).testBit row := by
  let u : Nat := (if hi then 10 else 0)+q.val
  have ql := q.isLt
  have u20 : u<20 := by cases hi <;> simp [u] <;> omega
  let start := 5*(j+(if hi then 1 else 0))
  let tick := start+q.val/2
  have plus : tick=5*j+u/2 := by cases hi <;> simp [tick,start,u] <;> omega
  have full : (5*j-5)+(5+u/2)=tick := by omega
  have small : tick<512 := by omega
  have bits := StairField2V3Trace.origin_letters x origin tr tick small
  have col := StockArchiveTruth.observedLabel (5*j-5) x ECDSAAdd.p row record ⟨u,u20⟩
  change (rawCol u).testBit row=letterBit (SkywalkTrace.code (WideReference.canonical ((5*j-5)+(5+u/2)) x ECDSAAdd.p)) u at col
  rw [full] at col
  unfold WideReference.canonical at col
  change origin (base (if q.val%2=0 then start+q.val/2 else 1028+start+q.val/2))=(rawCol u).testBit row
  rw [col]; unfold letterBit
  have parity : u%2=q.val%2 := by cases hi <;> simp [u] <;> omega
  rw [parity]
  split
  · exact bits.1
  · simpa only [tick,Nat.add_assoc] using bits.2

/-- One complete stock packet, including the two discarded zero slots, at any mixed field cut. -/
theorem cut_byte (cut j x row : Nat) (positive : 1≤j) (bound : j+2≤102)
    (rowBound : row<63145) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (tr : TraceOK x origin) (record : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (X Y : Fp) (s : State) (fr : CutFrame cut origin X Y s) (hi : Bool) (q : Fin 10) :
    let k := j+(if hi then 1 else 0)
    s.basis (History5.historyMap base (5*k) q) =
      (CodecBitSliceVerify.get (storage (native (decide (cut≤k)) hi)) q).testBit row := by
  let k := j+(if hi then 1 else 0)
  have boundK : k<102 := by cases hi <;> simp [k] <;> omega
  have posK : k≠0 := by cases hi <;> simp [k] <;> omega
  change s.basis (History5.historyMap base (5*k) q) = (CodecBitSliceVerify.get (storage (native (decide (cut≤k)) hi)) q).testBit row
  obtain ⟨raw,_,pair,eq⟩ := fr
  rw [eq,allEncodeCut_factor base cut base_pool_nodup 102 k (by decide) boundK raw]
  rw [run_preserves_outside _ _ _ _ (StairField2V3LastRecXPar.other_away base cut k
    base_pool_nodup 102 (by decide) boundK q),encodeGroup,if_neg posK,encodeAt]
  apply (StockArchiveByte.run_byte (decide (cut≤k)) hi row rowBound (History5.historyMap base (5*k))
    (History5.historyMap_injective base base_pool_nodup _ (by omega)) raw [] ?_).2 q
  intro i
  have away := History5.history_words_away base (base 2409) ctx.hn (ctx.hp _ (by simp))
    (5*k) (by omega) i
  rw [pair.2.2 _ away.1 away.2]
  exact originBits j x row (by omega) (by omega) origin tr record hi i
end ECDSAAdd.Entrant.StairPacket.WindowFieldHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
def applyAff (s : State) : Aff→State
  | .x w => flip w true s
  | .cx c w => flip w (s.basis c) s
def lawful (t : Wire) : Aff→Prop
  | .x w => w≠t
  | .cx c w => c≠w ∧ c≠t ∧ w≠t
def effect (p : List Aff) (s : State) := p.foldl applyAff s
theorem aff_run (p : List Aff) (m : List Bool) (s : State) : run (affine p) m s = effect p s := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    cases g with
    | x w =>
      simp only [affine,List.map_cons,gate,run,effect,List.foldl_cons,applyAff] at ih ⊢
      rw [←ih]; congr 1; apply congrArg₂ State.mk rfl; funext q
      by_cases e : q=w <;> simp [flip,writeBit,e]
    | cx c w => exact ih _
private theorem self (g : Aff) (t : Wire) (h : lawful t g) (s : State) : applyAff (applyAff s g) g=s := by
  cases g with
  | x w => simp only [applyAff,flip_twice,Bool.xor_self,flip_zero]
  | cx c w => simp only [applyAff,at_other _ _ _ _ h.1,flip_twice,Bool.xor_self,flip_zero]
private theorem commute (g : Aff) (t : Wire) (h : lawful t g) (s : State) (v : Bool) :
    applyAff (flip t v s) g=flip t v (applyAff s g) := by
  cases g with
  | x w => exact flip_comm s w t _ _ h
  | cx c w =>
    rw [applyAff,at_other _ _ _ _ h.2.1]
    exact flip_comm s w t _ _ h.2.2
theorem undo (p : List Aff) (t : Wire) (h : ∀g∈p,lawful t g) (s : State) (v : Bool) :
    effect p.reverse (flip t v (effect p s))=flip t v s := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    have gOK := h g (by simp)
    have tail := ih (fun k hk=>h k (List.mem_cons_of_mem _ hk)) (applyAff s g)
    change effect (g::p).reverse (flip t v (effect p (applyAff s g)))=_
    rw [List.reverse_cons,effect,List.foldl_append]
    change applyAff (effect p.reverse (flip t v (effect p (applyAff s g)))) g=_
    rw [tail,commute _ _ gOK,self _ _ gOK]

inductive Formula where
  | var (q : Wire)
  | one
  | xor (a b : Formula)
  | and (a b : Formula)
def Formula.eval (w : BasisState) : Formula→Bool
  | .var q => w q
  | .one => true
  | .xor a b => (a.eval w ^^ b.eval w)
  | .and a b => a.eval w && b.eval w

def symbolic (r : Wire→Formula) : Aff→(Wire→Formula)
  | .x w => Function.update r w (.xor (r w) .one)
  | .cx c w => Function.update r w (.xor (r w) (r c))
theorem symbol_step (g : Aff) (r : Wire→Formula) (s : State) (base : BasisState)
    (frame : ∀q,s.basis q=(r q).eval base) (q : Wire) :
    (applyAff s g).basis q=((symbolic r g) q).eval base := by
  cases g with
  | x w =>
    by_cases e : q=w
    · subst q; simp [applyAff,symbolic,flip,writeBit,Formula.eval,frame]
    · simp [applyAff,symbolic,flip,writeBit,e,frame]
  | cx c w =>
    by_cases e : q=w
    · subst q; simp [applyAff,symbolic,flip,writeBit,Formula.eval,frame]
    · simp [applyAff,symbolic,flip,writeBit,e,frame]
theorem symbol_eval (p : List Aff) (s : State) (q : Wire) :
    (effect p s).basis q=((p.foldl symbolic Formula.var) q).eval s.basis := by
  have gen (ls : List Aff) (a : State) (r : Wire→Formula) (h : ∀i,a.basis i=(r i).eval s.basis) :
      ∀i,(effect ls a).basis i=((ls.foldl symbolic r) i).eval s.basis := by
    induction ls generalizing a r with
    | nil => exact h
    | cons g ls ih => exact ih _ _ (symbol_step g r a s.basis h)
  exact gen p s _ (fun _=>rfl) q
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityRelease
open Arithmetic Secp256k1 Challenge Baselines

def entry : Challenge.Entry := fun C => normalizeProgram (WindowParityCaller.program C)
def bounds : Challenge.Bounds := ⟨2153619,1512390,1543,51930861⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowParityCaller.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowParityCaller.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowParityCaller.metrics C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1512390
    rw [normalize_measurements]
    exact (WindowParityCaller.metrics C).2.1
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1543
    rw [normalize_qubits]
    exact WindowParityCaller.width C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 51930861
    rw [normalize_slots]
    exact (WindowParityCaller.metrics C).2.2

end ECDSAAdd.Entrant.StairPacket.WindowParityRelease

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open Arithmetic MappedCompressed Secp256k1 OB5 DirectSkywalk Rolling1588.Integer
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588.reverse

theorem sig_pool (i : Nat) (hi : i≤511) (q : Wire) (hq : q∈skywalkPoolWires base) :
    sig i q∈skywalkPoolWires base := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
  have b := List.mem_range'_1.mp hj
  rw [sig_base i j hi]
  apply OB5.base_pool
  split <;> omega

theorem host_pool (q : Wire) (hq : q∈skywalkPoolWires base) :
    Rolling1588Lifetime.phaseHost q∈skywalkPoolWires base := by
  simp only [Rolling1588Lifetime.phaseHost,Equiv.trans_apply,Equiv.swap_apply_def]
  split_ifs <;> first | assumption | exact OB5.base_pool _ (by decide)

theorem raw511 (hn : (skywalkSharedWires base).Nodup) (d : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (Rolling1588TickGap.stackForward d) m s = pullState (sig 511) (run (regularForward base d 1 511) m s) := by
  rw [Rolling1588TickGap.stackForward_run_eq d x hx0 hx s m first,
    ←Rolling1588.Integer.stackForward_eq_packets,
    Rolling1588.Integer.stackForwardT_run d hn StackOB5.historyAbove x hx0 hx s m first,
    Rolling1588.Integer.forward_run d x hx0 hx s m first]

theorem reverse_input (x y : Nat) (hx0 : 0<x) (hx : x<p) (hn : (skywalkSharedWires base).Nodup)
    (s v : State) (input : SkywalkArithmeticInput base x y s.basis)
    (matchP : v.phase=(run (Rolling1588TickGap.firstPhase false) [] s).phase)
    (matchB : ∀q∈skywalkPoolWires base,v.basis q=(run (Rolling1588TickGap.firstPhase false) [] s).basis q)
    (m : List Bool) :
    let one := run (FrontierEntry1591Native.forward base) [] s
    ∃ raw : State, run (skywalkArithmeticClear base ++ head) m v = pullState (sig 505) raw ∧
      ∀q∈skywalkPoolWires base,raw.basis q=(run (regularForward base false 1 505) [] one).basis q := by
  dsimp only
  obtain ⟨one,eo⟩ : ∃ u : State,run (FrontierEntry1591Native.forward base) [] s=u := ⟨_,rfl⟩
  rw [eo]
  have st := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s [] input
  rw [eo] at st
  obtain ⟨ref,er⟩ : ∃ z : State,run (regularForward base false 1 511) [] one=z := ⟨_,rfl⟩
  let C := skywalkArithmeticClear base
  let w := run C [] v
  have orig : run (Rolling1588TickGap.firstPhase false) [] s = run C [] (pullState (sig 511) ref) := by
    simp only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,run_append,List.take_nil,List.drop_nil]
    rw [eo,raw511 hn false x hx0 hx _ [] st,er]
  rw [orig] at matchP matchB
  have same := pool_run_agrees C (skywalkPoolWires base).toFinset EntryFuse.clear_pool5 [] v _ matchP
    (fun q hq => matchB q (List.mem_toFinset.mp hq))
  have twice : run C [] (run C [] (pullState (sig 511) ref))=pullState (sig 511) ref := by
    exact skywalkTerminalClear_twice (base 511) (base 512) (base 770) (arith_clear_gates base hn) _ [] []
  rw [twice] at same
  let v5 := pullState (sig 511) w
  have eq5 : w=pullState (sig 511) v5 := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg w.basis (sig_invol 511 (by decide) q).symm
  have eqb (q : Wire) (hq : q∈skywalkPoolWires base) : v5.basis q=ref.basis q := by
    have r := same.2 _ (List.mem_toFinset.mpr (sig_pool 511 (by decide) q hq))
    simpa only [pullState,sig_invol 511 (by decide)] using r
  have noM : measurementCount (skywalkArithmeticClear base)=0 := by simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  rw [run_append,noM,List.take_zero,List.drop_zero]
  change ∃ raw,run head m w=pullState (sig 505) raw ∧ _
  rw [eq5]
  rw [←er] at eqb
  exact after_head x hx0 hx one st [] v5 eqb m

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.StairPacket.Logical225Exit
open Arithmetic MappedCompressed WideReference NativePack225
set_option maxRecDepth 25000
set_option maxHeartbeats 2600000
attribute [local irreducible] run body
def newBank : List Wire := []
def oldFive := (List.finRange 10).map (History5.historyMap base 220)

theorem window (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,(historyState.basis (history i))=
      (run (Rolling1588.encodeAt base d 220) [] (run (span 225 15) [] raw)).basis (History5.historyMap base 220 i))
    (q:Wire) (ordinarySite:q∉newBank) :
    (endRaw 225 raw historyState).basis q=
      (run (Rolling1588.encodeAt base d 220) [] (run (span 225 15) [] raw)).basis q := by
  have locations : ∀q∈sites 225,q∈oldFive ∨ q∈newBank := by decide +kernel
  have port : ∀i:Fin 10,history i=History5.historyMap base 220 i := by decide +kernel
  have own:∀q∈oldFive,q∈sites 225:=by decide +kernel
  by_cases inside:q∈sites 225
  · have old: q∈oldFive:=((locations q inside).resolve_right ordinarySite)
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp old
    rw [endRaw_inside _ _ _ fixed225 _ inside,←port i]
    exact (ordinaryBits i).trans (congrArg (run (Rolling1588.encodeAt base d 220) [] (run (span 225 15) [] raw)).basis (port i).symm)
  · have cover:wires (Rolling1588.encodeAt base d 220)⊆oldFive.toFinset := by cases d <;> decide +kernel
    rw [endRaw_outside _ (by decide) _ _ fixed225 _ inside]
    exact (run_preserves_outside _ _ _ q (fun used=>inside (own q (List.mem_toFinset.mp (cover used))))).symm
end ECDSAAdd.Entrant.StairPacket.Logical225Exit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Logical240Exit
open Arithmetic MappedCompressed WideReference NativePack240
set_option maxRecDepth 25000
set_option maxHeartbeats 2600000
attribute [local irreducible] run body
def newBank : List Wire := (List.range' 230 10).flatMap (fun r=>[base r,base (1028+r)])
def oldFive := (List.finRange 10).map (History5.historyMap base 225)

theorem window (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,(historyState.basis (history i))=
      (run (Rolling1588.encodeAt base d 225) [] (run (span 240 15) [] raw)).basis (History5.historyMap base 225 i))
    (q:Wire) (ordinarySite:q∉newBank) :
    (endRaw 240 raw historyState).basis q=
      (run (Rolling1588.encodeAt base d 225) [] (run (span 240 15) [] raw)).basis q := by
  have locations : ∀q∈sites 240,q∈oldFive ∨ q∈newBank := by decide +kernel
  have port : ∀i:Fin 10,history i=History5.historyMap base 225 i := by decide +kernel
  have own:∀q∈oldFive,q∈sites 240:=by decide +kernel
  by_cases inside:q∈sites 240
  · have old: q∈oldFive:=((locations q inside).resolve_right ordinarySite)
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp old
    rw [endRaw_inside _ _ _ fixed240 _ inside,←port i]
    exact (ordinaryBits i).trans (congrArg (run (Rolling1588.encodeAt base d 225) [] (run (span 240 15) [] raw)).basis (port i).symm)
  · have cover:wires (Rolling1588.encodeAt base d 225)⊆oldFive.toFinset := by cases d <;> decide +kernel
    rw [endRaw_outside _ (by decide) _ _ fixed240 _ inside]
    exact (run_preserves_outside _ _ _ q (fun used=>inside (own q (List.mem_toFinset.mp (cover used))))).symm
end ECDSAAdd.Entrant.StairPacket.Logical240Exit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Logical255Exit
open Arithmetic MappedCompressed WideReference NativePack255
set_option maxRecDepth 25000
set_option maxHeartbeats 2600000
attribute [local irreducible] run body
def newBank : List Wire := (List.range' 245 10).flatMap (fun r=>[base r,base (1028+r)])
def oldFive := (List.finRange 10).map (History5.historyMap base 240)

theorem window (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,(historyState.basis (history i))=
      (run (Rolling1588.encodeAt base d 240) [] (run (span 255 15) [] raw)).basis (History5.historyMap base 240 i))
    (q:Wire) (ordinarySite:q∉newBank) :
    (endRaw 255 raw historyState).basis q=
      (run (Rolling1588.encodeAt base d 240) [] (run (span 255 15) [] raw)).basis q := by
  have locations : ∀q∈sites 255,q∈oldFive ∨ q∈newBank := by decide +kernel
  have port : ∀i:Fin 10,history i=History5.historyMap base 240 i := by decide +kernel
  have own:∀q∈oldFive,q∈sites 255:=by decide +kernel
  by_cases inside:q∈sites 255
  · have old: q∈oldFive:=((locations q inside).resolve_right ordinarySite)
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp old
    rw [endRaw_inside _ _ _ fixed255 _ inside,←port i]
    exact (ordinaryBits i).trans (congrArg (run (Rolling1588.encodeAt base d 240) [] (run (span 255 15) [] raw)).basis (port i).symm)
  · have cover:wires (Rolling1588.encodeAt base d 240)⊆oldFive.toFinset := by cases d <;> decide +kernel
    rw [endRaw_outside _ (by decide) _ _ fixed255 _ inside]
    exact (run_preserves_outside _ _ _ q (fun used=>inside (own q (List.mem_toFinset.mp (cover used))))).symm
end ECDSAAdd.Entrant.StairPacket.Logical255Exit

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary270Native
open Arithmetic IntegerPacket MappedCompressed Secp256k1 WideReference SkywalkRails NativePack270 Partial ParkEndpoint StockWindowTicket
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool)
    (pre:At270 d x p raw s g sg pg ps) :
    ArchiveHistoryCompare.Except Ordinary270Terminal.newBank (run (lastWindow d) m s)
      (pullState (OB5.sig 270) (run (Rolling1588.encodeAt base d 255) [] (run EndTick.canonical [] raw))) := by
  obtain ⟨ref,stage,read,hist,spare,spaces⟩:=terminal d x raw pre.domain
  let z:=unsigned 270 x p
  let v:=run EndTick.canonical [] raw
  let p1:=m.drop (measurementCount park270)
  let p2:=p1.drop (measurementCount portal270Inv)
  let p3:=p2.drop (measurementCount EndTick.physP)
  let p4:=p3.drop (measurementCount (program d))
  have lim:min z.u z.v<2^121:=true_small x p 270 (lt_trans good.small good.cap) good.cap (by decide)
  have mode:farAt 121 270 x p=(3*2^137≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have first:=parked_release z lim raw s m p1 g sg (readInput 270 x p raw g sg pre.input)
    (by simpa only [mode] using pre.cut) (empty_from_cut _ _ _ _ _ pre.cut spaces)
  have tick:=EndTick.physical d x good.nonzero good.small raw ref s read stage hist spare p2
  let loaded:=run (archiveLoad270 d) p4 (run (program d) p3 (stash s (pullState (OB5.sig 270) v)))
  have actual:run (lastWindow d) m s=loaded := by
    simp only [lastWindow,endSlice,run_append,run_take]
    change run (archiveLoad270 d) p4 (run (program d) p3 (run EndTick.physP p2 (run portal270Inv p1 (run park270 m s))))=_
    rw [first.1,tick.1]
  obtain ⟨row,_,_,frame⟩:=(step270 d x good s m ⟨raw,g,sg,pg,ps,pre⟩).2.1.last
  rw [actual] at frame
  have zeros (q:Wire) (h:q∈Ordinary270Terminal.zeros) : v.basis (OB5.sig 270 q)=false:=by
    rcases List.mem_append.mp h with carryLane|tag
    · have table:∀q∈List.range' 1556 134,∃k:Fin 134,OB5.sig 270 q=1556+k.val:=by decide +kernel
      obtain ⟨k,eq⟩:=table _ carryLane
      rw [eq];exact (EndTick.after_cells d x good.nonzero good.small raw ref read stage).2 k
    · have coords:∀q∈dst,OB5.sig 270 q=OB5.sig 269 q := by decide +kernel
      have nocell:=EndTick.spared q tag
      have cover:=W.compactSkywalkTick_support base 270 (by decide) base_pool_nodup
      have no:OB5.sig 270 q∉wires EndTick.canonical:=fun used=>nocell (List.mem_toFinset.mp (cover used))
      exact (run_preserves_outside _ _ _ _ no).trans (by rw [coords q tag];exact spaces q tag)
  rw [actual]
  exact Ordinary270Terminal.basis d v s p3 p4 row zeros frame
end ECDSAAdd.Entrant.StairPacket.Ordinary270Native

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanks
open Arithmetic MappedCompressed Secp256k1 WideReference StockBaseline ArchiveStockSuffix
open ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 100000
attribute [local irreducible] run span
abbrev Bank := Fin 3
def ports (b:Bank):Ports:=if b=0 then ArchiveBoundary240.codePorts else if b=1 then ArchiveBoundary255.codePorts else ArchiveBoundary270.codePorts
def siteAt (b:Bank) (j:Fin 16):Wire:=ports b ⟨j.val,by omega⟩
def group (b:Bank) (j:Fin 16):StockGroups.Group:=⟨2+3*b.val+j.val/8,by omega⟩
def index (j:Fin 16):Fin 10:=⟨if j.val%8<5 then j.val%8 else j.val%8+1,by split <;> omega⟩
def tick (b:Bank):Nat:=225+15*b.val
theorem chart:∀(b:Bank)(j:Fin 16),
    siteAt b j=OB5.sig 270 (StockGroups.slot (group b j) (index j)) ∧
    packet (group b j)=tick b ∧ group b j∈StockGroups.packed ∧ siteAt b j∈archives:=by decide +kernel
theorem byte:∀(d:Bool)(b:Bank)(j:Fin 16),get (storage (native d (high (group b j)))) (index j)=get (StairArchiveNativeCut.canonical d d) j:=by decide +kernel

def nativeAt (d:Bool) (b:Bank) (r:Nat) (s:State):Prop:=∀j:Fin 16,s.basis (siteAt b j)=(get (StairArchiveNativeCut.canonical d d) j).testBit r
section
attribute [local irreducible] StockGroups.batch StockGroups.slot StockDelayed.packs
  Rolling1588TickGap.forward StockGroups.all siteAt group index tick native storage CodecBitSliceVerify.get
  StairArchiveNativeCut.canonical ArchiveStockRows.Chronology
theorem stock_state (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 s.basis):
    run (Rolling1588TickGap.forward d 225 46) m (pullState (OB5.sig 224) s)=
    pullState (OB5.sig 270) (run (StockGroups.batch d StockGroups.all) [] (run (span 225 46) [] s)):=by
  rw [←StockGroups.stockEq]
  exact StockDelayed.window d x good.nonzero good.small 225 46 (by decide) (by decide) s m stage

theorem readback (z:State) (q w:Wire) (eq:q=OB5.sig 270 w):
    (pullState (OB5.sig 270) z).basis q=z.basis w:=by
  change z.basis (OB5.sig 270 q)=z.basis w
  rw [eq,OB5.sig_invol 270 (by decide)]

theorem stored (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 s.basis) (b:Bank) (row:Nat) (lim:row<63145)
    (truth:ArchiveStockRows.Chronology (tick b) x p row):
    nativeAt d b row (run (Rolling1588TickGap.forward d 225 46) m (pullState (OB5.sig 224) s)):=by
  intro j
  obtain ⟨addr,clock,used,_⟩:=chart b j
  have dom:=WideReference.initial 225 x p (by decide) d s stage
  have bit:=receipt d x good s dom (group b j) used row lim (clock ▸ truth) (index j)
  rw [stock_state d x good s m stage,readback _ _ _ addr]
  exact bit.trans (congrArg (fun a:Nat=>a.testBit row) (byte d b j))
end
theorem keptAt (d:Bool) (x:Nat) (a:State) (res:ArchiveStockRows.Final d x p a) (b:Bank):
    ∃row<63145,ArchiveStockRows.Chronology (tick b) x p row ∧ Kept (ports b) d row a:=by
  rcases b with ⟨n,lt⟩
  rcases n with _|n;exact res.first
  rcases n with _|n;exact res.middle
  have eq:n=0:=by omega
  subst n
  obtain ⟨r,l,t,f⟩:=res.last
  exact ⟨r,l,t,fun j=>f ⟨j,by omega⟩⟩

structure Paired (d:Bool) (x:Nat) (a s:State) (rows:Bank→Nat):Prop where
  equality:Same a s
  labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b)
  custom:∀b,Kept (ports b) d (rows b) a
  stock:∀b,nativeAt d b (rows b) s

theorem paired (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 s.basis) (res:ArchiveStockRows.Final d x p a)
    (normalized:Same a (StockArchiveReference.common d s)):
    ∃rows,Paired d x a (run (Rolling1588TickGap.forward d 225 46) m (pullState (OB5.sig 224) s)) rows:=by
  classical
  let rows (b:Bank):Nat:=(keptAt d x a res b).choose
  have facts (b:Bank):= (keptAt d x a res b).choose_spec
  have cmp:=comparison d x good s a m stage res
  exact ⟨rows,⟨⟨normalized.1.trans cmp.1.symm,fun q off=>(normalized.2 q off).trans (cmp.2 q off).symm⟩,
    fun b=>⟨(facts b).1,(facts b).2.1⟩,fun b=>(facts b).2.2,
    fun b=>stored d x good s m stage b (rows b) (facts b).1 (facts b).2.1⟩⟩

theorem Paired.through {d x a s rows} (pair:Paired d x a s rows) (P:Program)
    (off:∀q∈archives,q∉wires P) (m:List Bool):Paired d x (run P m a) (run P m s) rows:=by
  have h:=independent P off m a s pair.equality
  refine ⟨h.1,pair.labels,?_,?_⟩
  · intro b j
    exact (h.2 (siteAt b j) (chart b j).2.2.2).trans (pair.custom b j)
  · intro b j
    exact (run_preserves_outside P m s (siteAt b j) (off _ (chart b j).2.2.2)).trans (pair.stock b j)
end ECDSAAdd.Entrant.StairPacket.StockArchiveBanks

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockBaseline
open Arithmetic MappedCompressed WideReference Secp256k1 StockArchiveReference
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward
theorem forward_phase (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:1 ≤ i) (hi:i+n≤512) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis):
    (run (Rolling1588TickGap.forward d i n) m (pullState (OB5.sig (i-1)) s)).phase=s.phase:=by
  have spec:=Rolling1588TickGap.forward_gen d x good.nonzero good.small n i lo hi s m stage
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have ph:=(Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p i n hp0 good.nonzero odd cap (by norm_num [p]) good.small cop hi s m stage).1
  exact (congrArg State.phase spec).trans ph
theorem common_phase (d:Bool) (x:Nat) (good:Bounds x p) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 225 s.basis):(common d s).phase=s.phase:=by
  have final:=(StockWindowChain.result d x good s [] stage).2.1
  have same:=(comparison d x good s _ [] stage final).1
  exact same.symm.trans (forward_phase d x good 225 46 (by decide) (by decide) s [] stage)
end ECDSAAdd.Entrant.StairPacket.StockBaseline

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairArchiveNativeCut StairArchiveRelease
open WindowFieldMask ArchiveFieldScratch StairField2V3Seg
def wire (q : Wire) := StairArchiveInactive.host (OB5.sig 511 q)
theorem injective : Function.Injective wire :=
  StairArchiveInactive.host.injective.comp (OB5.sig_injective 511 (by decide))
def high (q : Nat) := decide (8≤q)
def lane (q : Nat) : Fin 10 := ⟨if q%8<5 then q%8 else q%8+1,by split <;> omega⟩
def histPort (j q : Nat) := History5.historyMap base (5*(j+(if high q then 1 else 0))) (lane q)
def physical (j : Nat) := ((List.range 16).all (fun q=>fieldPort j q == wire (histPort j q))) &&
  (fieldPort j 16 == base 720) &&
  (List.range' 17 104).all (fun q=>fieldPort j q == wire (base (Placement5.H (8+(q-17)))))
private theorem physical_ok : WindowBankCheck.banks.all physical=true := by decide +kernel
def lookup (l h : Bool) := (List.range 16).all (fun q=>
  CodecBitSliceVerify.get (StairArchiveNativeCut.canonical l h) q == CodecBitSliceVerify.get (storage (native (if high q then h else l) (high q))) (lane q))
private theorem lookup_ok (l h : Bool) : lookup l h=true := by cases l <;> cases h <;> decide +kernel
private theorem upper_zero (l h : Bool) : (List.range' 16 105).all (fun q=>CodecBitSliceVerify.get (StairArchiveNativeCut.canonical l h) q == 0)=true := by
  cases l <;> cases h <;> decide +kernel
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
attribute [local irreducible] run wire StairArchiveNativeCut.canonical StairArchiveRelease.fieldPort CodecBitSliceVerify.get
def boundaryCols (j c : Nat) := StairArchiveNativeCut.canonical (decide (c≤j)) (decide (c≤j+1))

/-- Reading the actual 121-port frame needs agreement only on these observed stock lines.
The extra tag is a separate physical loan, while all 104 arithmetic holes follow from CutFrame. -/
theorem observed (j c x row : Nat) (hj : j∈WindowBankCheck.banks) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (X Y : Fp) (ideal actual : State) (cf : CutFrame c origin X Y (pullState wire ideal))
    (tag : actual.basis (base 720)=false)
    (view : ∀q∈inside j,q≠base 720→actual.basis q=ideal.basis q) :
    frame j row (boundaryCols j c) actual := by
  have geometry := List.all_eq_true.mp physical_ok j hj
  simp only [physical,Bool.and_eq_true,beq_iff_eq] at geometry
  have jBounds : 1≤j ∧ j+2≤102 := by
    simp only [WindowBankCheck.banks,List.mem_cons,List.mem_nil_iff,or_false] at hj; omega
  intro q hq
  have upper := Finset.mem_range.mp hq
  have eq16 := geometry.1.2
  have nd := field_inj j (List.mem_range'_1.mpr (by
      simp only [WindowBankCheck.banks,List.mem_cons,List.mem_nil_iff,or_false] at hj; omega))
  by_cases isTag : q=16
  · subst q
    rw [eq16,tag]
    have zero := beq_iff_eq.mp (List.all_eq_true.mp (upper_zero (decide (c≤j)) (decide (c≤j+1))) 16 (by decide))
    simp [boundaryCols,zero]
  · have off : fieldPort j q ≠ base 720 := fun he=>isTag (nd _ hq 16 (by decide) (he.trans eq16.symm))
    rw [view _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩) off]
    by_cases low : q<16
    · have loc := beq_iff_eq.mp (List.all_eq_true.mp geometry.1.1 q (List.mem_range.mpr low))
      rw [loc]
      have byte := WindowFieldHistory.cut_byte c j x row jBounds.1 jBounds.2 rb origin ctx tr history X Y
        (pullState wire ideal) cf (high q) (lane q)
      change ideal.basis (wire (histPort j q))=_ at byte
      rw [byte]
      have col := beq_iff_eq.mp (List.all_eq_true.mp (lookup_ok (decide (c≤j)) (decide (c≤j+1))) q (List.mem_range.mpr low))
      unfold boundaryCols; rw [col]
      cases high q <;> simp
    · have member : q∈List.range' 17 104 := List.mem_range'_1.mpr ⟨by omega,by omega⟩
      have loc := beq_iff_eq.mp (List.all_eq_true.mp geometry.2 q member)
      rw [loc]
      have k : 8+(q-17)∈ArchiveFieldScratch.indices := List.mem_range'_1.mpr ⟨by omega,by omega⟩
      have clean := ArchiveFieldScratch.clean c origin ctx X Y _ cf _ k
      change ideal.basis (wire (base (Placement5.H (8+(q-17)))))=false at clean
      have zero := beq_iff_eq.mp (List.all_eq_true.mp (upper_zero (decide (c≤j)) (decide (c≤j+1))) q
        (List.mem_range'_1.mpr ⟨by omega,by omega⟩))
      simp only [boundaryCols,zero,clean,Nat.zero_testBit]
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run mcx chain

def productForm (env : Wire→Formula) (last : Wire) : Hops→Formula
  | [] => env last
  | (c,_)::xs => .and (env c) (productForm env last xs)
def predicate (c : Clause) :=
  let e := c.prep.foldl symbolic Formula.var
  Formula.and (.and (e c.a) (e c.b)) (productForm e c.last c.xs)
theorem product_eval (c : Clause) (s : State) : ∀ xs,
    product c.last (effect c.prep s).basis xs=(productForm (c.prep.foldl symbolic Formula.var) c.last xs).eval s.basis := by
  intro xs; induction xs with
  | nil => exact symbol_eval _ _ _
  | cons term xs ih =>
    rcases term with ⟨q,b⟩
    simp only [product,productForm,Formula.eval,symbol_eval,ih]
instance (t : Wire) (g : Aff) : Decidable (lawful t g) := by cases g <;> unfold lawful <;> infer_instance
instance (q j : Wire) (xs : Hops) : Decidable (outside q j xs) := by unfold outside; infer_instance
instance dsafe (last target src : Wire) (xs : Hops) : Decidable (safe last target src xs) := by
  cases xs with
  | nil => unfold safe; infer_instance
  | cons pair tail =>
    obtain ⟨c,b⟩ := pair
    letI := dsafe last target b tail
    unfold safe; infer_instance

theorem valid_clause (c : Clause) (hc : c∈clauses) : Good c.a c.b 17 c.last 16 c.xs ∧ ∀g∈c.prep,lawful 16 g := by
  simp only [clauses,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals constructor
  all_goals first | (constructor <;> decide +kernel) | decide +kernel

theorem body_run (c : Clause) (hc : c∈clauses) (m : List Bool) (s : State) :
    run (body c) m s=flip 16 ((predicate c).eval s.basis) s := by
  obtain ⟨bounded,valid⟩ := valid_clause c hc
  simp only [body,run_append,run_take,aff_run,mcx_run _ _ _ _ _ _ _ _ bounded,undo _ _ valid]
  rw [product_eval,symbol_eval,symbol_eval]
  rfl
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.Stair44DivTerm
open Arithmetic MappedCompressed Secp256k1 OB5 DirectSkywalk Rolling1588.Integer Stair44WalkMap
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588.reverse
  Stair44WalkRun.backward FrontierEntry1591NativeH.inverse FrontierEntry1591Native.forward

private def firstSites := [1026,514,1541,501,1542,500]
private theorem fixed (s : State) (z : ∀j∈firstSites,s.basis (base j)=false) : pullState first s=s := by
  have a := cleanWireRebind id s s _ _ rfl (z 1026 (by decide)) (z 514 (by decide))
  have b := cleanWireRebind _ s s _ _ a (z 1541 (by decide)) (z 501 (by decide))
  exact cleanWireRebind _ s s _ _ b (z 1542 (by decide)) (z 500 (by decide))

private theorem input_zero (x y : Nat) (s : State) (input : SkywalkArithmeticInput base x y s.basis) :
    ∀j∈firstSites,s.basis (base j)=false := by
  have chk : ∀j∈firstSites,base j∈skywalkSharedWires base ∧ base j∉skywalkArithmeticDivisor base ∧
      base j∉skywalkArithmeticNumerator base := by decide +kernel
  intro j hj
  obtain ⟨a,b,c⟩ := chk j hj
  exact input.2.2 _ a b c

private theorem byPool {P : Program} (bound : wires P ⊆ (skywalkPoolWires base).toFinset)
    (t u : State) (bits : ∀q∈skywalkPoolWires base,t.basis q=u.basis q)
    (m : List Bool) : ∀q∈skywalkPoolWires base,(run P m t).basis q=(run P m u).basis q := by
  let v : State := ⟨t.phase,u.basis⟩
  have h := pool_run_agrees P _ bound m t v rfl (fun q hq => bits q (List.mem_toFinset.mp hq))
  intro q hq
  exact (h.2 q (List.mem_toFinset.mpr hq)).trans (congrFun (run_basis_records P v u m m rfl) q)

theorem inverse_end (x y : Nat) (hx : x<p) (hn : (skywalkSharedWires base).Nodup)
    (s logical actual : State) (input : SkywalkArithmeticInput base x y s.basis)
    (eq : pullState first actual=logical)
    (hb : ∀q∈skywalkPoolWires base,logical.basis q=(run (FrontierEntry1591Native.forward base) [] s).basis q)
    (m : List Bool) :
    run (renameProgram first (FrontierEntry1591NativeH.inverse base)) m actual =
      run (FrontierEntry1591NativeH.inverse base) m logical := by
  let I := FrontierEntry1591NativeH.inverse base
  have bd := (FrontierEntry1591NativeH.wires_sub base base_pool_nodup).trans
    (FrontierEntry1591Native.native_pool base base_pool_nodup).2
  have keep := byPool bd logical _ hb m
  have orig := FrontierEntry1591NativeH.inverse_roundtrip base hn x y hx s [] m input
  rw [orig] at keep
  have z (j : Nat) (hj : j∈firstSites) : (run I m logical).basis (base j)=false :=
    (keep _ (OB5.base_pool _ (by simp [firstSites] at hj; omega))).trans (input_zero x y s input _ hj)
  apply MappedCompressed.pullState_perm_injective first
  rw [run_rename _ first.injective,eq]
  exact (fixed _ z).symm

def routedClose := (skywalkArithmeticClear base ++ head) ++
  (Stair44WalkRun.backward false 490 ++ renameProgram first (FrontierEntry1591NativeH.inverse base))

theorem close (x y : Nat) (hx0 : 0<x) (hx : x<p) (hn : (skywalkSharedWires base).Nodup)
    (s v : State) (input : SkywalkArithmeticInput base x y s.basis)
    (phase : v.phase=(run (Rolling1588TickGap.firstPhase false) [] s).phase)
    (pool : ∀q∈skywalkPoolWires base,v.basis q=(run (Rolling1588TickGap.firstPhase false) [] s).basis q)
    (m : List Bool) :
    run routedClose m v=run (InverseFive23.lastPhase15 false) m v := by
  let C := skywalkArithmeticClear base ++ head
  let tape := m.drop (measurementCount C)
  let B := Stair44WalkRun.backward false 490
  let R := Rolling1588.reverse false 1 505
  let I := FrontierEntry1591NativeH.inverse base
  have sh : InverseFive23.lastPhase15 false=C ++ (R ++ I) := by
    simp only [C,head,R,I,InverseFive23.lastPhase15,InverseFive23.stackReverse15,
      InverseFive23.reverseTail15,P1,List.append_assoc]
  rw [sh,routedClose,run_append,run_append C]
  change run (B ++ renameProgram first I) tape (run C (m.take (measurementCount C)) v) =
    run (R ++ I) tape (run C (m.take (measurementCount C)) v)
  obtain ⟨a,ha,hb⟩ := reverse_input x y hx0 hx hn s v input phase pool (m.take (measurementCount C))
  change run C _ v=pullState (sig 505) a at ha
  rw [ha,run_append,run_append]
  have bm : measurementCount B=measurementCount R := (Stair44WalkRun.metrics false 490).2.2.1
  rw [bm]
  obtain ⟨one,eo⟩ : ∃ st : State,run (FrontierEntry1591Native.forward base) [] s=st := ⟨_,rfl⟩
  rw [eo] at hb
  have st := FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s [] input
  rw [eo] at st
  have h1 := stage_one base false x p one st
  let ws := tape.take (measurementCount R)
  have rr := Stair44WalkCuts.backward_record false 490 x (by decide) hx0 hx one a [] ws h1 hb
  have rp := Stair44WalkCuts.restore_raw false 490 x (by decide) hx0 hx one a [] ws h1 hb
  apply inverse_end x y hx hn s _ _ input rr
  simpa only [eo] using rp

end ECDSAAdd.Entrant.Stair44DivTerm

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary225Native
open Arithmetic MappedCompressed IntegerPacket WideReference Partial NativePack225
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body routed
theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (domain:Domain 225 x p raw)
    (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 neg far long
      (pullState (OB5.sig 224) raw) s)
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run enter225 a s).basis) :
    let historyState:=run (body idx (program d)) b (run enter225 a s)
    ArchiveHistoryCompare.Except Logical225Exit.newBank (endRaw 225 raw historyState)
      (run (Rolling1588.encodeAt base d 220) [] (run (span 225 15) [] raw)) := by
  let e:=run enter225 a s
  have input:∀i,(run (routed idx 0 1) b e).basis (history i)=raw.basis (History5.historyMap base 220 i) := by
    exact history_from_stock raw s e cut a b rfl z odd active
  exact Logical225Exit.window d raw _ (Ordinary225Exit.result d raw e b x p good domain input)
end ECDSAAdd.Entrant.StairPacket.Ordinary225Native

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary240Native
open Arithmetic MappedCompressed IntegerPacket WideReference Partial NativePack240
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body routed
theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (domain:Domain 240 x p raw)
    (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter240.lowerPairs Enter240.upperPairs 255 1715 1713 1714 neg far long
      (pullState (OB5.sig 239) raw) (eraseSites Enter240.pending s))
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run enter240 a s).basis) :
    let historyState:=run (body idx (withArchive d)) b (run enter240 a s)
    ArchiveHistoryCompare.Except Logical240Exit.newBank (endRaw 240 raw historyState)
      (run (Rolling1588.encodeAt base d 225) [] (run (span 240 15) [] raw)) := by
  let e:=run enter240 a s
  have input:∀i,(run (routed idx 0 1) b e).basis (history i)=raw.basis (History5.historyMap base 225 i) := by
    intro i
    have kept:=prefix_kept s a b z odd active i
    have geom:∀i:Fin 10,history i∉Enter240.pending ∧ history i≠1715 ∧ history i≠1713 ∧ history i≠1714 ∧
      history i∉RailPair.sites Enter240.upperPairs ∧ OB5.sig 239 (history i)=History5.historyMap base 225 i:=by decide +kernel
    obtain ⟨notTag,hn,hf,hu,hi,same⟩:=geom i
    exact kept.trans (by simpa only [eraseSites,if_neg notTag,pullState,same] using cut.unchanged _ hn hf hu hi)
  exact Logical240Exit.window d raw _ (Ordinary240Exit.result d raw e b x p good domain input)
end ECDSAAdd.Entrant.StairPacket.Ordinary240Native

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary255Native
open Arithmetic MappedCompressed IntegerPacket WideReference Partial NativePack255
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
attribute [local irreducible] run body routed
theorem result (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (domain:Domain 255 x p raw)
    (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut Enter255.lowerPairs Enter255.upperPairs 270 1708 1706 1707 neg far long
      (pullState (OB5.sig 254) raw) (eraseSites Enter255.pending s))
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1)
    (active:onRails idx 0 z (run enter255 a s).basis) :
    let historyState:=run (body idx (withArchive d)) b (run enter255 a s)
    ArchiveHistoryCompare.Except Logical255Exit.newBank (endRaw 255 raw historyState)
      (run (Rolling1588.encodeAt base d 240) [] (run (span 255 15) [] raw)) := by
  let e:=run enter255 a s
  have input:∀i,(run (routed idx 0 1) b e).basis (history i)=raw.basis (History5.historyMap base 240 i) := by
    intro i
    have kept:=prefix_kept s a b z odd active i
    have geom:∀i:Fin 10,history i∉Enter255.pending ∧ history i≠1708 ∧ history i≠1706 ∧ history i≠1707 ∧
      history i∉RailPair.sites Enter255.upperPairs ∧ OB5.sig 254 (history i)=History5.historyMap base 240 i:=by decide +kernel
    obtain ⟨notTag,hn,hf,hu,hi,same⟩:=geom i
    exact kept.trans (by simpa only [eraseSites,if_neg notTag,pullState,same] using cut.unchanged _ hn hf hu hi)
  exact Logical255Exit.window d raw _ (Ordinary255Exit.result d raw e b x p good domain input)
end ECDSAAdd.Entrant.StairPacket.Ordinary255Native

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 20000
attribute [local irreducible] wires domain
theorem reverse_domain (d : Bool) : ∀ q ∈ wires (reverse45plus1 d), domain q = true := by
  intro q h
  cases d
  · simp only [reverse45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site30 q h
    · exact site31 q h
    · exact site32 q h
    · exact site33 q h
    · exact site34 q h
    · exact site35 q h
    · exact site36 q h
    · exact site37 q h
    · exact site38 q h
    · exact site39 q h
    · exact site40 q h
    · exact site41 q h
    · exact site42 q h
    · exact site43 q h
    · exact site44 q h
    · exact site45 q h
    · exact site46 q h
    · exact site47 q h
    · exact site48 q h
    · exact site49 q h
    · exact site50 q h
    · exact site51 q h
    · exact site52 q h
  · simp only [reverse45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site53 q h
    · exact site54 q h
    · exact site32 q h
    · exact site33 q h
    · exact site34 q h
    · exact site35 q h
    · exact site36 q h
    · exact site55 q h
    · exact site56 q h
    · exact site39 q h
    · exact site40 q h
    · exact site41 q h
    · exact site42 q h
    · exact site57 q h
    · exact site58 q h
    · exact site45 q h
    · exact site46 q h
    · exact site47 q h
    · exact site48 q h
    · exact site59 q h
    · exact site50 q h
    · exact site51 q h
    · exact site52 q h

theorem inside (n:Nat) (use:domain n=true):(16:Nat)≤n ∧ n≤1812:=by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at use
  rcases use with ⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩
  all_goals exact ⟨Nat.le_trans (by decide) lo,Nat.le_trans hi (by decide)⟩
theorem range_pool (n:Nat) (lo:16 ≤ n) (hi:n≤1812):n∈skywalkPoolWires base:=by
  have hit:=StackOB5Base.base_pool (n-16) (by omega)
  simpa only [base,Nat.sub_add_cancel lo] using hit
theorem pool_partial (d:Bool):wires (reverse45plus1 d)⊆(skywalkPoolWires base).toFinset:=by
  intro q h
  have b:=inside q (reverse_domain d q h)
  exact List.mem_toFinset.mpr (range_pool q b.1 b.2)
theorem pool_old (d:Bool) (i n:Nat) (lo:1 ≤ i) (hi:i+n≤512):wires (Rolling1588.reverse d i n)⊆(skywalkPoolWires base).toFinset:=by
  intro q h
  rw [Rolling1588.reverse_support_eq,NewStackOB5.reverse_support_eq] at h
  obtain ⟨k,rfl,range⟩:=StackOB5Base.integerSites_mem q |>.mp ((StackOB5.support_gen i n lo hi).2 q h)
  exact List.mem_toFinset.mpr (StackOB5Base.base_pool k (by omega))
end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockRowVector
open Arithmetic MappedCompressed Secp256k1 StockCanonicalRow StockStrongChain StockArchiveBanks
open StairArchiveRaw WideReference ArchiveStockSuffix ArchivePortAction
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

noncomputable def keys (x p:Nat) (b:Bank):Nat→Bool:=
  if b=0 then value x p 225 144 cross225 else if b=1 then value x p 240 136 cross240 else value x p 255 129 cross255
noncomputable def rows (x p:Nat) (b:Bank):Nat:=select (keys x p b)

theorem fields (d:Bool) (x p:Nat) (s:State) (h:final d x p s) (b:Bank):
    SavedKey (keys x p b) (ports b) d s:=by
  rcases b with ⟨n,lt⟩
  rcases n with _|n;exact h.1
  rcases n with _|n;exact h.2.1
  have eq:n=0:=by omega
  subst n
  exact h.2.2

theorem historical (b i x p:Nat) (c:SkywalkNat.State→Bool) (r:Nat)
    (labels:Encodes (value x p i b c) r):ArchiveStockRows.Chronology i x p r:=by
  intro j
  have bit:=labels ⟨j,by omega⟩
  simpa only [value,key,rawBit,j.isLt,if_true] using bit

theorem trace {d x p s} (h:final d x p s) (b:Bank):
    ArchiveStockRows.Chronology (tick b) x p (rows x p b):=by
  rcases b with ⟨n,lt⟩
  rcases n with _|n
  · exact historical 144 225 x p cross225 _ h.1.2.1
  rcases n with _|n
  · exact historical 136 240 x p cross240 _ h.2.1.2.1
  have eq:n=0:=by omega
  subst n
  exact historical 129 255 x p cross255 _ h.2.2.2.1

theorem binding (d:Bool) (x:Nat) (good:Bounds x p) (raw a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis)
    (stored:final d x p a) (same:Same a (run (Rolling1588TickGap.forward d 225 46) m (pullState (OB5.sig 224) raw))):
    Paired d x a (run (Rolling1588TickGap.forward d 225 46) m (pullState (OB5.sig 224) raw)) (rows x p):=by
  refine ⟨same,fun b=>⟨(fields d x p a stored b).1,trace stored b⟩,fun b=>(fields d x p a stored b).2.2,?_⟩
  intro b
  exact StockArchiveBanks.stored d x good raw m stage b _ (fields d x p a stored b).1 (trace stored b)
end ECDSAAdd.Entrant.StairPacket.StockRowVector

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkPrefix
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks
set_option maxRecDepth 8500
set_option maxHeartbeats 2000000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount renameProgram
def first (d:Bool):Program:=Stair44WalkRun.forward d 209
def regular (d:Bool) (s:State) (m:List Bool):State:=run (Rolling1588.Integer.regularForward base d 1 224) m s
theorem cut225 (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Rolling1588.Integer.Stage base d x p 225 (regular d s m).basis ∧
    pullState Stair44WalkMap.rest (run (first d) m a)=pullState (OB5.sig 224) (regular d s m):=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have spec:=Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p 1 224 hp0 good.nonzero odd cap (by norm_num [p]) good.small cop (by decide) s m stage
  refine ⟨spec.2,?_⟩
  have entry:=Stair44WalkRun.forward_run d 209 x good.nonzero good.small s a m stage input
  have logical:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 224 1 (by decide) (by decide) s m stage
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  rw [show 1-1=0 from rfl,init] at logical
  exact entry.trans logical

def forwardEnd (d:Bool) (n:Nat):Program:=Partial.forward45plus1 d++Rolling1588TickGap.forward d 271 n
theorem split (d:Bool) (n:Nat):WindowWalkCosts.forward d n=first d++renameProgram Stair44WalkMap.rest (forwardEnd d n):=by
  simp only [WindowWalkCosts.forward,first,Stair44WalkRun.forward,forwardEnd,renameProgram,List.map_append,List.append_assoc]
theorem placed (d:Bool) (n x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    pullState Stair44WalkMap.rest (run (WindowWalkCosts.forward d n) m a)=
      run (forwardEnd d n) (m.drop (measurementCount (first d))) (pullState (OB5.sig 224) (regular d s m)):=by
  rw [split,run_append,run_take,run_rename _ Stair44WalkMap.rest.injective,(cut225 d x good s a m stage input).2]
end ECDSAAdd.Entrant.StairPacket.StockWalkPrefix

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg
attribute [local irreducible] run wires measurementCount wire group StairArchiveInactive.packet
set_option maxRecDepth 2600
set_option maxHeartbeats 500000

theorem packet_map (d : Bool) (j : Nat) :
    packet d j = renameProgram wire (Rolling1588.packet d j) := by
  unfold packet
  calc
    _ = renameProgram host (renameProgram (OB5.sig 511) (StairGroups.packet d 0 j)) := hosts_eq _ _ _
    _ = _ := by rw [StairGroups.packet_zero,renameProgram_comp]; unfold wire; rfl

def surface : Finset Wire := ((Finset.Icc 1 84).biUnion (fun j=>wires (packet false j) ∪ wires (packet true j))) ∪ bankIds.biUnion inside
def tracks (actual ideal : State) := ∀q∈surface,q≠base 720→actual.basis q=ideal.basis q
def StockCut (c : Nat) (origin : BasisState) (r : State) : Prop :=
  r.basis (base 720)=false ∧ ∃ (X Y : Fp) (ideal : State),
    Rolling1588.CutFrame c origin X Y (pullState wire ideal) ∧ tracks r ideal

private def allowedTag (k : Nat) := !(cover k).contains (preimage k (base 720))
private theorem tagged : (List.range' 1 84).all allowedTag=true := by decide +kernel
private theorem packetUses (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) {q : Wire} (h : q∈wires (packet d k)) :
    q∈surface ∧ q≠base 720 := by
  constructor
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨k,Finset.mem_Icc.mpr ⟨lo,hi⟩,?_⟩
    cases d
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ h
  · rintro rfl
    have yes := original d k (by omega) h
    have no := List.all_eq_true.mp tagged k (List.mem_range'_1.mpr ⟨lo,by omega⟩)
    simp [allowedTag,yes] at no

private theorem follow (P : Program) (m : List Bool) (a b : State) (h : tracks a b) (tag : a.basis (base 720)=false)
    (incl : ∀q∈wires P,q∈surface ∧ q≠base 720) :
    tracks (run P m a) (run P m b) ∧ (run P m a).basis (base 720)=false := by
  have bound := Arithmetic.run_local_increment P a b m (fun q hq=>h q (incl q hq).1 (incl q hq).2)
  constructor
  · intro q use off
    by_cases gate : q∈wires P
    · exact bound.2 q gate
    · rw [run_preserves_outside _ _ _ _ gate,run_preserves_outside _ _ _ _ gate,h q use off]
  · rw [run_preserves_outside _ _ _ _ (fun use=>(incl _ use).2 rfl),tag]

theorem step (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : StockCut (if d then j else j+1) origin r) :
    StockCut (if d then j+1 else j) origin (run (packet d j) m r) := by
  obtain ⟨zero,X,Y,b,fr,match_⟩ := initial
  obtain ⟨same,afterZero⟩ := follow _ m r b match_ zero (fun _ h=>packetUses d j lo hi h)
  have actual := Rolling1588.packet_cut_frame d j lo (by omega) origin ctx enabled X Y _ m fr
  let V := CompressedFieldSupport.directionalPayload (!d) (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
  refine ⟨afterZero,V.1,V.2,run (packet d j) m b,?_,same⟩
  rw [packet_map,run_rename wire injective]; exact actual.2

theorem selected (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : StockCut (if d then j else j+n) origin r) :
    StockCut (if d then j+n else j) origin (run (group d j n) m r) := by
  rw [group,distribute,distributed]
  induction n generalizing j r m with
  | zero =>
    simpa only [PacketSequence.program,run,Nat.add_zero] using initial
  | succ n ih =>
    cases d with
    | false =>
      simp only [Bool.false_eq_true,if_false] at initial ⊢
      simp only [PacketSequence.program,Bool.false_eq_true,if_false,run_append,run_take]
      apply step false j lo (by omega) origin ctx enabled
      apply ih (j+1) (by omega) (by omega) r m
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using initial
    | true =>
      simp only [if_true] at initial ⊢
      simp only [PacketSequence.program,if_true,run_append,run_take]
      have first := step true j lo (by omega) origin ctx enabled r m initial
      have last := ih (j+1) (by omega) (by omega) _ (m.drop (measurementCount (packet true j))) first
      simpa only [if_true,Nat.add_assoc,Nat.add_comm 1 n] using last
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify StairArchiveNativeRows WindowParityDirty
set_option maxRecDepth 8000
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 100000
set_option linter.unusedSimpArgs false
def bounded : Formula→Bool
  | .var q => decide (q<16)
  | .one => true
  | .xor l r | .and l r => bounded l && bounded r
def column (data : Cols) : Formula→Nat
  | .var q => get data q
  | .one => ones
  | .xor a b => column data a ^^^ column data b
  | .and a b => column data a &&& column data b
theorem column_sound (data : Cols) (s : State) (row : Nat) (rb : row<63145)
    (input : ∀ i<16,s.basis i=(get data i).testBit row) (f : Formula) (valid : bounded f=true) :
    f.eval s.basis=(column data f).testBit row := by
  induction f with
  | var q => exact input _ (of_decide_eq_true valid)
  | one =>
    change true=(2^63145-1).testBit row
    rw [Nat.testBit_two_pow_sub_one]; exact (decide_eq_true rb).symm
  | xor a b ha hb =>
    simp only [bounded,Bool.and_eq_true] at valid
    obtain ⟨left,right⟩ := valid
    simp only [Formula.eval,column,Nat.testBit_xor,ha left,hb right]
  | and a b ha hb =>
    simp only [bounded,Bool.and_eq_true] at valid
    obtain ⟨left,right⟩ := valid
    simp only [Formula.eval,column,Nat.testBit_and,ha left,hb right]
private theorem small : clauses.all (fun c=>bounded (predicate c))=true := by decide +kernel
def total (cs : Cols) (items : List Clause) := (items.map (fun c=>column cs (predicate c))).foldr (· ^^^ ·) 0
def parity (cs : Cols) := ((List.range 16).map (get cs)).foldr (· ^^^ ·) 0
private theorem columnMatch (d : Bool) :
    total (ArchivePortAction.code d) clauses =
      (parity (ArchivePortAction.code d) ^^^ parity (StairArchiveNativeCut.canonical d d)) := by
  cases d <;> decide +kernel
private theorem runList (cs : Cols) (items : List Clause) (valid : ∀c∈items,c∈clauses)
    (row : Nat) (rb : row<63145) (m : List Bool) (s : State)
    (data : ∀i<16,s.basis i=(get cs i).testBit row) :
    run (items.flatMap ECDSAAdd.Entrant.StairPacket.WindowParityDirty.body) m s = flip 16 ((total cs items).testBit row) s := by
  induction items generalizing m s with
  | nil => simp only [List.flatMap_nil,run,total,List.map_nil,List.foldr_nil,Nat.zero_testBit,flip_zero]
  | cons c xs ih =>
    have mem := valid c (by simp)
    have more := fun k (hk : k∈xs)=>valid k (List.mem_cons_of_mem _ hk)
    have val := column_sound cs s row rb data (predicate c) (List.all_eq_true.mp small _ mem)
    have pre := ECDSAAdd.Entrant.StairPacket.WindowParityDirty.body_run c mem m s
    rw [val] at pre
    have dnext : ∀i<16,(flip 16 ((column cs (predicate c)).testBit row) s).basis i=(get cs i).testBit row := by
      intro i hi; rw [at_other s i 16 _ (Nat.ne_of_lt hi)]; exact data i hi
    rw [List.flatMap_cons,run_append,run_take,pre,ih more _ _ dnext,flip_twice]
    rw [show total cs (c::xs)=((column cs (predicate c)) ^^^ total cs xs) by rfl,Nat.testBit_xor]

theorem region_run (d : Bool) (row : Nat) (rb : row<63145) (m : List Bool) (s : State)
    (data : ∀i<16,s.basis i=(get (ArchivePortAction.code d) i).testBit row) :
    run region m s = flip 16 (((parity (ArchivePortAction.code d)).testBit row) ^^
      ((parity (StairArchiveNativeCut.canonical d d)).testBit row)) s := by
  rw [region,runList _ _ (fun _ h=>h) _ rb m s data,columnMatch d,Nat.testBit_xor]
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.Stair44Kernel
open Arithmetic MappedCompressed Secp256k1 OB5 DirectSkywalk Rolling1588.Integer Stair44WalkMap
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires measurementCount regularForward Rolling1588TickGap.forward
  Stair44WalkRun.forward FrontierEntry1591Native.forward

def firstR := renameProgram first (FrontierEntry1591Native.forward base)
def openR (d : Bool) (a : Nat) := firstR ++ Stair44WalkRun.forward d a
def openS (d : Bool) (a : Nat) := FrontierEntry1591Native.forward base ++ Rolling1588TickGap.forward d 1 (15+a)

private theorem inFix (x y : Nat) (s : State) (h : SkywalkArithmeticInput base x y s.basis) : pullState first s=s := by
  let l := [1026,514,1541,501,1542,500]
  have tab : ∀j∈l,base j∈skywalkSharedWires base ∧ base j∉skywalkArithmeticDivisor base ∧
      base j∉skywalkArithmeticNumerator base := by decide +kernel
  have z (j : Nat) (hj : j∈l) := h.2.2 _ (tab j hj).1 (tab j hj).2.1 (tab j hj).2.2
  have a := cleanWireRebind id s s _ _ rfl (z 1026 (by decide)) (z 514 (by decide))
  have b := cleanWireRebind _ s s _ _ a (z 1541 (by decide)) (z 501 (by decide))
  exact cleanWireRebind _ s s _ _ b (z 1542 (by decide)) (z 500 (by decide))

theorem open_count (d : Bool) (a : Nat) : measurementCount (openR d a)=measurementCount (openS d a) := by
  rw [openR,openS,measurementCount_append,measurementCount_append,firstR,(renameProgram_counts _ _).2,
    (Stair44WalkRun.metrics d a).1.2.1]

theorem open_run (d : Bool) (a x y : Nat) (atCut : 1+(15+a)∈[425,505,506]) (hx0 : 0<x) (hx : x<p)
    (hn : (skywalkSharedWires base).Nodup) (s : State) (input : SkywalkArithmeticInput base x y s.basis)
    (m : List Bool) : run (openR d a) m s=run (openS d a) m s := by
  rw [openR,openS,run_append,run_append,firstR,(renameProgram_counts _ _).2]
  let N := FrontierEntry1591Native.forward base
  let mn := m.take (measurementCount N)
  have r := run_rename first first.injective N mn s
  rw [inFix x y s input] at r
  have st := stage_one base d x p _ (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  exact Stair44WalkCuts.forward_done d a x atCut hx0 hx _ _ _ st r

theorem with_tail (d : Bool) (a x y : Nat) (atCut : 1+(15+a)∈[425,505,506]) (hx0 : 0<x) (hx : x<p)
    (hn : (skywalkSharedWires base).Nodup) (s : State) (input : SkywalkArithmeticInput base x y s.basis)
    (T : Program) (m : List Bool) :
    run (openR d a ++ T) m s=run (openS d a ++ T) m s := by
  rw [run_append,run_append,open_count,open_run d a x y atCut hx0 hx hn s input]

end ECDSAAdd.Entrant.Stair44Kernel

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference NativePack225 EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body measurementCount
theorem ordinary225 (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool) (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    ArchiveHistoryCompare.Except Logical225Exit.newBank (endRaw 225 raw (run (firstWindow d) m (pullState (OB5.sig 224) raw)))
      (run (Rolling1588.encodeAt base d 220) [] (run (span 225 15) [] raw)) := by
  let z:=SkywalkNat.step^[225] (SkywalkNat.init x p)
  let origin:=pullState (OB5.sig 224) raw
  let cut:=run Partial.portal225 m origin
  let n:=m.drop (measurementCount Partial.portal225)
  let pre:=run Partial.enter225 n cut
  let tape:=n.drop (measurementCount Partial.enter225)
  let T:=Shadow.reduced 144 15 z
  have small:min z.u z.v<2^144:=true_small x p 225 (lt_trans good.small good.cap) good.cap (by decide)
  obtain ⟨G,S,input⟩:=PortalValues.real_input d x p 225 good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime (by decide) raw stage
  have pcut:=Portal225Flag.physical_frame_for d x p good.positive good.nonzero good.odd good.cap good.gap good.small good.coprime raw m stage G S input
  have same:Shadow.far 144 15 z=(3*2^160≤z.u+z.v):=by
    apply propext
    unfold Shadow.far Shadow.high Shadow.limb
    exact Nat.le_div_iff_mul_le (by positivity)
  have normalized:PackedCut Enter225.lowerPairs Enter225.upperPairs 240 1723 1721 1722 (PortalValues.negative S z.u)
      (decide (Shadow.far 144 15 z)) (decide (Shadow.far 144 15 z ∧ 2^144≤z.u)) origin cut:=by
    simpa only [same] using pcut
  have ready:=Enter225.ready_from_cut raw cut z G S n small normalized input
    (fun r=>by simpa only [Nat.add_assoc] using stock_history d x p 225 raw stage (225+r) (by omega) (by have hr:=r.isLt;omega))
  have zo:z.v%2=1:=(SkywalkNat.iter_valid 225 (SkywalkNat.init x p) good.positive good.odd).2.1
  have to':T.v%2=1:=shadow_odd 144 z small zo
  have parity:((encode G S T.u T.v).a+(encode G S T.u T.v).b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have h:=Ordinary225Native.result d x p good raw cut (initial 225 x p (by decide) d raw stage) n tape _ _ _ pcut _ parity ready.2
  simpa only [firstWindow,window,run_append,run_take,origin,n,tape,cut] using h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference NativePack240 EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body measurementCount
theorem ordinary240 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:At240 d x p raw s g sg pg ps) :
    ArchiveHistoryCompare.Except Logical240Exit.newBank (endRaw 240 raw (run (nextWindow d) m s))
      (run (Rolling1588.encodeAt base d 225) [] (run (span 240 15) [] raw)) := by
  let z:=unsigned 240 x p
  let T:=Shadow.reduced 136 15 z
  have nums:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) pre.domain
  have inp:=readInput 240 x p raw g sg pre.input
  have ready:=Enter240.ready_pending raw s z g sg m nums.small pre.cut inp hist
  have odd:T.v%2=1:=shadow_odd 136 z nums.small nums.odd
  have parity:((encode g sg T.u T.v).a+(encode g sg T.u T.v).b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have h:=Ordinary240Native.result d x p good raw s pre.domain m (m.drop (measurementCount Partial.enter240)) _ _ _ pre.cut _ parity ready.2.1
  simpa only [nextWindow,window,run_append,run_take] using h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails WideReference NativePack255 EnterProof
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] run body measurementCount
theorem ordinary255 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:At255 d x p raw s g sg pg ps) :
    ArchiveHistoryCompare.Except Logical255Exit.newBank (endRaw 255 raw (run (nextWindow d) m s))
      (run (Rolling1588.encodeAt base d 240) [] (run (span 255 15) [] raw)) := by
  let z:=unsigned 255 x p
  let T:=Shadow.reduced 129 15 z
  have nums:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) pre.domain
  have inp:=readInput 255 x p raw g sg pre.input
  have ready:=Enter255.ready_pending raw s z g sg m nums.small pre.cut inp hist (carry (by decide) pre.domain)
  have odd:T.v%2=1:=shadow_odd 129 z nums.small nums.odd
  have parity:((encode g sg T.u T.v).a+(encode g sg T.u T.v).b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have h:=Ordinary255Native.result d x p good raw s pre.domain m (m.drop (measurementCount Partial.enter255)) _ _ _ pre.cut _ parity ready.2.1
  simpa only [nextWindow,window,run_append,run_take] using h
end ECDSAAdd.Entrant.StairPacket.StockWindowTicket

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic MappedCompressed BalancedField Secp256k1 StairArchiveRelease StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask StairField2V3RecScratch StairPhysicalLayout
set_option maxRecDepth 2200
set_option maxHeartbeats 500000

private def regular (z : Wire) := !(EP.contains z) && !((futurePayload 87).contains z)
private def archiveGood (j : Nat) := (List.range 121).all (fun q => q==16 || regular (host.symm (fieldPort j q)))
private theorem portsCheck : WindowBankCheck.banks.all archiveGood=true := by decide +kernel
private theorem cleanPort (j q : Nat) (jb : j∈bankIds) (qb : q<121) (ne : fieldPort j q≠base 720) :
    Off (host.symm (fieldPort j q)) ∧ host.symm (fieldPort j q)∉futurePayload 87 := by
  have jm : j∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using jb
  have ok := List.all_eq_true.mp (List.all_eq_true.mp portsCheck _ jm) q (List.mem_range.mpr qb)
  have eq16 : fieldPort j 16=base 720 := by
    simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at jb
    rcases jb with rfl|rfl|rfl <;> decide
  have qne : q≠16 := fun h=>ne (h ▸ eq16)
  simp only [beq_iff_eq,Bool.or_eq_true,regular,Bool.and_eq_true,Bool.not_eq_true'] at ok
  rcases ok with h|⟨f,g⟩
  · contradiction
  · refine ⟨off_of_not_EP _ ?_,?_⟩
    · intro h; simp [h] at f
    · intro h; simp [h] at g

private theorem packet_original (d : Bool) (k : Nat) :
    packet d k=renameProgram host (renameProgram (OB5.sig 511) (Rolling1588.packet d k)) := by
  rw [packet,hosts_eq,StairGroups.packet_zero]; rfl

private theorem groupOne (d : Bool) (k : Nat) : Rolling1588.groups d k 1=Rolling1588.packet d k := by
  cases d <;> simp only [Rolling1588.groups,PacketSequence.program,Bool.false_eq_true,if_true,if_false,
    List.nil_append,List.append_nil]
attribute [local irreducible] surface StairArchiveInactive.host OB5.sig wires Rolling1588.packet Rolling1588.groups StairArchiveInactive.packet futurePayload Off
theorem reliable {q : Wire} (use : q∈surface) (ntag : q≠base 720) :
    Off (host.symm q) ∧ host.symm q∉futurePayload 87 := by
  rw [surface,Finset.mem_union] at use
  rcases use with packet_|archive_
  · obtain ⟨k,hk,dirs⟩ := Finset.mem_biUnion.mp packet_
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hk
    have both (d : Bool) (used : q∈wires (packet d k)) : Off (host.symm q) ∧ host.symm q∉futurePayload 87 := by
      rw [packet_original,renameProgram_support] at used
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp used
      rw [Equiv.symm_apply_apply]
      rw [←groupOne d k] at hv
      constructor
      · cases d
        · exact StairField2V3ExitRec.groupsF_off k 1 lo (by omega) v hv
        · exact groups_off k 1 lo (by omega) v hv
      · intro bad
        exact StairField2V3Groups.groups_avoid_payload d 87 (by decide) 1 k
          (by change k+1≤85; omega) v bad hv
    exact (Finset.mem_union.mp dirs).elim (both false) (both true)
  · obtain ⟨j,hj,hq⟩ := Finset.mem_biUnion.mp archive_
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact cleanPort j i hj (Finset.mem_range.mp hi) ntag

theorem from_record (c : Nat) (origin : BasisState) (X Y : Fp) (r s : State)
    (cut : Rolling1588.CutFrame c origin X Y (pullState (OB5.sig 511) s))
    (tag : r.basis (base 720)=false)
    (hosted : ∀q, r.basis (host q)=r.basis q)
    (agrees : ∀ q, Off q → q∉futurePayload 87 → r.basis q=s.basis q) :
    StockCut c origin r := by
  let b := pullState host.symm s
  have back : pullState wire b=pullState (OB5.sig 511) s := by
    apply State.extensionality; · rfl
    funext q; change s.basis (host.symm (host (OB5.sig 511 q)))=_
    rw [Equiv.symm_apply_apply]; rfl
  refine ⟨tag,X,Y,b,back.symm ▸ cut,?_⟩
  intro q hq ntag
  have ready := reliable hq ntag
  have fixed := hosted (host.symm q)
  rw [Equiv.apply_symm_apply] at fixed
  exact fixed.trans (agrees _ ready.1 ready.2)

theorem host_fixed (r : State) (zero : ∀q∈StairSchedule.exclusiveRoles++hosts 87,r.basis q=false) :
    ∀q,r.basis (host q)=r.basis q := by
  have general (rs hs : List Wire) (clean : ∀q∈rs++hs,r.basis q=false) :
      ∀q,r.basis (rebinder rs hs q)=r.basis q := by
    induction rs generalizing hs with
    | nil => cases hs <;> intro q <;> rfl
    | cons a rest ih =>
      cases hs with
      | nil => intro q; rfl
      | cons b tail =>
        intro q
        have a0 := clean a (by simp)
        have b0 := clean b (by simp)
        have tails := ih tail (fun q h => clean q (by simpa only [List.mem_append,List.mem_cons] using (show (q=a ∨ q∈rest) ∨ q=b ∨ q∈tail from by rcases List.mem_append.mp h with left|right; exact Or.inl (Or.inr left); exact Or.inr (Or.inr right))))
        change r.basis ((Equiv.swap a b) (rebinder rest tail q)) = _
        rw [←tails q]; generalize rebinder rest tail q=v
        by_cases av : v=a
        · subst v; simp [a0,b0]
        by_cases bv : v=b
        · subst v; simp [a0,b0]
        rw [Equiv.swap_apply_of_ne_of_ne av bv]
  rw [host]; exact general _ _ zero
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
attribute [local irreducible] run group ten measurementCount packet surface
  ArchiveStockRows.Chronology Rolling1588.CutFrame StairArchiveNativeCut.canonical
set_option maxRecDepth 1600
set_option maxHeartbeats 400000

private theorem see (j c x row : Nat) (hj : j∈bankIds) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (r : State) (state : StockCut c origin r) : frame j row (boundaryCols j c) r := by
  obtain ⟨zero,X,Y,model,fr,view⟩ := state
  have list : j∈WindowBankCheck.banks := by simpa [WindowBankCheck.banks,bankIds] using hj
  apply observed j c x row list rb origin ctx tr history X Y model r fr zero
  intro q inside_ off
  exact view q (by rw [surface];exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,inside_⟩)) off

theorem pair_cuts (d : Bool) (j x row : Nat) (hj : j∈bankIds) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (r : State) (m : List Bool) (state : StockCut (if d then j else j+2) origin r) :
    (frame j row (StairArchiveNativeCut.canonical d d) r ∧ frame j row middle (refMiddle j (!d) m r) ∧
      frame j row (StairArchiveNativeCut.canonical (!d) (!d)) (refExit j (!d) m r)) ∧
    StockCut (if d then j+2 else j) origin (refExit j (!d) m r) := by
  have bounds : 1≤j ∧ j+1≤84 := by simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at hj; omega
  let observe := fun c t (h : StockCut c origin t) => see j c x row hj rb origin ctx tr history t h
  have lo : boundaryCols j j=StairArchiveNativeCut.canonical true true := by simp [boundaryCols]
  have mid : boundaryCols j (j+1)=middle := by simp [boundaryCols,middle]
  have hi : boundaryCols j (j+2)=StairArchiveNativeCut.canonical false false := by simp [boundaryCols]
  cases d
  · have one : StockCut (j+1) origin (refMiddle j true m r) :=
      step false (j+1) (by omega) (by omega) origin ctx en r _ state
    have two : StockCut j origin (refExit j true m r) :=
      step false j (by omega) (by omega) origin ctx en _ _ one
    exact ⟨⟨hi ▸ observe _ _ state,mid ▸ observe _ _ one,lo ▸ observe _ _ two⟩,two⟩
  · have one : StockCut (j+1) origin (refMiddle j false m r) :=
      step true j (by omega) (by omega) origin ctx en r _ state
    have two : StockCut (j+2) origin (refExit j false m r) :=
      step true (j+1) (by omega) (by omega) origin ctx en _ _ one
    exact ⟨⟨lo ▸ observe _ _ state,mid ▸ observe _ _ one,hi ▸ observe _ _ two⟩,two⟩

def span : Leg → Nat×Nat
  | .native j n => (j,n)
  | .paired j => (j,2)
def next (d : Bool) (l : Leg) := if d then (span l).1+(span l).2 else (span l).1
def prev (d : Bool) (l : Leg) := if d then (span l).1 else (span l).1+(span l).2
def feasible : Leg→Prop
  | .native j n => 1≤j ∧ j+n≤85
  | .paired j => j∈bankIds
def path (d : Bool) : Nat→List Leg→Prop
  | _,[] => True
  | c,l::ls => c=prev d l ∧ feasible l ∧ path d (next d l) ls
theorem trail (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (c : Nat) (ls : List Leg) (m : List Bool) (r : State) (route : path d c ls) (start : StockCut c origin r) :
    NativeTrail d rows ls m r := by
  induction ls generalizing c m r with
  | nil => trivial
  | cons l ls ih =>
    obtain ⟨rfl,good,more⟩ := route
    cases l with
    | native j n =>
      have post := selected d j n good.1 good.2 origin ctx en r m start
      exact ⟨trivial,ih _ _ _ more post⟩
    | paired j =>
      have event := pair_cuts d j x (rows j) good (rb _ good) origin ctx en tr (history _ good) r m start
      exact ⟨event.1,ih _ _ _ more event.2⟩

theorem three_run (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (ref : StockCut (if d then 1 else 85) origin r) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84 d) m a)
      (run (group d 1 84) (referenceTape d (plan d) m) r) := by
  have route : path d (if d then 1 else 85) (plan d) := by cases d <;> simp [path,plan,prev,next,span,feasible,bankIds]
  have all := group_run d rows rb m a r initial (trail d x rows rb origin ctx en tr history _ _ m r route ref)
  rwa [ref_run,reference_eq] at all
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify WindowParityDirty
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
def addr (i : Nat) := OB5.sig 511 (NewHistory5.payloadWire base i)
private def block (j : Nat) := (List.range 16).map (8*j+·)
private def stable0 := List.range 368
private def stable1 := List.range' 384 8
private def stable2 := List.range' 408 8
private def stable3 := List.range' 432 384
private theorem split : List.range 816 = stable0 ++ block 46 ++ stable1 ++ block 49 ++ stable2 ++ block 52 ++ stable3 := by decide +kernel
private theorem join (l r : List Bool) : TraceParity5.parity (l++r) = (TraceParity5.parity l ^^ TraceParity5.parity r) := by
  induction l with
  | nil => simp [TraceParity5.parity]
  | cons x xs ih => simp only [List.cons_append,TraceParity5.parity,ih,Bool.xor_assoc]
private theorem reduce (cs : Cols) (r : Nat) (l : List Nat) :
    TraceParity5.parity (l.map (fun i=>(get cs i).testBit r)) =
    (((l.map (get cs)).foldr (· ^^^ ·) 0).testBit r) := by
  induction l with
  | nil => simp [TraceParity5.parity]
  | cons i xs ih => simp only [List.map_cons,List.foldr_cons,TraceParity5.parity,ih,Nat.testBit_xor]
private def sum (l : List Nat) (s : State) := TraceParity5.parity (l.map (fun i=>s.basis (addr i)))
private theorem fromData (s : State) (j : Nat) (cs : Cols) (r : Nat)
    (bits : ∀ i<16,s.basis (site j i)=(get cs i).testBit r) :
    sum (block j) s=(parity cs).testBit r := by
  unfold sum block parity
  rw [List.map_map,←reduce]
  congr 1
  apply List.map_congr_left
  intro i hi; exact bits i (List.mem_range.mp hi)
private theorem stable_sum (l : List Nat) (a b : State)
    (eq : ∀i∈l,a.basis (addr i)=b.basis (addr i)) : sum l a=sum l b :=
  congrArg TraceParity5.parity (List.map_congr_left eq)
def Elsewhere (i : Nat) := i<368 ∨ (384 ≤ i ∧ i<392) ∨ (408 ≤ i ∧ i<416) ∨ (432 ≤ i ∧ i<816)
def stockParity (s : State) := TraceParity5.parity (FrontierEntry1591Field.controls.map s.basis)
private theorem allSum (s : State) : stockParity s=
    ((((((sum stable0 s ^^ sum (block 46) s) ^^ sum stable1 s) ^^ sum (block 49) s) ^^
      sum stable2 s) ^^ sum (block 52) s) ^^ sum stable3 s) := by
  unfold stockParity FrontierEntry1591Field.controls ParityHost5.payloadControls
  rw [split]
  simp only [List.map_append,List.map_map,join,sum,Function.comp_def,addr]
theorem fold_pair (rows : Nat→Nat) (dirs : Nat→Bool) (a b : State)
    (rest : ∀i,Elsewhere i→a.basis (addr i)=b.basis (addr i))
    (custom : ∀j,j=46 ∨ j=49 ∨ j=52 → ∀i<16,a.basis (site j i)=(get (ArchivePortAction.code (dirs j)) i).testBit (rows j))
    (stock : ∀j,j=46 ∨ j=49 ∨ j=52 → ∀i<16,b.basis (site j i)=(get (StairArchiveNativeCut.canonical (dirs j) (dirs j)) i).testBit (rows j)) :
    (stockParity a ^^ stockParity b) =
    ((((parity (ArchivePortAction.code (dirs 46))).testBit (rows 46) ^^ (parity (StairArchiveNativeCut.canonical (dirs 46) (dirs 46))).testBit (rows 46)) ^^
      ((parity (ArchivePortAction.code (dirs 49))).testBit (rows 49) ^^ (parity (StairArchiveNativeCut.canonical (dirs 49) (dirs 49))).testBit (rows 49))) ^^
      ((parity (ArchivePortAction.code (dirs 52))).testBit (rows 52) ^^ (parity (StairArchiveNativeCut.canonical (dirs 52) (dirs 52))).testBit (rows 52))) := by
  have h0 := stable_sum stable0 a b (fun i hi=>rest i (Or.inl (List.mem_range.mp hi)))
  have h1 := stable_sum stable1 a b (fun i hi=>rest i (Or.inr (Or.inl (by
    simpa only [stable1,List.mem_range'_1] using hi))))
  have h2 := stable_sum stable2 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inl (by
    simpa only [stable2,List.mem_range'_1] using hi)))))
  have h3 := stable_sum stable3 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (by
    simpa only [stable3,List.mem_range'_1] using hi)))))
  rw [allSum a,allSum b,h0,h1,h2,h3,fromData _ _ _ _ (custom 46 (Or.inl rfl)),fromData _ _ _ _ (custom 49 (Or.inr (Or.inl rfl))),
    fromData _ _ _ _ (custom 52 (Or.inr (Or.inr rfl))),fromData _ _ _ _ (stock 46 (Or.inl rfl)),
    fromData _ _ _ _ (stock 49 (Or.inr (Or.inl rfl))),fromData _ _ _ _ (stock 52 (Or.inr (Or.inr rfl)))]
  simp only [Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm,Bool.xor_self,Bool.false_xor,Bool.xor_false]
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.Stair44Kernel
open Arithmetic MappedCompressed Secp256k1 DirectSkywalk StairConcreteAssembly
open Rolling1588Lifetime
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount wires renameProgram

abbrev divLead := renameProgram phaseHost (openR true 409 ++ checkpointPrimitives.firstPack)
abbrev fieldD := StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan
def division := (divLead ++ fieldD) ++ renameProgram phaseHost Stair44DivTerm.routedClose

private theorem reallead : StairSchedule.firstPhase checkpointPrimitives =
    openS true 409 ++ checkpointPrimitives.firstPack := by
  simp only [openS,StairSchedule.firstPhase,StairSchedule.stackForward6,List.append_assoc]

private theorem leadCount : measurementCount divLead =
    measurementCount (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)) := by
  rw [reallead,(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,open_count]

private theorem leadRun {t : State} (F : EntryFrame t) (m : List Bool) :
    run divLead m t=run (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)) m t := by
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,
    StairField13V3Clean.pull_phaseHost_entry F,reallead]
  exact with_tail true 409 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup t (StairField13V3Clean.entryInput F) _ m

private theorem transferPool (v old target : State) (e : pullState phaseHost old=target)
    (h : v.phase=old.phase ∧ ∀q∈skywalkPoolWires base,v.basis q=old.basis q) :
    (pullState phaseHost v).phase=target.phase ∧
      ∀q∈skywalkPoolWires base,(pullState phaseHost v).basis q=target.basis q := by
  subst target
  exact ⟨h.1,fun q hq => h.2 _ (Stair44DivTerm.host_pool q hq)⟩

theorem division_run {t : State} (F : EntryFrame t) (m : List Bool) :
    run division m t = run (StairHostsSchedule.entryKernel checkpointPrimitives hostPlan) m t := by
  let A := Stair44DivisionCut.beforeClose checkpointPrimitives hostPlan
  let L := renameProgram phaseHost (InverseFive23.lastPhase15 false)
  have stock : StairHostsSchedule.entryKernel checkpointPrimitives hostPlan=A++L := rfl
  have same (u : List Bool) : run (divLead ++ fieldD) u t=run A u t := by
    change _=run (_++_) u t
    rw [run_append,run_append,leadCount,leadRun F]
  have cnt : measurementCount (divLead++fieldD)=measurementCount A := by
    change _=measurementCount (_++_)
    rw [measurementCount_append,measurementCount_append,leadCount]
  rw [division,stock,run_append (divLead++fieldD),run_append A,cnt,same]
  obtain ⟨v,ev⟩ : ∃ v : State,run A (m.take (measurementCount A)) t=v := ⟨_,rfl⟩
  rw [ev]
  have h := Stair44DivisionCut.pool F (m.take (measurementCount A))
  change (run A _ t).phase=_ ∧ ∀q∈skywalkPoolWires base,(run A _ t).basis q=_ at h
  rw [ev] at h
  let P := Rolling1588TickGap.firstPhase false
  have first := StairLoanField7Values.first_phase_hosted false F.sharedNodup F.historyAbove F.x _
    F.x_pos F.x_lt t [] (StairField13V3Clean.entryInput F)
  have before := run_rename phaseHost phaseHost.injective P [] t
  change pullState phaseHost (run (renameProgram phaseHost (Rolling1588TickGap.firstPhase false)) [] t)=_ at before
  rw [first,StairField13V3Clean.pull_phaseHost_entry F] at before
  apply MappedCompressed.pullState_perm_injective phaseHost
  change pullState phaseHost (run (renameProgram phaseHost _) _ v)=pullState phaseHost (run (renameProgram phaseHost _) _ v)
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  have good := transferPool v _ _ before h
  exact Stair44DivTerm.close F.x _ F.x_pos F.x_lt F.sharedNodup t _ (StairField13V3Clean.entryInput F) good.1 good.2 _

theorem hostReplay : ∀ k,StairSemanticComposition.HostedReplayInterface k :=
  StairSemanticComposition.hostedReplayInterface_of
    (StairHostReplayField.hostReplay_of_field (StairOpenWiring.host_replay_of StairOpenWiring.remaining))
    (StairCertificate.replay_interfaces (StairOpenWiring.stairOpen_of_remaining StairOpenWiring.remaining))

theorem division_correct : FrontierEntry1591Callers.EntryCorrect division := by
  intro hn hl ho hf x Y hx0 hx s t m input hg hs phase eq val
  let F : EntryFrame t := ⟨hn,hl,ho,hf,x,Y,hx0,hx,s,input,hg,hs,phase,eq,val⟩
  have old := StairCallerReplay.hostedEntry_correct hostReplay hn hl ho hf x Y hx0 hx s t m input hg hs phase eq val
  dsimp only at old ⊢
  rw [division_run F]
  exact old

end ECDSAAdd.Entrant.Stair44Kernel

end

section

namespace ECDSAAdd.Entrant.Stair44Kernel
open Arithmetic MappedCompressed Stair44WalkMap
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

def rawOut := Stair44PointMap.chain [(base 1542,base 500),(base 1026,base 501),(base 1541,base 502),
  (base 723,base 503),(base 724,base 504)]
def rawX := rawOut.trans (Equiv.swap (base 501) (base 514))
def changeList := [1542,1026,1541,723,724,500,501,502,503,504,514].map base

private theorem off (w : Wire) (h : w∉changeList) : rawOut.symm w=w ∧ rawX.symm w=w ∧ first.symm w=w := by
  simp only [changeList,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  obtain ⟨a,b,c,d,e,f,g,i,j,k,l⟩ := h
  simp [rawOut,rawX,Stair44PointMap.chain,first,shared,Equiv.swap_apply_def,a,b,c,d,e,f,g,i,j,k,l]

private theorem encode_eq (f g : Equiv.Perm Wire) (z : List Wire)
    (chk : ∀q∈changeList,f.symm q=g.symm q ∨ f.symm q∈z ∧ g.symm q∈z)
    (far : ∀q,q∉changeList → f.symm q=g.symm q) (u : State) (hu : ∀q∈z,u.basis q=false) :
    pullState f.symm u = pullState g.symm u := by
  apply State.extensionality
  · rfl
  · funext q;change u.basis (f.symm q)=u.basis (g.symm q)
    by_cases h : q∈changeList
    · rcases chk q h with eq|⟨a,b⟩
      · rw [eq]
      · rw [hu _ a,hu _ b]
    · rw [far q h]

theorem xBefore (u : State) (hz : ∀j∈Stair44WalkExit.firstClean,u.basis (base j)=false) :
    pullState first.symm u=pullState rawX.symm u := by
  apply encode_eq first rawX (Stair44WalkExit.firstClean.map base) (by decide +kernel)
    (fun q h => (off q h).2.2.trans (off q h).2.1.symm)
  intro q h
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
  exact hz _ hj

theorem xAfter (u : State) (a : u.basis (base 1026)=false) (b : u.basis (base 514)=false) :
    pullState rawX.symm u=pullState rawOut.symm u := by
  apply encode_eq rawX rawOut [base 1026,base 514] (by decide +kernel)
    (fun q h => (off q h).2.1.trans (off q h).1.symm)
  intro q h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl
  · exact a
  · exact b

attribute [local irreducible] run wires measurementCount Rolling1588.reverse Rolling1588TickGap.forward
  Rolling1588.Integer.regularForward Stair44WalkRun.backward ParityXExitInverse23Kernel.x1N

theorem routed_at_X (a x : Nat) (cut : 16+a∈[425,505,506]) (hx0 : 0<x) (hx : x<p) (s1 : State) (firstStage :
    W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t : State) (enc : List Bool) (atCut : t=run (Rolling1588TickGap.forward true 1 (15+a)) enc s1)
    (mr : List Bool) :
    run (Stair44WalkRun.backward true a) mr t = pullState rawX.symm (run (Rolling1588.reverse true 1 (15+a)) mr t) := by
  have r := Rolling1588TickGap.forward_gen true x hx0 hx (15+a) 1 (by decide) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at cut;omega) s1 enc
    (Rolling1588.Integer.stage_one base true x p s1 firstStage)
  have init : pullState (OB5.sig 0) s1=s1 := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg s1.basis (OB5.sig_zero q)
  rw [show 1-1=0 by decide,init] at r
  obtain ⟨raw,er⟩ : ∃ u : State,run (Rolling1588.Integer.regularForward base true 1 (15+a)) enc s1=u := ⟨_,rfl⟩
  rw [er] at r
  have et : t=pullState (OB5.sig (16+a-1)) raw := atCut.trans (by simpa only [show 1+(15+a)=16+a by omega] using r)
  have h1 := Rolling1588.Integer.stage_one base true x p s1 firstStage
  have eqb (q : Wire) (_ : q∈skywalkPoolWires base) := (congrArg (fun u : State => u.basis q) er).symm
  let R := Rolling1588.reverse true 1 (15+a)
  obtain ⟨v,ev⟩ : ∃ w,run R mr t=w := ⟨_,rfl⟩
  obtain ⟨act,ea⟩ : ∃ w,run (Stair44WalkRun.backward true a) mr t=w := ⟨_,rfl⟩
  have dec : pullState first act=v := by
    rw [←ea,←ev,et]
    exact Stair44WalkCuts.backward_record true a x cut hx0 hx s1 raw enc mr h1 eqb
  have pool : ∀q∈skywalkPoolWires base,v.basis q = s1.basis q := by
    rw [←ev,et]
    exact Stair44WalkCuts.restore_raw true a x cut hx0 hx s1 raw enc mr h1 eqb
  have z (j : Nat) (hj : j∈Stair44WalkExit.firstClean) : v.basis (base j)=false :=
    (pool _ (OB5.base_pool _ (by simp [Stair44WalkExit.firstClean] at hj; omega))).trans
      (Stair44WalkExit.first_ready true x p s1 h1 j hj)
  have revertEq (e : Equiv.Perm Wire) (u : State) : pullState e.symm (pullState e u)=u := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg u.basis (e.apply_symm_apply q)
  have registered := congrArg (pullState first.symm) dec
  rw [revertEq,xBefore v z] at registered
  change run (Stair44WalkRun.backward true a) mr t=pullState rawX.symm (run R mr t)
  rw [ea,ev]; exact registered

theorem reverseX (k x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (firstStage :
    W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t : State) (enc : List Bool) (atCut : t=run (Rolling1588TickGap.forward true 1 424) enc s1)
    (m : List Bool) :
    let R := Rolling1588.reverse true 1 424
    let X := ParityXExitInverse23Kernel.x1N k
    let old := run (R++X) m t
    run (Stair44WalkRun.backward true 409 ++ renameProgram rawX X) m t = pullState rawX.symm old := by
  dsimp only
  rw [run_append,run_append,(Stair44WalkRun.metrics true 409).2.2.1,
    routed_at_X 409 x (by decide) hx0 hx s1 firstStage t enc atCut]
  apply MappedCompressed.pullState_perm_injective rawX
  rw [run_rename _ rawX.injective]
  have flip (u : State) : pullState rawX (pullState rawX.symm u)=u := by
    apply State.extensionality
    · rfl
    · funext q; exact congrArg u.basis (rawX.symm_apply_apply q)
  rw [flip,flip]

end ECDSAAdd.Entrant.Stair44Kernel

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChain
open Arithmetic MappedCompressed WideReference IntegerPacket ArchiveHistoryCompare
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run
theorem early (i q:Nat) (h:oldRange i q):Earlier i q := by
  obtain a|b:=h
  · exact ⟨q-16,by omega,Or.inl (by simp only [base,Wire];omega)⟩
  · exact ⟨q-1044,by omega,Or.inr (by simp only [base,Wire];omega)⟩
def mask225:=Logical225Exit.newBank
def prog225 (d:Bool):=Rolling1588.encodeAt base d 220
def lastBank:= (List.range' 260 10).flatMap (fun r=>[base r,base (1028+r)])

def mask240:=mask225++Logical240Exit.newBank
def prog240 (d:Bool):=prog225 d ++ Rolling1588.encodeAt base d 225

theorem add240 (d:Bool) (raw baseRaw out:State)
    (old:Except mask225 raw (run (prog225 d) [] (run (span 225 15) [] baseRaw)))
    (step:Except Logical240Exit.newBank out (run (Rolling1588.encodeAt base d 225) [] (run (span 240 15) [] raw))) :
    Except mask240 out (run (prog240 d) [] (run (span 225 30) [] baseRaw)) := by
  have maskEarly:∀q∈mask225,oldRange 240 q:=by decide +kernel
  have progEarly:∀q∈wires (prog225 d),oldRange 240 q:=by cases d <;> decide +kernel
  have apart:∀q∈mask225,q∉wires (Rolling1588.encodeAt base d 225):=by cases d <;> decide +kernel
  have h:=extend 240 15 (by decide) _ _ _ _ raw (run (span 225 15) [] baseRaw) out old step
    (fun q hit=>early _ _ (maskEarly q hit)) (fun q hit=>early _ _ (progEarly q hit)) apart
  have chronology:run (span 225 30) [] baseRaw=run (span 240 15) [] (run (span 225 15) [] baseRaw):=by
    rw [spanAppend 225 15 15,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h

def mask255:=mask240++Logical255Exit.newBank
def prog255 (d:Bool):=prog240 d ++ Rolling1588.encodeAt base d 240

theorem add255 (d:Bool) (raw baseRaw out:State)
    (old:Except mask240 raw (run (prog240 d) [] (run (span 225 30) [] baseRaw)))
    (step:Except Logical255Exit.newBank out (run (Rolling1588.encodeAt base d 240) [] (run (span 255 15) [] raw))) :
    Except mask255 out (run (prog255 d) [] (run (span 225 45) [] baseRaw)) := by
  have maskEarly:∀q∈mask240,oldRange 255 q:=by decide +kernel
  have progEarly:∀q∈wires (prog240 d),oldRange 255 q:=by cases d <;> decide +kernel
  have apart:∀q∈mask240,q∉wires (Rolling1588.encodeAt base d 240):=by cases d <;> decide +kernel
  have h:=extend 255 15 (by decide) _ _ _ _ raw (run (span 225 30) [] baseRaw) out old step
    (fun q hit=>early _ _ (maskEarly q hit)) (fun q hit=>early _ _ (progEarly q hit)) apart
  have chronology:run (span 225 45) [] baseRaw=run (span 255 15) [] (run (span 225 30) [] baseRaw):=by
    rw [spanAppend 225 30 15,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h

def mask270:=mask255++lastBank
def prog270 (d:Bool):=prog255 d ++ Rolling1588.encodeAt base d 255

theorem add270 (d:Bool) (raw baseRaw out:State)
    (old:Except mask255 raw (run (prog255 d) [] (run (span 225 45) [] baseRaw)))
    (step:Except lastBank out (run (Rolling1588.encodeAt base d 255) [] (run (span 270 1) [] raw))) :
    Except mask270 out (run (prog270 d) [] (run (span 225 46) [] baseRaw)) := by
  have maskEarly:∀q∈mask255,oldRange 270 q:=by decide +kernel
  have progEarly:∀q∈wires (prog255 d),oldRange 270 q:=by cases d <;> decide +kernel
  have apart:∀q∈mask255,q∉wires (Rolling1588.encodeAt base d 255):=by cases d <;> decide +kernel
  have h:=extend 270 1 (by decide) _ _ _ _ raw (run (span 225 45) [] baseRaw) out old step
    (fun q hit=>early _ _ (maskEarly q hit)) (fun q hit=>early _ _ (progEarly q hit)) apart
  have chronology:run (span 225 46) [] baseRaw=run (span 270 1) [] (run (span 225 45) [] baseRaw):=by
    rw [spanAppend 225 45 1,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h
end ECDSAAdd.Entrant.StairPacket.OrdinaryChain

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open WindowFieldMask WindowFieldCosts WindowFieldJourney StairField2V3Seg StairPhysicalLayout
open StairField2V3LastRecX StairField2V3RecScratch StairField2V3Replay StairField2V3Delta
open StairOuterPlacement
set_option maxRecDepth 1600
set_option maxHeartbeats 300000
attribute [local irreducible] run

theorem exitFrame (c x : Nat) (t : State) (h : StairField2V3ExitRec.InvE x c t) : FrameAt x c t := by
  obtain ⟨o,X,Y,s,ctx,en,tr,_,frame,agree⟩ := h
  exact ⟨o,X,Y,s,ctx,en,tr,frame,agree⟩

/-- Instantiate the three real windows from the pinned native field invariant and the original
staircase loan agreement. No per-packet event, schedule, or frame is an input. -/
theorem caller (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (actual ref record : State) (m : List Bool)
    (initial : Fits rows (initialCode d) actual (pullIn ref))
    (pinned : FrameAt x (if d then 1 else 85) record) (agreement : AgreeOutside (Δv 87) ref record)
    (tag : ref.basis (fieldPlace (base 720))=false)
    (loan : ∀ q∈StairSchedule.exclusiveRoles++hosts 87, ref.basis (fieldPlace q)=false) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84 d) m actual)
      (run (group d 1 84) (referenceTape d (plan d) m) (pullIn ref)) := by
  obtain ⟨origin,X,Y,s,ctx,en,tr,fr,ag⟩ := pinned
  apply three_run d x rows rb origin ctx en tr history m _ _ initial
  apply from_record _ origin X Y (pullIn ref) s fr tag (host_fixed (pullIn ref) loan)
  intro q off future
  apply Eq.trans (agreement.2 (fieldPlace q) ?_) (ag q off)
  intro used
  obtain ⟨v,hv,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp used)
  have same := congrArg fieldPlaceInv eq
  rw [inv_fieldPlace,inv_fieldPlace] at same
  exact future (same ▸ hv)
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.Stair44Kernel
open Arithmetic MappedCompressed Secp256k1 DirectSkywalk StairConcreteAssembly Rolling1588Lifetime
open ParityXExitInverse23Kernel
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount wires renameProgram

def finishM := Six505.merged6 ++ Six505.packP false ++ ForwardSixPlacement.after false ++ skywalkArithmeticClear base
def mulLead := renameProgram phaseHost (openR false 489 ++ finishM)
def beforeX := (mulLead ++ StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) ++
  renameProgram phaseHost checkpointPrimitives.firstUnpack
def stockBeforeX := Stair44MultiplyCut.beforeClose hostPlan ++ renameProgram phaseHost checkpointPrimitives.firstUnpack
def mulRawTail (k : Nat) := Stair44WalkRun.backward true 409 ++ renameProgram rawX (x1N k)
def stockTail (k : Nat) := Rolling1588.reverse true 1 424 ++ x1N k
def multiplication (k : Nat) := beforeX ++ renameProgram phaseHost (mulRawTail k)
def outMap : Equiv.Perm Wire := (phaseHost.symm.trans rawOut).trans phaseHost

private theorem actualOpening : Rolling1588TickGap.firstPhase false = openS false 489 ++ finishM := by
  simp only [Rolling1588TickGap.firstPhase, Rolling1588TickGap.tailPhase, Rolling1588TickGap.stackForward,
    Six505.stackForward6,openS,finishM,List.append_assoc]

private theorem leadCountM : measurementCount mulLead = measurementCount StairField2V3Replay.exitReferenceOpening := by
  rw [StairField2V3Replay.exitReferenceOpening,actualOpening,mulLead,(renameProgram_counts _ _).2,
    (renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,open_count]

private theorem leadRunM (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    run mulLead m s=run StairField2V3Replay.exitReferenceOpening m s := by
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [mulLead, StairField2V3Replay.exitReferenceOpening,run_rename _ phaseHost.injective,
    run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_exit F,actualOpening]
  exact with_tail false 489 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup s F.input _ m

private theorem prefixCount (A B V W : Program) (h : measurementCount A=measurementCount B) :
    measurementCount ((A++V)++W)=measurementCount ((B++V)++W) := by
  simp only [measurementCount_append,h]

private theorem prefixRun (A B V W : Program) (s : State) (m : List Bool)
    (cnt : measurementCount A=measurementCount B) (same : ∀ n,run A n s=run B n s) :
    run ((A++V)++W) m s=run ((B++V)++W) m s := by
  simp only [run_append,measurementCount_append,cnt,same]

private theorem countHead : measurementCount beforeX=measurementCount stockBeforeX :=
  prefixCount mulLead StairField2V3Replay.exitReferenceOpening
    (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)
    (renameProgram phaseHost checkpointPrimitives.firstUnpack) leadCountM

private theorem runHead (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    run beforeX m s=run stockBeforeX m s :=
  prefixRun mulLead StairField2V3Replay.exitReferenceOpening
    (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)
    (renameProgram phaseHost checkpointPrimitives.firstUnpack) s m leadCountM (leadRunM k F)

private theorem stockShape (k : Nat) : StairHostsSchedule.exitKernel checkpointPrimitives hostPlan k=
    stockBeforeX ++ renameProgram phaseHost (stockTail k) := by
  simp only [StairHostsSchedule.exitKernel,stockBeforeX,Stair44MultiplyCut.beforeClose,
    StairField2V3Replay.exitReferenceOpening,StairHostsSchedule.lastXN,StairSchedule.stackReverse15,
    stockTail,Six505.rename_append,List.append_assoc]

private theorem actualStockZeros (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    let out := run (StairHostsSchedule.exitKernel checkpointPrimitives hostPlan k) m s
    (pullState phaseHost out).basis (base 1026)=false ∧ (pullState phaseHost out).basis (base 514)=false := by
  have old := StairCallerReplay.hostedExit_pw hostReplay k F.k_lt F.sharedNodup F.historyAbove F.selectorsAway
    F.transcript F.x F.Y F.x_pos F.x_lt s m F.input F.selectorG_zero F.selectorS_zero
  have info := kernelX_correct k F.k_lt F.sharedNodup F.historyAbove F.selectorsAway F.transcript
    F.x F.Y F.x_pos F.x_lt s m F.input F.selectorG_zero F.selectorS_zero
  dsimp only
  rw [old]
  have z (j : Nat) (h : j=721 ∨ j=514) : (run (kernelX k) m s).basis (base j)=false := by
    rcases h with rfl|rfl
    all_goals exact (info.2.2.2 _ (by decide) (by decide)).trans (F.input.2.2 _ (by decide) (by decide) (by decide))
  simp only [pullState,show phaseHost (base 1026)=base 721 by decide +kernel,
    show phaseHost (base 514)=base 514 by decide +kernel]
  simpa only [ParityEven.put,writeBit,Function.update_of_ne (by decide : base 721≠pkP),
    Function.update_of_ne (by decide : base 514≠pkP)] using And.intro (z 721 (Or.inl rfl)) (z 514 (Or.inr rfl))

private theorem tailJoin (beforeX stockBeforeX : Program) (old : Nat→Program) (k x : Nat) {s : State} (m : List Bool)
    (countHead : measurementCount beforeX=measurementCount stockBeforeX)
    (runHead : ∀ u,run beforeX u s=run stockBeforeX u s)
    (hp : 0<x) (hx : x<p)
    (quantified : ∀u,∃ (s1 : State) (enc : List Bool),W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis ∧
      pullState phaseHost (run stockBeforeX u s)=run (Rolling1588TickGap.forward true 1 424) enc s1)
    (stockShape : old k=stockBeforeX ++ renameProgram phaseHost (stockTail k))
    (z0 : (pullState phaseHost (run (old k) m s)).basis (base 1026)=false ∧ (pullState phaseHost (run (old k) m s)).basis (base 514)=false) :
    run (beforeX ++ renameProgram phaseHost (mulRawTail k)) m s=pullState outMap.symm (run (old k) m s) := by
  let out := run (old k) m s
  let suffix := m.drop (measurementCount stockBeforeX)
  let tape := m.take (measurementCount stockBeforeX)
  obtain ⟨v,ev⟩ : ∃ u : State,run stockBeforeX tape s=u := ⟨_,rfl⟩
  have quant : ∃ s1 enc,
      W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 (State.basis s1) ∧
      pullState phaseHost v=run (Rolling1588TickGap.forward true 1 424) enc s1 := by
    rw [←ev];exact quantified tape
  obtain ⟨s1,enc,stage,eq⟩ := quant
  have src : pullState phaseHost out=run (stockTail k) suffix (pullState phaseHost v) := by
    change pullState phaseHost (run (old k) m s)=_
    rw [stockShape,run_append]
    change pullState phaseHost (run (renameProgram phaseHost (stockTail k)) suffix (run stockBeforeX tape s))=_
    rw [ev,run_rename _ phaseHost.injective]
  have z := z0
  have reduce := reverseX k x hp hx s1 stage (pullState phaseHost v) enc eq suffix
  change run (mulRawTail k) suffix _ = pullState rawX.symm (run (stockTail k) suffix _) at reduce
  rw [←src,xAfter _ z.1 z.2] at reduce
  change run (beforeX ++ renameProgram phaseHost (mulRawTail k)) m s=pullState outMap.symm out
  rw [run_append,countHead,runHead];change run _ suffix (run stockBeforeX tape s)=_
  rw [ev]
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [run_rename _ phaseHost.injective,reduce]
  apply State.extensionality
  · rfl
  · funext q
    simp only [out,pullState,outMap,Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.symm_apply_apply]

theorem mul_run (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    run (multiplication k) m s=pullState outMap.symm
      (run (StairHostsSchedule.exitKernel checkpointPrimitives hostPlan k) m s) := by
  apply tailJoin beforeX stockBeforeX (StairHostsSchedule.exitKernel checkpointPrimitives hostPlan)
    k F.x m countHead (runHead k F) F.x_pos F.x_lt _ (stockShape k) (actualStockZeros k F m)
  intro u
  rw [stockBeforeX,run_append]
  exact Stair44MultiplyCut.pool k F _ _

end ECDSAAdd.Entrant.Stair44Kernel

end

section

namespace ECDSAAdd.Entrant.Stair44Placement
open Arithmetic MappedCompressed Baselines StairPlaceFast Stair44PointMap Stair44WalkMap Stair44Kernel
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000

def phys (q : Wire) := wireFn2 layout (Rolling1588Lifetime.phaseHost q)
def fast (q : Wire) := pwB (swB 785 1813 (phaseHostB q)-16)

theorem phys_fast (q : Wire) : phys q=fast q := by
  simp only [phys,fast,wireFn2_eqN,phaseHost_eqN,phaseHostB,phaseHostN,pwB_eq,swB_eq]

private theorem high (q : Wire) (h : 2428 ≤ q) : fast q=0 := by
  have ne (i : Nat) (hi : i<2428) : q≠i := fun eq => (Nat.not_lt_of_ge h) (eq ▸ hi)
  have hrest : 12≤q-16-2400 := Nat.le_sub_of_add_le (Nat.le_sub_of_add_le h)
  have ne2 (i : Nat) (hi : i<12) : q-16-2400≠i := fun eq => (Nat.not_lt_of_ge hrest) (eq ▸ hi)
  have above : ¬q-16<2314 := Nat.not_lt_of_ge (Nat.le_trans (by decide : 2314≤2412) (Nat.le_sub_of_add_le h))
  simp only [fast,phaseHostB,swB_eq,pwB_eq,sw,pwN,metaN,above,
    ne _ (by decide : 1042<2428),ne _ (by decide : 737<2428),ne _ (by decide : 1557<2428),
    ne _ (by decide : 738<2428),ne _ (by decide : 1558<2428),ne _ (by decide : 736<2428),
    ne _ (by decide : 785<2428),ne _ (by decide : 1813<2428),ite_false]
  simp (disch := decide) only [ne2,ite_false]

private theorem boundMap (q : Wire) (h : 2428 ≤ q) : first q=q ∧ rawX q=q ∧ rawOut q=q := by
  have ne (i : Nat) (hi : base i<2428) : q≠base i := fun eq => (Nat.not_lt_of_ge h) (eq ▸ hi)
  simp (disch := decide) only [rawX,rawOut,first,shared,chain,Equiv.trans_apply,Equiv.swap_apply_def,
    ne,ite_false,Equiv.refl_apply,and_self]

def test (q : Wire) := fast (first q)==integerFirst (fast q) &&
  fast (rawX q)==duringX (fast q) && fast (rawOut q)==outer (fast q)

private theorem checked : (List.range 2428).all test=true := by decide +kernel

theorem maps (q : Wire) : phys (first q)=integerFirst (phys q) ∧
    phys (rawX q)=duringX (phys q) ∧ phys (rawOut q)=outer (phys q) := by
  simp only [phys_fast]
  by_cases h : q<2428
  · have t := List.all_eq_true.mp checked q (List.mem_range.mpr h)
    simpa only [test,Bool.and_eq_true,beq_iff_eq,and_assoc] using t
  · have f := boundMap q (Nat.le_of_not_gt h)
    rw [f.1,f.2.1,f.2.2,high q (Nat.le_of_not_gt h)]
    decide +kernel

end ECDSAAdd.Entrant.Stair44Placement

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChain
open Arithmetic MappedCompressed IntegerPacket WideReference StockWindowTicket
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
theorem holes240 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool)
    (pre:At240 d x p raw s g sg pg ps) :
    ∀q∈NativePack240.fourHoles,(endRaw 240 raw (run (NativePack240.nextWindow d) m s)).basis q=false := by
  let z:=unsigned 240 x p
  have nums:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+240+r))=false:=by
    simpa only [Nat.add_assoc] using future_history (j:=240+r.val) (by omega) (by have hr:=r.isLt;omega) pre.domain
  have inp:=readInput 240 x p raw g sg pre.input
  have prev:=Leave225Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have clear:=NativePack240.cleared_holes d raw s m z g sg nums.odd nums.small pre.cut inp hist (unsigned 225 x p) pg ps _ prev.odd prev.small pre.facts
  have inside:∀q∈NativePack240.fourHoles,q∈sites 240:=by decide +kernel
  intro q h
  rw [endRaw_inside _ _ _ fixed240 _ (inside q h)]
  exact clear q h

theorem holes255 (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool)
    (pre:At255 d x p raw s g sg pg ps) :
    ∀q∈NativePack255.fourHoles,(endRaw 255 raw (run (NativePack255.nextWindow d) m s)).basis q=false := by
  let z:=unsigned 255 x p
  have nums:=Leave255Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have hist (r:Fin 15):raw.basis (base (1028+255+r))=false:=by
    simpa only [Nat.add_assoc] using future_history (j:=255+r.val) (by omega) (by have hr:=r.isLt;omega) pre.domain
  have inp:=readInput 255 x p raw g sg pre.input
  have prev:=Leave240Admission.actualNumbers x p good.positive good.odd (lt_trans good.small good.cap) good.cap
  have clear:=NativePack255.cleared_holes d raw s m z g sg nums.odd nums.small pre.cut inp hist (carry (by decide) pre.domain) (unsigned 240 x p) pg ps _ prev.odd prev.small pre.facts
  have inside:∀q∈NativePack255.fourHoles,q∈sites 255:=by decide +kernel
  intro q h
  rw [endRaw_inside _ _ _ fixed255 _ (inside q h)]
  exact clear q h

theorem carry255 (raw history:State) (clear:∀q∈NativePack240.fourHoles,raw.basis q=false):
    ∀q∈NativePack240.fourHoles,(endRaw 255 raw history).basis q=false := by
  have old:∀q∈NativePack240.fourHoles,oldRange 255 q:=by decide +kernel
  have outside:∀q∈NativePack240.fourHoles,q∉sites 255:=by decide +kernel
  intro q h
  rw [endRaw_outside _ (by decide) _ _ fixed255 _ (outside q h),run_preserves_outside _ _ _ _ (pastOffSpan _ _ _ (by decide) (early 255 q (old q h)))]
  exact clear q h
end ECDSAAdd.Entrant.StairPacket.OrdinaryChain

end

section

namespace ECDSAAdd.Entrant.Stair44CallerSupport
open Arithmetic MappedCompressed DirectSkywalk StairConcreteAssembly StairSemanticFinal
open Stair44WalkMap Stair44Kernel
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
attribute [local irreducible] wires renameProgram

private theorem swap (i j : Nat) (hi : i < 2314) (hj : j < 2314) :
    PreservesCaller (Equiv.swap (base i) (base j)) :=
  preserves_swap _ _ (base_mem_caller _ (Or.inl hi)) (base_mem_caller _ (Or.inl hj))

private theorem firstOK : PreservesCaller Stair44WalkMap.first := by
  unfold Stair44WalkMap.first shared
  repeat' apply preserves_perm_trans
  all_goals exact swap _ _ (by decide) (by decide)

private theorem restOK : PreservesCaller rest := by
  unfold rest shared
  repeat' apply preserves_perm_trans
  all_goals exact swap _ _ (by decide) (by decide)

private theorem rawOK : PreservesCaller rawX := by
  unfold rawX rawOut
  simp only [Stair44PointMap.chain]
  repeat' apply preserves_perm_trans
  all_goals first | exact swap _ _ (by decide) (by decide) | exact fun _ h => h

private theorem forward (d : Bool) (a : Nat) (h : 15+a ≤ 504) :
    wires (Stair44WalkRun.forward d a) ⊆ callerDomain := by
  have both := forward_own d (15+a) h
  rw [tickGap_forward_split d 15 1 a, wires_append, Finset.union_subset_iff] at both
  exact wires_sub_of_parts _ _ (rename_caller _ firstOK _ both.1) (rename_caller _ restOK _ both.2)

private theorem backward (d : Bool) (a : Nat) (h : 15+a ≤ 505) :
    wires (Stair44WalkRun.backward d a) ⊆ callerDomain := by
  have both := reverse_own d (15+a) h
  rw [reverse_split d 15 1 a,wires_append,Finset.union_subset_iff] at both
  exact wires_sub_of_parts _ _ (rename_caller _ restOK _ both.1) (rename_caller _ firstOK _ both.2)

private theorem opening (d : Bool) (a : Nat) (h : 15+a ≤ 504) :
    wires (openR d a) ⊆ callerDomain :=
  wires_sub_of_parts _ _ (rename_caller _ firstOK _ nativeForward_own) (forward d a h)

private theorem closing : wires Stair44DivTerm.routedClose ⊆ callerDomain := by
  have h := lastPhase_false_own
  simp only [InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
    wires_append,Finset.union_subset_iff] at h
  unfold Stair44DivTerm.routedClose Stair44DivTerm.head
  exact wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ h.1.1 (wires_sub_of_parts _ _ h.1.2.1 h.1.2.2.1))
    (wires_sub_of_parts _ _ (backward false 490 (by decide)) (rename_caller _ firstOK _ h.2))

theorem division : wires Stair44Kernel.division ⊆ callerDomain :=
  wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ (phaseHost_caller _ (wires_sub_of_parts _ _
      (opening true 409 (by decide)) cp_firstPack)) entryFieldHostedV3_caller)
    (phaseHost_caller _ closing)

private theorem finish : wires finishM ⊆ callerDomain := by
  have h := firstPhase_own false
  simp only [Rolling1588TickGap.firstPhase, Rolling1588TickGap.tailPhase,
    Rolling1588TickGap.stackForward,Six505.stackForward6,wires_append,Finset.union_subset_iff] at h
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ h.2.1.2.1 h.2.1.2.2.1) h.2.1.2.2.2) h.2.2

theorem multiplication (k : Nat) : wires (Stair44Kernel.multiplication k) ⊆ callerDomain :=
  wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (phaseHost_caller _ (wires_sub_of_parts _ _ (opening false 489 (by decide)) finish))
    exitFieldHostedV3_caller) (phaseHost_caller _ cp_firstUnpack))
    (phaseHost_caller _ (wires_sub_of_parts _ _ (backward true 409 (by decide))
      (rename_caller _ rawOK _ (x1N_own k))))

end ECDSAAdd.Entrant.Stair44CallerSupport

end

section

namespace ECDSAAdd.Entrant.Stair44Splits
open Arithmetic MappedCompressed Baselines Stair44Placement Stair44PointMap Stair44WalkMap Stair44Kernel
open Stair44Outer Rolling1588Lifetime Secp256k1
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

def tick := renameProgram integerFirst (E1QubitPlacement.tickF layout)

theorem placeMove (f g : Wire → Wire) (h : ∀q,phys (f q)=g (phys q)) (P : Program) :
    phasePlace (renameProgram f P)=renameProgram g (phasePlace P) := by
  simp only [phasePlace,kernelPlace,renameProgram_comp]
  congr 1; funext q;exact h q

theorem tick_eq : phasePlace firstR=tick := by
  rw [firstR,placeMove first integerFirst (fun q => (maps q).1)]
  exact congrArg (renameProgram integerFirst) (E1QubitPlacement.tick_eq layout)

theorem phaseAppend (P Q : Program) : phasePlace (P++Q)=phasePlace P++phasePlace Q := by
  simp only [phasePlace,kernelPlace,Six505.rename_append]

theorem div_split : FrontierEntry1591Callers.entry Stair44Kernel.division layout = tick ++ Stair44Outer.divide := by
  change kernelPlace ((renameProgram phaseHost (openR true 409 ++ _) ++ _) ++ renameProgram phaseHost _) = _
  simp only [Stair44Outer.divide,openR,Stair44DivTerm.routedClose,kernelPlace,Six505.rename_append,List.append_assoc]
  change phasePlace firstR ++ _ = tick ++ _
  rw [tick_eq]
  simp only [reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,phasePlace,kernelPlace,Six505.rename_append,List.append_assoc]

theorem mul_split (k : Nat) : FrontierEntry1591Callers.exit (multiplication k) layout=tick ++ multiply k := by
  change kernelPlace (multiplication k) = _
  simp only [multiplication,beforeX,mulLead,openR,mulRawTail,multiply,kernelPlace,Six505.rename_append,List.append_assoc]
  change phasePlace firstR ++ _ = tick ++ _
  rw [tick_eq]
  rw [show Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k)) =
      phasePlace (renameProgram rawX (ParityXExitInverse23Kernel.x1N k)) from
    (placeMove rawX duringX (fun q => (maps q).2.1) _).symm]
  rfl
end ECDSAAdd.Entrant.Stair44Splits

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChain
open Arithmetic MappedCompressed IntegerPacket WideReference StockWindowTicket Partial ArchiveHistoryCompare Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 3800000
attribute [local irreducible] run measurementCount
def older:=NativePack240.fourHoles++NativePack255.fourHoles
def norm (d:Bool) (raw:State):=run (prog270 d) [] (run (span 225 46) [] raw)

private theorem project (d:Bool) (raw out:State) (direct:Except Ordinary270Terminal.newBank out (pullState (OB5.sig 270) (run (Rolling1588.encodeAt base d 255) [] (run EndTick.canonical [] raw)))):
    Except lastBank (pullState (OB5.sig 270) out) (run (Rolling1588.encodeAt base d 255) [] (run (span 270 1) [] raw)) := by
  have one:span 270 1=EndTick.canonical:=by simp [span,EndTick.canonical]
  rw [one]
  intro q absent
  have map:∀w∈Ordinary270Terminal.newBank,OB5.sig 270 w∈lastBank:=by decide +kernel
  have free:OB5.sig 270 q∉Ordinary270Terminal.newBank:=fun hit=>absent (by simpa only [OB5.sig_invol 270 (by decide)] using map _ hit)
  simpa only [pullState,OB5.sig_invol 270 (by decide)] using direct _ free

private theorem readOld (out standard raw:State)
    (direct:Except Ordinary270Terminal.newBank out (pullState (OB5.sig 270) standard))
    (untouched:∀q∈older,standard.basis q=raw.basis q) (cleared:∀q∈older,raw.basis q=false)
    (q:Wire) (hit:q∈older):out.basis q=false:=by
  have fix:∀w∈older,OB5.sig 270 w=w:=by decide +kernel
  have free:∀w∈older,w∉Ordinary270Terminal.newBank:=by decide +kernel
  have eq:=direct q (free q hit)
  change out.basis q=standard.basis (OB5.sig 270 q) at eq
  rw [fix q hit] at eq
  exact eq.trans ((untouched q hit).trans (cleared q hit))

private theorem keepTick (raw:State) (q:Wire) (hit:q∈older):(run EndTick.canonical [] raw).basis q=raw.basis q:=by
  have earlier:∀w∈older,oldRange 270 w:=by decide +kernel
  have one:span 270 1=EndTick.canonical:=by simp [span,EndTick.canonical]
  rw [←one]
  exact run_preserves_outside _ _ _ _ (pastOffSpan _ _ _ (by decide) (early _ _ (earlier q hit)))

private theorem keepEncode (d:Bool) (raw:State) (q:Wire) (hit:q∈older):(run (Rolling1588.encodeAt base d 255) [] raw).basis q=raw.basis q:=by
  have safe:∀w∈older,w∉wires (Rolling1588.encodeAt base d 255):=by cases d <;> decide +kernel
  exact run_preserves_outside _ _ _ _ (safe q hit)

private theorem finish (d:Bool) (out initial:State)
    (all:Except mask270 (pullState (OB5.sig 270) out) (norm d initial))
    (saved:∀q∈older,out.basis q=false) (last:∀q∈NativePack270.fourHoles,out.basis q=false):
    ∀q∉ArchiveStockSuffix.archives,out.basis q=(StockArchiveReference.common d initial).basis q := by
  intro q away
  let y:=OB5.sig 270 q
  have inv:OB5.sig 270 y=q:=OB5.sig_invol 270 (by decide) q
  change out.basis q=(eraseSites StockArchiveReference.holes (norm d initial)).basis y
  by_cases hole:y∈StockArchiveReference.holes
  · have which:∀w∈StockArchiveReference.holes,OB5.sig 270 w∈older ∨ OB5.sig 270 w∈NativePack270.fourHoles:=by decide +kernel
    have h:=which y hole
    rw [inv] at h
    simp only [eraseSites,if_pos hole]
    exact h.elim (saved q) (last q)
  · have census:∀w∈mask270,w∈StockArchiveReference.holes ∨ OB5.sig 270 w∈ArchiveStockSuffix.archives:=by decide +kernel
    have free:y∉mask270:=fun hit=>away (inv ▸ (census _ hit).resolve_left hole)
    have value:=all y free
    change out.basis (OB5.sig 270 y)=(norm d initial).basis y at value
    rw [inv] at value
    simpa only [eraseSites,if_neg hole] using value

theorem terminal (d:Bool) (x:Nat) (good:Bounds x p) (raw s initial:State) (g sg pg ps:Bool) (m:List Bool)
    (pre:At270 d x p raw s g sg pg ps)
    (prior:Except mask255 raw (run (prog255 d) [] (run (span 225 45) [] initial)))
    (cleared:∀q∈older,raw.basis q=false) :
    let out:=run (NativePack270.lastWindow d) m s
    ∀q∉ArchiveStockSuffix.archives,out.basis q=(StockArchiveReference.common d initial).basis q := by
  let out:=run (NativePack270.lastWindow d) m s
  have direct:=Ordinary270Native.result d x good raw s g sg pg ps m pre
  obtain ⟨row,_,_,frame⟩:=(step270 d x good s m ⟨raw,g,sg,pg,ps,pre⟩).2.1.last
  exact finish d out initial (add270 d raw initial _ prior (project d raw out direct))
    (readOld out _ raw direct (fun q hit=>(keepEncode d _ q hit).trans (keepTick raw q hit)) cleared) (NativePack270.cleared_holes d row out frame)
end ECDSAAdd.Entrant.StairPacket.OrdinaryChain

end

section

namespace ECDSAAdd.Entrant.Stair44PointWord
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog ParityEven ParityXExitInverse23Kernel StairSemanticFinal
  Stair44Kernel Stair44PointMap Baselines StairConcreteAssembly
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run wires measurementCount

def normalized (k : Nat) := renameProgram outMap.symm (multiplication k)

private theorem conjugate (p a : Equiv.Perm Wire) (q : Wire) :
    ((p.symm.trans a).trans p).symm (p q)=p (a.symm q) := by
  simp only [Equiv.symm_trans_apply,Equiv.symm_symm,Equiv.symm_apply_apply]

private theorem conjugateInv (p a : Equiv.Perm Wire) (q : Wire) :
    ((p.symm.trans a).trans p).symm q=p (a.symm (p.symm q)) := by
  simp only [Equiv.symm_trans_apply,Equiv.symm_symm]

private theorem clean {k : Nat} {s : State} (F : ExitFrame k s) : pullState outMap.symm s=s := by
  let pairs : List (Wire × Wire) := [(base 1542,base 500),(base 1026,base 501),(base 1541,base 502),
    (base 723,base 503),(base 724,base 504)]
  let ok (q : Wire) := phaseHost q∈skywalkSharedWires base ∧ phaseHost q∉wireBlock base 770 256 ∧
    phaseHost q∉wireBlock base 2056 256
  have small : ∀ab∈pairs,ok ab.1 ∧ ok ab.2 := by unfold ok; decide +kernel
  have z (q : Wire) (hq : ok q) : (pullState phaseHost s).basis q=false := F.input.2.2 _ hq.1 hq.2.1 hq.2.2
  have fixed : pullState rawOut (pullState phaseHost s)=pullState phaseHost s :=
    (clean_chain pairs id _ _ (fun ab hab => ⟨z _ (small ab hab).1,z _ (small ab hab).2⟩)).mpr rfl
  have inv := congrArg (pullState rawOut.symm) fixed
  rw [Stair44PlacedHead.unpull] at inv
  apply MappedCompressed.pullState_perm_injective phaseHost
  apply State.extensionality
  · rfl
  · funext q
    exact (congrArg s.basis (conjugate phaseHost rawOut q)).trans
      (congrFun (congrArg State.basis inv.symm) q)

private theorem rawOutPreserves : PreservesCaller rawOut.symm := by
  unfold rawOut
  simp only [chain]
  repeat' apply preserves_symm_trans
  all_goals first | exact preserves_swap_symm _ _ (base_mem_caller _ (Or.inl (by decide))) (base_mem_caller _ (Or.inl (by decide))) | exact fun _ h => h

private theorem keep : PreservesCaller outMap.symm :=
  preserves_symm_trans _ _ (preserves_symm_trans _ _ preserves_phaseHost rawOutPreserves) preserves_phaseHost_symm

private theorem normSupport (k : Nat) : wires (normalized k)⊆callerDomain :=
  rename_caller outMap.symm keep (multiplication k) (Stair44CallerSupport.multiplication k)

private theorem normalizedRun {k : Nat} {s : State} (F : ExitFrame k s) (m : List Bool) :
    run (normalized k) m s=run (StairHostsSchedule.exitKernel StairConcreteAssembly.checkpointPrimitives StairConcreteAssembly.hostPlan k) m s := by
  apply MappedCompressed.pullState_perm_injective outMap.symm
  rw [normalized,run_rename _ outMap.symm.injective,clean F,mul_run k F]

theorem physInv (q : Wire) : wireFn2 layout (outMap.symm q)=outer.symm (wireFn2 layout q) := by
  rw [show outMap.symm q=phaseHost (rawOut.symm (phaseHost.symm q)) from conjugateInv _ _ _]
  apply outer.injective
  rw [Equiv.apply_symm_apply]
  have e := (Stair44Placement.maps (rawOut.symm (phaseHost.symm q))).2.2.symm
  rw [Equiv.apply_symm_apply] at e
  simpa only [Stair44Placement.phys,Equiv.apply_symm_apply] using e

theorem transport (f a b : Wire→Wire) (P : Program) (eq : ∀q,f (a q)=b (f q)) :
    renameProgram f (renameProgram a P)=renameProgram b (renameProgram f P) :=
  (renameProgram_comp f a P).trans ((congrArg (fun g : Wire→Wire => renameProgram g P) (funext eq)).trans
    (renameProgram_comp b f P).symm)

theorem fullWord (k X Y : Nat) (hk : k<p) (hp : 0<X) (hx : X<p) (hy : Y<p) (s : State) (m : List Bool)
    (sx : regValue layout.point.x s.basis=X) (sy : regValue layout.point.y s.basis=Y)
    (sc : regValue layout.dialogPool s.basis=0) :
    let C := FrontierEntry1591Callers.exit (multiplication k) layout
    run C m s=pullState outer.symm (put (run (FrontierEntry1591Callers.exit (kernelX k) layout) m s)
      (wireFn2 layout pkP) (s.basis layout.core.generic && decide (k<X))) := by
  intro C
  have yn : (Y:Fp).val=Y := ZMod.val_natCast_of_lt hy
  rcases placement2 layout layout_widths layout_nodup with ⟨_,dx,dy,g,_,sg,ss,_⟩
  have pk : pkP∈callerDomain := by
    have a := E1QubitPlacement.sw_logical 724 (by unfold E1QubitPlacement.Rng; omega)
    exact logical_sub_caller (by simpa [E1QubitPlacement.sw,pkP] using a)
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have W := wordTransferN layout (wireFn2 layout) k callerDomain
    (wireFn2_injOn_caller layout layout_widths layout_nodup) dx dy g (sharedWork_caller layout layout_widths)
    sg ss divisor_caller numerator_caller generic_caller pk X (Y:Fp) s m sx (sy.trans yn.symm) sc
    (normalized k) (kernelX k) (normSupport k) ((kernelX_support k).trans logical_sub_caller)
    (fun t records input hg hs => by
      let F : ExitFrame k t := ⟨hk,config.1,above,config.2.1,config.2.2,X,(Y:Fp),hp,hx,input,hg,hs⟩
      rw [normalizedRun F]
      exact StairCallerReplay.hostedExit_pw hostReplay k hk config.1 above config.2.1 config.2.2 X (Y:Fp) hp hx t records input hg hs)
  have place : renameProgram (wireFn2 layout) (normalized k)=renameProgram outer.symm C :=
    transport (wireFn2 layout) outMap.symm outer.symm (multiplication k) physInv
  have o : pullState outer.symm s=s := by
    have members : ∀ab∈earlyPairs,ab.1∈layout.dialogPool ∧ ab.2∈layout.dialogPool := by decide +kernel
    have f : pullState outer s=s := (clean_chain earlyPairs id s s (fun ab h =>
      ⟨(regValue_zero _ _).mp sc _ (members ab h).1,(regValue_zero _ _).mp sc _ (members ab h).2⟩)).mpr rfl
    have u := congrArg (pullState outer.symm) f
    rw [Stair44PlacedHead.unpull] at u; exact u.symm
  rw [place] at W
  have e := run_rename outer.symm outer.symm.injective C m s
  rw [o,W] at e
  exact e.symm

end ECDSAAdd.Entrant.Stair44PointWord

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorCaller
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines StairSemanticFinal StairConcreteAssembly
open StairRestSupport StairPhysicalV3 ArchiveFieldScratch StairArchiveRelease StairArchiveGates
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] wires packet renameProgram
def GoodP (P:Program):Prop:=wires P ⊆ callerDomain
private theorem app {a b:Program} (ha:GoodP a) (hb:GoodP b):GoodP (a++b):=by
  intro w hit
  exact (Finset.mem_union.mp (wires_append a b ▸ hit)).elim (fun x=>ha x) (fun x=>hb x)
private theorem ordinary (d:Bool) (j n:Nat) (hi:j+n≤102):GoodP (group d j n):=hostedGroupV3_caller d 0 j n (by decide) hi
private theorem singleton (d:Bool) (j:Nat) (hi:j+1≤102):GoodP (packet d j):=by
  have pass:=ordinary d j 1 hi
  change GoodP (StairHostsSchedule.hostedGroup hostPlan d 0 j 1) at pass
  rw [distribute] at pass
  cases d <;> simpa only [distributed,PacketSequence.program,if_true,if_false,Bool.false_eq_true,List.append_nil,List.nil_append] using pass
private theorem hook (j:Nat) (hj:j∈[46,49,52]) (op:Stage):GoodP (fieldHook j op):=by
  have span:j∈List.range' 1 83:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;apply List.mem_range'_1.mpr;omega
  have table:∀(j:Nat),j∈[46,49,52]→∀q∈fieldSites j,16 ≤ q ∧ q < 2330:=by decide +kernel
  intro q hit
  rw [fieldHook,renameProgram_support] at hit
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hit
  have len:(fieldSites j).length=121:=by have hh:=(layout_frame j span).2;rwa [←field_layout,List.length_map] at hh
  have lt:w < (fieldSites j).length:=len ▸ (Finset.mem_range.mp (sub op hw))
  have pos:=table j hj ((fieldSites j)[w]) (List.getElem_mem lt)
  have toCaller (v:Nat) (h:16≤v ∧ v<2330):v∈callerDomain:=by
    have baseEq:base (v-16)=v:=by simp only [base,Wire];omega
    rw [←baseEq]
    exact base_mem_caller _ (Or.inl (by omega))
  have yes:=toCaller _ pos
  simpa only [fieldPort,List.getElem?_eq_getElem lt,Option.getD_some] using yes
private theorem pair (d:Bool) (j:Nat) (hj:j∈[46,49,52]) (hi:j≤83):GoodP (ten j (!d)):=by
  have here:=singleton d j (by omega)
  have next:=singleton d (j+1) (by omega)
  have a:GoodP (first j (!d)):=by cases d <;> first | exact here | exact next
  have b:GoodP (second j (!d)):=by cases d <;> first | exact here | exact next
  exact app (hook j hj _) (app a (app (hook j hj _) (app b (hook j hj _))))
theorem group84_good (d:Bool):GoodP (group84 d):=by
  have ord {a b:Program} (x:GoodP a) (y:GoodP b):GoodP (ordered d a b):=by cases d <;> first | exact app x y | exact app y x
  exact ord (ordinary d 1 45 (by decide)) (ord (pair d 46 (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide)) (ord (pair d 49 (by decide) (by decide))
    (ord (ordinary d 51 1 (by decide)) (ord (pair d 52 (by decide) (by decide)) (ordinary d 54 31 (by decide)))))))

theorem entryTailPrefix_ours :
    wires (WindowCallerCosts.entryTailPrefix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.entryTailPrefix
  simp only [wires_append, Finset.union_subset_iff, and_assoc]
  exact ⟨group84_good true,
    fseg_caller 87 62 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 14 85 5 (by omega) (by omega),
    fseg_caller 62 47 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 23 90 3 (by omega) (by omega),
    fseg_caller 47 32 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 31 93 3 (by omega) (by omega),
    fseg_caller 32 22 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 37 96 2 (by omega) (by omega),
    fseg_caller 22 12 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 42 98 2 (by omega) (by omega),
    forwardLastV3_caller⟩

theorem exitHeadSuffix_ours :
    wires (WindowCallerCosts.exitHeadSuffix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.exitHeadSuffix
  simp only [wires_append, Finset.union_subset_iff, and_assoc]
  exact ⟨reverseLastV3_caller,
    hostedGroupV3_caller false 42 98 2 (by omega) (by omega),
    rseg_caller 22 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 37 96 2 (by omega) (by omega),
    rseg_caller 32 22 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 31 93 3 (by omega) (by omega),
    rseg_caller 47 32 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 23 90 3 (by omega) (by omega),
    rseg_caller 62 47 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 14 85 5 (by omega) (by omega),
    rseg_caller 87 62 (by decide) (by decide) (by decide) (by decide) (by decide),
    group84_good false⟩

theorem entryLowPrefix_ours :
    wires (WindowCallerCosts.entryLowPrefix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.entryLowPrefix
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (hostedFirstPacketV3_caller true) glue_own.2.2.1)
    (borrow_caller _ entryTailPrefix_ours)) glue_own.2.2.2

theorem exitLowSuffix_ours :
    wires (WindowCallerCosts.exitLowSuffix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.exitLowSuffix
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _ glue_own.2.2.1
    (borrow_caller _ exitHeadSuffix_ours)) glue_own.2.2.2)
    (hostedFirstPacketV3_caller false)

theorem entryFieldHosted_ours :
    wires (WindowCallerCosts.entryFieldHosted StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.entryFieldHosted
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
      (fieldRename_caller _ entryLowPrefix_ours) glue_own.2.1) glue_own.1)
    (fieldRename_caller _ entryLowSuffixV3_caller)) glue_own.1) glue_own.2.1

theorem exitFieldHosted_ours :
    wires (WindowCallerCosts.exitFieldHosted StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.exitFieldHosted
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ (wires_sub_of_parts _ _ glue_own.2.1 glue_own.1)
      (fieldRename_caller _ exitLowPrefixV3_caller)) glue_own.2.1) glue_own.1)
    (fieldRename_caller _ exitLowSuffix_ours)
end ECDSAAdd.Entrant.StairPacket.ExteriorCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChain
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowTicket Partial ArchiveHistoryCompare
set_option maxRecDepth 30000
set_option maxHeartbeats 3800000
attribute [local irreducible] run measurementCount body NativePack225.firstWindow NativePack240.nextWindow NativePack255.nextWindow NativePack270.lastWindow leave225 leave240 leave255
def Ref240 (d:Bool) (x:Nat) (initial s:State):Prop:=
  ∃raw g sg pg ps,At240 d x p raw s g sg pg ps ∧ Except mask225 raw (run (prog225 d) [] (run (span 225 15) [] initial))

def Ref255 (d:Bool) (x:Nat) (initial s:State):Prop:=
  ∃raw g sg pg ps,At255 d x p raw s g sg pg ps ∧ Except mask240 raw (run (prog240 d) [] (run (span 225 30) [] initial)) ∧ (∀q∈NativePack240.fourHoles,raw.basis q=false)

def Ref270 (d:Bool) (x:Nat) (initial s:State):Prop:=
  ∃raw g sg pg ps,At270 d x p raw s g sg pg ps ∧ Except mask255 raw (run (prog255 d) [] (run (span 225 45) [] initial)) ∧ (∀q∈older,raw.basis q=false)

theorem begin225 (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (a b:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis):
    Ref240 d x raw (run leave225 b (run (NativePack225.firstWindow d) a (pullState (OB5.sig 224) raw))) := by
  obtain ⟨g,sg,pg,ps,pre⟩:=pinned225 d x p good raw a b stage
  exact ⟨_,g,sg,pg,ps,pre,ordinary225 d x p good raw a stage⟩

theorem next240 (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State) (c e:List Bool) (h:Ref240 d x initial s):
    Ref255 d x initial (run leave240 e (run (NativePack240.nextWindow d) c s)) := by
  obtain ⟨raw,g,sg,pg,ps,pre,old⟩:=h
  obtain ⟨g',sg',pg',ps',pre'⟩:=pinned240 d x p good raw s g sg pg ps c e pre
  have values:=add240 d raw initial _ old (ordinary240 d x p good raw s g sg pg ps c pre)
  exact ⟨_,g',sg',pg',ps',pre',values,holes240 d x p good raw s g sg pg ps c pre⟩

theorem next255 (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State) (f h:List Bool) (input:Ref255 d x initial s):
    Ref270 d x initial (run leave255 h (run (NativePack255.nextWindow d) f s)) := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=input
  obtain ⟨g',sg',pg',ps',pre'⟩:=pinned255 d x p good raw s g sg pg ps f h pre
  have values:=add255 d raw initial _ old (ordinary255 d x p good raw s g sg pg ps f pre)
  have newZero:=holes255 d x p good raw s g sg pg ps f pre
  exact ⟨_,g',sg',pg',ps',pre',values,fun q hq=>(List.mem_append.mp hq).elim (carry255 raw _ zeros q) (newZero q)⟩

theorem last270 (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State) (j:List Bool) (h:Ref270 d x initial s):
    ∀q∉ArchiveStockSuffix.archives,(run (NativePack270.lastWindow d) j s).basis q=(StockArchiveReference.common d initial).basis q := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  exact terminal d x good raw s initial g sg pg ps j pre old zeros
end ECDSAAdd.Entrant.StairPacket.OrdinaryChain

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelPrograms
open Arithmetic MappedCompressed Baselines Stair44Placement Stair44PointMap Stair44WalkMap Stair44Kernel
open Stair44Outer Rolling1588Lifetime Secp256k1 StairConcreteAssembly StairSemanticFinal
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

def openWalk (d:Bool) (tail:Nat):Program:=Stair44Kernel.firstR++WindowWalkCosts.forward d tail
def divBefore:Program:=renameProgram phaseHost (openWalk true 154++checkpointPrimitives.firstPack)++WindowParityCaller.entryFieldHosted checkpointPrimitives
def divAfter:Program:=Stair44Outer.reverseEnd++(WindowWalkCosts.backward false 235++renameProgram first (FrontierEntry1591NativeH.inverse base))
def division:Program:=divBefore++renameProgram phaseHost divAfter
def mulBefore:Program:=(renameProgram phaseHost (openWalk false 234++Stair44Outer.forwardEnd)++WindowParityCaller.exitFieldHosted checkpointPrimitives)++renameProgram phaseHost checkpointPrimitives.firstUnpack
def mulAfter (k:Nat):Program:=WindowWalkCosts.backward true 154++renameProgram rawX (ParityXExitInverse23Kernel.x1N k)
def multiplication (k:Nat):Program:=mulBefore++renameProgram phaseHost (mulAfter k)

theorem div_split : FrontierEntry1591Callers.entry division layout = Stair44Splits.tick ++ WindowParityCaller.divide := by
  change kernelPlace (divBefore++renameProgram phaseHost divAfter)=_
  simp only [divBefore,divAfter,openWalk,WindowParityCaller.divide,kernelPlace,Six505.rename_append,List.append_assoc]
  change phasePlace Stair44Kernel.firstR ++ _=Stair44Splits.tick ++ _
  rw [Stair44Splits.tick_eq]
  rfl
theorem mul_split (k:Nat) : FrontierEntry1591Callers.exit (multiplication k) layout=Stair44Splits.tick ++ WindowParityCaller.multiply k := by
  change kernelPlace (multiplication k)=_
  simp only [multiplication,mulBefore,mulAfter,openWalk,WindowParityCaller.multiply,kernelPlace,Six505.rename_append,List.append_assoc]
  change phasePlace Stair44Kernel.firstR ++ _=Stair44Splits.tick ++ _
  rw [Stair44Splits.tick_eq]
  rw [show Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k)) =
      phasePlace (renameProgram rawX (ParityXExitInverse23Kernel.x1N k)) from
    (Stair44Splits.placeMove rawX duringX (fun q => (maps q).2.1) _).symm]
  rfl

structure Contracts:Prop where
  divSites:wires division⊆callerDomain
  mulSites:∀k,wires (multiplication k)⊆callerDomain
  enter:FrontierEntry1591Callers.EntryCorrect division
  exit:∀k {s:State},ExitFrame k s→∀m,run (multiplication k) m s=run (Stair44Kernel.multiplication k) m s
end ECDSAAdd.Entrant.StairPacket.WindowKernelPrograms

end

section

namespace ECDSAAdd.Entrant.Stair44PointSecond
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic
  Stair44PointMap Stair44PlacedHead
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount fastConstAdd

theorem joinRecords (A B : Program) (a b : List Bool) (s : State) :
    run (A++B) (pfx (measurementCount A) a ++ b) s=run B b (run A a s) := by
  rw [run_append,List.take_append_of_le_length (by rw [pfx_length]),List.take_of_length_le (by rw [pfx_length]),
    List.drop_append_of_le_length (by rw [pfx_length]),List.drop_of_length_le (by rw [pfx_length]),run_pfx]
  rfl

theorem tripleRun (A B C : Program) (m : List Bool) (s : State) :
    let a := m.take (measurementCount A)
    let tail := m.drop (measurementCount A)
    run ((A++B)++C) m s=run C (tail.drop (measurementCount B)) (run B (tail.take (measurementCount B)) (run A a s)) := by
  rw [List.append_assoc,run_append A,run_append B]

theorem chosenRun (A B C : Program) (r y : List Bool) (s : State) :
    run ((A++B)++C) (pfx (measurementCount A) []++(pfx (measurementCount B) r++y)) s=
    run C y (run B r (run A [] s)) := by
  rw [List.append_assoc,run_pre A,joinRecords B]

def second (k cy cx : Fp) := Stair44Square.program k ++ Stair44Outer.multiply cx.val ++ encodeY (exitYAll layout cy)

theorem runNil (A B : Program) (s : State) : run (A++B) [] s=run B [] (run A [] s) := by
  rw [run_append,List.take_nil,List.drop_nil]

theorem stockCut (k X Y : Fp) (G : Bool) (origin : BasisState) (s w : State)
    (v : PointDialogValues layout X Y G origin s.basis)
    (ew : run (SquareCarryLoan719BF.program layout ++ fastConstAdd layout layout.point.x k) [] s=w) :
    run (squareEntry layout k) [] s=run (E1QubitPlacement.tickF layout) [] w :=
  (squareEntry_base layout layout_widths layout_nodup k X Y G origin s [] [] v).trans
    ((runNil _ _ s).trans (congrArg (run (E1QubitPlacement.tickF layout) []) ew))

theorem squareCut (k X Y : Fp) (G : Bool) (origin : BasisState) (s w : State) (m : List Bool)
    (v : PointDialogValues layout X Y G origin s.basis)
    (ew : run (SquareCarryLoan719BF.program layout ++ fastConstAdd layout layout.point.x k) [] s=w)
    (x : Nat) (vx : regValue layout.point.x w.basis=x) (hx : x<p) (hc : regValue layout.dialogPool w.basis=0) :
    run (Stair44Square.program k) m s=pullState integerFirst.symm (run (E1QubitPlacement.tickF layout) [] w) := by
  have sq := Stair44Square.fullRun k X Y G origin s m [] v
  rw [runNil,ew] at sq
  exact sq.trans (square_to_integer _ (fun q hq => Stair44OuterX.tickZero w [] x vx hx hc q
    ((by decide +kernel : ∀i∈([4835,4837,4615,4616]:List Wire),i∈firstClean) q hq)))

theorem productCut (cx X Y : Fp) (G : Bool) (origin : BasisState) (w v : State) (rm : List Bool)
    (values : PointDialogValues layout X Y G origin w.basis) (hp : 0<X.val)
    (eq : v=pullState integerFirst.symm (run (E1QubitPlacement.tickF layout) [] w)) :
    let F := E1QubitPlacement.tickF layout
    let d := pfx (measurementCount F) [] ++ rm
    let a := run (FrontierEntry1591Callers.exit (kernelX cx.val) layout) d w
    run (Stair44Outer.multiply cx.val) rm v=pullState outer.symm (put a (pkW layout) (G && decide (cx.val<X.val))) := by
  intro F d a
  have ww := Stair44PointWord.fullWord cx.val X.val Y.val cx.isLt hp X.isLt Y.isLt w d values.x values.y values.clean
  change run (FrontierEntry1591Callers.exit (Stair44Kernel.multiplication cx.val) layout) d w =
    pullState outer.symm (put a _ _) at ww
  rw [Stair44Splits.mul_split] at ww
  have dt : d=pfx (measurementCount Stair44Splits.tick) [] ++ rm :=
    congrArg (fun z => pfx z [] ++ rm) (renameProgram_counts _ _).2.symm
  rw [dt,run_pre,show run Stair44Splits.tick [] w=pullState integerFirst.symm (run F [] w) from
    encodedTick w [] values.clean,←eq,values.generic,pk_wire] at ww
  exact ww

theorem actual (k cy cx X Y : Fp) (G : Bool) (origin : BasisState) (s : State)
    (v : PointDialogValues layout X Y G origin s.basis)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+(if G then k else 0)≠0)
    (m : List Bool) : ∃ n,run (second k cy cx) m s=pullState outer.symm (run (secondStageN layout k cy cx) n s) := by
  let square := Stair44Square.program k
  let mul := Stair44Outer.multiply cx.val
  let A := SquareCarryLoan719BF.program layout ++ fastConstAdd layout layout.point.x k
  let Z := X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let X' := Z+(if G then k else 0)
  obtain ⟨w,ew⟩ : ∃z : State, run A [] s=z := ⟨_,rfl⟩
  let F := E1QubitPlacement.tickF layout
  let u := run F [] w
  let sm := m.take (measurementCount square)
  let tail := m.drop (measurementCount square)
  let rm := tail.take (measurementCount mul)
  let ym := tail.drop (measurementCount mul)
  let d := pfx (measurementCount F) [] ++ rm
  obtain ⟨plainOut,ep⟩ : ∃z : State,run (FrontierEntry1591Callers.exit (kernelX cx.val) layout) d w=z := ⟨_,rfl⟩
  let flag := G && decide (cx.val<X'.val)
  let oldSq := squareEntry layout k
  let oldMul := restXXN layout cx.val
  have sq := SquareCarryLoan719BF.step layout layout_widths layout_nodup X Y G origin
  have add := fastStep_addX layout layout_widths layout_nodup Z Y G origin k
  have vw : PointDialogValues layout X' Y G origin w.basis := by
    rw [←ew];exact ((sq.seq add) s [] v).2
  have hp : 0<X'.val := Nat.pos_of_ne_zero (fun eq => hx ((ZMod.val_eq_zero X').mp eq))
  have core : run oldSq [] s=u := stockCut k X Y G origin s w v ew
  have realSquare : run square sm s=pullState integerFirst.symm u := squareCut k X Y G origin s w sm v ew X'.val vw.x X'.isLt vw.clean
  have nw : run mul rm (run square sm s)=pullState outer.symm (put plainOut (pkW layout) flag) := by
    rw [←ep];exact productCut cx X' Y G origin w _ rm vw hp realSquare
  have o := exitX_correct layout layout_widths layout_nodup cx.val cx.isLt X'.val Y.val X'.isLt hp Y.isLt
    w d vw.x vw.y vw.clean
  rw [ep] at o
  have oc : regValue layout.dialogPool plainOut.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    o.2.2.2 q (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2)
      (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).1))).trans vw.clean
  have oy : regValue layout.point.y plainOut.basis=centerWord ((Y*X')/2) := by simpa only [ZMod.natCast_zmod_val] using o.2.1
  have stock := rest_pw layout layout_widths layout_nodup k cx X Y G origin s v hx [] rm
  have oldRest : run (restXX layout cx.val) rm (run oldSq [] s)=plainOut := by
    rw [←ep,exit_splitX,show d=pfx (measurementCount F) []++rm from rfl,run_pre,core]
  rw [oldRest] at stock
  let actual := run mul rm (run square sm s)
  have Yres := Stair44OuterY.exit ((Y*X')/2) cy plainOut actual ym flag oy oc (by
    rw [show actual=pullState outer.symm (put plainOut (pkW layout) flag) from nw]
    exact unpull outer.symm _)
  have final := congrArg (pullState outer.symm) Yres
  rw [unpull] at final
  refine ⟨pfx (measurementCount oldSq) [] ++ (pfx (measurementCount oldMul) rm ++ ym),?_⟩
  change run ((square++mul)++_) m s=pullState outer.symm (run ((oldSq++oldMul)++_) _ s)
  rw [tripleRun square mul,chosenRun oldSq oldMul,stock]
  exact final

end ECDSAAdd.Entrant.Stair44PointSecond

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorCaller
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairSemanticFinal
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
private theorem localSite {q:Nat} (h:16 ≤ q ∧ q < 2330):q∈callerDomain:=by
  have e:base (q-16)=q:=by simp only [base,Wire];omega
  exact e ▸ base_mem_caller _ (Or.inl (by omega))
private theorem setup:GoodP WindowFieldParity.setup:=by
  apply wires_sub_of_parts _ _ glue_own.2.1
  have table:StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330)) WindowFieldParity.correction=true:=by decide +kernel
  intro q h
  exact localSite (of_decide_eq_true (StairWireCheck.allSites_sound _ _ table q h))

theorem entryFieldHosted_corrected :
    wires (WindowParityCaller.entryFieldHosted StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowParityCaller.entryFieldHosted
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
      (fieldRename_caller _ entryLowPrefix_ours) setup) glue_own.1)
    (fieldRename_caller _ entryLowSuffixV3_caller)) glue_own.1) setup

theorem exitFieldHosted_corrected :
    wires (WindowParityCaller.exitFieldHosted StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowParityCaller.exitFieldHosted
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ (wires_sub_of_parts _ _ setup glue_own.1)
      (fieldRename_caller _ exitLowPrefixV3_caller)) setup) glue_own.1)
    (fieldRename_caller _ exitLowSuffix_ours)

end ECDSAAdd.Entrant.StairPacket.ExteriorCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChain
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowTicket Partial ArchiveHistoryCompare
set_option maxRecDepth 30000
set_option maxHeartbeats 3800000
attribute [local irreducible] run measurementCount body NativePack225.firstWindow NativePack240.nextWindow NativePack255.nextWindow NativePack270.lastWindow leave225 leave240 leave255
private theorem seven (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (a b c e f h j:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    let origin:=pullState (OB5.sig 224) raw
    let v1:=run (NativePack225.firstWindow d) a origin
    let s2:=run leave225 b v1
    let v2:=run (NativePack240.nextWindow d) c s2
    let s3:=run leave240 e v2
    let v3:=run (NativePack255.nextWindow d) f s3
    let s4:=run leave255 h v3
    let out:=run (NativePack270.lastWindow d) j s4
    ∀q∉ArchiveStockSuffix.archives,out.basis q=(StockArchiveReference.common d raw).basis q := by
  let origin:=pullState (OB5.sig 224) raw
  let v1:=run (NativePack225.firstWindow d) a origin
  let s2:=run leave225 b v1
  let v2:=run (NativePack240.nextWindow d) c s2
  let s3:=run leave240 e v2
  let v3:=run (NativePack255.nextWindow d) f s3
  let s4:=run leave255 h v3
  let out:=run (NativePack270.lastWindow d) j s4
  exact last270 d x good raw s4 j (next255 d x good raw s3 f h (next240 d x good raw s2 c e (begin225 d x good raw a b stage)))

theorem wires (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    ∀q∉ArchiveStockSuffix.archives,(run (forward45plus1 d) m (pullState (OB5.sig 224) raw)).basis q=
      (StockArchiveReference.common d raw).basis q := by
  rw [assembly]
  simp only [List.append_assoc,run_append,run_take]
  exact seven d x good raw m _ _ _ _ _ _ stage
end ECDSAAdd.Entrant.StairPacket.OrdinaryChain

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockNativeCompare
open Arithmetic MappedCompressed WideReference Secp256k1
attribute [local irreducible] run
theorem normalized (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) :
    ArchiveStockSuffix.Same (run (Partial.forward45plus1 d) m (pullState (OB5.sig 224) raw))
      (StockArchiveReference.common d raw) :=
  ⟨(StockWindowChain.result d x good raw m stage).1.trans (StockBaseline.common_phase d x good raw stage).symm,
    OrdinaryChain.wires d x good raw m stage⟩
end ECDSAAdd.Entrant.StairPacket.StockNativeCompare

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks ArchiveStockSuffix StockWalkPrefix
set_option maxRecDepth 9500
set_option maxHeartbeats 3000000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount Partial.forward45plus1
def NewNormalized (d:Bool) (x:Nat):Prop:=∀(raw:State)(m:List Bool),Rolling1588.Integer.Stage base d x p 225 raw.basis →
    Same (run (Partial.forward45plus1 d) m (pullState (OB5.sig 224) raw)) (StockArchiveReference.common d raw)

theorem steady (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:0 < i) (hi:i+n≤512) (s:State) (u v:List Bool) (stage:Rolling1588.Integer.Stage base d x p i s.basis):
    run (Rolling1588TickGap.forward d i n) u (pullState (OB5.sig (i-1)) s)=run (Rolling1588TickGap.forward d i n) v (pullState (OB5.sig (i-1)) s):=
  (StockDelayed.window d x good.nonzero good.small i n lo hi s u stage).trans
    (StockDelayed.window d x good.nonzero good.small i n lo hi s v stage).symm
theorem suffix_independent (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 225 s.basis) (u v y z:List Bool):
    let t:=pullState (OB5.sig 224) s
    let old:=Rolling1588TickGap.forward d 225 46
    let tail:=Rolling1588TickGap.forward d 271 n
    run tail u (run old v t)=run tail y (run old z t):=by
  let t:=pullState (OB5.sig 224) s
  let A:=Rolling1588TickGap.forward d 225 46
  let B:=Rolling1588TickGap.forward d 271 n
  let mix (v u:List Bool):=FlagEntry.pfx (measurementCount A) v++u
  have eq:=steady d x good 225 (46+n) (by decide) (by omega) s (mix v u) (mix z y) stage
  rw [StairRestSupport.forward_append d 46 225 n] at eq
  exact (Stair44PointSecond.joinRecords A B v u t).symm.trans (eq.trans (Stair44PointSecond.joinRecords A B z y t))

theorem window (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) (m stockTape:List Bool) (norm:NewNormalized d x):
    let s:=pullState (OB5.sig 224) raw
    Paired d x (run (forwardEnd d n) m s) (run (Rolling1588TickGap.forward d 225 (46+n)) stockTape s) (StockRowVector.rows x p):=by
  let s:=pullState (OB5.sig 224) raw
  have result:=StockWindowChain.result d x good raw m stage
  have old:=StockBaseline.comparison d x good raw _ m stage result.2.1
  have new:=norm raw m stage
  have eq:Same _ _:=⟨new.1.trans old.1.symm,fun q off=>(new.2 q off).trans (old.2 q off).symm⟩
  have h:=StockRowVector.binding d x good raw _ m stage (StockStrongChain.result d x good raw m stage).2.1 eq
  have onward:=h.through (Rolling1588TickGap.forward d 271 n) (fun q h=>(safe d 271 n (by decide) bound q h).1) (m.drop (measurementCount (Partial.forward45plus1 d)))
  simp only [forwardEnd,StairRestSupport.forward_append d 46 225 n,run_append,run_take]
  rw [←suffix_independent d n x good bound raw stage (m.drop (measurementCount (Partial.forward45plus1 d))) m (stockTape.drop (measurementCount (Rolling1588TickGap.forward d 225 46))) stockTape]
  exact onward
end ECDSAAdd.Entrant.StairPacket.StockWalkWindow

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockPlacedWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks ArchiveStockSuffix StockWalkPrefix StockWalkWindow
set_option maxRecDepth 12000
set_option maxHeartbeats 2500000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount Partial.forward45plus1
theorem fixed:∀(b:Bank)(j:Fin 16),Stair44WalkMap.rest (siteAt b j)=siteAt b j:=by decide +kernel
theorem bank_rep (q:Wire) (h:q∈archives):∃(b:Bank)(j:Fin 16),siteAt b j=q:=by
  simp only [archives,bank,Finset.mem_union,List.mem_toFinset,List.mem_map,List.mem_finRange,true_and] at h
  rcases h with (⟨j,rfl⟩|⟨j,rfl⟩)|⟨j,rfl⟩
  · exact ⟨0,j,congrArg ArchiveBoundary240.codePorts (Fin.ext (Nat.mod_eq_of_lt (by omega : j.val<157)).symm)⟩
  · exact ⟨1,j,congrArg ArchiveBoundary255.codePorts (Fin.ext (Nat.mod_eq_of_lt (by omega : j.val<157)).symm)⟩
  · exact ⟨2,j,congrArg ArchiveBoundary270.codePorts (Fin.ext (Nat.mod_eq_of_lt (by omega : j.val<157)).symm)⟩
theorem unplace {d x a s rows} (pair:Paired d x (pullState Stair44WalkMap.rest a) (pullState Stair44WalkMap.rest s) rows):Paired d x a s rows:=by
  refine ⟨⟨pair.equality.1,?_⟩,pair.labels,?_,?_⟩
  · intro q off
    have safe:Stair44WalkMap.rest.symm q∉archives:=by
      intro hit
      obtain ⟨b,j,e⟩:=bank_rep _ hit
      apply off
      have same:=congrArg Stair44WalkMap.rest e
      rw [fixed,Equiv.apply_symm_apply] at same
      exact same ▸ (chart b j).2.2.2
    simpa only [pullState,Equiv.apply_symm_apply] using pair.equality.2 _ safe
  · intro b j
    change a.basis (siteAt b j)=_
    rw [←fixed b j]
    exact pair.custom b j
  · intro b j
    rw [←fixed b j]
    exact pair.stock b j

theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.forward d (255+n)=
    first d++renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 225 (46+n)):=by
  have e:=StairRestSupport.forward_append d 209 16 (46+n)
  change Rolling1588TickGap.forward d 16 (209+(46+n))=Rolling1588TickGap.forward d 16 209++Rolling1588TickGap.forward d 225 (46+n) at e
  rw [show 255+n=209+(46+n) by omega]
  simp only [Stair44WalkRun.forward,first,e,renameProgram,List.map_append,List.append_assoc]

theorem forward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s) (norm:NewNormalized d x):
    Paired d x (run (WindowWalkCosts.forward d n) m a) (run (Stair44WalkRun.forward d (255+n)) m a) (StockRowVector.rows x p):=by
  let t:=m.drop (measurementCount (first d))
  have rel:=window d n x good bound (regular d s m) (cut225 d x good s a m stage input).1 t t norm
  apply unplace
  rw [placed d n x good s a m stage input,old_split,run_append,run_take,run_rename _ Stair44WalkMap.rest.injective,(cut225 d x good s a m stage input).2]
  exact rel
end ECDSAAdd.Entrant.StairPacket.StockPlacedWindow

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks ArchiveStockSuffix StairArchiveRelease WindowFieldMask
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
def groupId (b:Bank):Nat:=46+3*b.val
def parityPort (b:Bank) (i:Fin 16):Wire:=OB5.sig 511 (NewHistory5.payloadWire base (8*groupId b+i.val))
theorem native_ports:∀(b:Bank)(i:Fin 16),parityPort b i=siteAt b i:=by decide +kernel
theorem host_ports:∀(b:Bank)(i:Fin 16),Rolling1588Lifetime.phaseHost (siteAt b i)=siteAt b i:=by decide +kernel
theorem field_ports:∀(b:Bank)(i:Fin 16),fieldPort (groupId b) i.val=siteAt b i:=by decide +kernel
theorem whole:allBanks=archives:=by decide +kernel
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockInverseReplay
open Arithmetic MappedCompressed Secp256k1 WideReference ArchiveStockSuffix StockArchiveBanks StockWalkWindow StockPlacedWindow
set_option maxRecDepth 11000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse
  Rolling1588.Integer.regularForward Rolling1588.Integer.regularReverse Partial.forward45plus1 Partial.reverse45plus1
abbrev pool := (skywalkPoolWires base).toFinset
def poolEq (a b:State):Prop:=∀q∈pool,a.basis q=b.basis q

theorem reverse_forward (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:1 ≤ i) (hi:i+n≤512) (raw:State) (m r:List Bool)
    (st:Rolling1588.Integer.Stage base d x p i raw.basis):
    let start:=pullState (OB5.sig (i-1)) raw
    run (Rolling1588.reverse d i n) r (run (Rolling1588TickGap.forward d i n) m start)=start:=by
  dsimp only
  let v:=run (Rolling1588.Integer.regularForward base d i n) m raw
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have one:=Rolling1588TickGap.forward_gen d x good.nonzero good.small n i lo hi raw m st
  have two:=(Rolling1588.Integer.reverse_gen d x good.nonzero good.small n i lo hi raw m v r st (fun _ _=>rfl)).1
  rw [Rolling1588.Integer.reverse_eq_packets] at two
  have undo:=Rolling1588.Integer.regularReverse_roundtrip base d base_pool_nodup StackOB5.historyAbove x p hp0 good.nonzero odd cap (by norm_num [p]) good.small cop n i hi raw m r st
  exact (congrArg (run (Rolling1588.reverse d i n) r) one).trans (two.trans (congrArg (pullState (OB5.sig (i-1))) undo))

theorem paired_pool {d x rows a ref b old} (actual:Paired d x a ref rows) (ghost:Paired d x b old rows)
    (agree:poolEq ref old):poolEq a b:=by
  intro q hq
  by_cases h:q∈archives
  · obtain ⟨k,j,rfl⟩:=bank_rep q h
    exact (actual.custom k j).trans (ghost.custom k j).symm
  · exact (actual.equality.2 q h).trans ((agree q hq).trans (ghost.equality.2 q h).symm)

theorem replay (P Q:Program) (m:List Bool) (a ref b old origin:State) (A:wires P⊆pool) (B:wires Q⊆pool)
    (outside:∀q∉pool,a.basis q=ref.basis q) (phase:a.phase=ref.phase) (gp:b.phase=old.phase)
    (h1:poolEq a b) (h2:poolEq ref old) (one:run P m b=origin) (two:run Q m old=origin):
    run P m a=run Q m ref:=by
  have frame (h:poolEq a b):∀q∈wires P,a.basis q=b.basis q:=fun q hq=>h q (A hq)
  have left:=run_local_increment P a b m (frame h1)
  have right:=run_local_increment Q ref old m (fun q hq=>h2 q (B hq))
  rw [one] at left
  rw [two] at right
  apply State.extensionality
  · have h:=(left.1.trans (congrArg (fun v:Bool=>origin.phase ^^ v) gp)).trans right.1.symm
    rw [phase] at h
    cases ref.phase <;> simpa using h
  · funext q
    by_cases u:q∈pool
    · have output (C:Program) (ac gh:State) (g:poolEq ac gh) (h:run C m gh=origin)
          (eq:∀q∈wires C,(run C m ac).basis q=origin.basis q):
          (run C m ac).basis q=origin.basis q:=by
        by_cases use:q∈wires C
        · exact eq q use
        · rw [←h,run_preserves_outside C m ac q use,run_preserves_outside C m gh q use]
          exact g q u
      exact (output P a b h1 one left.2).trans (output Q ref old h2 two right.2).symm
    · rw [run_preserves_outside P m a q (fun hit=>u (A hit)),run_preserves_outside Q m ref q (fun hit=>u (B hit))]
      exact outside q u

theorem archives_pool (q:Wire) (hit:q∈archives):q∈pool:=by
  obtain ⟨b,j,rfl⟩:=bank_rep q hit
  have good:∀(b:Bank)(j:Fin 16),16≤siteAt b j ∧ siteAt b j≤1812:=by decide +kernel
  exact List.mem_toFinset.mpr (PartialSites.range_pool _ (good b j).1 (good b j).2)
end ECDSAAdd.Entrant.StairPacket.StockInverseReplay

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks ArchiveStockSuffix StairArchiveRelease WindowFieldMask CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def fieldRows (r:Bank→Nat) (j:Nat):Nat:=r (if j=46 then 0 else if j=49 then 1 else 2)
theorem rowsAt (r:Bank→Nat) (b:Bank):fieldRows r (groupId b)=r b:=by
  have tab:∀b:Bank,(if groupId b=46 then (0:Bank) else if groupId b=49 then 1 else 2)=b:=by decide +kernel
  exact congrArg r (tab b)
theorem idAt : ∀j∈bankIds,∃b:Bank,groupId b=j:=by decide +kernel
theorem enterCode (d:Bool) (j:Nat): (code d).take 16=(WindowFieldJourney.initialCode d j).take 16:=by
  cases d
  · simpa only [code,List.take_take,Nat.min_self] using StairArchiveHandoff.archive_edges.2.1
  · simpa only [code,List.take_take,Nat.min_self] using StairArchiveHandoff.archive_edges.1
theorem fits {d x a s rows} (pair:Paired d x a s rows):
    Fits (fieldRows rows) (WindowFieldJourney.initialCode d) a s := by
  refine ⟨pair.equality.1,fun q h=>pair.equality.2 q (whole ▸ h),?_⟩
  intro j hj q hq
  obtain ⟨b,rfl⟩:=idAt j hj
  let i:Fin 16:=⟨q,Finset.mem_range.mp hq⟩
  rw [rowsAt]
  have h:=pair.custom b i
  rw [show fieldPort (groupId b) q=siteAt b i from field_ports b i]
  exact h.trans (StairArchiveHandoff.wires_eq _ _ 16 (enterCode d _) q _ i.isLt)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockBackWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkWindow ArchiveStockSuffix StockInverseReplay
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse
  Rolling1588.Integer.regularForward Partial.forward45plus1 Partial.reverse45plus1

def real (d:Bool) (raw:State):State:=run (Partial.forward45plus1 d) [] (pullState (OB5.sig 224) raw)
def stock (d:Bool) (raw:State):State:=run (Rolling1588TickGap.forward d 225 46) [] (pullState (OB5.sig 224) raw)
theorem shadow (d:Bool) (x:Nat) (good:Bounds x p) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) (norm:NewNormalized d x):
    Paired d x (real d raw) (stock d raw) (StockRowVector.rows x p):=by
  have e:=norm raw [] stage
  have cmp:=StockBaseline.comparison d x good raw _ [] stage (StockWindowChain.result d x good raw [] stage).2.1
  exact StockRowVector.binding d x good raw _ [] stage (StockStrongChain.result d x good raw [] stage).2.1
    ⟨e.1.trans cmp.1.symm,fun q off=>(e.2 q off).trans (cmp.2 q off).symm⟩
theorem candidate_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis):
    run (Partial.reverse45plus1 d) m (real d raw)=pullState (OB5.sig 224) raw:=
  (StockWindowChain.result d x good raw [] stage).2.2 m
theorem stock_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis):
    run (Rolling1588.reverse d 225 46) m (stock d raw)=pullState (OB5.sig 224) raw:=
  reverse_forward d x good 225 46 (by decide) (by decide) raw [] m stage
attribute [local irreducible] real stock poolEq
theorem inner (d:Bool) (x:Nat) (good:Bounds x p) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (stock d raw)):
    run (Partial.reverse45plus1 d) m a=run (Rolling1588.reverse d 225 46) m ref:=by
  have ghost:=shadow d x good raw stage norm
  exact replay _ _ m a ref (real d raw) (stock d raw) _ (PartialSites.pool_partial d) (PartialSites.pool_old d 225 46 (by decide) (by decide))
    (fun q off=>pair.equality.2 q (fun h=>off (archives_pool q h))) pair.equality.1 ghost.equality.1
    (paired_pool pair ghost agree) agree (candidate_undo d x good raw m stage) (stock_undo d x good raw m stage)

theorem pool_run {C:Program} (cover:wires C⊆pool) {a b} (h:poolEq a b) (m:List Bool):poolEq (run C m a) (run C m b):=by
  unfold poolEq at h ⊢
  have use:=run_local_increment C a b m (fun q hq=>h q (cover hq))
  intro q hq
  by_cases hit:q∈wires C
  · exact use.2 q hit
  · rw [run_preserves_outside C m a q hit,run_preserves_outside C m b q hit]
    exact h q hq

private theorem transport (F R:Program) (m:List Bool) (a b:State) (eq:a=b) (inv:run R m (run F [] b)=b):
    run R m (run F [] a)=a:=eq ▸ inv
theorem stageAt (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (hi:i+n≤512) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p i raw.basis):
    Rolling1588.Integer.Stage base d x p (i+n) (run (Rolling1588.Integer.regularForward base d i n) m raw).basis:=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  exact (Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p i n hp0 good.nonzero odd cap (by norm_num [p]) good.small cop hi raw m stage).2
theorem tail_cancel (d:Bool) (x i h n:Nat) (good:Bounds x p) (lo:1 ≤ i) (bound:i+h+n≤512) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p i raw.basis) (m:List Bool):
    let s:=pullState (OB5.sig (i-1)) raw
    let old:=run (Rolling1588TickGap.forward d i h) [] s
    run (Rolling1588.reverse d (i+h) n) m (run (Rolling1588TickGap.forward d (i+h) n) [] old)=old:=by
  let t:=run (Rolling1588.Integer.regularForward base d i h) [] raw
  have cut:i+h≤512:=by omega
  have st:=stageAt d x good i h cut raw [] stage
  have eq:=Rolling1588TickGap.forward_gen d x good.nonzero good.small h i lo cut raw [] stage
  exact transport _ _ _ _ _ eq (reverse_forward d x good (i+h) n (by omega) bound t [] m st)

def backwards (d:Bool) (n:Nat):Program:=Rolling1588.reverse d 271 n++Partial.reverse45plus1 d

theorem result (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 225 (46+n)) [] (pullState (OB5.sig 224) raw))):
    run (backwards d n) m a=run (Rolling1588.reverse d 225 (46+n)) m ref:=by
  have h:=pair.through (Rolling1588.reverse d 271 n) (fun q hq=>(safe d 271 n (by decide) bound q hq).2) m
  have pools:=pool_run (PartialSites.pool_old d 271 n (by decide) bound) agree m
  simp only [StairRestSupport.forward_append d 46 225 n,run_append,run_take,List.drop_nil] at pools
  rw [tail_cancel d x 225 46 n good (by decide) bound raw stage m] at pools
  simp only [backwards,StairRestSupport.reverse_append d 46 225 n,run_append,run_take]
  apply inner d x good raw _ _ _ stage norm h
  unfold stock
  exact pools
end ECDSAAdd.Entrant.StairPacket.StockBackWindow

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks ArchiveStockSuffix StairArchiveRelease WindowFieldMask CodecBitSliceVerify ArchivePortAction WindowFieldJourney
set_option maxRecDepth 25000
set_option maxHeartbeats 3200000
def Fixed (f:Wire→Wire):Prop:=∀b i,f (siteAt b i)=siteAt b i
theorem archive_pre {f:Wire→Wire} (inj:Function.Injective f) (fix:Fixed f) (q:Wire) (off:q∉archives):f q∉archives:=by
  intro hit
  obtain ⟨b,i,e⟩:=StockPlacedWindow.bank_rep _ hit
  have eq:=inj ((fix b i).trans e)
  exact off (eq ▸ (chart b i).2.2.2)
theorem pairPull (f:Wire→Wire) (inj:Function.Injective f) (fix:Fixed f) {d x rows a r}
    (pair:Paired d x a r rows):Paired d x (pullState f a) (pullState f r) rows:=by
  refine ⟨⟨pair.equality.1,fun q h=>pair.equality.2 _ (archive_pre inj fix q h)⟩,pair.labels,?_,?_⟩
  · intro b i
    change a.basis (f (siteAt b i))=_
    rw [fix];exact pair.custom b i
  · intro b i
    change r.basis (f (siteAt b i))=_
    rw [fix];exact pair.stock b i
theorem fitsPull (f:Wire→Wire) (inj:Function.Injective f) (fix:Fixed f) {rows cs a r}
    (ff:Fits rows cs a r):Fits rows cs (pullState f a) (pullState f r):=by
  refine ⟨ff.phase,?_,?_⟩
  · intro q off
    exact ff.outside _ (by rw [whole] at off ⊢;exact archive_pre inj fix q off)
  · intro j hj q hq
    obtain ⟨b,rfl⟩:=idAt _ hj
    let i:Fin 16:=⟨q,Finset.mem_range.mp hq⟩
    have fx:f (fieldPort (groupId b) q)=fieldPort (groupId b) q:=by change f (fieldPort (groupId b) i.val)=_;rw [field_ports,fix]
    change a.basis (f (fieldPort (groupId b) q))=_
    rw [fx];exact ff.bytes _ hj _ hq

theorem completeCode (d:Bool) (b:Bank):
    (finalCode d (plan d) (initialCode d) (groupId b)).take 16=(code (!d)).take 16:=by
  have toward:∀(d:Bool)(b:Bank),(finalCode d (plan d) (initialCode d) (groupId b)).take 16=
      (outputCols (StairArchiveNativeCut.leave (!d))).take 16:=by decide +kernel
  rw [toward]
  cases d
  · exact StairArchiveHandoff.archive_edges.2.2.2.2.2.2.2.trans ((enterCode true (groupId b)).symm)
  · exact StairArchiveHandoff.archive_edges.2.2.2.2.2.2.1.trans ((enterCode false (groupId b)).symm)

theorem pairFinished {d x rows a r} (ff:Fits (fieldRows rows) (finalCode d (plan d) (initialCode d)) a r)
    (labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b))
    (old:∀b,nativeAt (!d) b (rows b) r):Paired (!d) x a r rows:=by
  refine ⟨⟨ff.phase,fun q h=>ff.outside q (whole.symm ▸ h)⟩,labels,?_,old⟩
  intro b i
  have pick:∀b:Bank,groupId b∈bankIds:=by decide +kernel
  have v:=ff.bytes _ (pick b) i.val (Finset.mem_range.mpr i.isLt)
  rw [field_ports b i,rowsAt] at v
  exact v.trans (StairArchiveHandoff.wires_eq _ _ 16 (completeCode d b) i.val _ i.isLt)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockPlacedBack
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks ArchiveStockSuffix StockWalkWindow StockInverseReplay FlagEntry
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse Partial.reverse45plus1
theorem pull {d x a s rows} (h:Paired d x a s rows):
    Paired d x (pullState Stair44WalkMap.rest a) (pullState Stair44WalkMap.rest s) rows:=by
  refine ⟨⟨h.equality.1,?_⟩,h.labels,?_,?_⟩
  · intro q off
    apply h.equality.2
    intro hit
    obtain ⟨b,j,atSite⟩:=StockPlacedWindow.bank_rep _ hit
    have eq:siteAt b j=q:=Stair44WalkMap.rest.injective ((StockPlacedWindow.fixed b j).trans atSite)
    exact off (eq ▸ (chart b j).2.2.2)
  · intro b j
    change a.basis (Stair44WalkMap.rest (siteAt b j))=_
    rw [StockPlacedWindow.fixed]
    exact h.custom b j
  · intro b j
    change s.basis (Stair44WalkMap.rest (siteAt b j))=_
    rw [StockPlacedWindow.fixed]
    exact h.stock b j
def R (P:Program):Program:=renameProgram Stair44WalkMap.rest P
def remaining (d:Bool):Program:=R (Rolling1588.reverse d 16 209)++renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)
theorem split (d:Bool) (n:Nat):WindowWalkCosts.backward d n=R (StockBackWindow.backwards d n)++remaining d:=by
  simp only [WindowWalkCosts.backward,StockBackWindow.backwards,R,remaining,renameProgram,List.map_append,List.append_assoc]
theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.backward d (255+n)=R (Rolling1588.reverse d 225 (46+n))++remaining d:=by
  have e:=StairRestSupport.reverse_append d 209 16 (46+n)
  change Rolling1588.reverse d 16 (209+(46+n))=Rolling1588.reverse d 225 (46+n)++Rolling1588.reverse d 16 209 at e
  rw [show 255+n=209+(46+n) by omega]
  simp only [remaining,Stair44WalkRun.backward,e,R,renameProgram,List.map_append,List.append_assoc]

theorem backward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 225 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 225 (46+n)) [] (pullState (OB5.sig 224) raw))):
    ∃old,run (WindowWalkCosts.backward d n) m a=run (Stair44WalkRun.backward d (255+n)) old ref:=by
  let A:=R (StockBackWindow.backwards d n)
  let B:=R (Rolling1588.reverse d 225 (46+n))
  let tail:=m.drop (measurementCount A)
  have eq:run A m a=run B m ref:=by
    apply MappedCompressed.pullState_perm_injective Stair44WalkMap.rest
    simp only [A,B,R,run_rename _ Stair44WalkMap.rest.injective]
    exact StockBackWindow.result d n x good bound raw _ _ m stage norm (pull pair) agree
  refine ⟨pfx (measurementCount B) m++tail,?_⟩
  rw [split,old_split,Stair44PointSecond.joinRecords]
  rw [run_append,run_take]
  exact congrArg (run (remaining d) tail) eq
end ECDSAAdd.Entrant.StairPacket.StockPlacedBack

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks ArchiveStockSuffix WindowFieldMask CodecBitSliceVerify
open StairOuterPlacement StairField2V3Seg
set_option maxRecDepth 25000
set_option maxHeartbeats 1800000
attribute [local irreducible] run
def fieldEquiv:Equiv.Perm Wire:=⟨fieldPlace,fieldPlaceInv,inv_fieldPlace,fieldPlace_inv⟩
theorem fieldFix:Fixed fieldEquiv:=by unfold Fixed; decide +kernel
theorem phaseFix:Fixed Rolling1588Lifetime.phaseHost:=host_ports
theorem inverseFix {f:Equiv.Perm Wire} (fixed:Fixed f):Fixed f.symm:=by
  intro b i
  exact f.injective (by rw [Equiv.apply_symm_apply,fixed b i])
theorem pairUnpull (f:Equiv.Perm Wire) (fix:Fixed f) {d x rows a r}
    (pair:Paired d x (pullState f a) (pullState f r) rows):Paired d x a r rows:=by
  have h:=pairPull f.symm f.symm.injective (inverseFix fix) pair
  rwa [Stair44PlacedHead.unpull,Stair44PlacedHead.unpull] at h
theorem fitsUnpull (f:Equiv.Perm Wire) (fix:Fixed f) {rows cs a r}
    (ff:Fits rows cs (pullState f a) (pullState f r)):Fits rows cs a r:=by
  have h:=fitsPull f.symm f.symm.injective (inverseFix fix) ff
  rwa [Stair44PlacedHead.unpull,Stair44PlacedHead.unpull] at h
theorem hosted {rows cs A B a r m n}
    (ff:Fits rows cs (run A m (pullState fieldEquiv a)) (run B n (pullState fieldEquiv r))):
    Fits rows cs (run (renameProgram fieldEquiv A) m a) (run (renameProgram fieldEquiv B) n r):=by
  apply fitsUnpull fieldEquiv fieldFix
  rwa [run_rename _ fieldEquiv.injective,run_rename _ fieldEquiv.injective]
theorem placedShape (A:Program):StairSchedule.fieldRename (renameProgram Prefix1590.borrow A)=renameProgram fieldEquiv A:=by
  simp only [StairSchedule.fieldRename,StairSchedule.parityRename,renameProgram_comp]
  rfl
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkEndpoints
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockPlacedWindow StockInverseReplay StockWalkPrefix
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse Rolling1588.Integer.regularForward

theorem bounds (x:Nat) (nz:0 < x) (lt:x<p):Bounds x p:=by
  obtain ⟨h,odd,cap,cop⟩:=StackOB5.prime_facts x nz lt
  exact ⟨h,nz,odd,cap,by norm_num [p],lt,cop⟩
theorem opened (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (bound:271+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Paired d x (run (WindowWalkCosts.forward d n) m a) (run (Stair44WalkRun.forward d (255+n)) m a) (StockRowVector.rows x p):=
  StockPlacedWindow.forward d n x (bounds x nz lt) bound s a m stage input (StockNativeCompare.normalized d x (bounds x nz lt))

theorem rest_pool (q:Wire) (h:q∈pool):Stair44WalkMap.rest q∈pool:=by
  simp only [Stair44WalkMap.rest,Stair44WalkMap.shared,Equiv.trans_apply,Equiv.swap_apply_def]
  split_ifs <;> first | exact h | exact List.mem_toFinset.mpr (OB5.base_pool _ (by decide))
theorem fixed_old (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:271+n∈[425,505,506]) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (m:List Bool):
    let v:=run (Rolling1588TickGap.forward d 1 (270+n)) m s
    pullState Stair44WalkMap.rest v=v:=by
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have num:15+(255+n)=270+n:=by omega
  have cut:1+(15+(255+n))∈[425,505,506]:=by simpa only [show 1+(15+(255+n))=271+n by omega] using atCut
  have one:=Stair44WalkRun.forward_run d (255+n) x good.nonzero good.small s a m stage input
  have two:=Stair44WalkCuts.forward_done d (255+n) x cut good.nonzero good.small s a m stage input
  rw [two,num] at one
  exact one

theorem decompose (d:Bool) (x n:Nat) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:271+n≤512):
    let raw:=regular d s []
    run (Rolling1588TickGap.forward d 1 (270+n)) m s=
      run (Rolling1588TickGap.forward d 225 (46+n)) [] (pullState (OB5.sig 224) raw):=by
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  have same:=StockWalkWindow.steady d x good 1 (270+n) (by decide) (by omega) s m [] stage
  rw [show 1-1=0 from rfl,init] at same
  have cut:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 224 1 (by decide) (by decide) s [] stage
  rw [show 1-1=0 from rfl,init] at cut
  have shape:270+n=224+(46+n):=by omega
  rw [same,shape,StairRestSupport.forward_append d 224 1 (46+n),run_append,run_take,List.drop_nil,cut]
  rfl

theorem move {f:Wire→Wire} (a b c:State) (mem:∀q∈pool,f q∈pool) (eq:poolEq a b)
    (fixed:pullState f b=b) (next:b=c):poolEq (pullState f a) c:=by
  intro q hq
  exact (eq _ (mem q hq)).trans ((congrArg (fun s:State=>s.basis q) fixed).trans (congrArg (fun s:State=>s.basis q) next))
theorem endpoint_stage (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (stage:Rolling1588.Integer.Stage base d x p 1 s.basis):
    Rolling1588.Integer.Stage base d x p 225 (regular d s []).basis:=StockBackWindow.stageAt d x good 1 224 (by decide) s [] stage
theorem endpoint_pool (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:271+n∈[425,505,506]) (s ref:State) (enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:271+n≤512)
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (270+n)) enc s)):
    poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 225 (46+n)) [] (pullState (OB5.sig 224) (regular d s []))):=
  move _ _ _ rest_pool agree (fixed_old d n x good atCut s stage enc) (decompose d x n good s enc stage bound)
theorem closed (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:271+n∈[425,505,506]) (one a ref:State) (m enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (270+n)) enc one)):
    ∃old,run (WindowWalkCosts.backward d n) m a=run (Stair44WalkRun.backward d (255+n)) old ref:=by
  have good:=bounds x nz lt
  have bound:271+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
  exact StockPlacedBack.backward d n x good bound (regular d one []) a ref m (endpoint_stage d x good one stage)
    (StockNativeCompare.normalized d x good) pair (endpoint_pool d n x good atCut one ref enc stage bound agree)
end ECDSAAdd.Entrant.StairPacket.StockWalkEndpoints

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed WindowFieldMask
set_option maxRecDepth 6000
attribute [local irreducible] run measurementCount
/-- Change reference tapes separately at the field window and reuse the actual measurement suffix. -/
def Relates (A B:Program) (start finish:State→State→Prop):Prop:=
  ∀a r,start a r→∀m,∃n,finish (run A m a) (run B n r)
theorem compose {A B C D:Program} {src mid finish:State→State→Prop}
    (p:Relates A B src mid) (q:Relates C D mid finish):Relates (A++C) (B++D) src finish:=by
  intro a r h m
  obtain ⟨u,hm⟩:=p a r h m
  obtain ⟨v,hf⟩:=q _ _ hm (m.drop (measurementCount A))
  refine ⟨WindowFieldJourney.joinTapes B u v,?_⟩
  rw [WindowFieldJourney.joined,run_append,run_take]
  exact hf

theorem pass {rows cs P} (clear:avoids P allBanks):Relates P P (Fits rows cs) (Fits rows cs):=by
  intro a r h m
  exact ⟨m,plain P rows cs m a r h clear⟩
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowMiddleContract
open Arithmetic MappedCompressed Rolling1588Lifetime Secp256k1 StairConcreteAssembly
open WindowKernelPrograms StockArchiveBanks
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

def divHead:=divBefore++renameProgram phaseHost Stair44Outer.reverseEnd
def oldDivHead:=(Stair44Kernel.divLead++Stair44Kernel.fieldD)++renameProgram phaseHost Stair44Outer.reverseEnd
def mulHead:=mulBefore
def oldMulHead:=Stair44Kernel.beforeX

def entry:Prop:=∀{t:State} (F:EntryFrame t) (m:List Bool),
  ∃old,Paired false F.x (pullState phaseHost (run divHead m t))
    (pullState phaseHost (run oldDivHead old t)) (StockRowVector.rows F.x p)
def exit:Prop:=∀(k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool),
  ∃old,Paired true F.x (pullState phaseHost (run mulHead m t))
    (pullState phaseHost (run oldMulHead old t)) (StockRowVector.rows F.x p)

theorem div_head_split:WindowKernelPrograms.division=divHead++renameProgram phaseHost
    (WindowWalkCosts.backward false 235++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [WindowKernelPrograms.division,divAfter,divHead,Six505.rename_append,List.append_assoc]
theorem old_div_head_split:Stair44Kernel.division=oldDivHead++renameProgram phaseHost
    (Stair44WalkRun.backward false 490++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [Stair44Kernel.division,oldDivHead,Stair44DivTerm.routedClose,Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,Six505.rename_append,List.append_assoc]
theorem mul_head_split (k:Nat):WindowKernelPrograms.multiplication k=mulHead++renameProgram phaseHost
    (WindowWalkCosts.backward true 154++renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)):=rfl
theorem old_mul_head_split (k:Nat):Stair44Kernel.multiplication k=oldMulHead++renameProgram phaseHost
    (Stair44WalkRun.backward true 409++renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)):=rfl
end ECDSAAdd.Entrant.StairPacket.WindowMiddleContract

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowStartStates
open Arithmetic MappedCompressed Secp256k1 WideReference Stair44Kernel Rolling1588Lifetime StairConcreteAssembly
open WindowKernelPrograms StockArchiveBanks
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount FrontierEntry1591Native.forward

def opening (d:Bool) (n:Nat):Program:=renameProgram phaseHost (openWalk d n)
def original (d:Bool) (n:Nat):Program:=renameProgram phaseHost (openR d (255+n))

private theorem fixed (x y:Nat) (s:State) (h:SkywalkArithmeticInput base x y s.basis):
    pullState Stair44WalkMap.first s=s:=by
  let idx:List Nat:=[1026,514,1541,501,1542,500]
  have all:∀j∈idx,base j∈skywalkSharedWires base ∧ base j∉skywalkArithmeticDivisor base ∧ base j∉skywalkArithmeticNumerator base:=by decide +kernel
  have zero (j:Nat) (hj:j∈idx):s.basis (base j)=false:=h.2.2 _ (all j hj).1 (all j hj).2.1 (all j hj).2.2
  have a:=cleanWireRebind id s s _ _ rfl (zero 1026 (by decide)) (zero 514 (by decide))
  have b:=cleanWireRebind _ s s _ _ a (zero 1541 (by decide)) (zero 501 (by decide))
  exact cleanWireRebind _ s s _ _ b (zero 1542 (by decide)) (zero 500 (by decide))

theorem open_raw (d:Bool) (n x y:Nat) (nz:0 < x) (lt:x<p) (bound:271+n≤512)
    (hn:(skywalkSharedWires base).Nodup) (s:State) (input:SkywalkArithmeticInput base x y s.basis) (m:List Bool):
    Paired d x (run (openWalk d n) m s) (run (openR d (255+n)) m s) (StockRowVector.rows x p):=by
  let N:=FrontierEntry1591Native.forward base
  let t:=m.take (measurementCount firstR)
  have stage:=Rolling1588.Integer.stage_one base d x p _ (FrontierEntry1591Native.caller_first_stageW base hn x y nz lt s t input)
  have eq:=run_rename Stair44WalkMap.first Stair44WalkMap.first.injective N t s
  rw [fixed x y s input] at eq
  simp only [openWalk,openR,run_append]
  exact StockWalkEndpoints.opened d n x nz lt bound _ _ _ stage eq
theorem division {s:State} (F:EntryFrame s) (m:List Bool):
    Paired true F.x (pullState phaseHost (run (opening true 154) m s))
      (pullState phaseHost (run (original true 154) m s)) (StockRowVector.rows F.x p):=by
  rw [opening,original,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_entry F]
  exact open_raw true 154 F.x _ F.x_pos F.x_lt (by decide) F.sharedNodup s (StairField13V3Clean.entryInput F) m
theorem multiplication (k:Nat) {s:State} (F:ExitFrame k s) (m:List Bool):
    Paired false F.x (pullState phaseHost (run (opening false 234) m s))
      (pullState phaseHost (run (original false 234) m s)) (StockRowVector.rows F.x p):=by
  rw [opening,original,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_exit F]
  exact open_raw false 234 F.x _ F.x_pos F.x_lt (by decide) F.sharedNodup s F.input m
end ECDSAAdd.Entrant.StairPacket.WindowStartStates

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowStockHead
open Arithmetic MappedCompressed Secp256k1 WideReference Stair44Kernel Rolling1588Lifetime StairConcreteAssembly
open StockInverseReplay WindowMiddleContract
set_option maxRecDepth 17000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount renameProgram Rolling1588TickGap.forward Rolling1588.Integer.regularForward

theorem shapeD:StairSchedule.firstPhase checkpointPrimitives=openS true 409++checkpointPrimitives.firstPack:=by
  simp only [openS,StairSchedule.firstPhase,StairSchedule.stackForward6,List.append_assoc]
theorem shapeM:Rolling1588TickGap.firstPhase false=openS false 489++finishM:=by
  simp only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,openS,finishM,List.append_assoc]

theorem leadD {t:State} (F:EntryFrame t) (m:List Bool):
    run divLead m t=run (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)) m t:=by
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_entry F,shapeD]
  exact with_tail true 409 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup t (StairField13V3Clean.entryInput F) _ m
theorem leadM (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    run mulLead m t=run StairField2V3Replay.exitReferenceOpening m t:=by
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [mulLead,StairField2V3Replay.exitReferenceOpening,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,
    StairField13V3Clean.pull_phaseHost_exit F,shapeM]
  exact with_tail false 489 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup t F.input _ m

theorem beforeD {t:State} (F:EntryFrame t) (m:List Bool):
    run (divLead++fieldD) m t=run (Stair44DivisionCut.beforeClose checkpointPrimitives hostPlan) m t:=by
  have cnt:measurementCount divLead=measurementCount (renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)):=by
    rw [shapeD,(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,open_count]
  change run (_++_) m t=run (_++_) m t
  rw [run_append,run_append,leadD F,cnt]
theorem roundHead (A B V W:Program) (s:State) (m:List Bool) (cnt:measurementCount A=measurementCount B)
    (same:∀u,run A u s=run B u s):run ((A++V)++W) m s=run ((B++V)++W) m s:=by
  simp only [run_append,measurementCount_append,cnt,same]
theorem countM:measurementCount mulLead=measurementCount StairField2V3Replay.exitReferenceOpening:=by
  rw [StairField2V3Replay.exitReferenceOpening,shapeM,mulLead,(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,measurementCount_append,measurementCount_append,open_count]
theorem beforeM (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):run beforeX m t=run stockBeforeX m t:=
  roundHead mulLead StairField2V3Replay.exitReferenceOpening (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)
    (renameProgram phaseHost checkpointPrimitives.firstUnpack) t m countM (leadM k F)

def Endpoint (d:Bool) (x n:Nat) (ref:State):Prop:=
  ∃s enc,Rolling1588.Integer.Stage base d x p 1 s.basis ∧ poolEq ref (run (Rolling1588TickGap.forward d 1 n) enc s)
theorem mul_endpoint (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):Endpoint true F.x 424 (pullState phaseHost (run oldMulHead m t)):=by
  change Endpoint true F.x 424 (pullState phaseHost (run beforeX m t))
  rw [beforeM k F,stockBeforeX,run_append]
  obtain ⟨s,enc,st,eq⟩:=Stair44MultiplyCut.pool k F _ _
  exact ⟨s,enc,Rolling1588.Integer.stage_one base true F.x p s st,fun q _=>congrArg (fun u:State=>u.basis q) eq⟩

private theorem transfer {v old target:State} (e:pullState phaseHost old=target)
    (h:v.phase=old.phase ∧ ∀q∈skywalkPoolWires base,v.basis q=old.basis q):
    (pullState phaseHost v).phase=target.phase ∧ ∀q∈skywalkPoolWires base,(pullState phaseHost v).basis q=target.basis q:=by
  subst target
  exact ⟨h.1,fun q hq=>h.2 _ (Stair44DivTerm.host_pool q hq)⟩
theorem div_pool {t:State} (F:EntryFrame t) (m:List Bool):
    let v:=run (divLead++fieldD) m t
    let want:=run (Rolling1588TickGap.firstPhase false) [] t
    (pullState phaseHost v).phase=want.phase ∧ ∀q∈skywalkPoolWires base,(pullState phaseHost v).basis q=want.basis q:=by
  dsimp only
  rw [beforeD F]
  have first:=StairLoanField7Values.first_phase_hosted false F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt t [] (StairField13V3Clean.entryInput F)
  have before:=run_rename phaseHost phaseHost.injective (Rolling1588TickGap.firstPhase false) [] t
  change pullState phaseHost (run (renameProgram phaseHost (Rolling1588TickGap.firstPhase false)) [] t)=_ at before
  rw [first,StairField13V3Clean.pull_phaseHost_entry F] at before
  exact transfer before (Stair44DivisionCut.pool F m)

theorem regular_endpoint (d:Bool) (x i:Nat) (nz:0 < x) (lt:x<p) (bound:1+i≤512) (one raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (same:∀q∈skywalkPoolWires base,raw.basis q=(run (Rolling1588.Integer.regularForward base d 1 i) [] one).basis q):
    Endpoint d x i (pullState (OB5.sig i) raw):=by
  have eq:=Rolling1588TickGap.forward_gen d x nz lt i 1 (by decide) bound one [] stage
  have init:pullState (OB5.sig 0) one=one:=by
    apply State.extensionality _ one
    · rfl
    · funext q;exact congrArg one.basis (OB5.sig_zero q)
  rw [show 1-1=0 from rfl,init,show 1+i-1=i by omega] at eq
  refine ⟨one,[],stage,?_⟩
  rw [eq]
  intro q hq
  exact same _ (Stair44DivTerm.sig_pool i (by omega) q (List.mem_toFinset.mp hq))

def beforeDiv:Program:=divLead++fieldD
theorem reverseShape:Stair44Outer.reverseEnd=skywalkArithmeticClear base++Stair44DivTerm.head:=by
  simp only [Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,List.append_assoc]
attribute [local irreducible] Endpoint Stair44Outer.reverseEnd SkywalkArithmeticInput FrontierEntry1591Native.forward
private theorem gather (d:Bool) (x i:Nat) (nz:0 < x) (lt:x<p) (bound:1+i≤512) (one out:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (result:∃r:State,out=pullState (OB5.sig i) r ∧ ∀q∈skywalkPoolWires base,r.basis q=(run (Rolling1588.Integer.regularForward base d 1 i) [] one).basis q):
    Endpoint d x i out:=by
  obtain ⟨r,rfl,eq⟩:=result
  exact regular_endpoint d x i nz lt bound one r stage eq
private theorem afterTick (d:Bool) (x y:Nat) (nz:0 < x) (lt:x<p) (hn:(skywalkSharedWires base).Nodup)
    (s:State) (input:SkywalkArithmeticInput base x y s.basis):
    Rolling1588.Integer.Stage base d x p 1 (run (FrontierEntry1591Native.forward base) [] s).basis:=
  Rolling1588.Integer.stage_one base d x p _ (FrontierEntry1591Native.caller_first_stageW base hn x y nz lt s [] input)
theorem reverseRaw (x y:Nat) (nz:0 < x) (lt:x<p) (hn:(skywalkSharedWires base).Nodup) (s z:State)
    (input:SkywalkArithmeticInput base x y s.basis) (m:List Bool)
    (hp:z.phase=(run (Rolling1588TickGap.firstPhase false) [] s).phase)
    (hb:∀q∈skywalkPoolWires base,z.basis q=(run (Rolling1588TickGap.firstPhase false) [] s).basis q):
    Endpoint false x 505 (run Stair44Outer.reverseEnd m z):=by
  rw [reverseShape]
  exact gather false x 505 nz lt (by decide) _ _ (afterTick false x y nz lt hn s input)
    (Stair44DivTerm.reverse_input x y nz lt hn s z input hp hb m)

theorem divState (t:State) (m:List Bool):pullState phaseHost (run oldDivHead m t)=
    run Stair44Outer.reverseEnd (m.drop (measurementCount beforeDiv)) (pullState phaseHost (run beforeDiv (m.take (measurementCount beforeDiv)) t)):=by
  rw [oldDivHead,run_append,run_rename _ phaseHost.injective]
  rfl
theorem div_endpoint {t:State} (F:EntryFrame t) (m:List Bool):Endpoint false F.x 505 (pullState phaseHost (run oldDivHead m t)):=by
  rw [divState]
  have h:=div_pool F (m.take (measurementCount beforeDiv))
  exact reverseRaw F.x _ F.x_pos F.x_lt F.sharedNodup t _ (StairField13V3Clean.entryInput F) _ h.1 h.2

end ECDSAAdd.Entrant.StairPacket.WindowStockHead

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowEndBytes
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockInverseReplay WindowStockHead WindowMiddleContract
open Rolling1588Lifetime
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward

structure Native (d:Bool) (x:Nat) (ref:State):Prop where
  ids:∀b,StockRowVector.rows x p b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (StockRowVector.rows x p b)
  bytes:∀b,nativeAt d b (StockRowVector.rows x p b) ref

theorem ofEndpoint (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:271+n∈[425,505,506]) (ref:State)
    (h:Endpoint d x (270+n) ref):Native d x ref:=by
  obtain ⟨s,enc,stage,eq⟩:=h
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have bound:271+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
  have pair:=StockWalkEndpoints.opened d n x nz lt bound s a enc stage input
  have cut:1+(15+(255+n))∈[425,505,506]:=by simpa only [show 1+(15+(255+n))=271+n by omega] using atCut
  have same:=Stair44WalkCuts.forward_done d (255+n) x cut nz lt s a enc stage input
  rw [show 15+(255+n)=270+n by omega] at same
  refine ⟨pair.labels,?_⟩
  intro b j
  have loc:siteAt b j∈pool:=archives_pool _ (chart b j).2.2.2
  exact (eq _ loc).trans ((congrArg (fun s:State=>s.basis (siteAt b j)) same.symm).trans (pair.stock b j))

theorem div_native {s:State} (F:StairConcreteAssembly.EntryFrame s) (m:List Bool):
    Native false F.x (pullState phaseHost (run oldDivHead m s)):=
  ofEndpoint false 235 F.x F.x_pos F.x_lt (by decide) _ (div_endpoint F m)
theorem mul_native (k:Nat) {s:State} (F:StairConcreteAssembly.ExitFrame k s) (m:List Bool):
    Native true F.x (pullState phaseHost (run oldMulHead m s)):=
  ofEndpoint true 154 F.x F.x_pos F.x_lt (by decide) _ (mul_endpoint k F m)

theorem Native.pair {d x a ref} (old:Native d x ref) (eq:ArchiveStockSuffix.Same a ref)
    (bytes:∀b,Kept (ports b) d (StockRowVector.rows x p b) a):Paired d x a ref (StockRowVector.rows x p):=
  ⟨eq,old.ids,bytes,old.bytes⟩
end ECDSAAdd.Entrant.StairPacket.WindowEndBytes

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowMiddlePieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime FlagEntry StockArchiveBanks
open WindowMiddleContract WindowStartStates
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount renameProgram

def divSpan:=renameProgram phaseHost checkpointPrimitives.firstPack++
    WindowParityCaller.entryFieldHosted checkpointPrimitives++renameProgram phaseHost Stair44Outer.reverseEnd
def oldDivSpan:=renameProgram phaseHost checkpointPrimitives.firstPack++
    StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan++renameProgram phaseHost Stair44Outer.reverseEnd
def mulSpan:=renameProgram phaseHost Stair44Outer.forwardEnd++
    WindowParityCaller.exitFieldHosted checkpointPrimitives++renameProgram phaseHost checkpointPrimitives.firstUnpack
def oldMulSpan:=renameProgram phaseHost Stair44Outer.forwardEnd++
    StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan++renameProgram phaseHost checkpointPrimitives.firstUnpack

theorem divisionShape:divHead=opening true 154++divSpan ∧ oldDivHead=original true 154++oldDivSpan:=by
  simp only [divHead,WindowKernelPrograms.divBefore,divSpan,opening,oldDivHead,Stair44Kernel.divLead,Stair44Kernel.fieldD,original,oldDivSpan,Six505.rename_append,List.append_assoc]
  constructor <;> trivial
theorem multiplicationShape:mulHead=opening false 234++mulSpan ∧ oldMulHead=original false 234++oldMulSpan:=by
  simp only [mulHead,WindowKernelPrograms.mulBefore,mulSpan,opening,oldMulHead,Stair44Kernel.beforeX,Stair44Kernel.mulLead,original,oldMulSpan,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]
  constructor <;> trivial

def Related (d:Bool) (x:Nat) (a ref:State):Prop:=Paired d x (pullState phaseHost a) (pullState phaseHost ref) (StockRowVector.rows x p)

theorem division (H:∀{s:State} (F:EntryFrame s) (m t:List Bool),
    let a:=run (opening true 154) m s
    let b:=run (original true 154) m s
    Related true F.x a b → ∃old, Related false F.x (run divSpan t a) (run oldDivSpan old b)):
    WindowMiddleContract.entry:=by
  intro s F m
  let A:=opening true 154
  let B:=original true 154
  obtain ⟨old,rel⟩:=H F m (m.drop (measurementCount A)) (WindowStartStates.division F m)
  refine ⟨pfx (measurementCount B) m++old,?_⟩
  rw [divisionShape.1,divisionShape.2,Stair44PointSecond.joinRecords,run_append,run_take]
  exact rel

theorem multiplication (H:∀k {s:State} (F:ExitFrame k s) (m t:List Bool),
    let a:=run (opening false 234) m s
    let b:=run (original false 234) m s
    Related false F.x a b → ∃old, Related true F.x (run mulSpan t a) (run oldMulSpan old b)):
    WindowMiddleContract.exit:=by
  intro k s F m
  let A:=opening false 234
  let B:=original false 234
  obtain ⟨old,rel⟩:=H k F m (m.drop (measurementCount A)) (WindowStartStates.multiplication k F m)
  refine ⟨pfx (measurementCount B) m++old,?_⟩
  rw [multiplicationShape.1,multiplicationShape.2,Stair44PointSecond.joinRecords,run_append,run_take]
  exact rel
end ECDSAAdd.Entrant.StairPacket.WindowMiddlePieces

end

