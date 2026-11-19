import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Submission.Entrant.PrizeTail8dd9f9e60

section

namespace ECDSAAdd.Entrant.Stair44PointDivision
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXEntry FrontierEntry1591Callers Stair44PlacedHead
set_option maxHeartbeats 3500000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount fastConstAdd fusedY

def reference (kx ky : Fp) := fastConstAdd layout layout.point.x kx ++ fusedY layout ky

theorem standardHead (cx cy X Y : Fp) (G : Bool) (s : State) (m : List Bool)
    (v : PointDialogValues layout X Y G s.basis s.basis) :
    let e := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+(-cx).val) else false
    run (plain (-cx) (-cy)) m (put s (pkW layout) e) =
    run (E1QubitPlacement.tickF layout) [] (run (reference (-cx) (-cy)) [] s) := by
  intro e
  have a := (StairCallerEntry.head_pad_rest layout layout_widths layout_nodup cx cy X Y []
    s v.x v.y v.clean (by decide +kernel)).run_eq m
  have b := StairCallerEntry.stageAll_eq_ref layout layout_widths layout_nodup X Y (-cx) (-cy) []
    s (padE layout cy cx m) v.x v.y v.clean
  have c := E1QubitPlacement.entry1_eq layout layout_widths layout_nodup (-cx) (-cy) s X.val X.isLt Y G
    v.x v.y v.generic v.clean (padE layout cy cx m) []
  simp only [List.append_nil] at a b
  rw [plain,a,b,c,run_append,List.take_nil,List.drop_nil,reference]

theorem prepClean (kx ky X Y : Fp) (G : Bool) (s : State)
    (v : PointDialogValues layout X Y G s.basis s.basis) :
    regValue layout.dialogPool (run (reference kx ky) [] s).basis=0 := by
  let P := fastConstAdd layout layout.point.x kx
  have u := fastStep_addX layout layout_widths layout_nodup X Y G s.basis kx s [] v
  have f := fusedY_correct layout layout_widths layout_nodup Y ky (run P [] s) [] u.2.y u.2.clean
  rw [reference,run_append,List.take_nil,List.drop_nil]
  exact (regValue_congr _ _ (run P [] s).basis (fun q hq => f.2.2 q
    (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2))).trans u.2.clean

def part (cx cy : Fp) := routed (-cx) (-cy) ++ Stair44Outer.divide

theorem stage (cx cy X Y : Fp) (G : Bool) (s : State) (m : List Bool)
    (v : PointDialogValues layout X Y G s.basis s.basis) (hx : X+(if G then -cx else 0)≠0) :
    let e := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+(-cx).val) else false
    let u := run (part cx cy) m (pullState Stair44PointMap.outer.symm (put s (pkW layout) e))
    u.phase=s.phase ∧ PointDialogValues layout (X+(if G then -cx else 0))
      ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) G s.basis u.basis := by
  intro e u
  let P := reference (-cx) (-cy)
  let F := E1QubitPlacement.tickF layout
  let K := FrontierEntry1591Callers.entry Stair44Kernel.division layout
  let H := routed (-cx) (-cy)
  let r := m.drop (measurementCount H)
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX layout layout_widths layout_nodup X Y G s.basis (-cx)
  have div := StairSemanticFinal.division_stepD Stair44Kernel.division Stair44CallerSupport.division
    Stair44Kernel.division_correct layout layout_widths layout_nodup config.1 above config.2.1 config.2.2
    (X+(if G then -cx else 0)) Y (-cy) G s.basis hx
  have joint := add.seq div
  have equiv : (fastConstAdd layout layout.point.x (-cx) ++ FrontierEntry1591Callers.division Stair44Kernel.division layout (-cy))=P++K := List.append_assoc _ _ _ |>.symm
  rw [equiv] at joint
  have ans := joint s (pfx (measurementCount P) [] ++ (pfx (measurementCount Stair44Splits.tick) [] ++ r)) v
  rw [run_pre,show K=Stair44Splits.tick++Stair44Outer.divide from Stair44Splits.div_split,run_pre,
    show Stair44Splits.tick=renameProgram Stair44PointMap.integerFirst F from rfl,
    encodedTick _ _ (prepClean (-cx) (-cy) X Y G s v)] at ans
  have tr := encoded_head X Y (-cx) (-cy) s (m.take (measurementCount H)) v.x v.y v.clean
  dsimp only at tr
  rw [standardHead cx cy X Y G s _ v] at tr
  have replay : u=run Stair44Outer.divide r (pullState Stair44PointMap.integerFirst.symm (run F [] (run P [] s))) := by
    change run (H++Stair44Outer.divide) m _=_
    rw [run_append]
    exact congrArg (run Stair44Outer.divide r) tr
  rw [replay]
  exact ans

end ECDSAAdd.Entrant.Stair44PointDivision

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 20000
attribute [local irreducible] wires domain
theorem forward_domain (d : Bool) : ∀ q ∈ wires (forward45plus1 d), domain q = true := by
  intro q h
  cases d
  · simp only [forward45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site0 q h
    · exact site1 q h
    · exact site2 q h
    · exact site3 q h
    · exact site4 q h
    · exact site5 q h
    · exact site6 q h
    · exact site7 q h
    · exact site8 q h
    · exact site9 q h
    · exact site10 q h
    · exact site11 q h
    · exact site12 q h
    · exact site13 q h
    · exact site14 q h
    · exact site15 q h
    · exact site16 q h
    · exact site17 q h
    · exact site18 q h
    · exact site19 q h
    · exact site20 q h
    · exact site21 q h
    · exact site22 q h
  · simp only [forward45plus1,wires_append,Finset.mem_union,or_assoc] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact site0 q h
    · exact site1 q h
    · exact site2 q h
    · exact site23 q h
    · exact site4 q h
    · exact site5 q h
    · exact site6 q h
    · exact site7 q h
    · exact site24 q h
    · exact site25 q h
    · exact site10 q h
    · exact site11 q h
    · exact site12 q h
    · exact site13 q h
    · exact site26 q h
    · exact site27 q h
    · exact site16 q h
    · exact site17 q h
    · exact site18 q h
    · exact site19 q h
    · exact site20 q h
    · exact site28 q h
    · exact site29 q h
end ECDSAAdd.Entrant.StairPacket.PartialSites
namespace ECDSAAdd.Entrant.StairPacket.WindowIntegerSites
open Arithmetic MappedCompressed StairSemanticFinal Stair44WalkMap PartialSites WindowKernelPrograms
open DirectSkywalk StairConcreteAssembly Stair44Kernel
set_option maxRecDepth 12000
attribute [local irreducible] wires renameProgram

private theorem swap (a b:Nat) (ha:a<2314) (hb:b<2314):PreservesCaller (Equiv.swap (base a) (base b)):=
  preserves_swap _ _ (base_mem_caller _ (Or.inl ha)) (base_mem_caller _ (Or.inl hb))
theorem firstOK:PreservesCaller Stair44WalkMap.first:=by
  unfold Stair44WalkMap.first Stair44WalkMap.shared
  repeat' apply preserves_perm_trans
  all_goals exact swap _ _ (by decide) (by decide)
theorem restOK:PreservesCaller Stair44WalkMap.rest:=by
  unfold Stair44WalkMap.rest Stair44WalkMap.shared
  repeat' apply preserves_perm_trans
  all_goals exact swap _ _ (by decide) (by decide)
theorem range_ok (q:Nat) (use:PartialSites.domain q=true):q∈callerDomain:=by
  have h:=PartialSites.inside q use
  have eq:base (q-16)=q:=by change q-16+16=q;exact Nat.sub_add_cancel h.1
  exact eq ▸ base_mem_caller (q-16) (Or.inl (by omega))
theorem part (d:Bool):wires (Partial.forward45plus1 d)⊆callerDomain ∧ wires (Partial.reverse45plus1 d)⊆callerDomain:=
  ⟨fun q h=>range_ok q (forward_domain d _ h),fun q h=>range_ok q (reverse_domain d _ h)⟩

theorem forward (d:Bool) (n:Nat) (bound:270+n≤504):wires (WindowWalkCosts.forward d n)⊆callerDomain:=by
  have stock:=forward_own d (270+n) bound
  have shape:270+n=15+(209+(46+n)):=by omega
  rw [shape,tickGap_forward_split d 15 1 (209+(46+n)),tickGap_forward_split d 209 16 (46+n),tickGap_forward_split d 46 225 n] at stock
  simp only [wires_append,Finset.union_subset_iff] at stock
  apply wires_sub_of_parts _ _
  · exact rename_caller _ firstOK _ stock.1
  · apply rename_caller _ restOK
    exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ stock.2.1 (part d).1) stock.2.2.2

theorem backward (d:Bool) (n:Nat) (bound:270+n≤505):wires (WindowWalkCosts.backward d n)⊆callerDomain:=by
  have stock:=reverse_own d (270+n) bound
  have shape:270+n=15+(209+(46+n)):=by omega
  rw [shape,reverse_split d 15 1 (209+(46+n)),reverse_split d 209 16 (46+n),reverse_split d 46 225 n] at stock
  simp only [wires_append,Finset.union_subset_iff] at stock
  apply wires_sub_of_parts _ _
  · apply rename_caller _ restOK
    exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ stock.1.1.1 (part d).2) stock.1.2
  · exact rename_caller _ firstOK _ stock.2
end ECDSAAdd.Entrant.StairPacket.WindowIntegerSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelReplay
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime FlagEntry StairConcreteAssembly StockArchiveBanks
open WindowMiddleContract WindowStockHead
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount wires renameProgram

theorem tail (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (cut:271+n∈[425,505,506])
    (a ref:State) (P:Program) (m:List Bool)
    (pair:Paired d x (pullState phaseHost a) (pullState phaseHost ref) (StockRowVector.rows x p))
    (known:Endpoint d x (270+n) (pullState phaseHost ref)):
    ∃old,run (renameProgram phaseHost (WindowWalkCosts.backward d n++P)) m a=
      run (renameProgram phaseHost (Stair44WalkRun.backward d (255+n)++P)) old ref:=by
  obtain ⟨s,enc,stage,ag⟩:=known
  obtain ⟨old,eq⟩:=StockWalkEndpoints.closed d n x nz lt cut s _ _ m enc stage pair ag
  let A:=WindowWalkCosts.backward d n
  let B:=Stair44WalkRun.backward d (255+n)
  let suffix:=m.drop (measurementCount A)
  refine ⟨pfx (measurementCount B) old++suffix,?_⟩
  apply MappedCompressed.pullState_perm_injective phaseHost
  rw [run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,Stair44PointSecond.joinRecords]
  rw [run_append,run_take]
  exact congrArg (run P suffix) eq

theorem compose {A B P Q:Program} {s:State} {m old:List Bool}
    (h:∃r,run P (m.drop (measurementCount A)) (run A m s)=run Q r (run B old s)):
    ∃r,run (A++P) m s=run (B++Q) r s:=by
  obtain ⟨post,close⟩:=h
  refine ⟨pfx (measurementCount B) old++post,?_⟩
  rw [Stair44PointSecond.joinRecords,run_append,run_take]
  exact close
theorem div_run (geometry:WindowMiddleContract.entry) {t:State} (F:EntryFrame t) (m:List Bool):
    ∃old,run WindowKernelPrograms.division m t=run Stair44Kernel.division old t:=by
  obtain ⟨head,v⟩:=geometry F m
  rw [div_head_split,old_div_head_split]
  exact compose (old:=head) (tail false 235 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (div_endpoint F head))

theorem mul_run (geometry:WindowMiddleContract.exit) (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    ∃old,run (WindowKernelPrograms.multiplication k) m t=run (Stair44Kernel.multiplication k) old t:=by
  obtain ⟨head,v⟩:=geometry k F m
  rw [mul_head_split,old_mul_head_split]
  exact compose (old:=head) (tail true 154 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (mul_endpoint k F head))

theorem division_correct (geometry:WindowMiddleContract.entry):
    FrontierEntry1591Callers.EntryCorrect WindowKernelPrograms.division:=by
  intro hn hl ho hf x Y hx0 hx s t m input hg hs phase eq val
  let F:EntryFrame t:=⟨hn,hl,ho,hf,x,Y,hx0,hx,s,input,hg,hs,phase,eq,val⟩
  obtain ⟨old,same⟩:=div_run geometry F m
  dsimp only
  rw [same]
  exact Stair44Kernel.division_correct hn hl ho hf x Y hx0 hx s t old input hg hs phase eq val

private theorem afterPull (f : Wire → Wire) (s t : State) (h : s=pullState f t) : s.phase=t.phase := by
  subst s
  rfl

private theorem afterPut (s t : State) (q : Wire) (v : Bool) (h : s=ParityEven.put t q v) : s.phase=t.phase := by
  subst s
  rfl

private theorem correctPhase {K : Program} {k : Nat} (law : ParityXExitInverse23Kernel.ExitNegCorrect K k)
    {s : State} (F : ExitFrame k s) (m : List Bool) : (run K m s).phase=s.phase :=
  (law F.sharedNodup F.historyAbove F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt s m F.input
    F.selectorG_zero F.selectorS_zero).1

theorem old_phase (k:Nat) {s:State} (F:ExitFrame k s) (m:List Bool):
    (run (Stair44Kernel.multiplication k) m s).phase=s.phase:=by
  have a := afterPull _ _ _ (Stair44Kernel.mul_run k F m)
  have b := afterPut _ _ _ _ (StairCallerReplay.hostedExit_pw Stair44Kernel.hostReplay k F.k_lt F.sharedNodup F.historyAbove
    F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt s m F.input F.selectorG_zero F.selectorS_zero)
  exact a.trans (b.trans (correctPhase (ParityXExitInverse23Kernel.kernelX_correct k F.k_lt) F m))

theorem multiplication_eq (geometry:WindowMiddleContract.exit) (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    run (WindowKernelPrograms.multiplication k) m t=run (Stair44Kernel.multiplication k) m t:=by
  obtain ⟨other,eq⟩:=mul_run geometry k F m
  rw [eq]
  exact State.extensionality _ _ ((old_phase k F other).trans (old_phase k F m).symm)
    (Arithmetic.run_basis_records _ _ _ _ _ rfl)
end ECDSAAdd.Entrant.StairPacket.WindowKernelReplay

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify WindowParityDirty
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option linter.unusedSimpArgs false
def delta (d : Bool) (r : Nat) :=
  ((parity (ArchivePortAction.code d)).testBit r) ^^ ((parity (StairArchiveNativeCut.canonical d d)).testBit r)
def Active (j : Nat) := j=46 ∨ j=49 ∨ j=52
private theorem mesh : wires region⊆Finset.range 31 := by decide +kernel
private theorem portDistinct : ∀ j∈([46,49,52]:List Nat), ((List.range 31).map (port j)).Nodup := by decide +kernel
private theorem inj {j : Nat} (hj : Active j) :
    ∀a∈Finset.range 31,∀b∈Finset.range 31, port j a=port j b → a=b := by
  intro a ha b hb eq
  have mem : j∈([46,49,52]:List Nat) := by rcases hj with h|h|h <;> simp [h]
  have la := Finset.mem_range.mp ha
  have lb := Finset.mem_range.mp hb
  apply (List.Nodup.getElem_inj_iff (portDistinct j mem) (i:=a) (j:=b)
    (hi:=by simpa using la) (hj:=by simpa using lb)).mp
  simpa only [List.getElem_map,List.getElem_range] using eq
private theorem center (j : Nat) : port j 16=FrontierEntry1591Field.host := by rfl
theorem site_ne {j i : Nat} (hj : Active j) (hi : i<16) : site j i≠FrontierEntry1591Field.host := by
  intro bad
  have eq : port j i=port j 16 := by simpa only [port,if_pos hi,center] using bad
  have := inj hj i (Finset.mem_range.mpr (by omega)) 16 (by decide) eq
  omega
def Data (s : State) (j : Nat) (d : Bool) (r : Nat) :=
  ∀ i<16,s.basis (site j i)=(get (ArchivePortAction.code d) i).testBit r
attribute [local irreducible] run region port site
theorem bank_run (j : Nat) (hj : Active j) (d : Bool) (r : Nat) (hr : r<63145)
    (m : List Bool) (s : State) (h : Data s j d r) :
    run (bankCorrection j) m s = flip FrontierEntry1591Field.host (delta d r) s := by
  let loc := pullState (port j) s
  have dloc : ∀i<16,loc.basis i=(get (ArchivePortAction.code d) i).testBit r := by
    intro i hi; simpa only [loc,pullState,port,if_pos hi] using h i hi
  have hrun := run_rename_pool (port j) (Finset.range 31) (inj hj) region mesh m loc s rfl (fun _ _=>rfl)
  rw [region_run d r hr m loc dloc] at hrun
  apply State.extensionality
  · change (run (renameProgram (port j) region) m s).phase=s.phase
    exact hrun.1
  funext q
  by_cases mem : q∈(Finset.range 31).image (port j)
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp mem
    rw [show bankCorrection j=renameProgram (port j) region from rfl,hrun.2 k hk]
    by_cases e : k=16
    · subst k; rw [center,at_flip,at_flip]; simp only [loc,pullState,center,delta]
    · have neq : port j k≠FrontierEntry1591Field.host := fun bad=>e (inj hj _ hk 16 (by decide) (bad.trans (center j).symm))
      rw [at_other _ _ _ _ e,at_other _ _ _ _ neq]; rfl
  · have neq : q≠FrontierEntry1591Field.host := by
      intro bad; exact mem (Finset.mem_image.mpr ⟨16,by decide,(center j).trans bad.symm⟩)
    exact (run_rename_pool_outside _ _ _ mesh _ _ _ mem).trans (at_other _ _ _ _ neq).symm
private theorem data_flip (s : State) (v : Bool) {j : Nat} (hj : Active j) {d r} (h : Data s j d r) :
    Data (flip FrontierEntry1591Field.host v s) j d r := by
  intro i hi; rw [at_other _ _ _ _ (site_ne hj hi)]; exact h i hi
attribute [local irreducible] bankCorrection
theorem correction_run (dirs : Nat→Bool) (rows : Nat→Nat) (m : List Bool) (s : State)
    (hr : ∀j, Active j → rows j<63145) (hd : ∀j, Active j→Data s j (dirs j) (rows j)) :
    run correction m s = flip FrontierEntry1591Field.host
      ((delta (dirs 46) (rows 46) ^^ delta (dirs 49) (rows 49)) ^^ delta (dirs 52) (rows 52)) s := by
  have a : Active 46 := Or.inl rfl
  have b : Active 49 := Or.inr (Or.inl rfl)
  have c : Active 52 := Or.inr (Or.inr rfl)
  simp only [correction,run_append,run_take]
  rw [bank_run 46 a _ _ (hr _ a) _ s (hd _ a),
    bank_run 49 b _ _ (hr _ b) _ _ (data_flip _ _ b (hd _ b)),
    bank_run 52 c _ _ (hr _ c) _ _ (data_flip _ _ c (data_flip _ _ c (hd _ c))),
    flip_twice,flip_twice,Bool.xor_assoc]
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

set_option maxRecDepth 30000
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.Window45Dialog
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out ParityEven ParityUniform
open FlagExit
open ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic ParityXEntry
open MappedCompressed Stair44PointMap
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
attribute [local irreducible] run wires

def logical (cx cy : Fp) := renameProgram outer.symm (StairPacket.WindowParityCaller.generic cx cy)
def block (cx cy : Fp) := renameProgram (FlagTop.rho layout) (logical cx cy)
def borrow (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control) (block cx cy)
def middle (C : Point) (cx cy : Fp) := AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB ++
  borrow cx cy ++ AboveFieldPointDevelop.loadB ++ AboveFieldPointDevelop.decode C
def finite (C : Point) (cx cy : Fp) := FlagTop.stageNew layout C (pkW layout) ++
  middle C cx cy ++ ControlPointEncodingDevelop.borrowOut C
def wrapper (C : Point) (cx cy : Fp) := renameProgram (Wrapper5.U layout) (finite C cx cy)

def GenericReplay : Prop := ∀ (cx cy X Y : Fp) (G : Bool) (s : State) (e : Bool)
    (hv : PointDialogValues layout X Y G s.basis s.basis)
    (he : e = (if s.basis layout.core.generic then
      decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hg : pkW layout ≠ layout.core.generic)
    (hx1 : X+(if G then -cx else 0)≠0)
    (hx2 : (X+(if G then -cx else 0))-
        (if G then ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0)))*
          ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) else 0)+
        (if G then (SquareCarryLoan719BF.K:Fp) else 0)+
        (if G then ReflectionE1.correction cx else 0)≠0)
    (m : List Bool),
    ∃ old, run (StairPacket.WindowParityCaller.generic cx cy) m (pullState outer.symm (put s (pkW layout) e)) =
      pullState outer.symm (run (genericN layout cx cy) old (put s (pkW layout) e))

theorem logicalReplay (H : GenericReplay) (cx cy X Y : Fp) (G : Bool) (s : State) (e : Bool)
    (hv : PointDialogValues layout X Y G s.basis s.basis)
    (he : e = (if s.basis layout.core.generic then
      decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hg : pkW layout ≠ layout.core.generic)
    (hx1 : X+(if G then -cx else 0)≠0)
    (hx2 : (X+(if G then -cx else 0))-
        (if G then ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0)))*
          ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) else 0)+
        (if G then (SquareCarryLoan719BF.K:Fp) else 0)+
        (if G then ReflectionE1.correction cx else 0)≠0)
    (m : List Bool) :
    ∃ old, run (logical cx cy) m (put s (pkW layout) e) =
      run (genericN layout cx cy) old (put s (pkW layout) e) := by
  obtain ⟨old, eq⟩ := H cx cy X Y G s e hv he hg hx1 hx2 m
  refine ⟨old, MappedCompressed.pullState_perm_injective outer.symm ?_⟩
  rw [logical,run_rename _ outer.symm.injective,eq]
end ECDSAAdd.Entrant.Window45Dialog

namespace ECDSAAdd.Entrant.StairSemanticFinal.Window45
section Generic
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out ParityEven ParityUniform
open FlagExit
open ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic ParityXEntry
set_option maxHeartbeats 8000000 in
/-- Hosted counterpart of `FlagExit.generic_padp_true` (same hypotheses). -/
theorem routed_generic_eq_trueD
    (H : Window45Dialog.GenericReplay)
    (X Y cx cy : Fp) (s : State) (e : Bool)
    (hv : PointDialogValues layout X Y true s.basis s.basis)
    (he : e = (if s.basis layout.core.generic then
      decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hXc : X≠cx) (hd : cx-genericX X Y cx cy≠0) (hg : pkW layout ≠ layout.core.generic)
    (m : List Bool) :
    ∃ m', run (Window45Dialog.logical cx cy) m (put s (pkW layout) e) =
      run (genericN layout cx cy) m' (put s (pkW layout) e) := by
  let a:=genericSlope X Y cx cy
  let d:=cx-genericX X Y cx cy
  have hvv:=generic_inplace_values X Y cx cy hXc
  have ha : (Y-cy)/(X-cx)=a:=rfl
  have hd4 : (X-cx)-a*a+(SquareCarryLoan719BF.K:Nat)+ReflectionE1.correction cx=d := by
    have e:=hvv.2.1
    change (X-cx)-a*a+3*cx=d at e
    rw [←e]
    unfold ReflectionE1.correction
    ring
  apply Window45Dialog.logicalReplay H cx cy X Y true s e hv he hg
  · simpa only [if_true,←sub_eq_add_neg] using sub_ne_zero.mpr hXc
  · simp only [if_true,←sub_eq_add_neg,ha]
    rw [hd4]
    exact hd

set_option maxHeartbeats 8000000 in
/-- Hosted counterpart of `FlagExit.generic_padp_false` (same hypotheses). -/
theorem routed_generic_eq_falseD
    (H : Window45Dialog.GenericReplay)
    (X Y cx cy : Fp) (s : State) (e : Bool)
    (hv : PointDialogValues layout X Y false s.basis s.basis)
    (he : e = (if s.basis layout.core.generic then
      decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))
    (hX0 : X≠0) (hg : pkW layout ≠ layout.core.generic) (m : List Bool) :
    ∃ m', run (Window45Dialog.logical cx cy) m (put s (pkW layout) e) =
      run (genericN layout cx cy) m' (put s (pkW layout) e) := by
  apply Window45Dialog.logicalReplay H cx cy X Y false s e hv he hg
  · simpa only [Bool.false_eq_true,if_false,add_zero] using hX0
  · simpa only [Bool.false_eq_true,if_false,add_zero,sub_zero] using hX0

end Generic
section Block
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out FlagTop FlagExit OutFlag ParityEven
  ParityUniform FlagTop2
open ControlGenericPointDevelop

open Classical in
/-- Hosted counterpart of `ControlGenericPointDevelop.generic_pad_point`, as a
run equality with the record block on the same states. -/
theorem routed_block_eq_pointD
    (H : Window45Dialog.GenericReplay)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (t1 : State) (m2 : regValue layout.point.x t1.basis = codeX R)
    (t1y : regValue layout.point.y t1.basis = pointY R)
    (m3 : t1.basis layout.point.finite = false)
    (m4 : t1.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (hE' : t1.basis layout.core.equalNegY = false) (hD : t1.basis layout.doubleSelect = false)
    (hclean : regValue layout.dialogPool t1.basis = 0) (m : List Bool) :
    ∃ m', run (renameProgram (rho layout) (Window45Dialog.logical cx cy)) m
        (put t1 (pkW layout) (dialogOrdinary b R (.some hc) &&
          decide ((triOf (.some hc)).A < codeX R))) =
      run (renameProgram (rho layout) (genericN layout cx cy)) m'
        (put t1 (pkW layout) (dialogOrdinary b R (.some hc) &&
          decide ((triOf (.some hc)).A < codeX R))) := by
  classical
  have hC : (.some hc : Point) ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hgen : pkW layout ≠ layout.core.generic :=
    pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  have wrap : ∀ (X Y : Fp), X.val = codeX R → Y.val = pointY R →
      (PointDialogValues layout X Y (dialogOrdinary b R (.some hc))
          (pullState (rho layout) t1).basis (pullState (rho layout) t1).basis →
        ∃ m', run (Window45Dialog.logical cx cy) m
            (put (pullState (rho layout) t1) (pkW layout)
              (if dialogOrdinary b R (.some hc) then
                decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false)) =
          run (genericN layout cx cy) m'
            (put (pullState (rho layout) t1) (pkW layout)
              (if dialogOrdinary b R (.some hc) then
                decide (EntryFuseArithmetic.prime ≤ X.val + (-cx).val) else false))) →
      ∃ m', run (renameProgram (rho layout) (Window45Dialog.logical cx cy)) m
          (put t1 (pkW layout) (dialogOrdinary b R (.some hc) &&
            decide ((triOf (.some hc)).A < codeX R))) =
        run (renameProgram (rho layout) (genericN layout cx cy)) m'
          (put t1 (pkW layout) (dialogOrdinary b R (.some hc) &&
            decide ((triOf (.some hc)).A < codeX R))) := by
    intro X Y hXv hYv h
    have pvv := pulled_values t1 X Y (dialogOrdinary b R (.some hc)) (m2.trans hXv.symm)
      (t1y.trans hYv.symm) m3 m4 hE' hD hclean
    rw [flag_eq hc b R X hXv]
    obtain ⟨m', h'⟩ := h ⟨pvv.1, pvv.2.1, pvv.2.2.1, pvv.2.2.2, fun _ _ => rfl⟩
    exact ⟨m', rename_put_eqD (rho layout) rho_injective (pkW layout) rho_pk _ _ t1 _ m m' h'⟩
  by_cases hG : dialogOrdinary b R (.some hc) = true
  · obtain ⟨hb, h0, h1, h2, h3⟩ := (dialogOrdinary_true b R _ hC).mp hG
    cases R with
    | zero => exact absurd rfl h0
    | @some x y hr =>
      have den := dialog_denominators_ne_zero hr hc h1 h2 h3
      apply wrap x y rfl rfl
      intro hv
      rw [hG] at hv
      exact routed_generic_eq_trueD H x y cx cy _ _ hv
        (by rw [hv.generic, hG]) den.1 den.2 hgen m
  · have hG' : dialogOrdinary b R (.some hc) = false := by simpa using hG
    cases R with
    | zero =>
      apply wrap (FiniteFlagInterval.sentinel : Fp) 0 FiniteFlagInterval.sentinel_val rfl
      intro hv
      rw [hG'] at hv
      exact routed_generic_eq_falseD H _ 0 cx cy _ _ hv
        (by rw [hv.generic, hG']) FiniteFlagInterval.sentinel_ne_zero hgen m
    | @some x y hr =>
      apply wrap x y rfl rfl
      intro hv
      rw [hG'] at hv
      exact routed_generic_eq_falseD H x y cx cy _ _ hv
        (by rw [hv.generic, hG']) (curve_x_ne_zero hr) hgen m

set_option maxHeartbeats 8000000 in
open Classical in
/-- Hosted `generic_point_run`: the same complete output description. -/
theorem routed_hosted_generic_point_runD
    (H : Window45Dialog.GenericReplay)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis = codeX R)
    (hy : regValue layout.point.y s.basis = pointY R)
    (hf : s.basis layout.point.finite = false)
    (hg : s.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (he : s.basis layout.core.equalNegY = false) (hd : s.basis layout.doubleSelect = false)
    (hz : regValue layout.dialogPool s.basis = 0) :
    let u:=put s (pkW layout) (dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < codeX R))
    let t:=run (renameProgram (rho layout) (Window45Dialog.logical cx cy)) m u
    t.phase=s.phase ∧
    regValue layout.point.x t.basis=codeX (if dialogOrdinary b R (.some hc) then R+.some hc else R) ∧
    regValue layout.point.y t.basis=pointY (if dialogOrdinary b R (.some hc) then R+.some hc else R) ∧
    t.basis (pkW layout)=vB hc b R ∧
    ∀q,q∉layout.point.x++layout.point.y→q≠pkW layout→t.basis q=s.basis q := by
  obtain ⟨m', eq⟩ := routed_block_eq_pointD H hc b R s hx hy hf hg he hd hz m
  dsimp only
  rw [eq]
  exact generic_point_run hc b R s m' hx hy hf hg he hd hz

set_option maxHeartbeats 8000000 in
/-- Hosted `GenericFalseDevelop.mapped_false`: on a non-generic dialog state the
hosted generic block is the identity. -/
theorem routed_hosted_mapped_falseD
    (H : Window45Dialog.GenericReplay)
    (X Y cx cy : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hy : regValue layout.point.y s.basis=Y.val)
    (hf : s.basis layout.point.finite=false) (hg : s.basis layout.genericSelect=false)
    (he : s.basis layout.core.equalNegY=false) (hd : s.basis layout.doubleSelect=false)
    (hz : regValue layout.dialogPool s.basis=0) (hx0 : X≠0) :
    run (renameProgram (rho layout) (Window45Dialog.logical cx cy)) m s=s := by
  have pv:=pulled_values s X Y false hx hy hf hg he hd hz
  have hv:PointDialogValues layout X Y false (pullState (rho layout) s).basis
      (pullState (rho layout) s).basis:=⟨pv.1,pv.2.1,pv.2.2.1,pv.2.2.2,fun _ _=>rfl⟩
  have hgen : pkW layout ≠ layout.core.generic :=
    pk_flag _ (by simp [ControlledPointLayout.inPlaceFlags])
  have hpk : s.basis (pkW layout) = false :=
    (regValue_zero _ _).mp hz _ (pk_pool layout layout_widths)
  have hput : put s (pkW layout) false = s := by
    apply State.extensionality _ s
    · rfl
    funext q
    by_cases hp : q = pkW layout
    · subst q; simp [put, writeBit, hpk]
    · simp [put, writeBit,  hp]
  have hgv : (pullState (rho layout) s).basis layout.core.generic = false := hv.generic
  obtain ⟨m', eq⟩ := routed_generic_eq_falseD H X Y cx cy
    (pullState (rho layout) s) false hv (by rw [hgv]; rfl) hx0 hgen m
  have lifted := rename_put_eqD (rho layout) rho_injective (pkW layout) rho_pk _ _ s false m m' eq
  rw [hput] at lifted
  rw [lifted]
  exact GenericFalseDevelop.mapped_false X Y cx cy s m' hx hy hf hg he hd hz hx0

end Block
section Parked
open Arithmetic RecordedQuantum MeasuredCodec5 Baselines Secp256k1 ControlledPointLayout
  InputSentinel CompressedPointDialog CompressedAllocation CompressedFieldSupport
  EntryFuse EntryFuseFinite ExitFusionResearch FrontierEntry1591Callers BalancedField
  Challenge ParityCarry FlagEntry ParityFinalBothInverse23Out FlagTop FlagExit OutFlag ParityEven
  ParityUniform FlagTop2
open ControlGenericPointDevelop
attribute [local irreducible] layout

set_option maxHeartbeats 8000000 in
open Classical in
/-- Hosted `ControlGenericPointDevelop.generic_parked_run`. -/
theorem routed_hosted_parked_runD
    (H : Window45Dialog.GenericReplay)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis = codeX R)
    (hy : regValue layout.point.y s.basis = pointY R)
    (hf : s.basis layout.point.finite = false)
    (hg : s.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (he : s.basis layout.core.equalNegY = false) (hd : s.basis layout.doubleSelect = false)
    (hz : ∀q∈layout.dialogPool,q≠pkW layout→s.basis q=false)
    (hpk:s.basis (pkW layout)=(dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < codeX R))) :
    let t:=run (Window45Dialog.block cx cy) m s
    t.phase=s.phase ∧
    regValue layout.point.x t.basis=codeX (if dialogOrdinary b R (.some hc) then R+.some hc else R) ∧
    regValue layout.point.y t.basis=pointY (if dialogOrdinary b R (.some hc) then R+.some hc else R) ∧
    t.basis (pkW layout)=vB hc b R ∧
    ∀q,q∉layout.point.x++layout.point.y→q≠pkW layout→t.basis q=s.basis q := by
  let a:=put s (pkW layout) false
  have ax:regValue layout.point.x a.basis=codeX R:=
    (put_reg _ _ _ _ (by decide +kernel)).trans hx
  have ay:regValue layout.point.y a.basis=pointY R:=
    (put_reg _ _ _ _ (by decide +kernel)).trans hy
  have af:a.basis layout.point.finite=false:=by
    simpa [a,put,writeBit,Function.update_apply,
      show layout.point.finite≠pkW layout by decide +kernel] using hf
  have ag:a.basis layout.genericSelect=dialogOrdinary b R (.some hc):=by
    simpa [a,put,writeBit,Function.update_apply,
      show layout.genericSelect≠pkW layout by decide +kernel] using hg
  have ae:a.basis layout.core.equalNegY=false:=by
    simpa [a,put,writeBit,Function.update_apply,
      show layout.core.equalNegY≠pkW layout by decide +kernel] using he
  have ad:a.basis layout.doubleSelect=false:=by
    simpa [a,put,writeBit,Function.update_apply,
      show layout.doubleSelect≠pkW layout by decide +kernel] using hd
  have az:regValue layout.dialogPool a.basis=0:=by
    apply (regValue_zero _ _).mpr
    intro q hq
    by_cases hp:q=pkW layout
    · simp [a,put,writeBit,hp]
    · simpa [a,put,writeBit,Function.update_apply,hp] using hz q hq hp
  have restore:put a (pkW layout) (dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < codeX R))=s:=by
    apply State.extensionality _ s
    · rfl
    funext q
    by_cases hp:q=pkW layout
    · subst q;simp [a,put,writeBit,←hpk]
    · simp [a,put,writeBit,hp]
  have h:=routed_hosted_generic_point_runD H hc b R a m ax ay af ag ae ad az
  dsimp only at h
  rw [restore] at h
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
  intro q hq hp
  exact (h.2.2.2.2 q hq hp).trans (by simp [a,put,writeBit,hp])

end Parked

end ECDSAAdd.Entrant.StairSemanticFinal.Window45

namespace ECDSAAdd.Entrant.AboveFieldTagDevelop.LT11Final.Window45
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel FlagTop FlagExit
  FlagTop2 ParityEven ControlGenericPointDevelop ControlPointEncodingDevelop
open StairSemanticFinal StairSemanticFinal.Window45
attribute [local irreducible] layout run wires

set_option maxHeartbeats 8000000 in
open Classical in
/-- Hosted `AboveFieldTagDevelop.generic_format_run`. -/
theorem routed_hosted_format_runD
    (H : Window45Dialog.GenericReplay)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis = formatX (.some hc) b (dialogOrdinary b R (.some hc)) R)
    (hy : regValue layout.point.y s.basis = formatY (.some hc) b (dialogOrdinary b R (.some hc)) R)
    (hf : s.basis layout.point.finite = false)
    (hg : s.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (he : s.basis layout.core.equalNegY = false) (hd : s.basis layout.doubleSelect = false)
    (hz : ∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→s.basis q=false)
    (hpk:s.basis (FlagEntry.pkW layout)=(dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < ControlSentinelDevelop.ordinaryX R))) :
    let G:=dialogOrdinary b R (.some hc)
    let O:=if G then R+.some hc else R
    let t:=run (Window45Dialog.block cx cy) m s
    t.phase=s.phase ∧
    regValue layout.point.x t.basis=formatX (.some hc) b G O ∧
    regValue layout.point.y t.basis=formatY (.some hc) b G O ∧
    t.basis (FlagEntry.pkW layout)=vB hc b R ∧
    ∀q,q∉layout.point.x++layout.point.y→q≠FlagEntry.pkW layout→t.basis q=s.basis q := by
  cases hG:dialogOrdinary b R (.some hc)
  · have hpk0:s.basis (FlagEntry.pkW layout)=false:=by simpa only [hG,Bool.false_and] using hpk
    have hclean:regValue layout.dialogPool s.basis=0:=by
      apply (regValue_zero _ _).mpr
      intro q hq
      by_cases hp:q=FlagEntry.pkW layout
      · simpa only [hp] using hpk0
      · exact hz q hq hp
    let X: Fp:=formatX (.some hc) b false R
    let Y: Fp:=formatY (.some hc) b false R
    have hXv:X.val=formatX (.some hc) b false R:=
      ZMod.val_natCast_of_lt (format_bounds (.some hc) b false R).1
    have hYv:Y.val=formatY (.some hc) b false R:=
      ZMod.val_natCast_of_lt (format_bounds (.some hc) b false R).2
    have hid:=StairSemanticFinal.Window45.routed_hosted_mapped_falseD H X Y cx cy s m
      (by simpa only [hXv,hG] using hx) (by simpa only [hYv,hG] using hy) hf
      (hg.trans hG) he hd hclean (formatX_fp_ne_zero (.some hc) b false R)
    change run (Window45Dialog.block cx cy) m s=s at hid
    dsimp only
    rw [hid]
    simp only [Bool.false_eq_true,if_false]
    exact ⟨True.intro,by simpa only [hG] using hx,by simpa only [hG] using hy,
      by simpa only [vB,hG,Bool.false_and] using hpk0,fun _ _ _=>True.intro⟩
  · have hx':regValue layout.point.x s.basis=codeX R:=by
      rw [codeX_ordinary]
      simpa only [formatX,hG,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false] using hx
    have hy':regValue layout.point.y s.basis=pointY R:=by
      simpa only [formatY,hG,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false] using hy
    have hpk':s.basis (FlagEntry.pkW layout)=(dialogOrdinary b R (.some hc) &&
        decide ((triOf (.some hc)).A < codeX R)):=by
      simpa only [codeX_ordinary] using hpk
    have h:=routed_hosted_parked_runD H hc b R s m hx' hy' hf hg he hd hz hpk'
    dsimp only at h ⊢
    simpa [hG,formatX,formatY,codeX_ordinary] using h

end ECDSAAdd.Entrant.AboveFieldTagDevelop.LT11Final.Window45

namespace ECDSAAdd.Entrant.AboveFieldPointDevelop.LT11Final.Window45
open ControlPointEncodingDevelop
open Arithmetic Challenge Secp256k1 Baselines ControlledPointLayout InputSentinel FlagTop FlagExit
  FlagTop2 ParityEven ControlGenericPointDevelop
open StairSemanticFinal StairSemanticFinal.Window45 AboveFieldTagDevelop.LT11Final AboveFieldTagDevelop.LT11Final.Window45
attribute [local irreducible] layout run wires

set_option maxHeartbeats 8000000 in
open Classical in
/-- The hosted middle block replays the record middle block on every state
the record's `middle_sequence` starts from. -/
theorem routed_hostedMiddle_replayD
    (H : Window45Dialog.GenericReplay)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State)
    (hx : regValue layout.point.x s.basis = ControlSentinelDevelop.ordinaryX R)
    (hy : regValue layout.point.y s.basis = pointY R)
    (hb:s.basis layout.control=b)
    (hf : s.basis layout.point.finite = false)
    (hg : s.basis layout.genericSelect = dialogOrdinary b R (.some hc))
    (he : s.basis layout.core.equalNegY = false) (hd : s.basis layout.doubleSelect = false)
    (hz : ∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→s.basis q=false)
    (hpk:s.basis (FlagEntry.pkW layout)=(dialogOrdinary b R (.some hc) &&
      decide ((triOf (.some hc)).A < ControlSentinelDevelop.ordinaryX R)))
    (m : List Bool) :
    ∃ m', run (Window45Dialog.middle (.some hc) cx cy) m s =
      run (middle (.some hc) cx cy) m' s := by
  let C:Point:=.some hc
  have eqH : Window45Dialog.middle C cx cy = (encode C ++ eraseB) ++
      (Window45Dialog.borrow cx cy ++ (loadB ++ decode C)) := by
    simp only [Window45Dialog.middle, List.append_assoc]
  have eqR : middle C cx cy = (encode C ++ eraseB) ++
      (borrowGeneric cx cy ++ (loadB ++ decode C)) := by
    simp only [middle, List.append_assoc]
  rw [eqH, eqR]
  apply StairCallerGeneric.mid_replay
  intro tape b'
  let G:=dialogOrdinary b R C
  have hG:G=ControlSentinelDevelop.generic C b R:=
    ControlSentinelDevelop.generic_agrees C R b (WeierstrassCurve.Affine.Point.some_ne_zero hc)
  have hcorner:(b && !G)=true→ControlSentinelDevelop.corner C R:=by
    rw [hG]
    cases b <;> by_cases hr:ControlSentinelDevelop.corner C R <;>
      simp [ControlSentinelDevelop.generic,hr]
  have hgb:G=true→b=true:=by
    rw [hG]
    cases b <;> simp [ControlSentinelDevelop.generic]
  let me := tape.take (measurementCount (encode C))
  let ma := tape.drop (measurementCount (encode C))
  have hsplit : run (encode C ++ eraseB) tape s = run eraseB ma (run (encode C) me s) := by
    rw [run_append]
  let a:=run (encode C) me s
  have hp:=encode_spec hc b G R s me hgb hcorner hx hy hb hg
    (fun i=>hz _ (work_pool i) (work_off_pk i))
  have ha:XYResult s a (formatX C b G R) (formatY C b G R):=hp.1
  have apool:∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→a.basis q=false:=by
    intro q hq hpq
    exact (ha.rest q (pool_off_xy q hq)).trans (hz q hq hpq)
  have af:a.basis layout.point.finite=false:=(ha.rest _ finite_off_xy).trans hf
  have ag:a.basis layout.genericSelect=G:=(ha.rest _ generic_off_xy).trans hg
  have ab:a.basis layout.control=b:=(ha.rest _ control_off_xy).trans hb
  have ae:a.basis layout.core.equalNegY=false:=(ha.rest _ eneg_off_xy).trans he
  have ad:a.basis layout.doubleSelect=false:=(ha.rest _ double_off_xy).trans hd
  have apk:a.basis (FlagEntry.pkW layout)=(G && decide ((triOf C).A < ControlSentinelDevelop.ordinaryX R)):=
    (ha.rest _ (pool_off_xy _ (FlagEntry.pk_pool layout layout_widths))).trans hpk
  let u:=put a layout.control false
  have erase:run eraseB ma a=u:=by
    apply eraseB_run a ma (formatX C b G R) (formatY C b G R) ha.x ha.y af
      (fun q hq=>apool _ (marker_work_pool q hq) (marker_work_off_pk q hq))
    rw [ag,format_recover C b G R hgb]
    exact ab
  have ux:regValue layout.point.x u.basis=formatX C b G R:=
    (put_reg _ _ _ _ (by decide +kernel)).trans ha.x
  have uy:regValue layout.point.y u.basis=formatY C b G R:=
    (put_reg _ _ _ _ (by decide +kernel)).trans ha.y
  have uf:u.basis layout.point.finite=false:=(put_away a _ _ false finite_off_control).trans af
  have ug:u.basis layout.genericSelect=G:=(put_away a _ _ false generic_off_control).trans ag
  have ue:u.basis layout.core.equalNegY=false:=(put_away a _ _ false eneg_off_control).trans ae
  have ud:u.basis layout.doubleSelect=false:=(put_away a _ _ false double_off_control).trans ad
  have ub:u.basis layout.control=false:=put_at _ _ _
  have upool:∀q∈layout.dialogPool,q≠FlagEntry.pkW layout→u.basis q=false:=by
    intro q hq hpq
    exact (put_away a _ _ false (pool_off_control q hq)).trans (apool q hq hpq)
  have upk:u.basis (FlagEntry.pkW layout)=(G && decide ((triOf C).A < ControlSentinelDevelop.ordinaryX R)):=
    (put_away a _ _ false pk_off_control).trans apk
  rw [hsplit, erase]
  have gt:=generic_format_run hc b R u b' ux uy uf ug ue ud upool upk
  have ht:=routed_hosted_format_runD H hc b R u b' ux uy uf ug ue ud upool upk
  have gd:(run (genericBlock cx cy) b' u).basis layout.doubleSelect=false:=
    (gt.2.2.2.2 _ double_off_xy double_off_pk).trans ud
  have hd':(run (Window45Dialog.block cx cy) b' u).basis
      layout.doubleSelect=false:=
    (ht.2.2.2.2 _ double_off_xy double_off_pk).trans ud
  rw [borrowGeneric_run cx cy u b' ub ud gd]
  have hsw : run (Window45Dialog.borrow cx cy) b' u =
      run (Window45Dialog.block cx cy) b' u :=
    by
      let perm := Equiv.swap layout.doubleSelect layout.control
      have pre : pullState perm u=u := FieldFrameOB5.pull_swap_zero _ _ u ud ub
      have postC := (ht.2.2.2.2 _ control_off_xy (by decide +kernel)).trans ub
      have post := FieldFrameOB5.pull_swap_zero _ _ _ hd' postC
      apply MappedCompressed.pullState_perm_injective perm
      rw [Window45Dialog.borrow,run_rename _ perm.injective,pre]
      exact post.symm
  rw [hsw]
  apply State.extensionality
  · exact ht.1.trans gt.1.symm
  · funext q
    by_cases hqx : q ∈ layout.point.x
    · exact (regValue_eq_iff _ _ _).mp (ht.2.1.trans gt.2.1.symm) q hqx
    by_cases hqy : q ∈ layout.point.y
    · exact (regValue_eq_iff _ _ _).mp (ht.2.2.1.trans gt.2.2.1.symm) q hqy
    by_cases hqp : q = FlagEntry.pkW layout
    · subst hqp
      exact ht.2.2.2.1.trans gt.2.2.2.1.symm
    · have hq : q ∉ layout.point.x ++ layout.point.y := by simp [hqx, hqy]
      exact (ht.2.2.2.2 q hq hqp).trans (gt.2.2.2.2 q hq hqp).symm



theorem routed_finite (H : Window45Dialog.GenericReplay)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool) (R : Point)
    (s : State) (fresh : List Bool) (hs : encodes b R s.basis) :
    ∃ old, run (Window45Dialog.wrapper (.some hc) cx cy) fresh s =
      run (AboveFieldPointDevelop.wrapperBorrow (.some hc) cx cy) old s := by
    let C : Point := .some hc
    let U : Equiv.Perm Wire := Wrapper5.U Baselines.layout
    have finiteReplay : ∀ t, Challenge.encodes b R t.basis → ∀ tape, ∃ old,
        run (Window45Dialog.finite C cx cy) tape t =
          run (AboveFieldPointDevelop.finiteBorrow C cx cy) old t := by
      intro t ht tape
      have hi := StairCallerMiddle.boundary_of_encodes b R t ht
      simpa only [Window45Dialog.finite, AboveFieldPointDevelop.finiteBorrow,
        List.append_assoc] using
        (append_replayD
          (FlagTop.stageNew Baselines.layout C (FlagEntry.pkW Baselines.layout))
          (Window45Dialog.middle C cx cy)
          (AboveFieldPointDevelop.middle C cx cy)
          (ControlPointEncodingDevelop.borrowOut C)
          (fun st => Staged C R b st)
          (fun st hv records ↦
            routed_hostedMiddle_replayD H hc b R st hv.x hv.y hv.control hv.finite hv.generic
              hv.eneg hv.double hv.clean hv.parked records)
          t tape (fun prefixTape ↦ stage_values hc b R t prefixTape hi))
    have pulled_eq : pullState U s = s := by
      change pullState
        (Equiv.swap (Baselines.layout.core.poolWire 684)
          (Baselines.layout.core.poolWire 717)) s = s
      exact FieldFrameOB5.pull_swap_zero _ _ s
        (hs.2.2 _ (by decide +kernel))
        (hs.2.2 _ (by decide +kernel))
    have pulled_encoded : Challenge.encodes b R (pullState U s).basis := by
      rw [pulled_eq]
      exact hs
    obtain ⟨old, outer⟩ := rename_replayD U
      (Window45Dialog.finite C cx cy)
      (AboveFieldPointDevelop.finiteBorrow C cx cy)
      (fun t ↦ Challenge.encodes b R t.basis) finiteReplay s pulled_encoded fresh
    refine ⟨old, ?_⟩
    simpa only [C, Window45Dialog.wrapper, AboveFieldPointDevelop.wrapperBorrow, U]
      using outer

end ECDSAAdd.Entrant.AboveFieldPointDevelop.LT11Final.Window45

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPointWord
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog ParityEven ParityXExitInverse23Kernel StairSemanticFinal
  Stair44Kernel Stair44PointMap Baselines StairConcreteAssembly
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run wires measurementCount

def normalized (k : Nat) := renameProgram outMap.symm (WindowKernelPrograms.multiplication k)

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

private theorem normSupport (H:WindowKernelPrograms.Contracts) (k : Nat) : wires (normalized k)⊆callerDomain :=
  rename_caller outMap.symm keep (WindowKernelPrograms.multiplication k) (H.mulSites k)

private theorem normalizedRun (H:WindowKernelPrograms.Contracts) {k : Nat} {s : State} (F : ExitFrame k s) (m : List Bool) :
    run (normalized k) m s=run (StairHostsSchedule.exitKernel StairConcreteAssembly.checkpointPrimitives StairConcreteAssembly.hostPlan k) m s := by
  apply MappedCompressed.pullState_perm_injective outMap.symm
  rw [normalized,run_rename _ outMap.symm.injective,clean F,H.exit k F,mul_run k F]

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

theorem fullWord (H:WindowKernelPrograms.Contracts) (k X Y : Nat) (hk : k<p) (hp : 0<X) (hx : X<p) (hy : Y<p) (s : State) (m : List Bool)
    (sx : regValue layout.point.x s.basis=X) (sy : regValue layout.point.y s.basis=Y)
    (sc : regValue layout.dialogPool s.basis=0) :
    let C := FrontierEntry1591Callers.exit (WindowKernelPrograms.multiplication k) layout
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
    (normalized k) (kernelX k) (normSupport H k) ((kernelX_support k).trans logical_sub_caller)
    (fun t records input hg hs => by
      let F : ExitFrame k t := ⟨hk,config.1,above,config.2.1,config.2.2,X,(Y:Fp),hp,hx,input,hg,hs⟩
      rw [normalizedRun H F]
      exact StairCallerReplay.hostedExit_pw hostReplay k hk config.1 above config.2.1 config.2.2 X (Y:Fp) hp hx t records input hg hs)
  have place : renameProgram (wireFn2 layout) (normalized k)=renameProgram outer.symm C :=
    transport (wireFn2 layout) outMap.symm outer.symm (WindowKernelPrograms.multiplication k) physInv
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

end ECDSAAdd.Entrant.StairPacket.WindowPointWord

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify WindowParityDirty FrontierEntry1591Field
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
private theorem stock_flip (m : List Bool) (s : State) :
    run StairSchedule.paritySetup m s=flip host (stockParity s) s :=
  ParityHost5.setup_run controls host s m host_not_controls
theorem setup_pair (rows : Nat→Nat) (dirs : Nat→Bool) (a b : State) (m : List Bool)
    (valid : ∀ j,Active j → rows j<63145)
    (rest : ∀i,Elsewhere i→a.basis (addr i)=b.basis (addr i))
    (actual : ∀j,Active j→Data a j (dirs j) (rows j))
    (stock : ∀j,Active j→∀i<16,b.basis (site j i)=(get (StairArchiveNativeCut.canonical (dirs j) (dirs j)) i).testBit (rows j)) :
    run setup m a=flip host (stockParity b) a := by
  have eq := fold_pair rows dirs a b rest actual stock
  have data : ∀ j, Active j→Data (flip host (stockParity a) a) j (dirs j) (rows j) := by
    intro j hj i hi; rw [at_other _ _ _ _ (site_ne hj hi)]; exact actual j hj i hi
  have cor := correction_run dirs rows (m.drop (measurementCount StairSchedule.paritySetup)) (flip host (stockParity a) a) valid data
  rw [setup,run_append,run_take,stock_flip,cor,flip_twice]
  change _=_
  simp only [delta] at *
  rw [←eq,←Bool.xor_assoc,Bool.xor_self,Bool.false_xor]
theorem host_matched (rows : Nat→Nat) (dirs : Nat→Bool) (a b : State) (m n : List Bool)
    (valid : ∀ j,Active j → rows j<63145)
    (rest : ∀i,Elsewhere i→a.basis (addr i)=b.basis (addr i)) (same : a.basis host=b.basis host)
    (actual : ∀j,Active j→Data a j (dirs j) (rows j))
    (stock : ∀j,Active j→∀i<16,b.basis (site j i)=(get (StairArchiveNativeCut.canonical (dirs j) (dirs j)) i).testBit (rows j)) :
    (run setup m a).basis host=(run StairSchedule.paritySetup n b).basis host := by
  rw [setup_pair rows dirs a b m valid rest actual stock,stock_flip,at_flip,at_flip,same]
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.Window45Dialog
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44PointMap
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires

private theorem swapComm (f : Wire → Wire) (inj : Function.Injective f) (a b : Wire)
    (fa : f a=a) (fb : f b=b) (q : Wire) :
    f (Equiv.swap a b q) = Equiv.swap a b (f q) := by
  by_cases ha : q=a
  · subst q; simp [fa,fb]
  by_cases hb : q=b
  · subst q; simp [fa,fb]
  have na : f q ≠ a := fun eq => ha (inj (eq.trans fa.symm))
  have nb : f q ≠ b := fun eq => hb (inj (eq.trans fb.symm))
  simp [Equiv.swap_apply_def,ha,hb,na,nb]

private theorem chainComm (f : Wire → Wire) (inj : Function.Injective f) (ps : List (Wire × Wire))
    (fixed : ∀ t ∈ ps, f t.1=t.1 ∧ f t.2=t.2) (q : Wire) : f (chain ps q) = chain ps (f q) := by
  induction ps generalizing q with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨a,b⟩ := t
    have h := fixed (a,b) List.mem_cons_self
    change f (chain ts (Equiv.swap a b q)) = chain ts (Equiv.swap a b (f q))
    rw [ih (fun z hz => fixed z (List.mem_cons_of_mem _ hz)),swapComm f inj a b h.1 h.2]

private theorem placed (f : Wire → Wire) (inj : Function.Injective f)
    (fixed : ∀ t ∈ earlyPairs, f t.1=t.1 ∧ f t.2=t.2) (P : Program) :
    encode (renameProgram f P) = renameProgram f (encode P) := by
  simp only [encode,renameProgram_comp]
  congr 1
  funext q
  exact (chainComm f inj earlyPairs fixed q).symm

private theorem borrowPlaced (cx cy : Fp) : encode (borrow cx cy)=StairPacket.WindowParityCaller.borrowGeneric cx cy := by
  unfold borrow block
  rw [placed _ (Equiv.swap _ _).injective (by decide +kernel),
    placed _ FlagTop.rho_injective (by decide +kernel)]
  have undo (P : Program) : encode (renameProgram outer.symm P)=P := by
    rw [encode,renameProgram_comp]
    have idMap : (outer : Wire → Wire) ∘ outer.symm = id := funext outer.apply_symm_apply
    rw [idMap]
    exact StairField2V3Win.renameProgram_id' P
  rw [logical,undo]
  rfl

private theorem app (P Q : Program) : encode (P++Q)=encode P++encode Q := by
  simp only [encode,renameProgram,List.map_append]

private theorem wrapperPlaced (C : Point) (cx cy : Fp) :
    encode (wrapper C cx cy)=renameProgram (Wrapper5.U layout) (StairPacket.WindowParityCaller.finite C cx cy) := by
  rw [wrapper,placed _ (Wrapper5.U _).injective (by decide +kernel)]
  congr 1
  simp only [finite,middle,StairPacket.WindowParityCaller.finite,app,borrowPlaced,List.append_assoc]

private theorem outerClean {b : Bool} {R : Point} {s : State} (h : encodes b R s.basis) :
    pullState outer s=s := by
  have high : ∀ t ∈ earlyPairs, 514 ≤ t.1 ∧ 514 ≤ t.2 := by decide +kernel
  exact (clean_chain earlyPairs id s s (fun ab hab =>
    ⟨h.2.2 _ (high ab hab).1,h.2.2 _ (high ab hab).2⟩)).mpr rfl

private theorem transport (P : BasisState → Prop) (phase : Bool) (a b : State)
    (eq : a=b) (hb : b.phase=phase ∧ P b.basis) : a.phase=phase ∧ P a.basis := eq ▸ hb

theorem correct (replay : GenericReplay) (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (StairPacket.WindowParityCaller.program C) (encodes b (if b then R+C else R)) := by
  intro s fresh hs
  cases C with
  | zero =>
    exact AboveFieldPointDevelop.program_correct_Q .zero b R s fresh hs
  | @some cx cy hc =>
    let C : Point := .some hc
    obtain ⟨old,eq⟩ := AboveFieldPointDevelop.LT11Final.Window45.routed_finite
      replay hc b R s fresh hs
    have spec := AboveFieldPointDevelop.program_correct_Q C b R s old hs
    let want := encodes b (if b then R+C else R)
    let reference := run (AboveFieldPointDevelop.wrapperBorrow C cx cy) old s
    change reference.phase=s.phase ∧ want reference.basis at spec
    have same := run_rename outer outer.injective (wrapper C cx cy) fresh s
    rw [outerClean hs,eq] at same
    change pullState outer (run (encode (wrapper C cx cy)) fresh s)=_ at same
    rw [wrapperPlaced] at same
    have strong := MappedCompressed.pullState_perm_injective outer
      (same.trans (outerClean spec.2).symm)
    let result := run (renameProgram (Wrapper5.U layout) (StairPacket.WindowParityCaller.finite C cx cy)) fresh s
    change result.phase=s.phase ∧ want result.basis
    exact transport want s.phase result reference strong spec

end ECDSAAdd.Entrant.Window45Dialog

namespace ECDSAAdd.Entrant.StairPacket.WindowPointCertificate
theorem certificate (replay : Window45Dialog.GenericReplay):
    Challenge.Certificate WindowParityRelease.entry WindowParityRelease.bounds:=
  WindowParityRelease.certificateOfSemantics (Window45Dialog.correct replay)
end ECDSAAdd.Entrant.StairPacket.WindowPointCertificate

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPointDivision
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXEntry FrontierEntry1591Callers Stair44PlacedHead
set_option maxHeartbeats 3500000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount fastConstAdd fusedY

def part (cx cy : Fp) := Stair44PlacedHead.routed (-cx) (-cy) ++ WindowParityCaller.divide

open Stair44PointDivision
theorem stage (Klaw:WindowKernelPrograms.Contracts) (cx cy X Y : Fp) (G : Bool) (s : State) (m : List Bool)
    (v : PointDialogValues layout X Y G s.basis s.basis) (hx : X+(if G then -cx else 0)≠0) :
    let e := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+(-cx).val) else false
    let u := run (part cx cy) m (pullState Stair44PointMap.outer.symm (put s (pkW layout) e))
    u.phase=s.phase ∧ PointDialogValues layout (X+(if G then -cx else 0))
      ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) G s.basis u.basis := by
  intro e u
  let P := reference (-cx) (-cy)
  let F := E1QubitPlacement.tickF layout
  let K := FrontierEntry1591Callers.entry WindowKernelPrograms.division layout
  let H := Stair44PlacedHead.routed (-cx) (-cy)
  let r := m.drop (measurementCount H)
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX layout layout_widths layout_nodup X Y G s.basis (-cx)
  have div := StairSemanticFinal.division_stepD WindowKernelPrograms.division Klaw.divSites
    Klaw.enter layout layout_widths layout_nodup config.1 above config.2.1 config.2.2
    (X+(if G then -cx else 0)) Y (-cy) G s.basis hx
  have joint := add.seq div
  have equiv : (fastConstAdd layout layout.point.x (-cx) ++ FrontierEntry1591Callers.division WindowKernelPrograms.division layout (-cy))=P++K := List.append_assoc _ _ _ |>.symm
  rw [equiv] at joint
  have ans := joint s (pfx (measurementCount P) [] ++ (pfx (measurementCount Stair44Splits.tick) [] ++ r)) v
  rw [run_pre,show K=Stair44Splits.tick++WindowParityCaller.divide from WindowKernelPrograms.div_split,run_pre,
    show Stair44Splits.tick=renameProgram Stair44PointMap.integerFirst F from rfl,
    encodedTick _ _ (prepClean (-cx) (-cy) X Y G s v)] at ans
  have tr := encoded_head X Y (-cx) (-cy) s (m.take (measurementCount H)) v.x v.y v.clean
  dsimp only at tr
  rw [standardHead cx cy X Y G s _ v] at tr
  have replay : u=run WindowParityCaller.divide r (pullState Stair44PointMap.integerFirst.symm (run F [] (run P [] s))) := by
    change run (H++WindowParityCaller.divide) m _=_
    rw [run_append]
    exact congrArg (run WindowParityCaller.divide r) tr
  rw [replay]
  exact ans

end ECDSAAdd.Entrant.StairPacket.WindowPointDivision

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPointSecond
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic
  Stair44PointMap Stair44PlacedHead
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount fastConstAdd

open Stair44PointSecond
def second (k cy cx : Fp) := Stair44Square.program k ++ WindowParityCaller.multiply cx.val ++ encodeY (exitYAll layout cy)

theorem productCut (H:WindowKernelPrograms.Contracts) (cx X Y : Fp) (G : Bool) (origin : BasisState) (w v : State) (rm : List Bool)
    (values : PointDialogValues layout X Y G origin w.basis) (hp : 0<X.val)
    (eq : v=pullState integerFirst.symm (run (E1QubitPlacement.tickF layout) [] w)) :
    let F := E1QubitPlacement.tickF layout
    let d := pfx (measurementCount F) [] ++ rm
    let a := run (FrontierEntry1591Callers.exit (kernelX cx.val) layout) d w
    run (WindowParityCaller.multiply cx.val) rm v=pullState outer.symm (put a (pkW layout) (G && decide (cx.val<X.val))) := by
  intro F d a
  have ww := WindowPointWord.fullWord H cx.val X.val Y.val cx.isLt hp X.isLt Y.isLt w d values.x values.y values.clean
  change run (FrontierEntry1591Callers.exit (WindowKernelPrograms.multiplication cx.val) layout) d w =
    pullState outer.symm (put a _ _) at ww
  rw [WindowKernelPrograms.mul_split] at ww
  have dt : d=pfx (measurementCount Stair44Splits.tick) [] ++ rm :=
    congrArg (fun z => pfx z [] ++ rm) (renameProgram_counts _ _).2.symm
  rw [dt,run_pre,show run Stair44Splits.tick [] w=pullState integerFirst.symm (run F [] w) from
    encodedTick w [] values.clean,←eq,values.generic,pk_wire] at ww
  exact ww

theorem actual (H:WindowKernelPrograms.Contracts) (k cy cx X Y : Fp) (G : Bool) (origin : BasisState) (s : State)
    (v : PointDialogValues layout X Y G origin s.basis)
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+(if G then k else 0)≠0)
    (m : List Bool) : ∃ n,run (second k cy cx) m s=pullState outer.symm (run (secondStageN layout k cy cx) n s) := by
  let square := Stair44Square.program k
  let mul := WindowParityCaller.multiply cx.val
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
    rw [←ep];exact productCut H cx X' Y G origin w _ rm vw hp realSquare
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

end ECDSAAdd.Entrant.StairPacket.WindowPointSecond

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowGeneric
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic
  Stair44PointMap Stair44PlacedHead
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount

theorem generic_eqD (K:WindowKernelPrograms.Contracts) (cx cy X Y : Fp) (G : Bool) (s : State) (e : Bool)
    (hv : PointDialogValues layout X Y G s.basis s.basis)
    (he : e=(if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+(-cx).val) else false))
    (hg : pkW layout≠layout.core.generic)
    (hx1 : X+(if G then -cx else 0)≠0)
    (hx2 : (X+(if G then -cx else 0))-
      (if G then ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0)))*
        ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) else 0)+
      (if G then (SquareCarryLoan719BF.K:Fp) else 0)+(if G then ReflectionE1.correction cx else 0)≠0)
    (m : List Bool) : ∃ m',run (WindowParityCaller.generic cx cy) m (pullState outer.symm (put s (pkW layout) e))=
      pullState outer.symm (run (genericN layout cx cy) m' (put s (pkW layout) e)) := by
  subst e
  let H := WindowPointDivision.part cx cy
  let H0 := (entryYAll layout (-cy) ++ entryXNew layout (pkW layout) (-cx)) ++ restEntry layout
  let flag := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+(-cx).val) else false
  let s0 := put s (pkW layout) flag
  let s1 := run H0 [] s0
  have hv0 := entryStageAll_step layout layout_widths layout_nodup X Y (-cx) (-cy) G s.basis hx1
    s (padE layout cy cx []) hv
  rw [←(head_pad layout layout_widths layout_nodup cx cy X Y s hv.x hv.y hv.clean hg).run_eq []] at hv0
  have hv1 := WindowPointDivision.stage K cx cy X Y G s (m.take (measurementCount H)) hv hx1
  have eq : run H (m.take (measurementCount H)) (pullState outer.symm s0)=s1 :=
    StairCallerEntry.state_eq_of_values hv1 hv0
  obtain ⟨n,hn⟩ := WindowPointSecond.actual K (ReflectionE1.correction cx) cy cx _ _ G s.basis s1
    hv0.2 hx2 (m.drop (measurementCount H))
  refine ⟨pfx (measurementCount H0) []++n,?_⟩
  have structureEq : WindowParityCaller.generic cx cy=H++WindowPointSecond.second (ReflectionE1.correction cx) cy cx := by
    simp only [H,WindowPointDivision.part,WindowPointSecond.second,WindowParityCaller.generic,Stair44PlacedHead.routed,List.append_assoc]
  rw [structureEq,run_append,eq,genericN,run_pre]
  exact hn

theorem certificate (K:WindowKernelPrograms.Contracts):Challenge.Certificate WindowParityRelease.entry WindowParityRelease.bounds:=
  WindowPointCertificate.certificate (generic_eqD K)
end ECDSAAdd.Entrant.StairPacket.WindowGeneric

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify WindowParityDirty FrontierEntry1591Field
open StockArchiveBanks ArchiveStockSuffix ExteriorPorts WindowFieldMask
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
private theorem ids {j : Nat} (h : Active j) : j∈bankIds := by
  rcases h with h|h|h <;> simp [h,bankIds]
private theorem alive (b : Bank) : Active (groupId b) := by
  revert b; unfold Active; decide +kernel
private def offset (w : Wire) :=
  let q := OB5.sig 511 w-16
  let side := decide (1028 ≤ q)
  let v := if side then q-1028 else q
  let i := 2*(v%5)+side.toNat
  8*(v/5)+(if i<5 then i else i-1)
private theorem offset_all : ∀i:Fin 816, offset (addr i)=i.val := by decide +kernel
private theorem addr_inj {a b : Nat} (ha : a<816) (hb : b<816) (eq : addr a=addr b) : a=b :=
  (offset_all ⟨a,ha⟩).symm.trans ((congrArg offset eq).trans (offset_all ⟨b,hb⟩))
private theorem not_inside (i : Nat) (hi : Elsewhere i) : addr i∉archives := by
  intro h
  obtain ⟨b,q,e⟩ := StockPlacedWindow.bank_rep _ h
  have eq : addr (8*groupId b+q.val)=addr i := (native_ports b q).trans e
  have bb := b.isLt
  have qq := q.isLt
  unfold Elsewhere at hi
  have k := addr_inj (a:=8*groupId b+q.val) (b:=i) (by unfold groupId;omega) (by omega) eq
  unfold groupId at k
  omega
private theorem host_outside : host∉archives := by
  intro h
  obtain ⟨b,i,e⟩ := StockPlacedWindow.bank_rep _ h
  exact site_ne (alive b) i.isLt ((native_ports b i).trans e)
theorem setup_through {d x a b rows} (pair : Paired d x a b rows) (m n : List Bool) :
    Paired d x (run setup m a) (run StairSchedule.paritySetup n b) rows := by
  let rr := fieldRows rows
  have rb (j : Nat) (hj : Active j) : rr j<63145 := by
    obtain ⟨v,rfl⟩ := idAt j (ids hj)
    rw [show rr (groupId v)=rows v from rowsAt rows v]
    exact (pair.labels _).1
  have cs (j : Nat) (hj : Active j) : Data a j d (rr j) := by
    obtain ⟨v,rfl⟩ := idAt j (ids hj)
    intro i hi
    let t : Fin 16 := ⟨i,hi⟩
    rw [show site (groupId v) i=siteAt v t from native_ports v t,show rr (groupId v)=rows v from rowsAt rows v]
    exact pair.custom v t
  have bs (j : Nat) (hj : Active j) : ∀i<16,b.basis (site j i)=(get (StairArchiveNativeCut.canonical d d) i).testBit (rr j) := by
    obtain ⟨v,rfl⟩ := idAt j (ids hj)
    intro i hi
    let t : Fin 16 := ⟨i,hi⟩
    rw [show site (groupId v) i=siteAt v t from native_ports v t,show rr (groupId v)=rows v from rowsAt rows v]
    exact pair.stock v t
  have eff := setup_pair rr (fun _=>d) a b m rb (fun i hi=>pair.equality.2 _ (not_inside i hi)) cs bs
  rw [eff,show run StairSchedule.paritySetup n b=flip host (stockParity b) b from
    ParityHost5.setup_run controls host b n host_not_controls]
  refine ⟨⟨pair.equality.1,?_⟩,pair.labels,?_,?_⟩
  · intro q h; by_cases e:q=host
    · subst q; simp only [at_flip,pair.equality.2 host host_outside]
    · rw [at_other _ _ _ _ e,at_other _ _ _ _ e]; exact pair.equality.2 q h
  · intro v i
    have ne : siteAt v i≠host := fun h=>site_ne (alive v) i.isLt ((native_ports v i).trans h)
    exact (at_other a (siteAt v i) host _ ne).trans (pair.custom v i)
  · intro v i
    have ne : siteAt v i≠host := fun h=>site_ne (alive v) i.isLt ((native_ports v i).trans h)
    exact (at_other b (siteAt v i) host _ ne).trans (pair.stock v i)
end ECDSAAdd.Entrant.StairPacket.WindowFieldParity

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowReleaseProof
open Arithmetic MappedCompressed Secp256k1 StairSemanticFinal StairConcreteAssembly Rolling1588Lifetime
set_option maxRecDepth 17000
set_option maxHeartbeats 3500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires renameProgram
theorem division (g:wires (WindowParityCaller.entryFieldHosted checkpointPrimitives)⊆callerDomain):
    wires WindowKernelPrograms.division⊆callerDomain:=by
  have original:=Stair44CallerSupport.division
  have f:=phaseHost_caller _ (WindowIntegerSites.forward true 154 (by decide))
  have b:=phaseHost_caller _ (WindowIntegerSites.backward false 235 (by decide))
  simp only [WindowKernelPrograms.division,WindowKernelPrograms.divBefore,WindowKernelPrograms.divAfter,
    WindowKernelPrograms.openWalk,Stair44Kernel.division,Stair44Kernel.divLead,Stair44Kernel.openR,
    Stair44DivTerm.routedClose,Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,
    Six505.rename_append,wires_append,Finset.union_subset_iff] at original ⊢
  tauto
theorem multiplication (k:Nat) (g:wires (WindowParityCaller.exitFieldHosted checkpointPrimitives)⊆callerDomain):
    wires (WindowKernelPrograms.multiplication k)⊆callerDomain:=by
  have original:=Stair44CallerSupport.multiplication k
  have f:=phaseHost_caller _ (WindowIntegerSites.forward false 234 (by decide))
  have b:=phaseHost_caller _ (WindowIntegerSites.backward true 154 (by decide))
  simp only [WindowKernelPrograms.multiplication,WindowKernelPrograms.mulBefore,WindowKernelPrograms.mulAfter,
    WindowKernelPrograms.openWalk,Stair44Kernel.multiplication,Stair44Kernel.beforeX,Stair44Kernel.mulLead,Stair44Kernel.openR,
    Stair44Kernel.mulRawTail,Stair44Kernel.finishM,Stair44Outer.forwardEnd,
    Six505.rename_append,wires_append,Finset.union_subset_iff] at original ⊢
  tauto

theorem certificate (enter:WindowMiddleContract.entry) (leave:WindowMiddleContract.exit):
    Challenge.Certificate WindowParityRelease.entry WindowParityRelease.bounds:=
  WindowGeneric.certificate ⟨division ExteriorCaller.entryFieldHosted_corrected,fun k=>multiplication k ExteriorCaller.exitFieldHosted_corrected,
    WindowKernelReplay.division_correct enter,WindowKernelReplay.multiplication_eq leave⟩
end ECDSAAdd.Entrant.StairPacket.WindowReleaseProof

end

