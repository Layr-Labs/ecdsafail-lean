import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Submission.Entrant.CRT
import ECDSAAdd.Submission.Entrant.FredCut
import ECDSAAdd.Submission.Entrant.OddField
import ECDSAAdd.Submission.Entrant.OddFieldC
import ECDSAAdd.Framework.Syntax
import ECDSAAdd.Framework.Semantics
import ECDSAAdd.Framework.RecordedPaths
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Submission.Entrant.MainP2
import ECDSAAdd.Submission.Entrant.TickCut


-- ===== RouteAResourcePhysical =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic BalancedCircuit BalancedField MappedCompressed Challenge Baselines RecordedQuantum
attribute [local irreducible] GatePhysical P1Life.half P1Life.dstart P1Life.dend P1Life.mend
attribute [local irreducible] JointForward1588.paddedGD JointInverse1588.paddedD


namespace Rolling1588
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] cell cellWith groups placedFirstPacket entryField exitField entryTail exitHead


theorem route_body_physical (divide : Bool) :
    GatePhysical (P1Life.half (base 760) divide base (base 2409)) :=
  (P1Life.half_resources _ _ _ _ half_ports_nodup route_retired_member).1


theorem route_junction_physical :
    GatePhysical (P1Life.dstart (base 760) base (base 2409)) ∧
    GatePhysical (P1Life.dend (base 760) base (base 2409)) ∧
    GatePhysical (P1Life.mend (base 760) base (base 2409)) :=
  ⟨(P1Life.dstart_resources _ _ _ half_ports_nodup route_retired_member).1,
   (P1Life.dend_resources _ _ _ half_ports_nodup route_retired_member).1,
   (P1Life.mend_resources _ _ _ half_ports_nodup route_retired_member).1⟩


theorem route_selected_physical (source flag : Wire) (P : Program)
    (away : source≠flag) (physical : GatePhysical P) : GatePhysical (SW.selW source flag P) := by
  have first : GatePhysical [.CX source flag] := by simp [GatePhysical,PhysicalInstr,ProperGate,away]
  have last : GatePhysical [.measureX flag [] [.Z source]] := by simp [GatePhysical,PhysicalInstr]
  simpa only [SW.selW,gatePhysical_append] using And.intro (And.intro first physical) last


theorem route_swap_physical : GatePhysical FrontierSW1591.swapBody := by
  rw [FrontierSW1591.swapBody]
  exact swapRegisters_physical _ _ _ FrontierReplay1591.base_sign_nd


theorem halfWindowWith_physical (P : Program) (hp : GatePhysical P)
    (j active hole : Nat) (hj : j<102) (ha : active<6) : GatePhysical (halfWindowWith P j active hole) := by
  apply ControlLoan1589.loanWindow_physical
  · exact HostOB5.host_ne _ _ (by first | omega | exact True.intro)
  · exact gatePhysical_rename _ (Equiv.swap (base 719) (s j hole)).injective _ hp


theorem cellWith_physical (divide : Bool) (P : Program) (hp : GatePhysical P)
    (j active hole : Nat) (hj : j<102) (ha : active<5) : GatePhysical (cellWith divide P j active hole) := by
  have half := halfWindowWith_physical P hp j active hole hj (by first | omega | exact True.intro)
  have swap := route_selected_physical (s j active) (base 2409) FrontierSW1591.swapBody
    (HostOB5.host_ne _ _ (by first | omega | exact True.intro)) route_swap_physical
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  · exact ⟨swap,half⟩
  · exact ⟨half,swap⟩


theorem cell_physical (divide : Bool) (j active hole : Nat) (hj : j<102) (ha : active<5) :
    GatePhysical (cell divide j active hole) := by
  have a := cellWith_physical divide _ (route_body_physical divide) j active hole hj ha
  cases divide <;> simpa only [cell,cellWith,halfWindow] using a


theorem onPacket_physical (j : Nat) (hj : j<102) (P : Program)
    (support : wires P⊆Finset.range 10) (physical : GatePhysical P) : GatePhysical (onPacket j P) :=
  gatePhysical_rename_support _ P
    (fun a ha b hb eq => FirstNonzeroCodec.label_inj'
      (History5.historyMap base (5*j))
      (History5.historyMap_injective base base_pool_nodup (5*j) (by first | omega | exact True.intro))
      a (support ha) b (support hb) eq) physical


theorem stage_physical : GatePhysical stageOpen ∧ GatePhysical stageClose ∧
    ∀divide k,k<2→GatePhysical (stageTransition divide k) := by
  refine ⟨?_,?_,?_⟩
  · apply physicalGateCheck_correct
    decide +kernel
  · apply physicalGateCheck_correct
    decide +kernel
  · intro divide k hk
    apply physicalGateCheck_correct
    cases divide <;> interval_cases k <;> decide +kernel


theorem basePacket_physical (divide : Bool) (j : Nat) (hj : j<102) :
    GatePhysical (basePacket divide j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_physical j hj (stageTransition d k) (stageTransition_support d k hk)
      (stage_physical.2.2 d k hk)
  have cellAt (k : Nat) (hk : k<5) := cell_physical divide j k 2 hj hk
  have junction := cellWith_physical true _ route_junction_physical.2.1 j 4 2 hj (by decide)
  cases divide <;> simp only [basePacket,Bool.false_eq_true,if_false,if_true,gatePhysical_append]
  all_goals try split_ifs
  all_goals repeat' apply And.intro
  all_goals first
    | exact junction
    | exact opening
    | exact closing
    | exact transfer false 0 (by decide)
    | exact transfer false 1 (by decide)
    | exact transfer true 0 (by decide)
    | exact transfer true 1 (by decide)
    | exact cellAt 3 (by decide)
    | exact cellAt 4 (by decide)


theorem packet_physical (divide : Bool) (j : Nat) (hj : j<102) :
    GatePhysical (packet divide j) :=
  gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ (basePacket_physical divide j hj)


section
attribute [local irreducible] SW.selW FrontierSW1591.swapBody
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.triple
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.e3 ECDSAAdd.Entrant.Rolling1588.d3
attribute [local irreducible] ECDSAAdd.Entrant.Rolling1588.e3short ECDSAAdd.Entrant.Rolling1588.d3short


end


end Rolling1588
end ECDSAAdd.Entrant.RouteA
end -- ticket 8 pasted module

-- ===== RouteAResourceSupportCore =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Secp256k1 BalancedField OffsetBorrowedCanonical DirectSkywalk Challenge RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] wires run
attribute [local irreducible] cell cellWith halfWindowWith groups placedFirstPacket
attribute [local irreducible] P1Life.half P1Life.dstart P1Life.dend P1Life.mend
attribute [local irreducible] ControlLoan1589.cell ControlLoan1589.halfWindow ControlLoan1589.groups








theorem rename_sub (f : Wire→Wire) (P Q : Program) (sub : wires P⊆wires Q) :
    wires (renameProgram f P)⊆wires (renameProgram f Q) := by
  rw [renameProgram_support,renameProgram_support]
  exact Finset.image_mono f sub


theorem append_extra (P Q P0 Q0 : Program) (extra : Wire)
    (hp : wires P⊆wires P0∪{extra}) (hq : wires Q⊆wires Q0∪{extra}) :
    wires (P++Q)⊆wires (P0++Q0)∪{extra} := by
  simp only [wires_append] at hp hq ⊢
  intro q used
  rcases Finset.mem_union.mp used with used|used
  · rcases Finset.mem_union.mp (hp used) with old|fresh
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ old)
    · exact Finset.mem_union_right _ fresh
  · rcases Finset.mem_union.mp (hq used) with old|fresh
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ old)
    · exact Finset.mem_union_right _ fresh


theorem rename_extra (f : Wire→Wire) (P Q : Program) (extra : Wire)
    (fixed : f extra=extra) (sub : wires P⊆wires Q∪{extra}) :
    wires (renameProgram f P)⊆wires (renameProgram f Q)∪{extra} := by
  rw [renameProgram_support,renameProgram_support]
  intro q used
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp used
  rcases Finset.mem_union.mp (sub ha) with old|fresh
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,old,rfl⟩)
  · have eq := Finset.mem_singleton.mp fresh
    subst a
    exact Finset.mem_union_right _ (Finset.mem_singleton.mpr fixed)


theorem rebind_support (a b : Wire) (P : Program) (off : b∉wires P) :
    wires (renameProgram (Equiv.swap a b) P)⊆wires P∪{b} := by
  rw [renameProgram_support]
  intro q used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  by_cases left : i=a
  · subst i
    exact Finset.mem_union_right _ (by simp)
  have right : i≠b := fun eq => off (eq ▸ hi)
  rw [Equiv.swap_apply_of_ne_of_ne left right]
  exact Finset.mem_union_left _ hi


theorem halfWindowWith_extra (P : Program) (support : HalfSupport P) (divide : Bool) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) :
    wires (halfWindowWith P j active hole)⊆
      wires (ControlLoan1589.halfWindow divide j (g j active))∪{s j hole} := by
  let Old := Q6EndpointCell.half divide base (base 2409)
  let F := P
  have off : s j hole∉wires F :=
    body_history_free P support _ (Or.inr ⟨by first | omega | exact True.intro,by first | omega | exact True.intro⟩)
  have fixed : Equiv.swap (packetCarry j) (g j active) (s j hole)=s j hole :=
    Equiv.swap_apply_of_ne_of_ne (HostOB5.host_ne _ _ (by first | omega | exact True.intro))
      (HostOB5.host_ne _ _ (by first | omega | exact True.intro))
  have mid := rename_extra (Equiv.swap (packetCarry j) (g j active))
    (renameProgram (Equiv.swap (base 719) (s j hole)) F) Old (s j hole) fixed
    ((rebind_support (base 719) (s j hole) F off).trans
      (Finset.union_subset_union (body_sub_old P support divide) (Finset.Subset.refl _)))
  have first := append_extra
    [.CX (g j active) (base 2409),.CX (base 2409) (g j active)] _
    [.CX (g j active) (base 2409),.CX (base 2409) (g j active)] _ (s j hole)
    Finset.subset_union_left mid
  have all := append_extra _ [.CX (base 2409) (g j active),
      .measureX (base 2409) [] [.Z (g j active)]]
    _ [.CX (base 2409) (g j active),.measureX (base 2409) [] [.Z (g j active)]]
    (s j hole) first Finset.subset_union_left
  simpa only [halfWindowWith,ControlLoan1589.halfWindow,ControlLoan1589.loanWindow,
    ControlLoan1589.packetCarry,packetCarry,F,Old] using all


theorem old_cell_parts (divide : Bool) (j active : Nat) (W : Finset Wire)
    (sub : wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W) :
    wires (ControlLoan1589.halfWindow divide j (g j active))⊆W ∧
      wires (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody)⊆W := by
  cases divide <;> simp only [ControlLoan1589.cell,Bool.false_eq_true,if_false,if_true,
    wires_append,Finset.union_subset_iff] at sub ⊢
  · exact sub.symm
  · exact sub


theorem history_controls (j k : Nat) (hk : k<5) :
    g j k∈wires (NewHistory5.encode base (5*j)) ∧
      s j k∈wires (NewHistory5.encode base (5*j)) := by
  simpa only [g,s,NewHistory5.encode_support_eq] using Replay5.history_controls (5*j) k hk


theorem cellWith_support_into (P : Program) (support : HalfSupport P) (divide : Bool) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) (W : Finset Wire)
    (old : wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W)
    (history : wires (NewHistory5.encode base (5*j))⊆W) :
    wires (cellWith divide P j active hole)⊆W := by
  have parts := old_cell_parts divide j active W old
  have half : wires (halfWindowWith P j active hole)⊆W := by
    intro q used
    rcases Finset.mem_union.mp (halfWindowWith_extra P support divide j active hole hj ha hh used) with old|fresh
    · exact parts.1 old
    · have eq := Finset.mem_singleton.mp fresh
      subst q
      exact history (history_controls j hole hh).2
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff]
  · exact ⟨parts.2,half⟩
  · exact ⟨half,parts.2⟩


theorem cell_support_into (divide : Bool) (j active hole : Nat)
    (hj : j<102) (ha : active<5) (hh : hole<5) (W : Finset Wire)
    (old : wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W)
    (history : wires (NewHistory5.encode base (5*j))⊆W) : wires (cell divide j active hole)⊆W := by
  have h := cellWith_support_into _ (half_support divide) divide j active hole hj ha hh W old history
  cases divide <;> simpa only [cell,cellWith,halfWindow] using h


theorem rawReplay_member (divide : Bool) (j : Nat)
    (letters : List MixedTranscriptLetter) (l : MixedTranscriptLetter) (member : l∈letters) :
    wires (ControlLoan1589.cell divide j l.1.1 l.1.2)⊆
      wires (ControlLoan1589.rawReplay divide j letters) := by
  induction letters with
  | nil => simp at member
  | cons head rest ih =>
    cases divide <;> simp only [ControlLoan1589.rawReplay,Bool.false_eq_true,if_false,if_true,wires_append]
    all_goals rcases List.mem_cons.mp member with rfl|member
    · exact Finset.subset_union_right
    · exact (ih member).trans Finset.subset_union_left
    · exact Finset.subset_union_left
    · exact (ih member).trans Finset.subset_union_right


theorem rawReplay_cell_at (divide : Bool) (j active : Nat)
    (hj : j<102) (ha : active<5) (letters : List MixedTranscriptLetter)
    (member : tapeLetter (5*j+active)∈letters) :
    wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆
      wires (ControlLoan1589.rawReplay divide j letters) := by
  have sub := rawReplay_member divide j letters _ member
  have tape := mixedTape_base_getD (5*j+active) (by first | omega | exact True.intro)
  simpa only [tapeLetter,tape,g,s,Nat.add_assoc] using sub


theorem onPacket_support_into (j : Nat) (P : Program)
    (support : wires P⊆Finset.range 10) (W : Finset Wire)
    (history : wires (NewHistory5.encode base (5*j))⊆W) :
    wires (onPacket j P)⊆W := by
  rw [onPacket,renameProgram_support]
  intro q used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  have bound := Finset.mem_range.mp (support hi)
  simpa only [MeasuredCodec5.label,dif_pos bound] using
    history (NewHistory5.history_site_mem base (5*j) ⟨i,bound⟩)


theorem basePacket_old_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (basePacket divide j)⊆wires (ControlLoan1589.basePacket divide j) := by
  let W := wires (ControlLoan1589.basePacket divide j)
  have history : wires (NewHistory5.encode base (5*j))⊆W := by
    simp only [W,ControlLoan1589.basePacket,wires_append]
    exact Finset.subset_union_right
  have old (active : Nat) (ha : active<5) :
      wires (ControlLoan1589.cell divide j (g j active) (s j active))⊆W := by
    have member : tapeLetter (5*j+active)∈Replay5.letters j :=
      List.mem_map.mpr ⟨active,List.mem_range.mpr ha,rfl⟩
    have sub := rawReplay_cell_at divide j active hj ha _ member
    exact sub.trans (by
      simp only [W,ControlLoan1589.basePacket,wires_append]
      exact Finset.subset_union_right.trans Finset.subset_union_left)
  have cellAt (active : Nat) (ha : active<5) :=
    cell_support_into divide j active 2 hj ha (by decide) W (old active ha) history
  have opening := onPacket_support_into j stageOpen stageOpen_support W history
  have closing := onPacket_support_into j stageClose stageClose_support W history
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_support_into j (stageTransition d k) (stageTransition_support d k hk) W history
  have junction : divide=true → wires (cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2)⊆W := by
    intro eq
    subst divide
    exact cellWith_support_into _ dend_support true j 4 2 hj (by decide) (by decide) W (old 4 (by decide)) history
  cases divide <;> simp only [basePacket,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff]
  all_goals try split_ifs
  all_goals repeat' apply And.intro
  all_goals first
    | exact junction rfl
    | exact opening
    | exact closing
    | exact transfer false 0 (by decide)
    | exact transfer false 1 (by decide)
    | exact transfer true 0 (by decide)
    | exact transfer true 1 (by decide)
    | exact cellAt 3 (by decide)
    | exact cellAt 4 (by decide)


theorem packet_old_support (divide : Bool) (j : Nat) (hj : j<102) :
    wires (packet divide j)⊆wires (ControlLoan1589.packet divide j) :=
  rename_sub _ _ _ (basePacket_old_support divide j hj)


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAResourceCounts =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit BalancedField MappedCompressed
open ECDSAAdd.Entrant.Rolling1588
open Rolling1588Lifetime
attribute [local irreducible] toffoliCount measurementCount


theorem route_retired_count_member : base 760∈(Q6EndpointCell.ports base (base 2409)).carry.take 254 :=
  List.mem_of_mem_drop route_retired_member


theorem route_selected_counts (source flag : Wire) (P : Program) :
    toffoliCount (SW.selW source flag P)=toffoliCount P ∧
    measurementCount (SW.selW source flag P)=measurementCount P+1 := by
  simp only [SW.selW,toffoliCount_append,measurementCount_append,toffoliCount,measurementCount]
  exact ⟨by omega,by omega⟩


theorem halfWindowWith_counts (P : Program) (j active hole : Nat) :
    toffoliCount (halfWindowWith P j active hole)=toffoliCount P ∧
    measurementCount (halfWindowWith P j active hole)=measurementCount P+1 := by
  have a := ControlLoan1589.loanWindow_counts (g j active) (base 2409) (packetCarry j)
    (renameProgram (Equiv.swap (base 719) (s j hole)) P)
  have b := route_selected_counts (g j active) (base 2409)
    (renameProgram (Equiv.swap (base 719) (s j hole)) P)
  simp only [renameProgram_counts] at b
  exact ⟨a.1.trans b.1,a.2.trans b.2⟩


theorem route_swap_counts : toffoliCount FrontierSW1591.swapBody=256 ∧
    measurementCount FrontierSW1591.swapBody=0 := by
  have a := ECDSAAdd.Entrant.Rolling1588.cell_resources true 0 3 2
  have b := ECDSAAdd.Entrant.Rolling1588.halfWindow_counts true 0 3 2
  have c := route_selected_counts (s 0 3) (base 2409) FrontierSW1591.swapBody
  simp only [ECDSAAdd.Entrant.Rolling1588.cell,if_true,toffoliCount_append,measurementCount_append] at a
  exact ⟨by omega,by omega⟩


theorem cellWith_counts (divide : Bool) (P : Program) (j active hole : Nat) :
    toffoliCount (cellWith divide P j active hole)=toffoliCount P+256 ∧
    measurementCount (cellWith divide P j active hole)=measurementCount P+2 := by
  have a := halfWindowWith_counts P j active hole
  have b := route_selected_counts (s j active) (base 2409) FrontierSW1591.swapBody
  rw [route_swap_counts.1,route_swap_counts.2] at b
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,
    toffoliCount_append,measurementCount_append] <;> exact ⟨by omega,by omega⟩


theorem cell_counts (divide : Bool) (j active hole : Nat) :
    toffoliCount (cell divide j active hole)=1273 ∧
    measurementCount (cell divide j active hole)=1019 := by
  have a := cellWith_counts divide (P1Life.half (base 760) divide base (base 2409)) j active hole
  have b := P1Life.half_counts (base 760) divide base (base 2409)
  have shape : cell divide j active hole=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j active hole := by
    cases divide <;> rfl
  rw [shape]
  exact ⟨by omega,by omega⟩


theorem route_junction_counts :
    toffoliCount (P1Life.dstart (base 760) base (base 2409))=1271 ∧
    measurementCount (P1Life.dstart (base 760) base (base 2409))=1271 ∧
    toffoliCount (P1Life.dend (base 760) base (base 2409))=1274 ∧
    measurementCount (P1Life.dend (base 760) base (base 2409))=1274 ∧
    toffoliCount (P1Life.mend (base 760) base (base 2409))=1271 ∧
    measurementCount (P1Life.mend (base 760) base (base 2409))=1271 := by
  have a := P1Life.dstart_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member
  have b := P1Life.dend_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member
  have c := P1Life.mend_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member
  exact ⟨a.1,a.2,b.1,b.2,c.1,c.2⟩


theorem cell_count_delta (divide : Bool) (j active hole : Nat) :
    toffoliCount (cell divide j active hole)+3=toffoliCount (ECDSAAdd.Entrant.Rolling1588.cell divide j active hole) ∧
    measurementCount (cell divide j active hole)+4=measurementCount (ECDSAAdd.Entrant.Rolling1588.cell divide j active hole) := by
  have a := cell_counts divide j active hole
  have b := ECDSAAdd.Entrant.Rolling1588.cell_resources divide j active hole
  exact ⟨by omega,by omega⟩


theorem packet_count_delta (divide : Bool) (j : Nat) :
    toffoliCount (packet divide j)+15=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet divide j)+(if divide && decide (j=84) then 257 else 0) ∧
    measurementCount (packet divide j)+20=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet divide j)+(if divide && decide (j=84) then 257 else 0) := by
  have a := cell_count_delta divide j 3 2
  have b := cell_count_delta divide j 4 2
  have c := cellWith_counts true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := route_junction_counts
  have e := cell_counts true j 4 2
  simp only [packet,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts]
  cases divide <;> by_cases last : j=84
  all_goals simp only [basePacket,ECDSAAdd.Entrant.Rolling1588.basePacket,
    Bool.false_eq_true,if_false,if_true,Bool.false_and,Bool.true_and,
    toffoliCount_append,measurementCount_append]
  all_goals try simp only [last,decide_true,decide_false,Bool.false_eq_true,if_true,if_false] at *
  all_goals try split_ifs at *
  all_goals exact ⟨by omega,by omega⟩


theorem groups_count_delta (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    toffoliCount (groups divide j n)+15*n=
      toffoliCount (ECDSAAdd.Entrant.Rolling1588.groups divide j n)+(if divide && decide (j≤84 ∧ 84<j+n) then 257 else 0) ∧
    measurementCount (groups divide j n)+20*n=
      measurementCount (ECDSAAdd.Entrant.Rolling1588.groups divide j n)+(if divide && decide (j≤84 ∧ 84<j+n) then 257 else 0) := by
  induction n generalizing j with
  | zero => simp [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,toffoliCount,measurementCount]
  | succ n ih =>
    have head := packet_count_delta divide j
    have tail := ih (j+1) (by omega)
    cases divide
    · simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        Bool.false_eq_true,if_false,toffoliCount_append,measurementCount_append,
        Bool.false_and] at head tail ⊢
      exact ⟨by omega,by omega⟩
    · have indicator : (if j=84 then 257 else 0)+(if j+1≤84 ∧ 84<j+1+n then 257 else 0)=
          (if j≤84 ∧ 84<j+(n+1) then 257 else 0) := by split_ifs <;> omega
      simp only [Bool.true_and,decide_eq_true_eq] at head tail ⊢
      simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        if_true,toffoliCount_append,measurementCount_append] at tail ⊢
      exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module

-- ===== RouteAFieldSlotDeltas =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed BalancedCircuit BalancedField Challenge Baselines
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] gateSlots


def halfSlotSaving (divide : Bool) : Nat := if divide then 34 else 28


theorem halfWindowWith_slots (P : Program) (j active hole : Nat) :
    gateSlots (halfWindowWith P j active hole)=gateSlots P+5 := by
  rw [halfWindowWith,ControlLoan1589.loanWindow_slots,SW.selW_slots,rename_gateSlots]


theorem cellWith_slots (divide : Bool) (P : Program) (j active hole : Nat) :
    gateSlots (cellWith divide P j active hole)=gateSlots P+776 := by
  have half := halfWindowWith_slots P j active hole
  have sw : gateSlots (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody)=771 := by
    rw [SW.selW_slots,FrontierSW1591.swapBody,swapRegisters_gateSlots,
      balancedSharedPorts_r,balancedSharedPorts_y,wireBlock_length,wireBlock_length]
    decide
  cases divide <;> simp only [cellWith,Bool.false_eq_true,if_false,if_true,gateSlots_append,half,sw] <;> omega


theorem cell_slot_delta (divide : Bool) (j active hole : Nat) :
    gateSlots (cell divide j active hole)+halfSlotSaving divide=
      gateSlots (ECDSAAdd.Entrant.Rolling1588.cell divide j active hole) := by
  have a := cellWith_slots divide (P1Life.half (base 760) divide base (base 2409)) j active hole
  have b := slot_half (base 760) divide base (base 2409)
  have c := ECDSAAdd.Entrant.Rolling1588.halfWindow_slots divide j active hole
  have old := slot_record_half divide
  have r := R2Life760.half760_slots divide
  have sw : gateSlots (SW.selW (s j active) (base 2409) FrontierSW1591.swapBody)=771 := by
    rw [SW.selW_slots,FrontierSW1591.swapBody,swapRegisters_gateSlots,
      balancedSharedPorts_r,balancedSharedPorts_y,wireBlock_length,wireBlock_length]
    decide
  have shape : cell divide j active hole=cellWith divide (P1Life.half (base 760) divide base (base 2409)) j active hole := by cases divide <;> rfl
  rw [shape,a]
  cases divide <;> simp only [halfSlotSaving,halfExtra,Bool.false_eq_true,if_false,if_true,
    ECDSAAdd.Entrant.Rolling1588.cell,gateSlots_append,sw] at old r c b ⊢
  all_goals first | omega | exact True.intro


theorem packet_slot_delta (divide : Bool) (j : Nat) :
    gateSlots (packet divide j)+5*halfSlotSaving divide=
      gateSlots (ECDSAAdd.Entrant.Rolling1588.packet divide j)+(if divide && decide (j=84) then 3877 else 0) := by
  have a := cell_slot_delta divide j 3 2
  have b := cell_slot_delta divide j 4 2
  have c := cellWith_slots true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) true base (base 2409)
  have regular := cellWith_slots true (P1Life.half (base 760) true base (base 2409)) j 4 2
  have eq : cell true j 4 2=cellWith true (P1Life.half (base 760) true base (base 2409)) j 4 2 := rfl
  rw [←eq] at regular
  simp only [packet,ECDSAAdd.Entrant.Rolling1588.packet,rename_gateSlots]
  cases divide <;> by_cases last : j=84
  all_goals simp only [basePacket,ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,
    if_false,if_true,Bool.false_and,Bool.true_and,gateSlots_append]
  all_goals try simp only [last,decide_true,decide_false,Bool.false_eq_true,if_true,if_false] at *
  all_goals first | omega | exact True.intro


theorem groups_slot_delta (divide : Bool) (j n : Nat) (bound : j+n≤102) :
    gateSlots (groups divide j n)+5*halfSlotSaving divide*n=
      gateSlots (ECDSAAdd.Entrant.Rolling1588.groups divide j n)+(if divide && decide (j≤84 ∧ 84<j+n) then 3877 else 0) := by
  induction n generalizing j with
  | zero => simp [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,gateSlots]
  | succ n ih =>
    have head := packet_slot_delta divide j
    have tail := ih (j+1) (by first | omega | exact True.intro)
    cases divide
    · simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        Bool.false_eq_true,if_false,gateSlots_append,Bool.false_and,halfSlotSaving] at head tail ⊢
      first | omega | exact True.intro
    · have indicator : (if j=84 then 3877 else 0)+(if j+1≤84 ∧ 84<j+1+n then 3877 else 0)=
          (if j≤84 ∧ 84<j+(n+1) then 3877 else 0) := by split_ifs <;> omega
      simp only [Bool.true_and,decide_eq_true_eq,halfSlotSaving,if_true] at head tail ⊢
      simp only [groups,ECDSAAdd.Entrant.Rolling1588.groups,PacketSequence.program,
        if_true,gateSlots_append] at tail ⊢
      first | omega | exact True.intro


end ECDSAAdd.Entrant.RouteA.Rolling1588
end -- ticket 8 pasted module


-- ===== RouteAOddPrefix (M1a: odd division slice, packets 1..84) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

/-- Division packet `j` whose first division cell runs `dstart` (standard words in, odd words out);
the other four cells are ordinary odd halves. -/
def dstartBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cellWith true (P1Life.dstart (base 760) base (base 2409)) j 3 2 ++ cell true j 4 2 ++ onPacket j bridge7 ++
      cell true j 4 2 ++ cell true j 3 2 ++ onPacket j bridge5 ++ cell true j 4 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def dstartPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (dstartBasePacket j)

theorem dstartBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j))) origin X Y)
      (dstartBasePacket j)
      (fun state => let V := regularPayload true j origin (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen)
      (CodeFrame centerWord centerWord (stageCodeAt true 0 (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_open_frame centerWord centerWord true j hj origin ctx V.1 V.2 state records input
  have firstStep (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (stageCodeAt true 0 (History5.historyMap base (5*j))) origin V.1 V.2)
      (cellWith true (P1Life.dstart (base 760) base (base 2409)) j 3 2)
      (Frame true 0 (regularStep true j origin 0 V)) := by
    intro state records input
    exact regular_cellWith_frame _ true centerWord P1Life.oddWord dstart_law dstart_support
      j 0 0 3 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (V : Fp×Fp) : StateTriple (Frame true 2 V) (onPacket j stageClose)
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!true) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame P1Life.oddWord P1Life.oddWord true j hj origin ctx V.1 V.2 state records input
  let V1 := regularStep true j origin 0 (X,Y)
  let V2 := regularStep true j origin 1 V1
  let V3 := regularStep true j origin 2 V2
  let V4 := regularStep true j origin 3 V3
  let V5 := regularStep true j origin 4 V4
  have result := (opening (X,Y)).seq
    ((firstStep (X,Y)).seq
    ((step true 0 1 4 (by decide) (by decide) V1).seq
    ((transfer true 0 (by decide) V2).seq
    ((step true 1 2 4 (by decide) (by decide) V2).seq
    ((step true 1 3 3 (by decide) (by decide) V3).seq
    ((transfer true 1 (by decide) V4).seq
    ((step true 2 4 4 (by decide) (by decide) V4).seq (closing V5))))))))
  simpa only [dstartBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    if_true,if_false,show ¬(1:Nat)=0 from by decide,List.append_assoc,Bool.not_true] using result

theorem dstartBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (dstartBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have first := cellWith_read_support true _ dstart_support j 3 2 hj (by decide) (by decide)
  have sites : wires (dstartBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [dstartBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨first,cellAt true 4 (by decide)⟩,
      transfer true 0 (by decide)⟩,cellAt true 4 (by decide)⟩,cellAt true 3 (by decide)⟩,
      transfer true 1 (by decide)⟩,cellAt true 4 (by decide)⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem dstartBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord j origin X Y) (dstartBasePacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame centerWord centerWord P1Life.oddWord P1Life.oddWord j (j+1) j hj origin X Y _ _
    (dstartBasePacket j) (otherEncodeCut_step base j 102)
    (otherEncodeCut_body_disjoint j j hj origin ctx _ (dstartBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := dstartBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq true j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem dstartPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord j origin X Y) (dstartPacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin V.1 V.2 state) := by
  intro state records input
  have raw := dstartBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (dstartBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region centerWord centerWord _ origin ctx X Y state input)
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
  change run (dstartPacket j) records state=run (dstartBasePacket j) records state at same
  rw [same]
  exact raw

theorem cutFrame_unique_route (cut : Nat) (origin : BasisState) (X Y : Fp)
    (a b : State) (ha : ECDSAAdd.Entrant.Rolling1588.CutFrame cut origin X Y a)
    (hb : ECDSAAdd.Entrant.Rolling1588.CutFrame cut origin X Y b)
    (phase : a.phase = b.phase) : a = b := by
  obtain ⟨rawA, phaseA, frameA, encodedA⟩ := ha
  obtain ⟨rawB, phaseB, frameB, encodedB⟩ := hb
  have rawEq : rawA = rawB := by
    apply State.extensionality
    · exact phaseA.trans (phase.trans phaseB.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ frameA frameB
  rw [encodedA, encodedB, rawEq]

theorem dstartPacket_counts :
    toffoliCount (dstartPacket 1)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet true 1)+239 ∧
    measurementCount (dstartPacket 1)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet true 1)+234 := by
  have a := cell_count_delta true 1 3 2
  have b := cell_count_delta true 1 4 2
  have c := cellWith_counts true (P1Life.dstart (base 760) base (base 2409)) 1 3 2
  have d := route_junction_counts
  have e := cell_counts true 1 3 2
  simp only [dstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,dstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem dstartPacket_slots :
    Challenge.gateSlots (dstartPacket 1)+136=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet true 1)+3304 := by
  have a := cell_slot_delta true 1 3 2
  have b := cell_slot_delta true 1 4 2
  have c := cellWith_slots true (P1Life.dstart (base 760) base (base 2409)) 1 3 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) true base (base 2409)
  have regular := cellWith_slots true (P1Life.half (base 760) true base (base 2409)) 1 3 2
  have eq : cell true 1 3 2=cellWith true (P1Life.half (base 760) true base (base 2409)) 1 3 2 := rfl
  rw [←eq] at regular
  simp only [if_true] at h
  simp only [dstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,dstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,Challenge.gateSlots_append]
  simp only [halfSlotSaving,if_true] at a b
  omega

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== RouteARecordHalfLower (support bridge: footprint minus 760 inside the record half) =====
section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum
attribute [local irreducible] ECDSAAdd.wires

theorem lw_majority (a b c d : Wire) : wires (Arithmetic.majority a b c d)={a,b,c,d} := by
  ext q
  simp [Arithmetic.majority,wires,Instr.wires]
  itauto

theorem lw_signComplement (s x : Wire) : ∀ xs : List Wire, x∈xs → x∈wires (signComplement s xs)
  | [], h => by simp at h
  | y::ys, h => by
    rw [show signComplement s (y::ys)=[Instr.CX s y]++signComplement s ys from rfl,wires_append,
      Finset.mem_union]
    rcases List.mem_cons.mp h with e | h
    · left; subst e; simp [wires,Instr.wires]
    · right; exact lw_signComplement s x ys h

theorem lw_head_or_tail (l : List Wire) (q : Wire) (h : q∈l) : q=l.getD 0 0 ∨ q∈l.drop 1 := by
  cases l with
  | nil => simp at h
  | cons x xs => simpa using h

theorem lw_compareChain (fwd : Bool) (target q : Wire) :
    ∀ (as bs cs : List Wire) (cin : Wire), bs.length=as.length → as.length≤cs.length+1 →
      q∈cs.take (as.length-1) → q∈wires (Q6LifetimeResearch.compareChain fwd as bs cs cin target) := by
  intro as
  induction as with
  | nil => intro bs cs cin _ _ h; simp at h
  | cons a as ih =>
    intro bs cs cin hb hc h
    cases as with
    | nil => simp at h
    | cons a' as' =>
      match bs, cs, hb, hc, h with
      | [], _, hb, _, _ => exact absurd hb (by simp)
      | [_], _, hb, _, _ => exact absurd hb (by simp)
      | _::_::_, [], _, hc, _ => exact absurd hc (by simp)
      | b::b'::bs', c::cs', hb, hc, h =>
        simp only [Q6LifetimeResearch.compareChain,wires_append,Finset.mem_union]
        have h' : q=c ∨ q∈cs'.take as'.length := by
          simpa only [List.length_cons,Nat.add_sub_cancel,List.take_succ_cons,List.mem_cons] using h
        rcases h' with e | h'
        · left; left; rw [lw_majority]; simp [e]
        · left; right
          exact ih (b'::bs') cs' c (by simpa using hb) (by simp only [List.length_cons] at hc ⊢; omega)
            (by simpa only [List.length_cons,Nat.add_sub_cancel] using h')

theorem rh_viaCompare (q : Wire) (h : q∈wires (Q6LifetimeResearch.compare (base 760) true (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.forward,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rh_viaRawAdd (q : Wire) (h : q∈wires (Q6LifetimeResearch.rawAdd (base 760) (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.forward,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rh_viaFold (q : Wire) (h : q∈wires (Q6LifetimeResearch.fold (base 760) (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.forward,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rh_regs (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r) :
    q∈wires (Q6LifetimeResearch.compare (base 760) true (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires (notRegister ((Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r)) := by
    rw [notRegister_wires]; exact List.mem_toFinset.mpr h
  simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rh_y (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).y) :
    q∈wires (Q6LifetimeResearch.rawAdd (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n := lw_signComplement (Q6EndpointCell.ports base (base 2409)).sign q (Q6EndpointCell.ports base (base 2409)).y h
  simp only [Q6LifetimeResearch.rawAdd,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rh_flags (q : Wire) (h : q=(Q6EndpointCell.ports base (base 2409)).parity ∨ q=(Q6EndpointCell.ports base (base 2409)).lower) :
    q∈wires (Q6LifetimeResearch.fold (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires [Instr.CCX (Q6EndpointCell.ports base (base 2409)).parity (Q6EndpointCell.ports base (base 2409)).lower (Q6EndpointCell.ports base (base 2409)).one, Instr.CX (Q6EndpointCell.ports base (base 2409)).lower (Q6EndpointCell.ports base (base 2409)).rmsb] := by
    rw [wires,wires,wires,Instr.wires,Instr.wires]
    rcases h with e | e
    · rw [e]; exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    · rw [e]; exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  simp only [Q6LifetimeResearch.fold,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rh_not_one (q : Wire) (hc : q∈(Q6EndpointCell.ports base (base 2409)).carry.take 254) : q≠(Q6EndpointCell.ports base (base 2409)).one := by
  intro e
  have hc' := List.mem_of_mem_take hc
  change q∈(List.range' 512 253).map base++[base 1540,base 1541,base 1026] at hc'
  change q=base 1027 at e
  subst e
  simp only [List.mem_append,List.mem_map,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
    or_false] at hc'
  rcases hc' with ⟨i,hi,e⟩ | e | e | e
  · have := base_injective e; omega
  · have := base_injective e; omega
  · have := base_injective e; omega
  · have := base_injective e; omega

theorem rh_carries_gen (L : Layout) (retired q : Wire) (hne : q≠retired) (hone : q≠L.one)
    (hlen : (L.carry.take 254).length=254) (hyl : (L.y.drop 1).length=255) (hrl : (L.r.drop 1).length=255)
    (hc : q∈L.carry.take 254) : q∈wires (Q6LifetimeResearch.compare retired true L) := by
  have hcs : q∈(Q6Structural.q6Carry L).take 255 := by
    rw [Q6Structural.q6Carry,List.append_assoc,List.take_append]
    exact List.mem_append_left _ (by rw [List.take_of_length_le (by omega)]; exact hc)
  have hcsl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    simp only [List.length_take,Q6Structural.q6Carry,List.length_append,List.length_singleton,hlen]
    omega
  rcases lw_head_or_tail _ q hcs with e | tail
  · have n : q∈wires (Arithmetic.majority (L.y.getD 0 0) (L.r.getD 0 0) L.one
        (((Q6Structural.q6Carry L).take 255).getD 0 0)) := by
      rw [lw_majority,e]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]
  · have hdl : (((Q6Structural.q6Carry L).take 255).drop 1).length=254 := by
      rw [List.length_drop,hcsl]
    have a3 : q∈(((Q6Structural.q6Carry L).take 255).drop 1).take ((L.y.drop 1).length-1) := by
      rw [hyl,List.take_of_length_le (by rw [hdl])]
      exact tail
    have chain := lw_compareChain true L.parity q (L.y.drop 1) (L.r.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
      (by rw [hyl,hrl]) (by rw [hdl,hyl]) a3
    have n : q∈wires (Q6LifetimeResearch.move retired L.one
        (Q6LifetimeResearch.compareChain true (L.y.drop 1) (L.r.drop 1)
          (((Q6Structural.q6Carry L).take 255).drop 1)
          (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity)) := by
      rw [Q6LifetimeResearch.move,renameProgram_support]
      exact Finset.mem_image.mpr ⟨q,chain,Equiv.swap_apply_of_ne_of_ne hne hone⟩
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem gen_y_length (L : Layout) (hw : L.Widths) : L.y.length=256 :=
  (BalancedCleanup.widths L.toLayout hw).2.2.1

theorem gen_r_length (L : Layout) (hw : L.Widths) : L.r.length=256 :=
  (BalancedCleanup.widths L.toLayout hw).2.1

theorem gen_carry_length (L : Layout) (hw : L.Widths) : (L.carry.take 254).length=254 :=
  (BalancedCleanup.widths L.toLayout hw).2.2.2

theorem gen_carries (L : Layout) (hw : L.Widths) (retired q : Wire) (hne : q≠retired) (hone : q≠L.one)
    (hc : q∈L.carry.take 254) : q∈wires (Q6LifetimeResearch.compare retired true L) :=
  rh_carries_gen L retired q hne hone (gen_carry_length L hw)
    (by rw [List.length_drop,gen_y_length L hw]) (by rw [List.length_drop,gen_r_length L hw]) hc

theorem rh_carries (q : Wire) (hne : q≠base 760) (hc : q∈(Q6EndpointCell.ports base (base 2409)).carry.take 254) :
    q∈wires (Q6LifetimeResearch.compare (base 760) true (Q6EndpointCell.ports base (base 2409))) :=
  gen_carries (Q6EndpointCell.ports base (base 2409)) (Q6EndpointCell.ports_widths base (base 2409))
    (base 760) q hne (rh_not_one q hc) hc

/-- Every wire of the junction footprint except the retired carry `base 760` occurs in the record
lifetime half of the division direction. -/
theorem record_half_lower :
    (P1Life.junctionFootprint (Q6EndpointCell.ports base (base 2409))).erase (base 760)⊆wires (R2Life760.half760 true) := by
  intro q hq
  obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hq
  have fwd : q∈wires (Q6LifetimeResearch.forward (base 760) false (Q6EndpointCell.ports base (base 2409))) ∨ q=base 2409 := by
    simp only [P1Life.junctionFootprint,List.mem_toFinset,List.mem_cons,List.mem_append] at hmem
    rcases hmem with e | e | e | e | (hr | hy) | hc
    · exact Or.inr e
    · exact Or.inl (rh_viaFold q (rh_flags q (Or.inl e)))
    · exact Or.inl (rh_viaFold q (rh_flags q (Or.inr e)))
    · exact Or.inl (rh_viaCompare q (rh_regs q (List.mem_cons.mpr (Or.inl e))))
    · exact Or.inl (rh_viaCompare q (rh_regs q (List.mem_cons_of_mem _ hr)))
    · exact Or.inl (rh_viaRawAdd q (rh_y q hy))
    · exact Or.inl (rh_viaCompare q (rh_carries q hne hc))
  rw [R2Life760.half760_true]
  simp only [Q6LifetimeResearch.half,if_true,wires_append,Finset.mem_union]
  rcases fwd with h | e
  · exact Or.inl (Or.inr h)
  · left; left
    rw [e,wires,wires,Instr.wires]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


-- ===== odd45: the odd division slice on packets 1..45 =====
/-
# odd45: odd division slice on packets 1..45

The window needs standard words in the first staircase group's packets 46..53.  The odd division slice
therefore runs `dstart` in packet 1, ordinary odd packets 2..44 and `dend` in packet 45 (`slice45`),
followed by the record packets 46..84 (`dslice`).  It saves 164 T / 389 M against the record packets.
`dendBasePacket` is the division packet with its last cell on `dend`, generic in `j` (`basePacket`
fixes the `dend` packet at `j = 84`).
-/
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

theorem odd45_program_true_add (p : Nat → Program) :
    ∀ (a b j : Nat),
      PacketSequence.program true p j (a + b) =
        PacketSequence.program true p j a ++
          PacketSequence.program true p (j + a) b
  | 0, b, j => by simp [PacketSequence.program]
  | a + 1, b, j => by
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h]
      simp only [PacketSequence.program, if_true, List.append_assoc]
      rw [odd45_program_true_add p a b (j + 1)]
      have hj : j + 1 + a = j + (a + 1) := by omega
      rw [hj]

/-- Division packet `j` whose last division cell runs `dend` (odd words in, standard words out);
the other four cells are ordinary odd halves. -/
def dendBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cell true j 3 2 ++ cell true j 4 2 ++ onPacket j bridge7 ++
      cell true j 4 2 ++ cell true j 3 2 ++ onPacket j bridge5 ++
      cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def dendPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (dendBasePacket j)

theorem dendBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j))) origin X Y)
      (dendBasePacket j)
      (fun state => let V := regularPayload true j origin (X,Y)
        CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (d : Bool) (V : Fp×Fp) : StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt d (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen) (Frame d 0 V) := by
    intro state records input
    exact regular_open_frame P1Life.oddWord P1Life.oddWord d j hj origin ctx V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (d : Bool) (V : Fp×Fp) : StateTriple (CodeFrame centerWord centerWord (stageCodeAt d 2 (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageClose)
      (CodeFrame centerWord centerWord (codeEncodeAt (!d) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame centerWord centerWord d j hj origin ctx V.1 V.2 state records input
  have finalStep (V : Fp×Fp) : StateTriple (Frame true 2 V)
      (cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2)
      (CodeFrame centerWord centerWord (stageCodeAt true 2 (History5.historyMap base (5*j))) origin
        (regularStep true j origin 4 V).1 (regularStep true j origin 4 V).2) := by
    intro state records input
    exact regular_cellWith_frame _ true P1Life.oddWord centerWord dend_law dend_support
      j 2 4 4 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  let V1 := regularStep true j origin 0 (X,Y)
  let V2 := regularStep true j origin 1 V1
  let V3 := regularStep true j origin 2 V2
  let V4 := regularStep true j origin 3 V3
  let V5 := regularStep true j origin 4 V4
  have result := (opening true (X,Y)).seq
    ((step true 0 0 3 (by decide) (by decide) (X,Y)).seq
    ((step true 0 1 4 (by decide) (by decide) V1).seq
    ((transfer true 0 (by decide) V2).seq
    ((step true 1 2 4 (by decide) (by decide) V2).seq
    ((step true 1 3 3 (by decide) (by decide) V3).seq
    ((transfer true 1 (by decide) V4).seq
    ((finalStep V4).seq (closing true V5))))))))
  simpa only [dendBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    if_true,if_false,show ¬(1:Nat)=0 from by decide,List.append_assoc] using result

theorem dendBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (dendBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have last := cellWith_read_support true _ dend_support j 4 2 hj (by decide) (by decide)
  have sites : wires (dendBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [dendBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt true 3 (by decide),cellAt true 4 (by decide)⟩,
      transfer true 0 (by decide)⟩,cellAt true 4 (by decide)⟩,cellAt true 3 (by decide)⟩,
      transfer true 1 (by decide)⟩,last⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem dendBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord j origin X Y) (dendBasePacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord (j+1) origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame P1Life.oddWord P1Life.oddWord centerWord centerWord j (j+1) j hj origin X Y _ _
    (dendBasePacket j) (otherEncodeCut_step base j 102)
    (otherEncodeCut_body_disjoint j j hj origin ctx _ (dendBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := dendBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq true j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem dendPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord j origin X Y) (dendPacket j)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord (j+1) origin V.1 V.2 state) := by
  intro state records input
  have raw := dendBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (dendBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (cutFrame_zero_region centerWord centerWord _ origin ctx _ _ _ raw.2)
  change run (dendPacket j) records state=run (dendBasePacket j) records state at same
  rw [same]
  exact raw

theorem dendPacket_counts (j : Nat) :
    toffoliCount (dendPacket j)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet true j)+242 ∧
    measurementCount (dendPacket j)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet true j)+237 := by
  have a := cell_count_delta true j 3 2
  have b := cell_count_delta true j 4 2
  have c := cellWith_counts true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := route_junction_counts
  have e := cell_counts true j 4 2
  simp only [dendPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,dendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,toffoliCount_append,measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem dendPacket_slots (j : Nat) :
    Challenge.gateSlots (dendPacket j)+170=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet true j)+3877 := by
  have a := cell_slot_delta true j 3 2
  have b := cell_slot_delta true j 4 2
  have c := cellWith_slots true (P1Life.dend (base 760) base (base 2409)) j 4 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) true base (base 2409)
  have regular := cellWith_slots true (P1Life.half (base 760) true base (base 2409)) j 4 2
  have eq : cell true j 4 2=cellWith true (P1Life.half (base 760) true base (base 2409)) j 4 2 := rfl
  rw [←eq] at regular
  simp only [if_true] at h
  simp only [dendPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,dendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,if_true,Challenge.gateSlots_append]
  simp only [halfSlotSaving,if_true] at a b
  omega

end ECDSAAdd.Entrant.RouteA.Rolling1588
end


section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== cell support: the hosted odd45 slice is physical, stays inside the
-- record packets 1..45 and, on a record cut frame at cut 1, ends where the record packets 1..45 end =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed Challenge RecordedQuantum
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] GatePhysical P1Life.half P1Life.dstart P1Life.dend P1Life.mend

/-- the `dstart` packet is physical. -/
theorem c45_dstartBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (dstartBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition true 0) (stageTransition_support true 0 (by decide))
    (stage_physical.2.2 true 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition true 1) (stageTransition_support true 1 (by decide))
    (stage_physical.2.2 true 1 (by decide))
  have c3 := cell_physical true j 3 2 hj (by decide)
  have c4 := cell_physical true j 4 2 hj (by decide)
  have d0 := cellWith_physical true _ route_junction_physical.1 j 3 2 hj (by decide)
  simp only [dstartBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨d0,c4⟩,t0⟩,c4⟩,c3⟩,t1⟩,c4⟩⟩,closing⟩

/-- the generic `dend` packet of odd45 is physical. -/
theorem c45_dendBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (dendBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition true 0) (stageTransition_support true 0 (by decide))
    (stage_physical.2.2 true 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition true 1) (stageTransition_support true 1 (by decide))
    (stage_physical.2.2 true 1 (by decide))
  have c3 := cell_physical true j 3 2 hj (by decide)
  have c4 := cell_physical true j 4 2 hj (by decide)
  have e0 := cellWith_physical true _ route_junction_physical.2.1 j 4 2 hj (by decide)
  simp only [dendBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨c3,c4⟩,t0⟩,c4⟩,c3⟩,t1⟩,e0⟩⟩,closing⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairLoanGroupSupport
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
attribute [local irreducible] wires StairLoan.half760Loan StairGroups.halfWindow StairGroups.cell Rolling1588.onPacket

/-- an odd division cell stays inside the record cell. -/
theorem c45_oddCell_sub (P : Program) (hP : RouteA.Rolling1588.HalfSupport P) (j active hole : Nat) :
    wires (RouteA.Rolling1588.cellWith true P j active hole) ⊆ wires (Rolling1588.cell true j active hole) := by
  have h : wires (RouteA.Rolling1588.halfWindowWith P j active hole) ⊆
      wires (Rolling1588.halfWindow true j active hole) := by
    unfold RouteA.Rolling1588.halfWindowWith Rolling1588.halfWindow
    exact loanWindow_sub _ _ _ _ _ (rename_sub _ _ _ (hP.trans RouteA.Rolling1588.record_half_lower))
  simp only [RouteA.Rolling1588.cellWith,Rolling1588.cell,if_true]
  exact append_sub _ _ _ _ h (Finset.Subset.refl _)

theorem c45_oddPlainCell_sub (j active hole : Nat) :
    wires (RouteA.Rolling1588.cell true j active hole) ⊆ wires (Rolling1588.cell true j active hole) := by
  have h := c45_oddCell_sub _ (RouteA.Rolling1588.half_support true) j active hole
  simpa only [RouteA.Rolling1588.cellWith,RouteA.Rolling1588.cell,RouteA.Rolling1588.halfWindow,if_true] using h

theorem c45_oddBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.basePacket true j) ⊆ wires (Rolling1588.basePacket true j) := by
  have c := fun active hole => c45_oddPlainCell_sub j active hole
  have last : wires (if j=84 then RouteA.Rolling1588.cellWith true (P1Life.dend (base 760) base (base 2409)) j 4 2
      else RouteA.Rolling1588.cell true j 4 2) ⊆ wires (Rolling1588.cell true j 4 2) := by
    split
    · exact c45_oddCell_sub _ RouteA.Rolling1588.dend_support j 4 2
    · exact c 4 2
  simp only [RouteA.Rolling1588.basePacket,Rolling1588.basePacket,if_true]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 3 2) (c 4 2)) (Finset.Subset.refl _)) (c 4 2)) (c 3 2))
    (Finset.Subset.refl _)) last

theorem c45_dstartBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.dstartBasePacket j) ⊆ wires (Rolling1588.basePacket true j) := by
  have c := fun active hole => c45_oddPlainCell_sub j active hole
  have hd := c45_oddCell_sub _ RouteA.Rolling1588.dstart_support j 3 2
  simp only [RouteA.Rolling1588.dstartBasePacket,Rolling1588.basePacket,if_true]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ hd (c 4 2)) (Finset.Subset.refl _)) (c 4 2)) (c 3 2))
    (Finset.Subset.refl _)) (c 4 2)

/-- the generic `dend` packet of odd45 stays inside the record division packet. -/
theorem c45_dendBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.dendBasePacket j) ⊆ wires (Rolling1588.basePacket true j) := by
  have c := fun active hole => c45_oddPlainCell_sub j active hole
  have hd := c45_oddCell_sub _ RouteA.Rolling1588.dend_support j 4 2
  simp only [RouteA.Rolling1588.dendBasePacket,Rolling1588.basePacket,if_true]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 3 2) (c 4 2)) (Finset.Subset.refl _)) (c 4 2)) (c 3 2))
    (Finset.Subset.refl _)) hd

theorem c45_oddPacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.packet true j) ⊆ wires (Rolling1588.packet true j) := by
  unfold RouteA.Rolling1588.packet Rolling1588.packet
  exact rename_sub _ _ _ (c45_oddBasePacket_sub j)

end ECDSAAdd.Entrant.StairLoanGroupSupport
end

-- ===== end odd division cell =====

-- ===== odd multiplication cell on packets 45..1 =====
-- The multiplication-kernel half cell `mstart` and its packets, the odd multiplication slices (`mslice` on
-- packets 84..1, `mslice45` on packets 45..1) with their frames, counts and slots, and the cell lemmas used by
-- the window.
/-
# Odd-word slice in the multiplication field

A multiplication packet runs `mstart` (standard words in, odd words out) in place of its first
multiplication half, or `mend` (odd words in, standard words out) in place of its last one; the
other halves are the ordinary odd halves of `P1Life`.  `mstart` is the inverse of `dend`: recode Y
to the odd code, accept the standard X (`acceptStandard`, the involution of `emitStandard`'s core),
then the odd inverse tail (`junctionOddRest`).
-/

-- ===== P1MultiplyStart =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.P1Life
open Arithmetic BalancedCircuit BalancedField


def acceptStandard (retired : Wire) (L : Layout) : Program :=
  [.CX L.rmsb L.lower] ++ signComplement L.lower L.r ++ [.X L.lower] ++ notRegister L.low ++
    Q6LifetimeResearch.move retired L.rmsb
      (literalConstAdd L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral)


def junctionOddRest (retired : Wire) (L : Layout) : Program :=
  prepareCompare L++exposure L++compare retired false L++(exposure L).reverse++
    (prepareCompare L).reverse++BiasedInverse.unbiasView L++unfoldStep retired L++
    rotateLeft (rawTarget L)++[.CX L.parity L.r0]++rawSub retired L


def mstart (retired : Wire) (w : Nat → Wire) (sign : Wire) : Program :=
  let L := Q6EndpointCell.ports w sign
  [.X sign] ++ recode retired true L L.y ++ acceptStandard retired L ++
    junctionOddRest retired L ++ [.X sign]


theorem junction_accept_standard_value (X : Int) (hx : Centered X) :
    (2^255-1-encodeWord 255 (magnitude X)+BalancedCleanup.positiveLiteral+
      (negative (junctionToOdd X)).toNat)%2^255=encodeWord 255 (oddNormalized (junctionToOdd X)) := by
  rw [junction_complement_encoded,Nat.add_assoc,DirectPass.encoded_add_nat,Nat.cast_add]
  have c := constants
  have lit : (BalancedCleanup.positiveLiteral : Int)=h-1 :=
    Int.toNat_of_nonneg (by omega)
  rw [lit]
  congr 1
  have sg := junction_to_odd_sign X hx
  unfold oddNormalized magnitude
  rw [sg]
  unfold Centered at hx
  by_cases xn : X<0 <;> simp [negative,xn,junctionToOdd] <;> omega


theorem accept_standard_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : Centered X) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (acceptStandard retired L)
      (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin (junctionToOdd X) Y) := by
  have range : -((2^255 : Nat) : Int)≤X ∧ X<((2^255 : Nat) : Int) := by
    have hp := constants
    unfold Centered at hx
    omega
  have a := DirectPass.prepare_sign_boundary_wide retired L hw hn origin X Y range
  have b := junction_flip_lower retired L hn origin (encodeWord 255 (magnitude X))
    (encodeWord 256 Y) false (negative X)
  have c := junction_not_low retired L hw hn origin (encodeWord 255 (magnitude X))
    (encodeWord 256 Y) false (!negative X)
  have d := junction_literal_boundary retired L hw hn (List.mem_of_mem_drop member) origin
    (2^255-1-encodeWord 255 (magnitude X)) (encodeWord 256 Y)
    BalancedCleanup.positiveLiteral false (!negative X)
  rw [←junction_to_odd_sign X hx] at b c d
  rw [junction_accept_standard_value X hx] at d
  simpa only [acceptStandard,BalancedCleanup.prepareSign,List.append_assoc] using
    Triple.seq a (Triple.seq b (Triple.seq c d))


theorem junction_odd_rest_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (F Y : Int) (hf : OddDomain F) (hy : OddDomain Y) :
    Triple (DirectPass.AfterComparison DirectPass.oddEncoding L retired origin F Y)
      (junctionOddRest retired L)
      (DirectPass.AfterHalf L retired origin (oddInverse (origin L.sign) F Y) Y) := by
  let B := origin L.sign
  let R := oddInverse B F Y
  let T := oddSum B R Y
  have hr : OddDomain R := oddRep_bounds _
  have ht := oddSum_bounds B R Y hr hy
  have result : oddFold T=F := oddForward_inverse B F Y hf hy
  have interval : originalParity T=decide (oddComparisonLeft F<oddComparisonY B F Y) := by
    have h := oddComparison_parity B R Y hr hy
    rw [result] at h
    exact h
  have mt : retired∈L.carry.take 254 := List.mem_of_mem_drop member
  have c := comparison_to_fold retired L hw hn member origin T F Y hf hy interval
  have d := fold_to_raw retired L hw hn mt origin T Y ht
  rw [result] at d
  have e := rawSub_boundary retired L hw hn member origin B R Y hr hy rfl
  simpa only [junctionOddRest,List.append_assoc] using Triple.seq c (Triple.seq d e)


theorem junction_sgo_boundary (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (origin : BasisState) (X Y : Int) (hx : Centered X) (hy : OddDomain Y) :
    Triple (DirectPass.AfterHalf L retired origin X Y) (acceptStandard retired L++junctionOddRest retired L)
      (DirectPass.AfterHalf L retired origin (oddInverse (origin L.sign) (junctionToOdd X) Y) Y) :=
  Triple.seq (accept_standard_boundary retired L hw hn member origin X Y hx)
    (junction_odd_rest_boundary retired L hw hn member origin _ Y (junction_to_odd_bounds X hx) hy)


theorem junction_to_odd_center (x : Fp) : junctionToOdd (centerFp x)=oddRep x := by
  rw [←junction_to_odd_rep _ (centerFp_bounds x),centerFp_cast]


theorem junction_sgo_frame (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (X Y : Fp) (s : State) (m : List Bool)
    (rv : regValue L.r s.basis=centerWord X) (yv : regValue L.y s.basis=oddWord Y)
    (flags : DirectPass.LiveFlags L false false false s.basis)
    (clean : DirectPass.CleanExcept (L.carry.take 254) retired s.basis) :
    let p := acceptStandard retired L++junctionOddRest retired L
    (run p m s).phase=s.phase ∧ DirectPass.WordFrame L.r s.basis
      (oddWord (2*X+(if !s.basis L.sign then -Y else Y))) (run p m s).basis := by
  have b := junction_sgo_boundary retired L hw hn member s.basis
    (centerFp X) (oddRep Y) (centerFp_bounds X) (oddRep_bounds Y)
  have h := DirectPass.kernel_frame_of_boundary retired L (centerFp X) (oddRep Y) _ _
    s m rv yv flags clean b
  have field := kernel_field false (!s.basis L.sign) X Y
  simp only [kernelResult,Bool.false_eq_true,if_false,Bool.not_not] at field
  rw [junction_to_odd_center X,field] at h
  exact h


theorem mstart_frame (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (centerWord X) (centerWord Y)) (mstart retired w sign)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (oddWord (2*X+(if origin sign then -Y else Y))) (oddWord Y)) := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  apply DirectPass.half_frame_from_pair_kernel retired w sign hn origin clean (centerWord X) (centerWord Y)
    (fun B => oddWord (2*X+(if B then -Y else Y))) (oddWord Y) (mstart retired w sign)
    (recode retired true L L.y++(acceptStandard retired L++junctionOddRest retired L))
    (by simp only [mstart,L,List.append_assoc])
  intro s m rv yv flags carry
  have h := junction_recode_before retired true L hw hn (List.mem_of_mem_drop member)
    (acceptStandard retired L++junctionOddRest retired L) (centerWord X) (centerWord Y)
    (fun B => oddWord (2*X+(if !B then -Y else Y))) s m rv yv flags carry (by
      intro u tape ur uy uf uc
      have uy' : regValue L.y u.basis=oddWord Y := by
        simpa only [if_true,←recode_odd_word,oddWord] using uy
      exact junction_sgo_frame retired L hw hn member X Y u tape ur uy' uf uc)
  simpa only [if_true,←recode_odd_word,oddWord] using h


theorem junction_odd_rest_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (junctionOddRest retired L)=766 ∧ measurementCount (junctionOddRest retired L)=766 := by
  have b := p1_compare_counts false retired L hw
  have c := p1_fold_counts true retired L hw
  have d := p1_raw_sub_counts retired L hw
  have pc := p1_compare_view_counts L
  have ub := p1_unbias_view_counts L
  have rot := rotate_counts (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at b c
  simp only [junctionOddRest,toffoliCount_append,measurementCount_append,toffoliCount_reverse,
    measurementCount_reverse,b.1,b.2,c.1,c.2,d.1,d.2,pc.1,pc.2,ub.1,ub.2,rot.2.2.1,rot.2.2.2,
    exposure,toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem accept_standard_counts (retired : Wire) (L : Layout) (hw : L.Widths) :
    toffoliCount (acceptStandard retired L)=254 ∧ measurementCount (acceptStandard retired L)=254 := by
  have lowlen : L.low.length=255 := by simp [BalancedCleanup.Layout.low,hw.1]
  have a := literalConstAdd_counts L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral
    (by simp [List.length_take,hw.2.2,lowlen])
  rw [lowlen] at a
  simp only [acceptStandard,toffoliCount_append,measurementCount_append,Q6LifetimeResearch.move,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,a.1,a.2,
    (notRegister_counts L.low).1,(notRegister_counts L.low).2,
    (signComplement_counts L.lower L.r).1,(signComplement_counts L.lower L.r).2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem mstart_counts (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    toffoliCount (mstart retired w sign)=1274 ∧ measurementCount (mstart retired w sign)=1274 := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have a := recode_counts retired true L hw hn member
  have b := accept_standard_counts retired L hw
  have c := junction_odd_rest_counts retired L hw
  dsimp only [L] at a b c
  simp only [mstart,toffoliCount_append,measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,
    toffoliCount,measurementCount]
  exact ⟨True.intro,True.intro⟩


theorem accept_standard_resources (retired : Wire) (L : Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (member : retired∈L.carry.take 254) :
    JunctionSafe ((junctionFootprint L).erase retired) (acceptStandard retired L) := by
  have nt := junction_not_resources retired L hn member L.low (by
    intro q hq
    simp [BalancedCleanup.Layout.r,hq])
  have lit := junction_literal_resources retired L hn BalancedCleanup.positiveLiteral
  have lower := junction_small_resources retired L hw hn member [.X L.lower]
    (by simp [junctionCliffordPieces])
  have top := junction_small_resources retired L hw hn member [.CX L.rmsb L.lower]
    (by simp [junctionCliffordPieces])
  have sc := junction_sign_resources retired L hn member L.lower L.r
    (by simp) (by intro q hq; simp [hq]) (by
      intro bad; exact BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [bad]))
  simp only [acceptStandard,junction_safe_append]
  exact ⟨⟨⟨⟨top,sc⟩,lower⟩,nt⟩,lit⟩


theorem mstart_resources (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1) :
    GatePhysical (mstart retired w sign) ∧ wires (mstart retired w sign)⊆
      (junctionFootprint (Q6EndpointCell.ports w sign)).erase retired := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have mt := List.mem_of_mem_drop member
  have acc := accept_standard_resources retired L hw hn mt
  have recoder := recode_y_resources retired true L hw hn mt
  have rest := junction_rest_resources true retired L hw hn member
  have flip := junction_small_resources retired L hw hn mt [.X L.sign]
    (by simp [junctionCliffordPieces])
  change JunctionSafe ((junctionFootprint L).erase retired) (mstart retired w sign)
  have shape : mstart retired w sign=[.X sign]++recode retired true L L.y++
      acceptStandard retired L++junctionOddRest retired L++[.X sign] := rfl
  rw [shape]
  simp only [junction_safe_append]
  exact ⟨⟨⟨⟨flip,recoder⟩,acc⟩,rest⟩,flip⟩

end ECDSAAdd.Entrant.P1Life
end

-- ===== RouteAMultiplyStartSlots =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace ECDSAAdd.Entrant.RouteA
open Arithmetic Challenge Baselines BalancedCircuit


theorem slot_odd_rest (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.junctionOddRest retired L)=14371 := by
  have len := slot_layout_lengths L hw
  have comp := slot_compare true false retired L hw
  have fold := slot_fold true true retired L hw
  have sub := slot_raw_sub true retired L hw
  have views := slot_views L hw
  have rt := rotate_slots (rawTarget L)
  simp only [Bool.false_eq_true,if_false,if_true] at comp fold sub
  simp only [P1Life.junctionOddRest,gateSlots_append,reverse_gateSlots,
    comp,fold,sub,views.1,views.2.1,views.2.2.1,views.2.2.2,rt.1,rt.2,len.2.2.2.1,
    P1Life.exposure,gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]


/-- `acceptStandard` has the gates of `emitStandard` in another order (no kernel evaluation). -/
theorem slot_accept_standard (retired : Wire) (L : Layout) (hw : L.Widths) :
    gateSlots (P1Life.acceptStandard retired L)=3532 := by
  have e := (slot_junction_emits retired L hw).2.2
  simp only [P1Life.acceptStandard,P1Life.emitStandard,gateSlots_append] at e ⊢
  omega


theorem slot_mstart (retired : Wire) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈(Q6EndpointCell.ports w sign).carry.take 254) :
    gateSlots (P1Life.mstart retired w sign)=20986 := by
  let L := Q6EndpointCell.ports w sign
  have hw := Q6EndpointCell.ports_widths w sign
  have acc := slot_accept_standard retired L hw
  have rest := slot_odd_rest retired L hw
  have odd := slot_recode retired true L hw hn member
  simp only [if_true] at odd
  dsimp only [L] at acc rest odd
  simp only [P1Life.mstart,gateSlots_append,acc,rest,odd,
    gateSlots_cons,gateSlots_nil,instructionSlots,List.length_nil]

end ECDSAAdd.Entrant.RouteA
end

-- ===== RouteARecordHalfLowerFalse (support bridge: footprint minus 760 inside the record multiply half) =====
section
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum
attribute [local irreducible] ECDSAAdd.wires

theorem rhf_viaCompare (q : Wire) (h : q∈wires (Q6LifetimeResearch.compare (base 760) false (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rhf_viaRawSub (q : Wire) (h : q∈wires (Q6LifetimeResearch.rawSubTail (base 760) (Q6EndpointCell.ports base (base 2409)))) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,h,true_or,or_true]

theorem rhf_regs (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r) :
    q∈wires (Q6LifetimeResearch.compare (base 760) false (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires (notRegister ((Q6EndpointCell.ports base (base 2409)).one::(Q6EndpointCell.ports base (base 2409)).r)) := by
    rw [notRegister_wires]; exact List.mem_toFinset.mpr h
  simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_y (q : Wire) (h : q∈(Q6EndpointCell.ports base (base 2409)).y) :
    q∈wires (Q6LifetimeResearch.rawSubTail (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n := lw_signComplement (Q6EndpointCell.ports base (base 2409)).sign q (Q6EndpointCell.ports base (base 2409)).y h
  simp only [Q6LifetimeResearch.rawSubTail,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_parity (q : Wire) (h : q=(Q6EndpointCell.ports base (base 2409)).parity) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires [Instr.CX (Q6EndpointCell.ports base (base 2409)).parity (Q6EndpointCell.ports base (base 2409)).r0] := by
    rw [wires,wires,Instr.wires,h]
    exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_lower (q : Wire) (h : q=(Q6EndpointCell.ports base (base 2409)).lower) :
    q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) := by
  have n : q∈wires [Instr.CX (Q6EndpointCell.ports base (base 2409)).rmsb (Q6EndpointCell.ports base (base 2409)).lower] := by
    rw [wires,wires,Instr.wires,h]
    exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have m : q∈wires (BalancedCleanup.prepareSign (Q6EndpointCell.ports base (base 2409)).toLayout) := by
    simp only [BalancedCleanup.prepareSign,wires_append,Finset.mem_union]
    exact Or.inl n
  simp only [Q6LifetimeResearch.inverse,wires_append,Finset.mem_union,m,true_or,or_true]

theorem rhf_carries_gen (fwd : Bool) (L : Layout) (retired q : Wire) (hne : q≠retired) (hone : q≠L.one)
    (hlen : (L.carry.take 254).length=254) (hyl : (L.y.drop 1).length=255) (hrl : (L.r.drop 1).length=255)
    (hc : q∈L.carry.take 254) : q∈wires (Q6LifetimeResearch.compare retired fwd L) := by
  have hcs : q∈(Q6Structural.q6Carry L).take 255 := by
    rw [Q6Structural.q6Carry,List.append_assoc,List.take_append]
    exact List.mem_append_left _ (by rw [List.take_of_length_le (by omega)]; exact hc)
  have hcsl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    simp only [List.length_take,Q6Structural.q6Carry,List.length_append,List.length_singleton,hlen]
    omega
  rcases lw_head_or_tail _ q hcs with e | tail
  · have n : q∈wires (Arithmetic.majority (L.y.getD 0 0) (L.r.getD 0 0) L.one
        (((Q6Structural.q6Carry L).take 255).getD 0 0)) := by
      rw [lw_majority,e]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_singleton_self _)))
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]
  · have hdl : (((Q6Structural.q6Carry L).take 255).drop 1).length=254 := by
      rw [List.length_drop,hcsl]
    have a3 : q∈(((Q6Structural.q6Carry L).take 255).drop 1).take ((L.y.drop 1).length-1) := by
      rw [hyl,List.take_of_length_le (by rw [hdl])]
      exact tail
    have chain := lw_compareChain fwd L.parity q (L.y.drop 1) (L.r.drop 1)
      (((Q6Structural.q6Carry L).take 255).drop 1) (((Q6Structural.q6Carry L).take 255).getD 0 0)
      (by rw [hyl,hrl]) (by rw [hdl,hyl]) a3
    have n : q∈wires (Q6LifetimeResearch.move retired L.one
        (Q6LifetimeResearch.compareChain fwd (L.y.drop 1) (L.r.drop 1)
          (((Q6Structural.q6Carry L).take 255).drop 1)
          (((Q6Structural.q6Carry L).take 255).getD 0 0) L.parity)) := by
      rw [Q6LifetimeResearch.move,renameProgram_support]
      exact Finset.mem_image.mpr ⟨q,chain,Equiv.swap_apply_of_ne_of_ne hne hone⟩
    simp only [Q6LifetimeResearch.compare,wires_append,Finset.mem_union,n,true_or,or_true]

theorem rhf_carries (q : Wire) (hne : q≠base 760) (hc : q∈(Q6EndpointCell.ports base (base 2409)).carry.take 254) :
    q∈wires (Q6LifetimeResearch.compare (base 760) false (Q6EndpointCell.ports base (base 2409))) :=
  rhf_carries_gen false (Q6EndpointCell.ports base (base 2409)) (base 760) q hne (rh_not_one q hc)
    (gen_carry_length _ (Q6EndpointCell.ports_widths base (base 2409)))
    (by rw [List.length_drop,gen_y_length _ (Q6EndpointCell.ports_widths base (base 2409))])
    (by rw [List.length_drop,gen_r_length _ (Q6EndpointCell.ports_widths base (base 2409))]) hc

/-- Every wire of the junction footprint except the retired carry `base 760` occurs in the record
lifetime half of the multiplication direction. -/
theorem record_half_lower_false :
    (P1Life.junctionFootprint (Q6EndpointCell.ports base (base 2409))).erase (base 760)⊆wires (R2Life760.half760 false) := by
  intro q hq
  obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hq
  have inv : q∈wires (Q6LifetimeResearch.inverse (base 760) (Q6EndpointCell.ports base (base 2409))) ∨ q=base 2409 := by
    simp only [P1Life.junctionFootprint,List.mem_toFinset,List.mem_cons,List.mem_append] at hmem
    rcases hmem with e | e | e | e | (hr | hy) | hc
    · exact Or.inr e
    · exact Or.inl (rhf_parity q e)
    · exact Or.inl (rhf_lower q e)
    · exact Or.inl (rhf_viaCompare q (rhf_regs q (List.mem_cons.mpr (Or.inl e))))
    · exact Or.inl (rhf_viaCompare q (rhf_regs q (List.mem_cons_of_mem _ hr)))
    · exact Or.inl (rhf_viaRawSub q (rhf_y q hy))
    · exact Or.inl (rhf_viaCompare q (rhf_carries q hne hc))
  rw [R2Life760.half760_false]
  rcases inv with h | e
  · simp only [Q6LifetimeResearch.half,Bool.false_eq_true,if_false,wires_append,Finset.mem_union,h,
      true_or,or_true]
  · rw [e]
    simp only [Q6LifetimeResearch.half,Bool.false_eq_true,if_false,wires_append,Finset.mem_union]
    left; left; left
    rw [wires,wires,Instr.wires]
    exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== RouteA odd multiplication slice (packets 84..1) =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

theorem mstart_law :
    HalfLaw (P1Life.mstart (base 760) base (base 2409)) false centerWord P1Life.oddWord := by
  intro origin clean X Y
  simpa only [Bool.false_eq_true,if_false] using
    P1Life.mstart_frame _ _ _ half_ports_nodup route_retired_member origin clean X Y

theorem mstart_support : HalfSupport (P1Life.mstart (base 760) base (base 2409)) :=
  (P1Life.mstart_resources _ _ _ half_ports_nodup route_retired_member).2

theorem route_mstart_physical : GatePhysical (P1Life.mstart (base 760) base (base 2409)) :=
  (P1Life.mstart_resources _ _ _ half_ports_nodup route_retired_member).1

theorem route_mstart_counts :
    toffoliCount (P1Life.mstart (base 760) base (base 2409))=1274 ∧
    measurementCount (P1Life.mstart (base 760) base (base 2409))=1274 :=
  P1Life.mstart_counts (base 760) base (base 2409) half_ports_nodup route_retired_count_member

/-- Multiplication packet `j` whose first multiplication cell runs `mstart` (standard words in,
odd words out); the other four cells are ordinary odd halves. -/
def mstartBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cellWith false (P1Life.mstart (base 760) base (base 2409)) j 4 2 ++ onPacket j bridge5 ++
      cell false j 3 2 ++ cell false j 4 2 ++ onPacket j bridge7inv ++
      cell false j 4 2 ++ cell false j 3 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def mstartPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (mstartBasePacket j)

/-- Multiplication packet `j` whose last multiplication cell runs `mend` (odd words in,
standard words out). -/
def mendBasePacket (j : Nat) : Program :=
  onPacket j (dp ++ ParityCodec5New.untwist) ++
    (cell false j 4 2 ++ onPacket j bridge5 ++
      cell false j 3 2 ++ cell false j 4 2 ++ onPacket j bridge7inv ++
      cell false j 4 2 ++ cellWith false (P1Life.mend (base 760) base (base 2409)) j 3 2) ++
    onPacket j (ParityCodec5New.twist ++ ep)

def mendPacket (j : Nat) : Program :=
  renameProgram (shifted (Placement5.pi j)) (mendBasePacket j)

theorem mstartBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j))) origin X Y)
      (mstartBasePacket j)
      (fun state => let V := regularPayload false j origin (X,Y)
        CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt true (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen)
      (CodeFrame centerWord centerWord (stageCodeAt false 0 (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_open_frame centerWord centerWord false j hj origin ctx V.1 V.2 state records input
  have firstStep (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (stageCodeAt false 0 (History5.historyMap base (5*j))) origin V.1 V.2)
      (cellWith false (P1Life.mstart (base 760) base (base 2409)) j 4 2)
      (Frame false 0 (regularStep false j origin 4 V)) := by
    intro state records input
    exact regular_cellWith_frame _ false centerWord P1Life.oddWord mstart_law mstart_support
      j 0 4 4 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have closing (V : Fp×Fp) : StateTriple (Frame false 2 V) (onPacket j stageClose)
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt (!false) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame P1Life.oddWord P1Life.oddWord false j hj origin ctx V.1 V.2 state records input
  let V1 := regularStep false j origin 4 (X,Y)
  let V2 := regularStep false j origin 3 V1
  let V3 := regularStep false j origin 2 V2
  let V4 := regularStep false j origin 1 V3
  let V5 := regularStep false j origin 0 V4
  have result := (opening (X,Y)).seq
    ((firstStep (X,Y)).seq
    ((transfer false 0 (by decide) V1).seq
    ((step false 1 3 3 (by decide) (by decide) V1).seq
    ((step false 1 2 4 (by decide) (by decide) V2).seq
    ((transfer false 1 (by decide) V3).seq
    ((step false 2 1 4 (by decide) (by decide) V3).seq
    ((step false 2 0 3 (by decide) (by decide) V4).seq (closing V5))))))))
  simpa only [mstartBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    Bool.false_eq_true,if_false,if_true,show ¬(1:Nat)=0 from by decide,List.append_assoc,
    Bool.not_false] using result

theorem mendBasePacket_frame (j : Nat) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j))) origin X Y)
      (mendBasePacket j)
      (fun state => let V := regularPayload false j origin (X,Y)
        CodeFrame centerWord centerWord (codeEncodeAt true (History5.historyMap base (5*j))) origin V.1 V.2 state) := by
  let Frame (d : Bool) (k : Nat) (V : Fp×Fp) :=
    CodeFrame P1Life.oddWord P1Life.oddWord (stageCodeAt d k (History5.historyMap base (5*j))) origin V.1 V.2
  have opening (V : Fp×Fp) : StateTriple
      (CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageOpen) (Frame false 0 V) := by
    intro state records input
    exact regular_open_frame P1Life.oddWord P1Life.oddWord false j hj origin ctx V.1 V.2 state records input
  have step (d : Bool) (k logical physical : Nat) (hk : k < 3)
      (used : (logical,physical)∈activeSlots d k) (V : Fp×Fp) :
      StateTriple (Frame d k V) (cell d j physical 2)
        (Frame d k (regularStep d j origin logical V)) := by
    intro state records input
    exact regular_cell_frame d j k logical physical hj hk used origin ctx enabled
      V.1 V.2 state records input
  have transfer (d : Bool) (k : Nat) (hk : k < 2) (V : Fp×Fp) :
      StateTriple (Frame d k V) (onPacket j (stageTransition d k)) (Frame d (k+1) V) := by
    intro state records input
    exact regular_transition_frame P1Life.oddWord P1Life.oddWord d j k hj hk origin ctx V.1 V.2 state records input
  have finalStep (V : Fp×Fp) : StateTriple (Frame false 2 V)
      (cellWith false (P1Life.mend (base 760) base (base 2409)) j 3 2)
      (CodeFrame centerWord centerWord (stageCodeAt false 2 (History5.historyMap base (5*j))) origin
        (regularStep false j origin 0 V).1 (regularStep false j origin 0 V).2) := by
    intro state records input
    exact regular_cellWith_frame _ false P1Life.oddWord centerWord mend_law mend_support
      j 2 0 3 hj (by decide) (by decide) origin ctx enabled V.1 V.2 state records input
  have closing (V : Fp×Fp) : StateTriple
      (CodeFrame centerWord centerWord (stageCodeAt false 2 (History5.historyMap base (5*j))) origin V.1 V.2)
      (onPacket j stageClose)
      (CodeFrame centerWord centerWord (codeEncodeAt (!false) (History5.historyMap base (5*j))) origin V.1 V.2) := by
    intro state records input
    exact regular_close_frame centerWord centerWord false j hj origin ctx V.1 V.2 state records input
  let V1 := regularStep false j origin 4 (X,Y)
  let V2 := regularStep false j origin 3 V1
  let V3 := regularStep false j origin 2 V2
  let V4 := regularStep false j origin 1 V3
  let V5 := regularStep false j origin 0 V4
  have result := (opening (X,Y)).seq
    ((step false 0 4 4 (by decide) (by decide) (X,Y)).seq
    ((transfer false 0 (by decide) V1).seq
    ((step false 1 3 3 (by decide) (by decide) V1).seq
    ((step false 1 2 4 (by decide) (by decide) V2).seq
    ((transfer false 1 (by decide) V3).seq
    ((step false 2 1 4 (by decide) (by decide) V3).seq
    ((finalStep V4).seq (closing V5))))))))
  simpa only [mendBasePacket,stageOpen,stageClose,stageTransition,regularPayload,
    Bool.false_eq_true,if_false,if_true,show ¬(1:Nat)=0 from by decide,List.append_assoc,
    Bool.not_false] using result

theorem mstartBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (mstartBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have first := cellWith_read_support false _ mstart_support j 4 2 hj (by decide) (by decide)
  have sites : wires (mstartBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [mstartBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨first,transfer false 0 (by decide)⟩,
      cellAt false 3 (by decide)⟩,cellAt false 4 (by decide)⟩,transfer false 1 (by decide)⟩,
      cellAt false 4 (by decide)⟩,cellAt false 3 (by decide)⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem mendBasePacket_read_support (j : Nat) (hj : j<102) :
    wires (mendBasePacket j)⊆NewHistory5.groupReadSites base (base 2400)
      (base 2409) (base 2410) (5*j) ∪ {base 2312} := by
  have opening := onPacket_read_support j stageOpen stageOpen_support
  have closing := onPacket_read_support j stageClose stageClose_support
  have transfer (d : Bool) (k : Nat) (hk : k<2) :=
    onPacket_read_support j (stageTransition d k) (stageTransition_support d k hk)
  have cellAt (d : Bool) (active : Nat) (ha : active<5) :=
    cell_read_support d j active 2 hj ha (by decide)
  have last := cellWith_read_support false _ mend_support j 3 2 hj (by decide) (by decide)
  have sites : wires (mendBasePacket j)⊆FrontierReplay1591.readSites (5*j) := by
    simp only [mendBasePacket,wires_append,Finset.union_subset_iff]
    exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨cellAt false 4 (by decide),transfer false 0 (by decide)⟩,
      cellAt false 3 (by decide)⟩,cellAt false 4 (by decide)⟩,transfer false 1 (by decide)⟩,
      cellAt false 4 (by decide)⟩,last⟩⟩,closing⟩
  exact sites.trans (FrontierReplay1591.readSites_sub (5*j))

theorem mstartBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord (j+1) origin X Y) (mstartBasePacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord j origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame centerWord centerWord P1Life.oddWord P1Life.oddWord (j+1) j j hj origin X Y _ _
    (mstartBasePacket j) (otherEncodeCut_step base j 102).symm
    (otherEncodeCut_body_disjoint (j+1) j hj origin ctx _ (mstartBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame centerWord centerWord (codeEncodeAt false (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := mstartBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq false j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem mendBasePacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin X Y) (mendBasePacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord j origin V.1 V.2 state) := by
  have nonzero : j≠0 := by omega
  intro state records input
  apply cut_window_frame P1Life.oddWord P1Life.oddWord centerWord centerWord (j+1) j j hj origin X Y _ _
    (mendBasePacket j) (otherEncodeCut_step base j 102).symm
    (otherEncodeCut_body_disjoint (j+1) j hj origin ctx _ (mendBasePacket_read_support j hj)) _ state records input
  intro current tape frame
  have normalized : CodeFrame P1Life.oddWord P1Life.oddWord (codeEncodeAt false (History5.historyMap base (5*j)))
      origin X Y current := by
    simpa [encodeGroup,nonzero,show ¬j+1≤j from by omega] using frame
  have result := mendBasePacket_frame j hj origin ctx enabled X Y current tape normalized
  simpa [regularPayload_eq false j hj origin enabled,encodeGroup,nonzero,show ¬j+1≤j from by omega] using result

theorem mstartPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame centerWord centerWord (j+1) origin X Y) (mstartPacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame P1Life.oddWord P1Life.oddWord j origin V.1 V.2 state) := by
  intro state records input
  have raw := mstartBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (mstartBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region centerWord centerWord _ origin ctx X Y state input)
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
  change run (mstartPacket j) records state=run (mstartBasePacket j) records state at same
  rw [same]
  exact raw

theorem mendPacket_cut_frame (j : Nat) (first : 1≤j) (hj : j<102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    StateTriple (CutFrame P1Life.oddWord P1Life.oddWord (j+1) origin X Y) (mendPacket j)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) (X,Y)
        CutFrame centerWord centerWord j origin V.1 V.2 state) := by
  intro state records input
  have raw := mendBasePacket_cut_frame j first hj origin ctx enabled X Y state records input
  have same := Replay5.placed_eq (Placement5.pi j) (mendBasePacket j)
    (fun q hq => Placement5.pi_outside j q hj hq) state records
    (cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (cutFrame_zero_region centerWord centerWord _ origin ctx _ _ _ raw.2)
  change run (mendPacket j) records state=run (mendBasePacket j) records state at same
  rw [same]
  exact raw

theorem mendPacket_counts :
    toffoliCount (mendPacket 1)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet false 1)+239 ∧
    measurementCount (mendPacket 1)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet false 1)+234 := by
  have a := cell_count_delta false 1 3 2
  have b := cell_count_delta false 1 4 2
  have c := cellWith_counts false (P1Life.mend (base 760) base (base 2409)) 1 3 2
  have d := route_junction_counts
  have e := cell_counts false 1 3 2
  simp only [mendPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,mendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,toffoliCount_append,
    measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem mendPacket_slots :
    Challenge.gateSlots (mendPacket 1)+112=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet false 1)+3821 := by
  have a := cell_slot_delta false 1 3 2
  have b := cell_slot_delta false 1 4 2
  have c := cellWith_slots false (P1Life.mend (base 760) base (base 2409)) 1 3 2
  have d := slot_junctions (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) false base (base 2409)
  have regular := cellWith_slots false (P1Life.half (base 760) false base (base 2409)) 1 3 2
  have eq : cell false 1 3 2=cellWith false (P1Life.half (base 760) false base (base 2409)) 1 3 2 := rfl
  rw [←eq] at regular
  simp only [Bool.false_eq_true,if_false] at h
  simp only [mendPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,mendBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,Challenge.gateSlots_append]
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at a b
  omega

theorem mstartBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (mstartBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition false 0) (stageTransition_support false 0 (by decide))
    (stage_physical.2.2 false 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition false 1) (stageTransition_support false 1 (by decide))
    (stage_physical.2.2 false 1 (by decide))
  have c3 := cell_physical false j 3 2 hj (by decide)
  have c4 := cell_physical false j 4 2 hj (by decide)
  have m0 := cellWith_physical false _ route_mstart_physical j 4 2 hj (by decide)
  simp only [mstartBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨m0,t0⟩,c3⟩,c4⟩,t1⟩,c4⟩,c3⟩⟩,closing⟩

theorem mendBasePacket_physical (j : Nat) (hj : j<102) : GatePhysical (mendBasePacket j) := by
  have opening := onPacket_physical j hj stageOpen stageOpen_support stage_physical.1
  have closing := onPacket_physical j hj stageClose stageClose_support stage_physical.2.1
  have t0 := onPacket_physical j hj (stageTransition false 0) (stageTransition_support false 0 (by decide))
    (stage_physical.2.2 false 0 (by decide))
  have t1 := onPacket_physical j hj (stageTransition false 1) (stageTransition_support false 1 (by decide))
    (stage_physical.2.2 false 1 (by decide))
  have c3 := cell_physical false j 3 2 hj (by decide)
  have c4 := cell_physical false j 4 2 hj (by decide)
  have m0 := cellWith_physical false _ route_junction_physical.2.2 j 3 2 hj (by decide)
  simp only [mendBasePacket,gatePhysical_append]
  exact ⟨⟨opening,⟨⟨⟨⟨⟨⟨c4,t0⟩,c3⟩,c4⟩,t1⟩,c4⟩,m0⟩⟩,closing⟩

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== odd45: the odd multiplication slice on packets 45..1 =====
/-
# odd45: odd multiplication slice on packets 45..1

The multiplication kernel runs the record packets 84..46, then `mstart` in packet 45, ordinary odd
packets 44..2 and `mend` in packet 1 (`mslice45`; with the record packets, `mdslice`).  The slice
saves 164 T / 389 M against the record packets 45..1 and uses 2120 more gate slots.
-/
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

theorem odd45_program_false_add (p : Nat → Program) :
    ∀ (a b j : Nat),
      PacketSequence.program false p j (a + b) =
        PacketSequence.program false p (j + a) b ++
          PacketSequence.program false p j a
  | 0, b, j => by simp [PacketSequence.program]
  | a + 1, b, j => by
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h]
      simp only [PacketSequence.program, Bool.false_eq_true, if_false,
        List.append_assoc]
      rw [odd45_program_false_add p a b (j + 1)]
      have hj : j + 1 + a = j + (a + 1) := by omega
      rw [hj, List.append_assoc]

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport
open ECDSAAdd.Entrant.Rolling1588
end ECDSAAdd.Entrant.RouteA.Rolling1588
end

-- ===== cell support: the hosted odd45 multiplication slice is physical, stays inside the
-- record packets 45..1 and, on a record cut frame at cut 46, ends where the record packets 45..1 end =====
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

end ECDSAAdd.Entrant.RouteA.Rolling1588
end

section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.StairLoanGroupSupport
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
attribute [local irreducible] wires StairLoan.half760Loan StairGroups.halfWindow StairGroups.cell Rolling1588.onPacket

/-- an odd multiplication cell stays inside the record cell. -/
theorem c45_oddCell_sub_false (P : Program) (hP : RouteA.Rolling1588.HalfSupport P) (j active hole : Nat) :
    wires (RouteA.Rolling1588.cellWith false P j active hole) ⊆ wires (Rolling1588.cell false j active hole) := by
  have h : wires (RouteA.Rolling1588.halfWindowWith P j active hole) ⊆
      wires (Rolling1588.halfWindow false j active hole) := by
    unfold RouteA.Rolling1588.halfWindowWith Rolling1588.halfWindow
    exact loanWindow_sub _ _ _ _ _ (rename_sub _ _ _ (hP.trans RouteA.Rolling1588.record_half_lower_false))
  simp only [RouteA.Rolling1588.cellWith,Rolling1588.cell,Bool.false_eq_true,if_false]
  exact append_sub _ _ _ _ (Finset.Subset.refl _) h

theorem c45_oddPlainCell_sub_false (j active hole : Nat) :
    wires (RouteA.Rolling1588.cell false j active hole) ⊆ wires (Rolling1588.cell false j active hole) := by
  have h := c45_oddCell_sub_false _ (RouteA.Rolling1588.half_support false) j active hole
  simpa only [RouteA.Rolling1588.cellWith,RouteA.Rolling1588.cell,RouteA.Rolling1588.halfWindow,
    Bool.false_eq_true,if_false] using h

theorem c45_oddBasePacket_sub_false (j : Nat) :
    wires (RouteA.Rolling1588.basePacket false j) ⊆ wires (Rolling1588.basePacket false j) := by
  have c := fun active hole => c45_oddPlainCell_sub_false j active hole
  simp only [RouteA.Rolling1588.basePacket,Rolling1588.basePacket,Bool.false_eq_true,if_false]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 4 2) (Finset.Subset.refl _)) (c 3 2)) (c 4 2))
    (Finset.Subset.refl _)) (c 4 2)) (c 3 2)

/-- the `mstart` packet stays inside the record multiplication packet. -/
theorem c45_mstartBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.mstartBasePacket j) ⊆ wires (Rolling1588.basePacket false j) := by
  have c := fun active hole => c45_oddPlainCell_sub_false j active hole
  have hm := c45_oddCell_sub_false _ RouteA.Rolling1588.mstart_support j 4 2
  simp only [RouteA.Rolling1588.mstartBasePacket,Rolling1588.basePacket,Bool.false_eq_true,if_false]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ hm (Finset.Subset.refl _)) (c 3 2)) (c 4 2))
    (Finset.Subset.refl _)) (c 4 2)) (c 3 2)

/-- the `mend` packet stays inside the record multiplication packet. -/
theorem c45_mendBasePacket_sub (j : Nat) :
    wires (RouteA.Rolling1588.mendBasePacket j) ⊆ wires (Rolling1588.basePacket false j) := by
  have c := fun active hole => c45_oddPlainCell_sub_false j active hole
  have hd := c45_oddCell_sub_false _ RouteA.Rolling1588.mend_support j 3 2
  simp only [RouteA.Rolling1588.mendBasePacket,Rolling1588.basePacket,Bool.false_eq_true,if_false]
  refine append_sub _ _ _ _ (append_sub _ _ _ _ (Finset.Subset.refl _) ?_) (Finset.Subset.refl _)
  exact append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _ (append_sub _ _ _ _
    (append_sub _ _ _ _ (append_sub _ _ _ _ (c 4 2) (Finset.Subset.refl _)) (c 3 2)) (c 4 2))
    (Finset.Subset.refl _)) (c 4 2)) hd

theorem c45_oddPacket_sub_false (j : Nat) :
    wires (RouteA.Rolling1588.packet false j) ⊆ wires (Rolling1588.packet false j) := by
  unfold RouteA.Rolling1588.packet Rolling1588.packet
  exact rename_sub _ _ _ (c45_oddBasePacket_sub_false j)

end ECDSAAdd.Entrant.StairLoanGroupSupport
end
-- ===== end odd multiplication cell =====


-- ==== part Main ====
-- Main = PrizeTail8dd9f9e60 ++ PrizeTail05e06b1e9 ++ PrizeTaila22007f05 ++ Main
-- ==== begin PrizeTail8dd9f9e60 ====
section

section

namespace ECDSAAdd.Entrant.Stair44PhaseSites
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairRestSupport StairConcreteAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

abbrev holes := StairPhysicalInventory.physicalHoles
abbrev valid (q : Nat) := Stair44OuterSites.fit (StairPlaceFast.phasePlaceB q)

private theorem ppiList {q : Nat} (h : PPI q) : q ∈ ppList := by
  unfold PPI at h
  simp only [ppList,List.mem_append,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false]
  omega

private def rawReady (q : Wire) : Bool := decide (q ∈ Stair44WalkSites.retired) || valid q
private theorem firstTable : ppList.all (fun x => rawReady (Stair44WalkMap.first x)) = true := by decide +kernel
private theorem restTable : ppList.all (fun x => rawReady (Stair44WalkMap.rest x)) = true := by decide +kernel

private theorem rebased {P : Program} (c : Equiv.Perm Wire)
    (table : ppList.all (fun x => rawReady (c x)) = true) (seen : ∀ q ∈ wires P, PPI q) :
    ∀ q ∈ wires (renameProgram c P), rawReady q = true := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  exact List.all_eq_true.mp table x (ppiList (seen x hx))

theorem walk {P : Program} (ready : ∀ q ∈ wires P, rawReady q = true)
    (free : ∀ q ∈ Stair44WalkSites.retired, q ∉ wires P) : PieceOK holes PP P := by
  apply Stair44OuterSites.fits
  intro q hq
  have t := ready q hq
  simp only [rawReady,Bool.or_eq_true,decide_eq_true_eq] at t
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace q) = true
  rw [StairPlaceFast.phasePlace_eqB]
  exact t.resolve_left (fun bad => free q bad hq)

attribute [local irreducible] wires Rolling1588TickGap.forward Rolling1588.reverse renameProgram

theorem forward (d : Bool) (n : Nat) (bound : 16+n ≤ 506) : PieceOK holes PP (Stair44WalkRun.forward d n) := by
  have orig := tickGap_forward_ppi d (15+n) (by omega)
  rw [forward_append d 15 1 n,wires_append] at orig
  apply walk (P := Stair44WalkRun.forward d n) (free := fun q hq => (Stair44WalkSites.routed_free d n bound q hq).1)
  intro q hq
  rw [Stair44WalkRun.forward,wires_append,Finset.mem_union] at hq
  exact hq.elim (rebased (P := Rolling1588TickGap.forward d 1 15) _ firstTable (fun x hx => orig x (Finset.mem_union_left _ hx)) q)
    (rebased (P := Rolling1588TickGap.forward d 16 n) _ restTable (fun x hx => orig x (Finset.mem_union_right _ hx)) q)
  
theorem backward (d : Bool) (n : Nat) (bound : 16+n ≤ 506) : PieceOK holes PP (Stair44WalkRun.backward d n) := by
  have orig := reverse_ppi d (15+n) (by omega)
  rw [reverse_append d 15 1 n,wires_append] at orig
  apply walk (P := Stair44WalkRun.backward d n) (free := fun q hq => (Stair44WalkSites.routed_free d n bound q hq).2)
  intro q hq
  rw [Stair44WalkRun.backward,wires_append,Finset.mem_union] at hq
  exact hq.elim (rebased (P := Rolling1588.reverse d 16 n) _ restTable (fun x hx => orig x (Finset.mem_union_left _ hx)) q)
    (rebased (P := Rolling1588.reverse d 1 15) _ firstTable (fun x hx => orig x (Finset.mem_union_right _ hx)) q)

set_option exponentiation.threshold 1024 in
private theorem nativeFits (x : Wire) (hx : x ∈ wires (FrontierEntry1591NativeH.inverse base)) :
    valid (Stair44WalkMap.first x) = true := by
  have h := (FrontierEntry1591Native.support base base_pool_nodup).2
    (FrontierEntry1591NativeH.wires_sub base base_pool_nodup hx)
  have m : x ≠ base 1797 ∧ x ∈ insert (base 511) (NativeFirstDirect.prefixSites base).toFinset :=
    Finset.mem_erase.mp h
  rcases Finset.mem_insert.mp m.2 with eq | inside
  · rw [eq]; decide +kernel
  · have table : (NativeFirstDirect.prefixSites base).all
        (fun z => decide (z = base 1797) || valid (Stair44WalkMap.first z)) = true := by decide +kernel
    have t := List.all_eq_true.mp table x (List.mem_toFinset.mp inside)
    simp only [Bool.or_eq_true,decide_eq_true_eq] at t
    exact t.resolve_left m.1

theorem native : PieceOK holes PP (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)) := by
  apply Stair44OuterSites.fits
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace _) = true
  rw [StairPlaceFast.phasePlace_eqB]
  exact nativeFits _ hx

end ECDSAAdd.Entrant.Stair44PhaseSites

end

section

/-! Five-wire square-tail routing on the public e9dca31f staircase.
The comparator and its successor use different scratch lifetimes. -/
section
namespace ECDSAAdd.Entrant.E1Reflected.Square31
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
def afterCompare (w : Nat → Wire) (g : Wire) (k : Nat) : Program :=
  (parGates w g k++rotateRight (kR w)++notRegister (kR w))++prodPart w g++loadK w g k++E1WholeKAdd52Research.flagKAdd52 w++loadK w g k++
  [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]++
  copyRegister none (wireBlock w 770 257) (hpR w)++hAddT w++[.CX (w 1028) (w 0),.X (w 0)]++
  loadT w g k++eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514)++loadT w g k++
  [.measureX (w 721) [] [.CZ g (w 1028)]]


theorem split (w : Nat → Wire) (g : Wire) (k : Nat) :
    merged w g k = comparePart w g k ++ afterCompare w g k := by
  simp only [merged, afterCompare, List.append_assoc]
def mS5 (w : Nat → Wire) (g : Wire) : List Wire :=
  wireBlock w 0 258 ++ [w 513, w 514] ++ wireBlock w 770 515 ++ wireBlock w 1540 258 ++
    [w 721, w 722, g]

theorem in_m5 (w : Nat → Wire) (g : Wire) (i : Nat)
    (hi : (i < 258 ∨ i = 513 ∨ i = 514) ∨ (770 ≤ i ∧ i < 1285) ∨ (1540 ≤ i ∧ i < 1798) ∨
      i = 721 ∨ i = 722) : w i ∈ mS5 w g := by
  have hA : ∀ a n : Nat, a ≤ i → i < a + n → w i ∈ wireBlock w a n := fun a n h1 h2 =>
    List.mem_map.mpr ⟨i, by simp only [List.mem_range'_1]; omega, rfl⟩
  simp only [mS5, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases hi with (h|h|h)|h|h|h|h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (hA 0 258 (by omega) (by omega)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (congrArg w h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (congrArg w h)))))
  · exact Or.inl (Or.inl (Or.inr (hA 770 515 (by omega) (by omega))))
  · exact Or.inl (Or.inr (hA 1540 258 (by omega) (by omega)))
  · exact Or.inr (Or.inl (congrArg w h))
  · exact Or.inr (Or.inr (Or.inl (congrArg w h)))

theorem blk_m5 (w : Nat → Wire) (g : Wire) (a n : Nat)
    (h : a + n ≤ 258 ∨ (770 ≤ a ∧ a + n ≤ 1285) ∨ (1540 ≤ a ∧ a + n ≤ 1798)) :
    ∀ q ∈ wireBlock w a n, q ∈ mS5 w g := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  exact in_m5 w g i (by omega)

theorem g_m5 (w : Nat → Wire) (g : Wire) : g ∈ mS5 w g :=
  List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem lsub5 (w : Nat → Wire) (g : Wire) (l : List Wire) (h : ∀ q ∈ l, q ∈ mS5 w g) :
    l.toFinset ⊆ (mS5 w g).toFinset := by
  intro q hq; exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem gate_sub5 (w : Nat → Wire) (g : Wire) (i : Instr) (h : ∀ q ∈ i.wires, q ∈ mS5 w g) :
    wires [i] ⊆ (mS5 w g).toFinset := by
  intro q hq
  simp only [wires, Finset.union_empty] at hq
  exact List.mem_toFinset.mpr (h q hq)

theorem afterCompare_support (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (afterCompare w g k) ⊆ (mS5 w g).toFinset := by
  have B := blk_m5 w g
  have I := in_m5 w g
  have G := g_m5 w g
  have mskH (c : Wire) (hc : c∈mS5 w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mS5 w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have cx (a b : Nat) (ha : (a < 258 ∨ a = 513 ∨ a = 514) ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : (b < 258 ∨ b = 513 ∨ b = 514) ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mS5 w g).toFinset := gate_sub5 w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : (b < 258 ∨ b = 513 ∨ b = 514) ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mS5 w g).toFinset := gate_sub5 w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mS5 w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mS5 w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub5 w g _ (B 770 258 (by omega))
  have hNot : wires (notRegister (kR w))⊆(mS5 w g).toFinset := by
    rw [notRegister_wires]
    exact lsub5 w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mS5 w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub5 <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mS5 w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub5 w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mS5 w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (E1WholeKAdd52Research.flagKAdd52 w)⊆(mS5 w g).toFinset := by
    have sub := E1ResourceBridge52Research.flag_support52 w
    rw [← kAdd_literal w] at sub
    apply sub.trans
    refine Finset.union_subset hKOld ?_
    exact Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr (I 1028 (by omega)))
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mS5 w g).toFinset := by
    apply gate_sub5; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mS5 w g).toFinset := by
    apply gate_sub5; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mS5 w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub5; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mS5 w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mS5 w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub5 w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mS5 w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mS5 w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mS5 w g).toFinset := (hAddT_wires w).trans hH
  simp only [afterCompare,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hP,hR'⟩,hNot⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩
end ECDSAAdd.Entrant.E1Reflected.Square31
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore
set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 4000000
def placed (p : Program) := renameProgram (pmapR Baselines.layout) p
def comparePhase (k : Fp) := placed (E1Reflected.comparePart base (base 2400) k.val)
def suffix (k : Fp) := placed (E1Reflected.Square31.afterCompare base (base 2400) k.val)
def moves : List (Wire × Wire) := (List.range 5).map fun i => (4835+i, pmapR Baselines.layout (base (258+i)))
def candidate (k : Fp) := hostRename StairSquareEntryR.entryPairs (comparePhase k) ++ hostRename moves (suffix k)
theorem stock_split (k : Fp) : entryR Baselines.layout k = comparePhase k ++ suffix k := by
  unfold entryR comparePhase suffix placed
  rw [E1Reflected.Square31.split]
  simp only [renameProgram, List.map_append]
attribute [local irreducible] wires E1Reflected.Square31.afterCompare E1Reflected.comparePart E1Reflected.merged pmapR Baselines.layout
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairSquareHolesCore
open ECDSAAdd Arithmetic
def permutation : List (Wire × Wire) → Equiv.Perm Wire
  | [] => Equiv.refl _
  | (a,b)::ps => (permutation ps).trans (Equiv.swap a b)
theorem fused (ps : List (Wire × Wire)) (p : Program) :
    hostRename ps p = renameProgram (permutation ps) p := by
  induction ps with
  | nil =>
    change p = renameProgram id p
    have ec (c : Correction) : renameCorrection id c = c := by cases c <;> rfl
    have ei (i : Instr) : renameInstr id i = i := by
      cases i <;> simp [renameInstr,funext ec]
    simp [renameProgram,funext ei]
  | cons ab ps ih =>
    rw [hostRename, ih, renameProgram_comp]
    rfl
theorem decode (ps : List (Wire × Wire)) (p : Program) (m : List Bool) (s : State) :
    pullState (permutation ps) (run (hostRename ps p) m s) =
        run p m (pullState (permutation ps) s) := by
  rw [fused]
  exact run_rename _ (permutation ps).injective _ _ _
end ECDSAAdd.Entrant.StairSquareHolesCore
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open Arithmetic Secp256k1 E1ReflectedPlacement StairSquareHolesCore
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem counts (k : Fp) : toffoliCount (candidate k) = toffoliCount (entryR Baselines.layout k) ∧
    measurementCount (candidate k) = measurementCount (entryR Baselines.layout k) ∧
    Challenge.gateSlots (candidate k) = Challenge.gateSlots (entryR Baselines.layout k) := by
  rw [stock_split]
  simp only [candidate,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    (hostRename_counts _ _).1,(hostRename_counts _ _).2,hostRename_slots,and_self]
theorem transport (k : Fp) (m : List Bool) (s : State)
    (compareRun : ∀ t, run (hostRename StairSquareEntryR.entryPairs (comparePhase k)) t s =
                         run (comparePhase k) t s)
    (clean : ∀ t, pullState (permutation moves) (run (comparePhase k) t s) =
                  run (comparePhase k) t s) :
    pullState (permutation moves) (run (candidate k) m s) = run (entryR Baselines.layout k) m s := by
  rw [stock_split]
  simp only [candidate,run_append,(hostRename_counts _ _).2,compareRun,decode,clean]
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore
set_option maxHeartbeats 1600000
attribute [local irreducible] wires run E1Reflected.merged E1Reflected.comparePart
  E1Reflected.Square31.afterCompare pmapR Baselines.layout
abbrev cleanIndex (i : Nat) : Prop := i < 515 ∨ (1026 ≤ i ∧ i < 1285) ∨
  (1540 ≤ i ∧ i < 1798) ∨ i = 721 ∨ i = 722
theorem atPool (i : Nat) (hi : cleanIndex i) : pmapR Baselines.layout (base i) ∈ Baselines.layout.dialogPool := by
  apply pmap_pool _ Baselines.layout_widths Baselines.layout_nodup
  · exact List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i (by unfold cleanIndex at hi; omega))
  · intro h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    unfold cleanIndex at hi
    omega
  · intro e
    have := base_injective e
    unfold cleanIndex at hi
    omega
theorem compareZero (k : Fp) (s : State) (m : List Bool)
    (hc : regValue Baselines.layout.dialogPool s.basis = 0)
    (i : Nat) (hi : cleanIndex i) (lo : 256 ≤ i) (nf : i ≠ 514) :
    (run (comparePhase k) m s).basis (pmapR Baselines.layout (base i)) = false := by
  let f := pmapR Baselines.layout
  let t := pullState f s
  have clean (j : Nat) (hj : cleanIndex j) : t.basis (base j) = false :=
    (regValue_zero _ _).mp hc _ (atPool j hj)
  have bk (a n : Nat) (h : a+n ≤ 514) : ∀ q ∈ wireBlock base a n, t.basis q=false := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact clean j (Or.inl (by omega))
  have ns (j : Nat) (hj : 256 ≤ j) : base j ∉ E1Reflected.srcR base := by
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hv
    have := base_injective e
    omega
  have diff (u v : Nat) (ne : u ≠ v) : base u ≠ base v := fun e => ne (base_injective e)
  have cf := E1Reflected.cfCompare base (base 2400) base_pool_nodup t.basis (t.basis (base 514))
    k.val _ (by have := k.val_lt; change k.val < p at this; have := E1Reflected.p_val; omega)
    rfl (bk 256 256 (by decide)) (clean 513 (Or.inl (by decide)))
    (ns 2400 (by decide)) (diff _ _ (by decide)) t m
    ⟨(regValue_zero _ _).mpr (bk 0 256 (by decide)), rfl, fun _ _ _ => rfl⟩
  have sup : wires (E1Reflected.comparePart base (base 2400) k.val) ⊆ S := by
    intro q hq
    apply mergedR_S k.val
    rw [E1Reflected.Square31.split,wires_append]
    exact Finset.mem_union_left _ hq
  have hS : base i ∈ S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i
    (by unfold cleanIndex at hi; omega))
  have mapped := run_rename_pool f S (pmap_inj _ Baselines.layout_widths Baselines.layout_nodup)
    _ sup m t s rfl (fun _ _ => rfl)
  exact ((mapped.2 _ hS).trans (cf.2.2.2 _ (ns i lo) (diff _ _ nf))).trans (clean i hi)
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.E1Reflected
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum
set_option linter.unusedSimpArgs false
theorem compare_support (w : Nat → Wire) (g : Wire) (k : Nat) : wires (comparePart w g k) ⊆ (mS5 w g).toFinset := by
  have B := blk_m5 w g
  have I := in_m5 w g
  have G := g_m5 w g
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mS5 w g).toFinset := by
    rw [notRegister_wires]; exact lsub5 w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))⊆(mS5 w g).toFinset := by
    rw [(compareLt_wires none (xR w) (srcR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,srcR,xR,wireBlock_length])).1]
    apply lsub5; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 770 256 (by omega) q hq
    · exact B 0 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mS5 w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨mskS _,cmp⟩,mskS _⟩
  exact hC
end ECDSAAdd.Entrant.E1Reflected
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore StairSquareEntryR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem placement : [(1542,4835),(1026,4836),(1541,4837),(721,4838),(722,4839),(258,4373),
    (259,4374),(260,4375),(261,4376),(262,4377),(514,4629)].all
      (fun (i,q) => pmapR Baselines.layout (base i) == q) = true := by decide +kernel
attribute [local irreducible] wires run E1Reflected.merged E1Reflected.comparePart
  E1Reflected.Square31.afterCompare pmapR Baselines.layout
theorem compareFree (k : Fp) : host512 ∉ wires (comparePhase k) := by
  intro hu
  unfold comparePhase placed at hu
  rw [renameProgram_support] at hu
  obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp hu
  have inS : y ∈ S := by
    apply mergedR_S k.val
    rw [E1Reflected.Square31.split,wires_append]
    exact Finset.mem_union_left _ hy
  have ib : base 512 ∈ S := List.mem_toFinset.mpr (E1Merge.in_mSites _ _ _ (Or.inl (by decide)))
  have same := pmap_inj L0 Baselines.layout_widths Baselines.layout_nodup _ inS _ ib (eq.trans StairSquareEntryR.pmapR_512.symm)
  have mem := List.mem_toFinset.mp (E1Reflected.compare_support base (base 2400) k.val hy)
  exact E1Reflected.base512_not_m5 (same ▸ mem)
theorem compareExact (k : Fp) (s : State) (hc : regValue L0.dialogPool s.basis=0) (m : List Bool) :
    run (hostRename entryPairs (comparePhase k)) m s = run (comparePhase k) m s := by
  apply hostRename_run_eq
  all_goals intro ab hab; simp only [entryPairs,List.mem_singleton] at hab; subst ab
  · rw [← StairSquareEntryR.pmapR_511]
    exact (regValue_zero _ _).mp hc _ (atPool 511 (Or.inl (by decide)))
  · rw [← StairSquareEntryR.pmapR_512]
    exact (regValue_zero _ _).mp hc _ (atPool 512 (Or.inl (by decide)))
  · rw [← StairSquareEntryR.pmapR_511]
    exact compareZero k s m hc 511 (Or.inl (by decide)) (by decide) (by decide)
  · exact compareFree k
theorem samePerm (ps : List (Wire × Wire)) (s : State)
    (eq : ∀ a ∈ ps, s.basis a.1 = s.basis a.2) : pullState (permutation ps) s = s := by
  have h (q : Wire) : s.basis (permutation ps q) = s.basis q := by
    induction ps generalizing q with
    | nil => rfl
    | cons a ps ih =>
      have eq1 := eq a List.mem_cons_self
      have eq2 := ih (fun x hx => eq x (List.mem_cons_of_mem _ hx)) q
      let v := permutation ps q
      change s.basis (Equiv.swap a.1 a.2 v) = s.basis q
      by_cases h1 : v=a.1
      · rw [h1,Equiv.swap_apply_left,←eq1,←h1]; exact eq2
      by_cases h2 : v=a.2
      · rw [h2,Equiv.swap_apply_right,eq1,←h2]; exact eq2
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact eq2
  exact State.extensionality _ _ rfl (funext h)
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed E1QubitPlacement E1ReflectedPlacement StairSquareHolesCore
attribute [local irreducible] wires run pmapR Baselines.layout
theorem afterCompareClean (k : Fp) (s : State) (hc : regValue Baselines.layout.dialogPool s.basis=0)
    (m : List Bool) : pullState (permutation moves) (run (comparePhase k) m s) = run (comparePhase k) m s := by
  apply samePerm
  intro pair hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  have h := List.mem_range.mp hi
  change (run (comparePhase k) m s).basis (4835+i) =
         (run (comparePhase k) m s).basis (pmapR Baselines.layout (base (258+i)))
  rw [compareZero k s m hc (258+i) (Or.inl (by omega)) (by omega) (by omega)]
  let raw := [1542,1026,1541,721,722]
  have elem : (raw[i]!,4835+i) ∈ [(1542,4835),(1026,4836),(1541,4837),(721,4838),(722,4839),
      (258,4373),(259,4374),(260,4375),(261,4376),(262,4377),(514,4629)] := by
    interval_cases i <;> decide
  have bound : cleanIndex (raw[i]!) ∧ 256≤raw[i]! ∧ raw[i]!≠514 := by interval_cases i <;> decide
  have pm : pmapR Baselines.layout (base (raw[i]!)) = 4835+i :=
    eq_of_beq (List.all_eq_true.mp placement _ elem)
  rw [← pm]
  exact compareZero k s m hc _ bound.1 bound.2.1 bound.2.2
theorem decoded (k : Fp) (s : State) (hc : regValue Baselines.layout.dialogPool s.basis=0) (m : List Bool) :
    pullState (permutation moves) (run (candidate k) m s) = run (entryR Baselines.layout k) m s :=
  transport k m s (compareExact k s hc) (afterCompareClean k s hc)
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
set_option maxHeartbeats 1200000
attribute [local irreducible] wires run E1Reflected.merged pmapR Baselines.layout
def exitClean := [1542,1541,721,722,258,259,260,261,262,514,500,501]
theorem stockExit (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) (i : Nat) (hi : i∈exitClean) :
    (run (entryR Baselines.layout k) m s).basis (pmapR Baselines.layout (base i)) = false := by
  let f := pmapR Baselines.layout
  let t := pullState f s
  have cl (j : Nat) (hj : cleanIndex j) : t.basis (base j) = false :=
    (regValue_zero _ _).mp hc _ (atPool j hj)
  have blk (a n : Nat) (h : a+n ≤ 515 ∨ (1026 ≤ a ∧ a+n ≤ 1285) ∨ (1540 ≤ a ∧ a+n ≤ 1798)) :
      regValue (wireBlock base a n) t.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range'_1] at hj
    exact cl j (by unfold cleanIndex; omega)
  have xv : regValue (E1Reflected.xR base) t.basis=X := by
    change regValue (wireBlock base 770 256) (fun q => s.basis (f q))=X
    rw [regValue_pull,pmap_x Baselines.layout Baselines.layout_widths Baselines.layout_nodup,hx]
  have kv : regValue (E1Reflected.kR base) t.basis=X := by
    rw [E1Reflected.kR_x base base_pool_nodup,xv,blk 1026 2 (by decide)]; simp
  have c (i : Nat) (h : cleanIndex i) := cl i h
  have tri := E1Reflected.merged_triple base (base 2400) base_pool_nodup g2400 k.val k.isLt t.basis X hX
    (fun j a b => cl j (Or.inl (by omega))) (cl 513 (Or.inl (by decide)))
    ((regValue_zero _ _).mp (blk 1540 257 (by decide))) (cl 1797 (by decide)) t m
    ⟨blk 0 258 (by decide),kv,blk 1029 256 (by decide),cl 1028 (by decide),cl 514 (by decide),
      cl 721 (by decide),cl 722 (by decide),fun _ _ => rfl⟩
  have range : cleanIndex i := by simp [exitClean] at hi; unfold cleanIndex; omega
  have isS : base i ∈ S := List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) i
    (by unfold cleanIndex at range; omega))
  have mapped := run_rename_pool f S (pmap_inj _ Baselines.layout_widths Baselines.layout_nodup) _
    (mergedR_S k.val) m t s rfl (fun _ _ => rfl)
  rw [entryR,mapped.2 _ isS]
  obtain ⟨_,_,_,_,hf,hg,hp,frame⟩ := tri.2
  by_cases eq1 : i=721
  · subst i; exact hg
  by_cases eq2 : i=722
  · subst i; exact hp
  by_cases eq3 : i=514
  · subst i; exact hf
  apply (frame (base i) ?_).trans (cl i range)
  simp [exitClean] at hi
  simp only [E1Reflected.mutL,E1Reflected.hR,E1Reflected.kR,E1Reflected.tR,wireBlock,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map,List.mem_range'_1,not_or]
  repeat' apply And.intro
  all_goals first
    | intro ⟨j,hj,ej⟩; have := base_injective ej; omega
    | intro ej; have := base_injective ej; omega
end ECDSAAdd.Entrant.StairEntryRehost
end

section
namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 MappedCompressed E1QubitPlacement E1ReflectedPlacement StairSquareHolesCore
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
def physicalMoves : List (Wire × Wire) := [(4835,4373),(4836,4374),(4837,4375),(4838,4376),(4839,4377)]
theorem moves_eq : moves = physicalMoves := by decide +kernel
def routed (k : Fp) := candidate k ++ swapBits 4374 4629
def landing : Equiv.Perm Wire := Equiv.swap 4836 4629
def touchedSites : List Wire := [4835,4373,4836,4374,4837,4375,4838,4376,4839,4377,4629]
def zeroSites : List Wire := [4835,4373,4374,4837,4375,4838,4376,4839,4377,4629]
def beforeTransfer (q : Wire) := (permutation physicalMoves).symm (Equiv.swap 4374 4629 q)
theorem finiteCheck : touchedSites.all (fun q =>
    beforeTransfer q == landing q || (zeroSites.contains (beforeTransfer q) && zeroSites.contains (landing q))) := by decide +kernel
theorem offSites (q : Wire) (hq : q ∉ touchedSites) : beforeTransfer q = landing q := by
  simp [touchedSites] at hq
  simp [beforeTransfer, physicalMoves, permutation, landing, Equiv.swap_apply_def, *]
theorem realSwap (a b : Wire) (hab : a≠b) (s : State) (m : List Bool) :
    run (swapBits a b) m s = pullState (Equiv.swap a b) s := by
  apply congrArg₂ State.mk
  · rfl
  · funext i
    by_cases h : i=a
    · subst i; cases h1:s.basis a <;> cases h2:s.basis b <;>
        simp [swapBits,run,writeBit,pullState,Equiv.swap_apply_def,hab,Ne.symm hab,h1,h2]
    by_cases k : i=b
    · subst i; cases h1:s.basis a <;> cases h2:s.basis b <;>
        simp [swapBits,run,writeBit,pullState,Equiv.swap_apply_def,hab,Ne.symm hab,h1,h2]
    · simp [swapBits,run,writeBit,pullState,Equiv.swap_apply_def,h,k]
attribute [local irreducible] wires run E1Reflected.merged pmapR Baselines.layout
theorem stockZeros (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) :
    ∀ q ∈ zeroSites, (run (entryR Baselines.layout k) m s).basis q = false := by
  intro q hq
  have e : ∃ i ∈ exitClean, (i,q) ∈ [(1542,4835),(1026,4836),(1541,4837),(721,4838),(722,4839),
      (258,4373),(259,4374),(260,4375),(261,4376),(262,4377),(514,4629)] := by
    simp only [zeroSites,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨1542,by decide,by decide⟩
    · exact ⟨258,by decide,by decide⟩
    · exact ⟨259,by decide,by decide⟩
    · exact ⟨1541,by decide,by decide⟩
    · exact ⟨260,by decide,by decide⟩
    · exact ⟨721,by decide,by decide⟩
    · exact ⟨261,by decide,by decide⟩
    · exact ⟨722,by decide,by decide⟩
    · exact ⟨262,by decide,by decide⟩
    · exact ⟨514,by decide,by decide⟩
  obtain ⟨i,hi,eq⟩ := e
  have p : pmapR Baselines.layout (base i) = q := eq_of_beq (List.all_eq_true.mp placement _ eq)
  rw [← p]
  exact stockExit k s m X hx hX hc i hi
theorem fullRun (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) :
    run (routed k) m s = pullState landing (run (entryR Baselines.layout k) m s) := by
  rw [routed,run_append,realSwap _ _ (by decide),run_take]
  have d := decoded k s hc m
  rw [moves_eq] at d
  apply State.extensionality
  · have eq := congrArg State.phase d
    exact eq
  · funext q
    let v := beforeTransfer q
    have val := congrArg (fun t : State => t.basis v) d
    change (run (candidate k) m s).basis (permutation physicalMoves v) =
        (run (entryR Baselines.layout k) m s).basis v at val
    simp only [v,beforeTransfer,Equiv.apply_symm_apply] at val
    change (run (candidate k) m s).basis (Equiv.swap 4374 4629 q) =
      (run (entryR Baselines.layout k) m s).basis (landing q)
    rw [val]
    change (run (entryR Baselines.layout k) m s).basis (beforeTransfer q) = _
    by_cases hq : q ∈ touchedSites
    · have h := List.all_eq_true.mp finiteCheck q hq
      simp only [Bool.or_eq_true,beq_iff_eq,Bool.and_eq_true,List.contains_iff_mem] at h
      rcases h with eq|⟨ha,hb⟩
      · rw [eq]
      · rw [stockZeros k s m X hx hX hc _ ha,stockZeros k s m X hx hX hc _ hb]
    · rw [offSites q hq]
end ECDSAAdd.Entrant.StairEntryRehost
end

end

section

namespace ECDSAAdd.Entrant.StairSquareKernel26C
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout StairSquareHolesCore StairSquareKernel26 StairSquareContract
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run wires
theorem domain_cases (q : Wire) (hq : q ∈ StairSqLoopA.hostDomain) :
    q ∈ holes K0 ∨ ∃ k, 99 ≤ k ∧ k < 123 ∧ k ≠ 108 ∧ q=(LowZero18LowK.ktmp K0).getD k 0 := by
  rcases List.mem_append.mp hq with old|fresh
  · exact holes39_cases q old
  · obtain ⟨n,hi,rfl⟩ := List.mem_map.mp fresh
    simp only [List.mem_range'_1] at hi
    exact Or.inl (holes_pool_of L0 hw0 n (by omega) (by omega))

theorem kA_run_eq44 (hs : List Wire) (body : Program) (hb : BodyAOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrA hs body) m t=run (recBrA body) m t := by
  have p := B3CarryPort.pool1540_facts L0 hw0 hn0
  rw [newBrA_eq,recBrA_eq]
  exact branchA_run_eq K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs)
    (regValue K0.core.low t.basis) (regValue K0.core.out t.basis) pre.outLt t m
    rfl rfl pre.prod0 pre.clean pre.sum0 pre.ext0 D0 p.1 p.2.1 pre.d0 body hb.support hb.eUfree hb.frame
    (fun ab h => hav _ (psOf_mem hs ab h))

theorem kB_run_eq_of_frame44 (hs : List Wire) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t)
    (frame : ∀ q, q∉K0.core.out → (run (recBrB body) m t).basis q=t.basis q) :
    run (newBrB hs body) m t=run (recBrB body) m t := by
  rw [newBrB_eq,recBrB_eq]
  rw [recBrB_eq] at frame
  exact branchB_run_eq_of_frame K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
    (fun ab h => hav _ (psOf_mem hs ab h)) t m pre.clean pre.prod0 pre.ext0 frame

theorem kB_run_eq44 (hs : List Wire) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrB hs body) m t=run (recBrB body) m t :=
  kB_run_eq_of_frame44 hs body hb hav t m pre (recBrB_correct body hb t m pre).2.2

theorem kC_run_eq44 (hs : List Wire) (body : Program) (hb : BodyCOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrC hs body) m t=run (recBrC body) m t := by
  have p := B3CarryPort.pool1540_facts L0 hw0 hn0
  have bound := low_sum_bound K0 hwK t pre.sum0
  rw [newBrC_eq,recBrC_eq]
  exact branchC_run_eq K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs)
    (regValue K0.core.low t.basis) (regValue K0.core.sum t.basis) (regValue K0.core.out t.basis) pre.outLt t m
    rfl rfl bound rfl pre.prod0 pre.clean pre.ext0 D0 p.1 p.2.1 pre.d0 body hb.support hb.frame
    (fun ab h => hav _ (psOf_mem hs ab h))

theorem kA_avoids44 (hs : List Wire) (hsub : ∀ q∈hs, q∈StairSqLoopA.hostDomain) (body : Program) (hb : BodyAOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrA hs body) := by
  rw [newBrA_eq]
  intro q hq
  rcases domain_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchA_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchA_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

theorem kB_avoids44 (hs : List Wire) (hsub : ∀ q∈hs, q∈StairSqLoopA.hostDomain) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrB hs body) := by
  rw [newBrB_eq]
  intro q hq
  rcases domain_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchB_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchB_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

theorem kC_avoids44 (hs : List Wire) (hsub : ∀ q∈hs, q∈StairSqLoopA.hostDomain) (body : Program) (hb : BodyCOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrC hs body) := by
  rw [newBrC_eq]
  intro q hq
  rcases domain_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchC_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchC_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

end ECDSAAdd.Entrant.StairSquareKernel26C

end

section

namespace ECDSAAdd.Entrant.Stair44OuterSites
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairConcreteAssembly StairSiteAvoidance StairSiteEasy Stair44PointMap
set_option maxRecDepth 40000
set_option maxHeartbeats 12000000

attribute [local irreducible] wires renameProgram GatePhysical

private theorem stages : ∀q∈stageList,fit (U (outer q)) = true := by
  intro q hq
  rw [U_fast]
  exact List.all_eq_true.mp (by decide +kernel :
    stageList.all (fun r => fit (StairPlaceFast.uB (outer r)))=true) q hq

theorem outputs : ∀q∈outList,fit (U (outer ((Equiv.swap layout.doubleSelect (layout.core.poolWire 511)) q)))=true := by
  intro q hq
  rw [U_fast]
  exact List.all_eq_true.mp (by decide +kernel :
    outList.all (fun r => fit (StairPlaceFast.uB (outer ((Equiv.swap layout.doubleSelect (layout.core.poolWire 511)) r))))=true) q hq

theorem ys : ∀q∈yList,fit (UG (duringY q))=true := by
  intro q hq
  rw [UG_fast]
  exact List.all_eq_true.mp ysFit q hq

section
variable {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy)

theorem initial : PieceOK StairPhysicalInventory.physicalHoles U
    (encode (FlagTop.stageNew layout (.some hc) (FlagEntry.pkW layout) ++
      AboveFieldPointDevelop.encode (.some hc) ++ AboveFieldPointDevelop.eraseB)) := by
  apply lifted
  intro q hq
  rw [wires_append,wires_append,Finset.mem_union,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · have mem := ControlStageSupportDevelop.stage_support hc h
    rw [stagePorts_eq] at mem
    exact stages q (List.mem_toFinset.mp mem)
  · exact stages q (aux_stageList ((AboveFieldTagDevelop.encoding_support hc).1 h))
  · exact stages q (aux_stageList (AboveFieldPointDevelop.marker_support.1 h))

theorem finalPart : PieceOK StairPhysicalInventory.physicalHoles U
    (encode (AboveFieldPointDevelop.loadB ++ AboveFieldPointDevelop.decode (.some hc) ++
      ControlPointEncodingDevelop.borrowOut (.some hc))) := by
  apply lifted
  intro q hq
  rw [wires_append,wires_append,Finset.mem_union,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · exact stages q (aux_stageList (AboveFieldPointDevelop.marker_support.2 h))
  · exact stages q (aux_stageList ((AboveFieldTagDevelop.encoding_support hc).2 h))
  · unfold ControlPointEncodingDevelop.borrowOut at h
    rw [renameProgram_support] at h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    have hr := OutSpareDevelop.output_support hc hy
    rw [outPorts_eq] at hr
    exact outputs y (List.mem_toFinset.mp hr)
end

theorem entryY (c : Fp) : PieceOK StairPhysicalInventory.physicalHoles UG
    (encodeY (EntryFuseOdd.entryYAllOdd layout c)) := by
  apply lifted
  exact fun q hq => ys q (yList_mem (EntryFuse.fusedY_support layout layout_widths c
    (EntryFuseOdd.entryYAllOdd_wires layout layout_widths c hq)))

theorem exitY (c : Fp) : PieceOK StairPhysicalInventory.physicalHoles UG
    (encodeY (EntryFuseOdd.exitYAllOdd layout c)) := by
  apply lifted
  exact fun q hq => ys q (yList_mem (ExitFusionResearch.exitY_support layout layout_widths c
    (EntryFuseOdd.exitYAllOdd_wires layout layout_widths c hq)))

theorem xs : ∀q∈xList,fit (UG (duringX (E1QubitPlacement.pmapR layout q)))=true := by
  intro q hq
  rw [UG_fast]
  exact xsFit q hq

private theorem placedX {P : Program} (h : wires P ⊆ (tSites base (base 2400)).toFinset) :
    ∀x∈wires (renameProgram (E1QubitPlacement.pmapR layout) P), fit (UG (duringX x))=true := by
  intro x hx
  rw [renameProgram_support] at hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact xs y (List.mem_toFinset.mp (h hy))

theorem entryX (c : Fp) : PieceOK StairPhysicalInventory.physicalHoles UG
    (switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) c)) := by
  apply lifted
  intro x hx
  have sw (w : Wire) (hw : w ∈ wires (FlagEntry.swp (FlagEntry.pkW layout)
      (E1QubitPlacement.pmapR layout (base 514)))) : fit (UG (duringX w))=true := by
    rw [UG_fast]
    exact allSites_sound (by decide +kernel : allSites (fun z => fit (StairPlaceFast.ugB (duringX z)))
      (FlagEntry.swp (FlagEntry.pkW layout) (E1QubitPlacement.pmapR layout (base 514)))=true) w hw
  unfold FlagEntry.entryXNew at hx
  split_ifs at hx
  · rw [wires_append,Finset.mem_union] at hx
    exact hx.elim (sw x) (placedX (tailX_tight base (base 2400) c.val) x)
  · rw [wires_append,wires_append,Finset.mem_union,Finset.mem_union] at hx
    rcases hx with h|h|h
    · exact placedX ccx_tight x h
    · exact sw x h
    · exact placedX (evenTail_tight c.val) x h

def phaseWire (q : Wire) := wireFn2 layout (Rolling1588Lifetime.phaseHost q)
private def piX (q : Wire) := phaseWire (ParityXExitInverse23Kernel.pi q)
private theorem invs : ∀q∈xList,fit (UG (duringX (piX q)))=true := xs

theorem exitX (k : Nat) : ∀q∈wires (ParityXExitInverse23Kernel.x1N k),
    fit (UG (duringX (phaseWire q))) = true := by
  intro x hx
  unfold ParityXExitInverse23Kernel.x1N at hx
  rw [renameProgram_support] at hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
  unfold ParityXExit.programN at hb
  rw [wires_append,Finset.mem_union] at hb
  rcases hb with hb|hb
  · exact invs b (List.mem_toFinset.mp (exitMerge_tight base (base 2400) k
      (ParityXExit.programAll_wires _ _ k (ParityXExit.prefix_sub _ _ k hb))))
  · change fit (UG (duringX (piX b)))=true
    rw [UG_fast]
    exact allSites_sound (by decide +kernel : allSites (fun z => fit (StairPlaceFast.ugB (duringX (piX z))))
      (FlagEntry.swp (base 514) (base 722))=true) b hb

end ECDSAAdd.Entrant.Stair44OuterSites

end

section

namespace ECDSAAdd.Entrant.Stair44OuterY
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
open ParityUniform FlagEntry ParityEven Stair44PointMap
set_option maxRecDepth 30000
set_option maxHeartbeats 1500000

private def poolSite (q : Wire) : Prop := q∈layout.dialogPool ∧ q≠pkW layout
private theorem metadata : ∀ ab∈yPairs, poolSite ab.1 ∧ poolSite ab.2 := by unfold poolSite; decide +kernel

private theorem entries (v : State) (flag : Bool) (clean : regValue layout.dialogPool v.basis=0) :
    YClean (put v (pkW layout) flag) := by
  intro ab hab
  have c (q : Wire) (ok : poolSite q) : (put v (pkW layout) flag).basis q=false := by
    have z := (regValue_zero _ _).mp clean q ok.1
    simpa [put,writeBit,Function.update_apply,ok.2] using z
  exact ⟨c _ (metadata ab hab).1,c _ (metadata ab hab).2⟩

private theorem realPool (s : State) (v : State) (clean : regValue layout.dialogPool s.basis = 0)
    (keep : ∀ q,q∉layout.point.y→v.basis q=s.basis q) : regValue layout.dialogPool v.basis=0 := by
  exact (regValue_congr _ _ _ (fun q hq => keep q
    (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2))).trans clean

private theorem flag_away : pkW layout ≠ layout.core.generic := by decide +kernel

theorem entry (Y k : Fp) (s actual : State) (m : List Bool) (flag : Bool)
    (hy : regValue layout.point.y s.basis=Y.val) (clean : regValue layout.dialogPool s.basis=0)
    (input : pullState outer actual = put s (pkW layout) flag) :
    pullState outer (run (encodeY (EntryFuseOdd.entryYAllOdd layout k)) m actual) =
      run (EntryFuseOdd.entryYAllOdd layout k) m (put s (pkW layout) flag) :=
  OddOuterBridge.outerY_entry_odd Y k s actual m flag hy clean input

theorem exit (Y k : Fp) (s actual : State) (m : List Bool) (flag : Bool)
    (hy : regValue layout.point.y s.basis=EntryFuseOdd.oddWord Y) (clean : regValue layout.dialogPool s.basis=0)
    (input : pullState outer actual = put s (pkW layout) flag) :
    pullState outer (run (encodeY (EntryFuseOdd.exitYAllOdd layout k)) m actual) =
      run (EntryFuseOdd.exitYAllOdd layout k) m (put s (pkW layout) flag) :=
  OddOuterBridge.outerY_exit_odd Y k s actual m flag hy clean input

end ECDSAAdd.Entrant.Stair44OuterY

end

section

namespace ECDSAAdd.Entrant.StairEntryRehost
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement StairSquareHolesCore
attribute [local irreducible] wires run E1Reflected.comparePart E1Reflected.Square31.afterCompare
def compareLabels (w : Nat → Wire) (g : Wire) :=
  [g,w 513,w 514] ++ E1Reflected.xR w ++ E1Reflected.srcR w ++ E1Reflected.cR w
theorem compare_support_tight (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (E1Reflected.comparePart w g k) ⊆ (compareLabels w g).toFinset := by
  have mask := maskedConstant_wires_subset g (E1Reflected.srcR w) k
  have cmp := (compareLt_wires none (E1Reflected.xR w) (E1Reflected.srcR w) (E1Reflected.cR w)
    (w 513) (w 514) (by simp [E1Reflected.srcR,E1Reflected.xR,wireBlock_length])
    (by simp [E1Reflected.cR,E1Reflected.srcR,wireBlock_length])).1
  have left : wires (maskedConstant g (E1Reflected.srcR w) k) ⊆ (compareLabels w g).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (mask hq)
    simp only [compareLabels,List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *
    tauto
  unfold E1Reflected.comparePart
  rw [wires_append,wires_append,Finset.union_subset_iff,Finset.union_subset_iff,cmp]
  refine ⟨⟨left,?_⟩,left⟩
  intro q h
  simp only [compareLabels,Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at *
  tauto
def compareWire (q : Wire) := permutation StairSquareEntryR.entryPairs (pmapR Baselines.layout q)
def suffixWire (q : Wire) := permutation moves (pmapR Baselines.layout q)
def labels := ((compareLabels base (base 2400)).map compareWire ++
    (E1Reflected.Square31.mS5 base (base 2400)).map suffixWire) ++ [4374,4629]
theorem uses_labels (k : Fp) : wires (routed k) ⊆ labels.toFinset := by
  intro q h
  simp only [routed,candidate,comparePhase,suffix,placed,fused,wires_append,renameProgram_support,
    Finset.mem_union,Finset.mem_image] at h
  simp only [labels,List.mem_toFinset,List.mem_append,List.mem_map]
  rcases h with ((⟨x,⟨y,hy,rfl⟩,rfl⟩ | ⟨x,⟨y,hy,rfl⟩,rfl⟩) | h)
  · exact Or.inl (Or.inl ⟨y,List.mem_toFinset.mp (compare_support_tight base (base 2400) k.val hy),rfl⟩)
  · exact Or.inl (Or.inr ⟨y,List.mem_toFinset.mp (E1Reflected.Square31.afterCompare_support _ _ _ hy),rfl⟩)
  · right
    simpa [Arithmetic.swapBits,wires,Instr.wires,or_comm,or_left_comm,or_assoc] using h
end ECDSAAdd.Entrant.StairEntryRehost

end

section

namespace ECDSAAdd.Entrant.Stair44Square
open Arithmetic Secp256k1 CompressedPointDialog MappedCompressed StairSquareContract StairSquareAssembly
set_option maxHeartbeats 1500000
attribute [local irreducible] run wires

/-- The three branches use the same expanded inner-S bank; the tail leaves the
one live high bit on the carrier consumed by the following integer stage. -/
def program (k : Fp) : Program :=
  placedN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA ++
    StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))

abbrev hs := StairSqLoopA.hostDomain
theorem coreOK : CoreOK L0 (coreN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA) :=
  PDSplitLeafSquare.coreOK

/-- On the following stage's physical carrier, the entire square executes the stock operation. -/
theorem fullRunOf (P : Program) (hP : CoreOK L0 P) (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L0 X Y G origin s.basis) :
    run (SquareCarryLoan719BF.place L0 P ++ StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))) m1 s = pullState StairEntryRehost.landing
      (run (SquareCarryLoan719BF.program L0 ++ fastConstAdd L0 L0.point.x k ++ E1QubitPlacement.tickF L0) m2 s) := by
  let C := SquareCarryLoan719BF.place L0 P
  let t := run C (m1.take (measurementCount C)) s
  have bound := placeG_boundary L0 hw0 hn0 P hP X Y G origin s (m1.take (measurementCount C)) v
  have clean : regValue L0.dialogPool t.basis = 0 := by
    rw [regValue_congr _ _ s.basis
      (fun q hq => bound.2.2 q (((E1QubitPlacement.lay L0 hw0 hn0 q).2.1 hq).1)), v.clean]
  let R := p-1-(X-(if G then Y*Y else 0)+(if G then (C163Low4Offsets.squareK : Fp) else 0)).val
  have pos : 0 < p := by norm_num [p]
  have hR : R < p := by dsimp only [R]; omega
  have boundary := StairEntryRehost.fullRun (k-(C163Low4Offsets.delta : Fp)) t
    (m1.drop (measurementCount C)) R bound.2.1 hR clean
  have oldTail : TailOK L0 (E1ReflectedPlacement.entryR L0) := by
    intro; intros; rfl
  have stock := squareG_base L0 hw0 hn0 P hP _ oldTail k X Y G origin s m1 m2 v
  rw [←stock]
  change run (C ++ _) m1 s = pullState _ (run (C ++ _) m1 s)
  simpa only [run_append] using boundary

theorem fullRun (k X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m1 m2 : List Bool)
    (v : PointDialogValues L0 X Y G origin s.basis) :
    run (program k) m1 s = pullState StairEntryRehost.landing
      (run (SquareCarryLoan719BF.program L0 ++ fastConstAdd L0 L0.point.x k ++ E1QubitPlacement.tickF L0) m2 s) :=
  fullRunOf _ coreOK k X Y G origin s m1 m2 v

end ECDSAAdd.Entrant.Stair44Square

end

section

namespace ECDSAAdd.Entrant.Stair44TailBounds
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement E1ReflectedPlacement
  StairSquareHolesCore StairEntryRehost
abbrev L0 := Baselines.layout
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def e1B (q : Nat) : Nat :=
  StairPlaceFast.swB 1558 736 (StairPlaceFast.swB 1557 738 (StairPlaceFast.swB 1042 737
    (StairPlaceFast.swB 1813 527 (StairPlaceFast.swB 738 740 (StairPlaceFast.swB 737 739
      (StairPlaceFast.swB 527 741 q))))))

private theorem e1_eq (q : Wire) : E1QubitPlacement.sig (E1QubitPlacement.rho q) = e1B q := by
  unfold E1QubitPlacement.sig E1QubitPlacement.phaseHost E1QubitPlacement.nativeSwap
    E1QubitPlacement.rho e1B
  simp only [Equiv.trans_apply, StairPlaceFast.swap_eq_sw, StairPlaceFast.swB_eq]
  rfl

/-- `pmapR L0` in closed form (`StairPlaceFast.wireFn2_eqB`). -/
private def pmB (q : Nat) : Nat :=
  StairPlaceFast.pwB (StairPlaceFast.swB 785 1813 (e1B q) - 16)

private theorem pmapR_fast (q : Wire) : pmapR L0 q = pmB q := by
  show wireFn2 Baselines.layout (E1QubitPlacement.sig (E1QubitPlacement.rho q)) = _
  rw [StairPlaceFast.wireFn2_eqB, e1_eq]
  rfl


def good (q : Nat) : Bool :=
  (Nat.ble q 513 || Nat.beq q 4112 || (Nat.ble 4115 q && Nat.blt q 4630) ||
    (Nat.ble 4886 q && Nat.blt q 5144) || (Nat.ble 5399 q && Nat.blt q 5656) || Nat.beq q 9814) &&
  !(Nat.beq q 5515 || Nat.beq q 5655 || Nat.beq q 5400 || Nat.beq q 5401)
private def fastPrefix (x : Wire) := StairPlaceFast.swB 4840 4627 (pmB x)
private def fastSuffix (x : Wire) := StairPlaceFast.swB 4835 4373 (StairPlaceFast.swB 4836 4374
  (StairPlaceFast.swB 4837 4375 (StairPlaceFast.swB 4838 4376 (StairPlaceFast.swB 4839 4377 (pmB x)))))
private theorem prefix_eq (x : Wire) : compareWire x = fastPrefix x := by
  have eq : StairSquareEntryR.entryPairs = [(4840,4627)] := by decide +kernel
  simp only [compareWire,eq,permutation,Equiv.trans_apply,Equiv.refl_apply,fastPrefix,
    StairPlaceFast.swB_eq,StairPlaceFast.swap_eq_sw,pmapR_fast]
private theorem suffix_eq (x : Wire) : suffixWire x = fastSuffix x := by
  simp only [suffixWire,moves_eq,physicalMoves,permutation,Equiv.trans_apply,Equiv.refl_apply,fastSuffix,
    StairPlaceFast.swB_eq,StairPlaceFast.swap_eq_sw,pmapR_fast]
private theorem prefix_good : (compareLabels base (base 2400)).all
    (fun x => good (StairPlaceFast.ugB (fastPrefix x))) = true := by decide +kernel
private theorem suffix_good : (E1Reflected.Square31.mS5 base (base 2400)).all
    (fun x => good (StairPlaceFast.ugB (fastSuffix x))) = true := by decide +kernel
theorem allGood (k : Fp) (q : Wire) (hq : q ∈ wires (routed k)) : good (StairPlaceFast.ugB q) = true := by
  have h := List.mem_toFinset.mp (uses_labels k hq)
  simp only [labels,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with ((⟨x,hx,rfl⟩|⟨x,hx,rfl⟩)|rfl|rfl)
  · rw [prefix_eq]; exact List.all_eq_true.mp prefix_good x hx
  · rw [suffix_eq]; exact List.all_eq_true.mp suffix_good x hx
  · decide +kernel
  · decide +kernel
end ECDSAAdd.Entrant.Stair44TailBounds

end

section

namespace ECDSAAdd.Entrant.Stair44Outer
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly

def kernelPlace (P : Program) := renameProgram (wireFn2 layout) P
def phasePlace (P : Program) := kernelPlace (renameProgram Rolling1588Lifetime.phaseHost P)

def reverseEnd := skywalkArithmeticClear base ++ renameProgram (sig 511) tickR ++
  renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)
def forwardEnd := Six505.merged6 ++ Six505.packP false ++ ForwardSixPlacement.after false ++ skywalkArithmeticClear base

def divide : Program :=
  phasePlace (Stair44WalkRun.forward true 409) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan) ++
    phasePlace reverseEnd ++ phasePlace (Stair44WalkRun.backward false 490) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (Stair44WalkRun.forward false 489) ++ phasePlace forwardEnd ++
    kernelPlace (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (Stair44WalkRun.backward true 409) ++
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

end ECDSAAdd.Entrant.Stair44Outer

end

section

namespace ECDSAAdd.Entrant.Stair44Square
open Arithmetic Secp256k1 StairSquareAssembly StairSquareContract StairSquareHolesCore
set_option maxHeartbeats 1000000

theorem routedMetrics (k : Fp) :
    toffoliCount (StairEntryRehost.routed k) = toffoliCount (E1ReflectedPlacement.entryR L0 k) ∧
    measurementCount (StairEntryRehost.routed k) = measurementCount (E1ReflectedPlacement.entryR L0 k) ∧
    Challenge.gateSlots (StairEntryRehost.routed k) = Challenge.gateSlots (E1ReflectedPlacement.entryR L0 k) + 3 := by
  obtain ⟨t,m,g⟩ := StairEntryRehost.counts k
  have st : toffoliCount (swapBits 4374 4629) = 0 := rfl
  have sm : measurementCount (swapBits 4374 4629) = 0 := rfl
  have sg : Challenge.gateSlots (swapBits 4374 4629) = 3 := rfl
  simp only [StairEntryRehost.routed,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,t,m,g,st,sm,sg,Nat.add_zero,and_self]

theorem routedPhysical (k : Fp) : GatePhysical (StairEntryRehost.routed k) := by
  have p := E1ReflectedPlacement.entryR_physical L0 Baselines.layout_widths Baselines.layout_nodup k
  rw [StairEntryRehost.stock_split,gatePhysical_append] at p
  exact (gatePhysical_append _ _).mpr ⟨(gatePhysical_append _ _).mpr
    ⟨hostRename_physical _ _ p.1,hostRename_physical _ _ p.2⟩,swapBits_physical _ _ (by decide)⟩

theorem changingTail (P : Program) (k : Fp) :
    toffoliCount (P ++ StairEntryRehost.routed k) = toffoliCount (P ++ StairSquareEntryR.entryRH k) ∧
    measurementCount (P ++ StairEntryRehost.routed k) = measurementCount (P ++ StairSquareEntryR.entryRH k) ∧
    Challenge.gateSlots (P ++ StairEntryRehost.routed k) = Challenge.gateSlots (P ++ StairSquareEntryR.entryRH k) + 3 := by
  obtain ⟨t,m,g⟩ := routedMetrics k
  obtain ⟨et,em⟩ := StairSquareEntryR.entryRH_counts k
  simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    t,m,g,et,em,StairSquareEntryR.entryRH_slots,Nat.add_assoc,and_self]

theorem metrics (k : Fp) :
    toffoliCount (program k) + 934 = toffoliCount (A161Generic.squareEntry L0 k) ∧
    measurementCount (program k) + 589 = measurementCount (A161Generic.squareEntry L0 k) ∧
    Challenge.gateSlots (program k) ≤ Challenge.gateSlots (A161Generic.squareEntry L0 k) + 5490126 := by
  have h : toffoliCount (program k) = toffoliCount (squareN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA k) ∧
      measurementCount (program k) = measurementCount (squareN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA k) ∧
      Challenge.gateSlots (program k) = Challenge.gateSlots (squareN PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA k) + 3 :=
    changingTail _ _
  have c := PDSplitLeafSquare.square_counts k
  have s := PDSplitLeafSquare.square_slots_le k
  exact ⟨by omega, by omega, by omega⟩

theorem physical (k : Fp) : GatePhysical (program k) := by
  have p := PDSplitLeafSquare.square_physical k
  rw [squareN, gatePhysical_append] at p
  exact (gatePhysical_append _ _).mpr ⟨p.1, routedPhysical _⟩
end ECDSAAdd.Entrant.Stair44Square

end

section

namespace ECDSAAdd.Entrant.Stair44Square
open ECDSAAdd Arithmetic ControlledPointLayout Secp256k1 CompressedPointDialog
  StairSquareContract StairSquareAssembly StairSquareSites
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] run wires
theorem hs_eq : hs = (List.range' 4840 35 ++ List.range' 4876 4) ++ List.range' 4835 5 := by decide +kernel
private theorem good_sites (q : Wire) (h : Stair44TailBounds.good q = true) :
    q ∈ StairHoleSupport.recordArena ∧ q ∉ StairHoleSupport.oldHoles ∧ q ∉ hs := by
  have old : ∀ v ∈ StairPhysicalLayout.oldHolesNat, Stair44TailBounds.good v = false := by decide +kernel
  have retired : ∀ v ∈ hs, Stair44TailBounds.good v = false := by rw [hs_eq]; decide +kernel
  refine ⟨?_,fun ho => Bool.noConfusion ((old q (StairPhysicalLayout.oldHoles_eq ▸ ho)).symm.trans h),
    fun hr => Bool.noConfusion ((retired q hr).symm.trans h)⟩
  rw [StairPhysicalLayout.recordArena_eq]
  simp only [StairPhysicalLayout.arenaNat,List.mem_append,List.mem_cons,List.mem_range'_1,
    List.not_mem_nil,or_false]
  simp only [Stair44TailBounds.good,Bool.and_eq_true,Bool.or_eq_true,Nat.ble_eq,Nat.blt_eq,Nat.beq_eq] at h
  rcases h.1 with (((((hq|hq)|hq)|hq)|hq)|hq)
  · cases q with
    | zero => decide
    | succ n => cases n with
      | zero => decide
      | succ n => omega
  all_goals first | (subst q; decide) | omega
theorem tailPiece (k : Fp) : StairSiteAvoidance.PieceOK hs StairSiteAvoidance.UG (StairEntryRehost.routed k) := by
  have spec (q : Wire) (hq : q ∈ wires (StairEntryRehost.routed k)) :=
    good_sites _ (Stair44TailBounds.allGood k q hq)
  have maps (q : Wire) : StairSiteAvoidance.UG q = StairPlaceFast.ugB q := StairPlaceFast.ug_eqB q
  constructor
  · intro q hq
    rw [maps q]
    exact ⟨(spec q hq).1,(spec q hq).2.1⟩
  · intro q hq
    rw [maps q]
    exact (spec q hq).2.2
private theorem fixedPlace : ∀ q ∈ hs, placeFn q = q := by
  rw [hs_eq]
  simp only [LT48K.placeFn_eq]
  decide +kernel
private theorem fixedUG : ∀ q ∈ hs, StairSiteAvoidance.UG q = q := by
  rw [hs_eq]
  change ∀ q ∈ _, Wrapper5.U _ ((Equiv.swap _ _) (StairOuterPlacement.rho Baselines.layout q)) = q
  simp only [StairPlaceFast.ug_eqB]
  decide +kernel
theorem piece (k : Fp) : StairSiteAvoidance.PieceOK hs StairSiteAvoidance.UG (program k) := by
  have avC := PDSplitLeafSquare.brC_avoids
  have avB := PDSplitLeafSquare.brB_avoids
  have avA := PDSplitLeafSquare.brA_avoids
  have hostsGood : ∀ h ∈ PDSplitLeafSquare.allowedWires,
      StairSiteAvoidance.UG (placeFn h) ∈ StairHoleSupport.recordArena ∧
        StairSiteAvoidance.UG (placeFn h) ∉ StairHoleSupport.oldHoles := by
    have allG : PDSplitLeafSquare.allowedWires.all
        (fun w => Stair44TailBounds.good (StairPlaceFast.ugB (LT48K.placeF w))) = true := by
      rw [PDSplitLeafSquare.allowedWires_eq]; decide +kernel
    intro h hh
    have hg := List.all_eq_true.mp allG h hh
    have hmap : StairSiteAvoidance.UG (placeFn h) = StairPlaceFast.ugB (LT48K.placeF h) := by
      rw [LT48K.placeFn_eq]; exact StairPlaceFast.ug_eqB _
    rw [hmap]
    exact ⟨(good_sites _ hg).1, (good_sites _ hg).2.1⟩
  have arena := placedN_arenaB PDSplitLeafSquare.bodyAPlain PDSplitLeafSquare.bodyB
    PDSplitLeafSquare.bodyCPlain PDSplitLeafSquare.brC PDSplitLeafSquare.brB PDSplitLeafSquare.brA
    PDSplitLeafSquare.allowedWires
    PDSplitLeafSquare.bodyAPlain_coarse PDSplitLeafSquare.bodyAPlain_fine
    PDSplitLeafSquare.bodyCPlain_fine PDSplitLeafSquare.bodyB_ok.support
    PDSplitLeafSquare.bodyB_normFlag
    PDSplitLeafSquare.brC_support PDSplitLeafSquare.brB_support
    PDSplitLeafSquare.brA_support hostsGood
  have unplaced := coreN_avoids hs _ _ _ avC avB avA
  apply StairSiteAvoidance.PieceOK.append _ (tailPiece _)
  refine ⟨arena,?_⟩
  intro x hx hxh
  have ex : x = StairSiteAvoidance.UG x := UG_inj (fixedUG _ hxh).symm
  unfold placedN at hx
  rw [placed_wires, Finset.mem_image] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have ey : y = StairSiteAvoidance.UG (placeFn y) := placeFn_inj (ex.trans (fixedPlace _ hxh).symm)
  rw [ey] at hy
  exact unplaced _ hxh hy
end ECDSAAdd.Entrant.Stair44Square

end

section

namespace ECDSAAdd.Entrant.Stair44PhaseSites
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairRestSupport Stair44Outer StairConcreteAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

private theorem fromValid {P : Program} (chk : allSites valid P = true) : PieceOK holes PP P := by
  apply Stair44OuterSites.fits
  intro q hq
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace q) = true
  rw [StairPlaceFast.phasePlace_eqB]
  exact allSites_sound chk q hq

theorem reverseTail : PieceOK holes PP reverseEnd := by
  unfold reverseEnd
  exact ((fromValid (by decide +kernel)).append (fromValid (by decide +kernel))).append (fromValid (by decide +kernel))

theorem forwardTail : PieceOK holes PP forwardEnd := by
  unfold forwardEnd
  exact (((fromValid (by decide +kernel)).append (fromValid (by decide +kernel))).append (fromValid (by decide +kernel))).append
    (fromValid (by decide +kernel))

theorem exitX (k : Nat) : PieceOK holes UG (Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))) := by
  apply Stair44OuterSites.fits
  intro q hq
  simp only [Stair44PointMap.switchX,phasePlace,kernelPlace,renameProgram_support,Finset.mem_image] at hq
  obtain ⟨_,⟨_,⟨x,hx,rfl⟩,rfl⟩,rfl⟩ := hq
  exact Stair44OuterSites.exitX k x hx
end ECDSAAdd.Entrant.Stair44PhaseSites

end

section

namespace ECDSAAdd.Entrant.Stair44Physical
open Arithmetic MappedCompressed Secp256k1 Baselines StairPhysicalV3 StairRestSupport
  Stair44Outer StairConcreteAssembly Stair44WalkMap
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
attribute [local irreducible] wires GatePhysical

end ECDSAAdd.Entrant.Stair44Physical

end

section

namespace ECDSAAdd.Entrant.Stair44Resources
open Arithmetic Secp256k1 MappedCompressed Baselines StairConcreteAssembly Stair44Outer Challenge
set_option maxRecDepth 30000
set_option maxHeartbeats 1500000
attribute [local irreducible] toffoliCount measurementCount gateSlots

/-- All three physical costs ignore wire labels and add across adjacent phases. -/
structure Cost where
  measure : Program → Nat
  append (a b : Program) : measure (a ++ b) = measure a + measure b
  rename (f : Wire → Wire) (a : Program) : measure (renameProgram f a) = measure a
  forward (d : Bool) (n : Nat) : measure (Stair44WalkRun.forward d n) =
    measure (Rolling1588TickGap.forward d 1 (15+n))
  backward (d : Bool) (n : Nat) : measure (Stair44WalkRun.backward d n) =
    measure (Rolling1588.reverse d 1 (15+n))

def tc : Cost := ⟨toffoliCount,toffoliCount_append,fun f a => (renameProgram_counts f a).1,
  fun d n => (Stair44WalkRun.metrics d n).1.1,fun d n => (Stair44WalkRun.metrics d n).2.1⟩
def mc : Cost := ⟨measurementCount,measurementCount_append,fun f a => (renameProgram_counts f a).2,
  fun d n => (Stair44WalkRun.metrics d n).1.2.1,fun d n => (Stair44WalkRun.metrics d n).2.2.1⟩
def slots : Cost := ⟨gateSlots,gateSlots_append,rename_gateSlots,
  fun d n => (Stair44WalkRun.metrics d n).1.2.2,fun d n => (Stair44WalkRun.metrics d n).2.2.2⟩

theorem divide_eq (c : Cost) : c.measure divide = c.measure (hostedEntryRest layout) := by
  simp only [divide,kernelPlace,phasePlace,hostedEntryRest,StairSchedule.stackForward6,
    reverseEnd,InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
    c.append,c.rename,c.forward,c.backward,Nat.add_assoc]

theorem multiply_eq (c : Cost) (k : Nat) : c.measure (multiply k) = c.measure (hostedExitRest layout k) := by
  simp only [multiply,kernelPlace,phasePlace,hostedExitRest,Stair44PointMap.switchX,forwardEnd,
    Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,
    StairHostsSchedule.lastXN,StairSchedule.stackReverse15,c.append,c.rename,c.forward,c.backward,Nat.add_assoc]

theorem finite_eq (c : Cost) (C : Point) (cx cy : Fp)
    (sq : c.measure (Stair44Square.program (ReflectionE1.correction cx)) =
      c.measure (StairSquareFinal.squareEntryHL StairSqLoopA.holes layout (ReflectionE1.correction cx))) :
    c.measure (finite C cx cy) = c.measure (hostedFinite C cx cy) := by
  simp only [finite,borrowGeneric,generic,hostedFinite,hostedMiddle,hostedBorrowGeneric,hostedGenericBlock,
    hostedGeneric,hostedSecondStage,Stair44PointMap.encode,Stair44PointMap.encodeY,Stair44PointMap.switchX,
    c.append,c.rename,divide_eq,multiply_eq,sq,Nat.add_assoc]

theorem finite_sub (c : Cost) (C : Point) (cx cy : Fp) (d : Nat)
    (sq : c.measure (Stair44Square.program (ReflectionE1.correction cx)) + d =
      c.measure (StairSquareFinal.squareEntryHL StairSqLoopA.holes layout (ReflectionE1.correction cx))) :
    c.measure (finite C cx cy) + d = c.measure (hostedFinite C cx cy) := by
  simp only [finite,borrowGeneric,generic,hostedFinite,hostedMiddle,hostedBorrowGeneric,hostedGenericBlock,
    hostedGeneric,hostedSecondStage,Stair44PointMap.encode,Stair44PointMap.encodeY,Stair44PointMap.switchX,
    c.append,c.rename,divide_eq,multiply_eq]
  omega

theorem totals (C : Point) : toffoliCount (program C) ≤ 2167840 ∧ measurementCount (program C) ≤ 1519658 := by
  have h := StairCountsHosted.count_totals C
  change toffoliCount (concreteProgram C) ≤ 2168925 ∧ measurementCount (concreteProgram C) ≤ 1520247 at h
  cases C with
  | zero =>
    change toffoliCount [] ≤ 2167840 ∧ measurementCount [] ≤ 1519658
    simp [toffoliCount, measurementCount]
  | @some cx cy hc =>
    let k := ReflectionE1.correction cx
    have old := StairSquareFinal.square_counts StairSqLoopA.holes k
    have new := Stair44Square.metrics k
    have ft := finite_sub tc (.some hc) cx cy 1085 (by
      change toffoliCount (Stair44Square.program k) + 1085 = toffoliCount (StairSquareFinal.squareEntryHL _ layout k)
      rw [StairSquareFinal.squareEntryHL_layout]; omega)
    have fm := finite_sub mc (.some hc) cx cy 589 (by
      change measurementCount (Stair44Square.program k) + 589 = measurementCount (StairSquareFinal.squareEntryHL _ layout k)
      rw [StairSquareFinal.squareEntryHL_layout]; omega)
    change toffoliCount _ + 1085 = toffoliCount _ at ft
    change measurementCount _ + 589 = measurementCount _ at fm
    simp only [program,concreteProgram,hostedWrapper,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2] at h ⊢
    exact ⟨by omega, by omega⟩
open StairSlotsPlan

theorem slotBound (C : Point) : gateSlots (program C) ≤ 56350587 := by
  cases C with
  | zero => simp [program]
  | @some cx cy hc =>
    let C : Point := .some hc
    let dE := v3Plan.entryDelta v3Costs v3Boundary1806
    let dX := v3Plan.exitDelta v3Costs v3Boundary1806
    have de : gateSlots divide ≤ gateSlots (ParityStageBothInverse23.restEntry layout) + dE := by
      have eq := divide_eq slots
      change gateSlots divide = gateSlots (hostedEntryRest layout) at eq
      rw [eq]
      exact entryRestOf_slots_le checkpointPrimitives hostPlan _ _ v3WalkFacts
        (v3GroupFacts _) (v3BoundaryFacts _) layout
    have dx : gateSlots (multiply cx.val) ≤ gateSlots (ParityXExitInverse23Kernel.restXXN layout cx.val) + dX := by
      have eq := multiply_eq slots cx.val
      change gateSlots (multiply cx.val) = gateSlots (hostedExitRest layout cx.val) at eq
      rw [eq]
      exact exitRestOf_slots_le checkpointPrimitives hostPlan _ _ v3WalkFacts
        (v3GroupFacts _) (v3BoundaryFacts _) layout cx.val
    have sq : gateSlots (Stair44Square.program (ReflectionE1.correction cx)) ≤
        gateSlots (A161Generic.squareEntry layout (ReflectionE1.correction cx)) + 5490126 :=
      (Stair44Square.metrics (ReflectionE1.correction cx)).2.2
    have gen : gateSlots (generic cx cy) ≤ gateSlots (FlagExit.genericN layout cx cy) + (dE + dX) + 5490126 := by
      simp only [generic,FlagExit.genericN,FlagExit.secondStageN,Stair44PointMap.encodeY,
        Stair44PointMap.switchX,gateSlots_append,rename_gateSlots]
      omega
    have whole : gateSlots (program C) ≤ gateSlots (AboveFieldPointDevelop.programQ C) + (dE + dX) + 5490126 := by
      simp only [C,program,finite,borrowGeneric,Stair44PointMap.encode,AboveFieldPointDevelop.programQ,
        AboveFieldPointDevelop.wrapperBorrow,AboveFieldPointDevelop.finiteBorrow,AboveFieldPointDevelop.middle,
        ControlPointEncodingDevelop.borrowGeneric,ControlPointEncodingDevelop.genericBlock,
        gateSlots_append,rename_gateSlots] at ⊢
      omega
    have sum : dE + dX = 335174 := v3_slotDelta_1806
    have old := AboveFieldPointDevelop.program_slots_Q C
    change gateSlots (program C) ≤ 56350587
    omega
end ECDSAAdd.Entrant.Stair44Resources

end

section

namespace ECDSAAdd.Entrant.Stair44FieldSites
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
  StairConcreteAssembly Stair44Outer
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

private theorem entryTail : PieceOK holes TP (StairHostsSchedule.entryTailPrefix pr hp) := by
  have pk := packEnd_rows
  unfold StairHostsSchedule.entryTailPrefix
  refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
    ?_).append ?_).append ?_).append ?_).append ?_)
  · exact Stair44Groups.hostedGroup44 true 0 1 84 (by decide)
  · exact forwardSegment_ok hsub 87 62 (by decide) (by decide) (by decide) pk.1
  · exact Stair44Groups.hostedGroup44 true 13 85 5 (by decide)
  · exact forwardSegment_ok hsub 62 47 (by decide) (by decide) (by decide) pk.2.1
  · exact Stair44Groups.hostedGroup44 true 22 90 3 (by decide)
  · exact forwardSegment_ok hsub 47 32 (by decide) (by decide) (by decide) pk.2.2.1
  · exact Stair44Groups.hostedGroup44 true 30 93 3 (by decide)
  · exact forwardSegment_ok hsub 32 22 (by decide) (by decide) (by decide) pk.2.2.2.1
  · exact Stair44Groups.hostedGroup44 true 36 96 2 (by decide)
  · exact forwardSegment_ok hsub 22 12 (by decide) (by decide) (by decide) pk.2.2.2.2
  · exact Stair44Groups.hostedGroup44 true 41 98 2 (by decide)
  · exact forwardLast_ok hsub

theorem exitHead : PieceOK holes TP (StairHostsSchedule.exitHeadSuffix pr hp) := by
  have up := unpackEnd_rows
  unfold StairHostsSchedule.exitHeadSuffix
  refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
    ?_).append ?_).append ?_).append ?_).append ?_)
  · exact reverseLast_ok hsub
  · exact Stair44Groups.hostedGroup44 false 41 98 2 (by decide)
  · exact reverseSegment_ok hsub 22 12 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.2
  · exact Stair44Groups.hostedGroup44 false 36 96 2 (by decide)
  · exact reverseSegment_ok hsub 32 22 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.1
  · exact Stair44Groups.hostedGroup44 false 30 93 3 (by decide)
  · exact reverseSegment_ok hsub 47 32 (by decide) (by decide) (by decide) (by decide)
      up.2.2.1
  · exact Stair44Groups.hostedGroup44 false 22 90 3 (by decide)
  · exact reverseSegment_ok hsub 62 47 (by decide) (by decide) (by decide) (by decide)
      up.2.1
  · exact Stair44Groups.hostedGroup44 false 13 85 5 (by decide)
  · exact reverseSegment_ok hsub 87 62 (by decide) (by decide) (by decide) (by decide) up.1
  · exact Stair44Groups.hostedGroup44 false 0 1 84 (by decide)

theorem entry : PieceOK holes KP (StairHostsSchedule.entryFieldHosted pr hp) := by
  have ps := ok_of_all hsub paritySetup_all
  have hx := ok_of_all hsub hostedX_all
  unfold StairHostsSchedule.entryFieldHosted
  refine ((((PieceOK.append ?_ ps).append hx).append ?_).append hx).append ps
  · apply ok_field
    unfold StairHostsSchedule.entryLowPrefix
    refine ((PieceOK.append (StairFirstPacketHosted.hostedFirstPacket_pieceOK holes hsub true) (ok_of_all hsub scratchClear_all)).append ?_).append (ok_of_all hsub scratchUnprefix_all)
    exact ok_borrow (entryTail)
  · apply ok_field
    unfold StairHostsSchedule.entryLowSuffix
    refine ((ok_of_all hsub scratchClear_all).append ?_).append (ok_of_all hsub scratchUnprefix_all)
    apply ok_borrow
    unfold StairHostsSchedule.entryTailSuffix
    exact ((Stair44Groups.hostedGroup44 true 43 100 2 (by decide)).append endpointD |>.append (ok_of_all hsub copyN_all)).append
      canon

theorem exit : PieceOK holes KP (StairHostsSchedule.exitFieldHosted pr hp) := by
  have ps := ok_of_all hsub paritySetup_all
  have hx := ok_of_all hsub hostedX_all
  unfold StairHostsSchedule.exitFieldHosted
  refine ((((ps.append hx).append ?_).append ps).append hx).append ?_
  · apply ok_field
    unfold StairHostsSchedule.exitLowPrefix
    refine ((ok_of_all hsub scratchClear_all).append ?_).append (ok_of_all hsub scratchUnprefix_all)
    apply ok_borrow
    unfold StairHostsSchedule.exitHeadPrefix
    exact ((center.append (ok_of_all hsub copyN_all)).append endpointM).append
      (Stair44Groups.hostedGroup44 false 43 100 2 (by decide))
  · apply ok_field
    unfold StairHostsSchedule.exitLowSuffix
    exact (((ok_of_all hsub scratchClear_all).append (ok_borrow (exitHead))).append
      (ok_of_all hsub scratchUnprefix_all)).append (StairFirstPacketHosted.hostedFirstPacket_pieceOK holes hsub false)
end ECDSAAdd.Entrant.Stair44FieldSites

end

section

namespace ECDSAAdd.Entrant.Stair44Release
open Arithmetic Secp256k1 Challenge Baselines StairSiteAvoidance Stair44Outer
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
attribute [local irreducible] wires renameProgram qubits toffoliCount measurementCount gateSlots

abbrev holes := StairPhysicalInventory.physicalHoles

theorem squareSites (k : Fp) : PieceOK holes UG (Stair44Square.program k) := by
  have sub : ∀ q ∈ holes, q ∈ Stair44Square.hs := by
    change ∀ q ∈ StairPhysicalInventory.physicalHoles, _
    rw [StairPhysicalLayout.physicalHoles_eq_nat,Stair44Square.hs_eq]
    decide +kernel
  have s := Stair44Square.piece k
  exact ⟨s.1,fun q hq h => s.2 q hq (sub _ h)⟩
end ECDSAAdd.Entrant.Stair44Release

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Partial Arithmetic MappedCompressed StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

-- The generic window's domain (K2's `WindowCovered.domainW`): `[101,529] [786,1045] [1049,1300] [1556,1812]`.
def domain (q : Nat) := (56 ≤ q && q ≤ 529) || (786 ≤ q && q ≤ 1045) || (1049 ≤ q && q ≤ 1300) || (1556 ≤ q && q ≤ 1812)

theorem domain_eq (q : Nat) : domain q = WindowCovered.domainW q := rfl

def Covered (P : Program) : Prop := ∀ q ∈ wires P, domain q = true

private theorem interval0 : (List.range' 101 429).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval0l : (List.range' 86 15).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval0ll : (List.range' 71 15).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval0lll : (List.range' 56 15).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval1 : (List.range' 786 260).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval2 : (List.range' 1049 252).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval3 : (List.range' 1556 257).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel

theorem valid {q : Wire} (h : domain q = true) : Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true := by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩
  · by_cases hq : (q:Nat) < 101
    · by_cases hq2 : (q:Nat) < 86
      · by_cases hq3 : (q:Nat) < 71
        · exact List.all_eq_true.mp interval0lll q (by simp only [List.mem_range'_1]; (try unfold Wire at *); omega)
        · exact List.all_eq_true.mp interval0ll q (by simp only [List.mem_range'_1]; (try unfold Wire at *); omega)
      · exact List.all_eq_true.mp interval0l q (by simp only [List.mem_range'_1]; (try unfold Wire at *); omega)
    · exact List.all_eq_true.mp interval0 q (by simp only [List.mem_range'_1]; (try unfold Wire at *); omega)
  · exact List.all_eq_true.mp interval1 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval2 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval3 q (by simp only [List.mem_range'_1]; omega)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

-- oddten:begin RA
section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

/-- oddten: the `mstart` packet at any position (`mstartPacket_counts` is the case 84). -/
theorem ot_mstartPacket_counts (j : Nat) :
    toffoliCount (mstartPacket j)=toffoliCount (ECDSAAdd.Entrant.Rolling1588.packet false j)+242 ∧
    measurementCount (mstartPacket j)=measurementCount (ECDSAAdd.Entrant.Rolling1588.packet false j)+237 := by
  have a := cell_count_delta false j 3 2
  have b := cell_count_delta false j 4 2
  have c := cellWith_counts false (P1Life.mstart (base 760) base (base 2409)) j 4 2
  have d := route_mstart_counts
  have e := cell_counts false j 4 2
  simp only [mstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,renameProgram_counts,mstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,toffoliCount_append,
    measurementCount_append]
  exact ⟨by omega,by omega⟩

/-- oddten: gate slots of the `mstart` packet at any position (`mstartPacket_slots` is the case 84). -/
theorem ot_mstartPacket_slots (j : Nat) :
    Challenge.gateSlots (mstartPacket j)+112=Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet false j)+4543 := by
  have a := cell_slot_delta false j 3 2
  have b := cell_slot_delta false j 4 2
  have c := cellWith_slots false (P1Life.mstart (base 760) base (base 2409)) j 4 2
  have d := slot_mstart (base 760) base (base 2409) Rolling1588Lifetime.half_ports_nodup route_retired_count_member
  have h := slot_half (base 760) false base (base 2409)
  have regular := cellWith_slots false (P1Life.half (base 760) false base (base 2409)) j 4 2
  have eq : cell false j 4 2=cellWith false (P1Life.half (base 760) false base (base 2409)) j 4 2 := rfl
  rw [←eq] at regular
  simp only [Bool.false_eq_true,if_false] at h
  simp only [mstartPacket,ECDSAAdd.Entrant.Rolling1588.packet,Baselines.rename_gateSlots,mstartBasePacket,
    ECDSAAdd.Entrant.Rolling1588.basePacket,Bool.false_eq_true,if_false,Challenge.gateSlots_append]
  simp only [halfSlotSaving,Bool.false_eq_true,if_false] at a b
  omega

theorem ot_dstartPacket_physical : GatePhysical (dstartPacket 1) :=
  gatePhysical_rename _ (shifted (Placement5.pi 1)).injective _ (c45_dstartBasePacket_physical 1 (by decide))
theorem ot_dendPacket_physical (j : Nat) (hj : j<102) : GatePhysical (dendPacket j) :=
  gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ (c45_dendBasePacket_physical j hj)
theorem ot_mstartPacket_physical (j : Nat) (hj : j<102) : GatePhysical (mstartPacket j) :=
  gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ (mstartBasePacket_physical j hj)
theorem ot_mendPacket_physical (j : Nat) (hj : j<102) : GatePhysical (mendPacket j) :=
  gatePhysical_rename _ (shifted (Placement5.pi j)).injective _ (mendBasePacket_physical j hj)

end ECDSAAdd.Entrant.RouteA.Rolling1588
end
-- oddten:end RA

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts
open Arithmetic MappedCompressed Stair44Resources StairConcreteAssembly StairArchiveInactive
open StairArchiveRelease StairArchiveNativeCut StairArchiveTen StairArchiveGates
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount measurementCount StairGroups.packet
  StairArchiveInactive.packet fieldHook

def distributed (d : Bool) (j n : Nat) :=
  PacketSequence.program d (StairArchiveInactive.packet d) j n
private theorem ren (f : Wire → Wire) (a b : Program) : renameProgram f (a++b)=renameProgram f a++renameProgram f b := List.map_append
theorem distribute (d : Bool) (j n : Nat) :
    StairHostsSchedule.hostedGroup hostPlan d 0 j n = distributed d j n := by
  change StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (PacketSequence.program d (StairGroups.packet d 0) j n)) = _
  simp only [hosts_eq,distributed,renameProgram_comp]
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,
      ren,ih,StairArchiveInactive.packet,hosts_eq,renameProgram_comp]

def group (d : Bool) (j n : Nat) := StairHostsSchedule.hostedGroup hostPlan d 0 j n

def ordered (d : Bool) (a b : Program) := if d then a++b else b++a


/-- oddten: packets `1..84` of both kernels run the odd-word cell (`dstart` / `dend` on the division kernel,
`mend` / `mstart` on the multiplication kernel), inside the archive ten-blocks too; packets `85..84` run the
record packets. -/
def oddPk (d : Bool) (k : Nat) : Program :=
  if 1≤k ∧ k<84 then RouteA.Rolling1588.packet d k
  else if k=84 then OddFullPass.P1LifeLoan.packet d 0 84
  else ECDSAAdd.Entrant.Rolling1588.packet d k

/-- packet `k` of the field group, hosted like the record packets. -/
def opk (d : Bool) (k : Nat) : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (oddPk d k))

def ogroup (d : Bool) (j n : Nat) : Program := PacketSequence.program d (opk d) j n
def ofirst (j : Nat) (rev : Bool) := opk (!rev) (if rev then j+1 else j)
def osecond (j : Nat) (rev : Bool) := opk (!rev) (if rev then j else j+1)
/-- dadon's archive ten-block around the field group's own packets `j`, `j+1`. -/
def oten (j : Nat) (rev : Bool) :=
  fieldHook j (enter rev) ++ (ofirst j rev ++ (fieldHook j (shift rev) ++
    (osecond j rev ++ fieldHook j (leave rev))))

/-- the field group: the odd-word cell on packets 1..84 with the archive ten-blocks of the eleven window banks
25, 28, ..., 55 (bank `b` belongs to the block starting at tick `5b-5`) around the cell's own packets. -/
def group84 (d : Bool) : Program :=
  ordered d (ogroup d 1 9) (ordered d (oten 10 (!d)) (ordered d (ogroup d 12 1) (ordered d (oten 13 (!d)) (ordered d (ogroup d 15 1) (ordered d (oten 16 (!d)) (ordered d (ogroup d 18 1) (ordered d (oten 19 (!d)) (ordered d (ogroup d 21 1) (ordered d (oten 22 (!d)) (ordered d (ogroup d 24 1) (ordered d (oten 25 (!d)) (ordered d (ogroup d 27 1) (ordered d (oten 28 (!d)) (ordered d (ogroup d 30 1) (ordered d (oten 31 (!d)) (ordered d (ogroup d 33 1) (ordered d (oten 34 (!d)) (ordered d (ogroup d 36 1) (ordered d (oten 37 (!d)) (ordered d (ogroup d 39 1) (ordered d (oten 40 (!d)) (ordered d (ogroup d 42 1) (ordered d (oten 43 (!d)) (ordered d (ogroup d 45 1) (ordered d (oten 46 (!d)) (ordered d (ogroup d 48 1) (ordered d (oten 49 (!d)) (ordered d (ogroup d 51 1) (ordered d (oten 52 (!d)) (ordered d (ogroup d 54 1) (ordered d (oten 55 (!d)) (ordered d (ogroup d 57 1) (ordered d (oten 58 (!d)) (ordered d (ogroup d 60 1) (ordered d (oten 61 (!d)) (ordered d (ogroup d 63 1) (ordered d (oten 64 (!d)) (ordered d (ogroup d 66 1) (ordered d (oten 67 (!d)) (ordered d (ogroup d 69 1) (ordered d (oten 70 (!d)) (ordered d (ogroup d 72 1) (ordered d (oten 73 (!d)) (ordered d (ogroup d 75 1) (ordered d (oten 76 (!d)) (ordered d (ogroup d 78 1) (ordered d (oten 79 (!d)) (ordered d (ogroup d 81 1) (ordered d (oten 82 (!d)) (ogroup d 84 1))))))))))))))))))))))))))))))))))))))))))))))))))

theorem oddPk_mid (d : Bool) (k : Nat) (h1 : 1≤k) (h2 : k<84) : oddPk d k=RouteA.Rolling1588.packet d k := by
  unfold oddPk; rw [if_pos ⟨h1,h2⟩]
theorem oddPk_end (d : Bool) :
    oddPk d 84=OddFullPass.P1LifeLoan.packet d 0 84 := by
  unfold oddPk; rw [if_neg (by decide),if_pos rfl]
theorem oddPk_std (d : Bool) (k : Nat) (h : 84<k) : oddPk d k=ECDSAAdd.Entrant.Rolling1588.packet d k := by
  unfold oddPk; rw [if_neg (by omega),if_neg (by omega)]

/-- every packet of the family uses only wires of the record packet at its place (no new wire). -/
theorem oddPk_sub (d : Bool) (k : Nat) : wires (oddPk d k) ⊆ wires (ECDSAAdd.Entrant.Rolling1588.packet d k) := by
  by_cases h12 : 1≤k ∧ k<84
  · rw [oddPk_mid d k h12.1 h12.2]
    cases d
    · exact StairLoanGroupSupport.c45_oddPacket_sub_false k
    · exact StairLoanGroupSupport.c45_oddPacket_sub k
  by_cases h3 : k=84
  · subst h3
    rw [oddPk_end]
    have h0 := OddFullPass.P1LifeLoan.packet_wires_sub d 0 84 (by decide) (by decide)
    simpa only [StairGroups.packet_zero] using h0
  · intro q hq
    unfold oddPk at hq
    rwa [if_neg h12,if_neg h3] at hq

/-- the odd packets are physical. -/
theorem oddPk_physical (d : Bool) (k : Nat) (hlo : 1≤k) (hk : k≤84) : GatePhysical (oddPk d k) := by
  by_cases h2 : k<84
  · rw [oddPk_mid d k hlo h2]
    exact RouteA.Rolling1588.packet_physical d k (by omega)
  · have h3 : k=84 := by omega
    subst h3
    rw [oddPk_end]
    exact OddFullPass.P1LifeLoan.packet_physical d 0 84 (by decide)

theorem ot_opk_sub (d : Bool) (k : Nat) : wires (opk d k) ⊆ wires (StairArchiveInactive.packet d k) := by
  simp only [opk,StairArchiveInactive.packet,StairArchiveInactive.hosts_eq,StairGroups.packet_zero]
  exact StairLoanGroupSupport.rename_sub _ _ _ (StairLoanGroupSupport.rename_sub _ _ _ (oddPk_sub d k))

theorem ot_opk_std (d : Bool) (k : Nat) (h : 84<k) : opk d k=StairArchiveInactive.packet d k := by
  simp only [opk,StairArchiveInactive.packet,StairGroups.packet_zero,oddPk_std d k h]

theorem ot_group_eq (d : Bool) (j n : Nat) : group d j n=StairLoan.rebindMany StairSchedule.exclusiveRoles
    (StairPhysicalLayout.hosts 87) (renameProgram (OB5.sig 511) (PacketSequence.program d (StairGroups.packet d 0) j n)) :=
  rfl

theorem ot_ogroup_sub (d : Bool) (j n : Nat) : wires (ogroup d j n) ⊆ wires (group d j n) := by
  rw [group,distribute]
  exact StairLoanGroupSupport.sequence_sub d _ _ (fun k => ot_opk_sub d k) j n

theorem ot_oten_sub (j : Nat) (rev : Bool) : wires (oten j rev) ⊆ wires (ten j rev) := by
  simp only [oten,ten,ofirst,osecond,StairArchiveTen.first,StairArchiveTen.second]
  exact StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
    (StairLoanGroupSupport.append_sub _ _ _ _ (ot_opk_sub _ _)
      (StairLoanGroupSupport.append_sub _ _ _ _ (Finset.Subset.refl _)
        (StairLoanGroupSupport.append_sub _ _ _ _ (ot_opk_sub _ _) (Finset.Subset.refl _))))
-- oddten:end WDEF

/-- the tape of the reference run is the actual tape (no cell any more). -/
def cellTape (_d : Bool) (m : List Bool) : List Bool := m




theorem ord (c : Cost) (d : Bool) (a b : Program) :
    c.measure (ordered d a b)=c.measure a+c.measure b := by
  cases d <;> simp [ordered,c.append,Nat.add_comm]

/-- every cost measure of a hosted record group is that of the record group. -/
theorem group_measure (c : Cost) (d : Bool) (j n : Nat) :
    c.measure (group d j n) = c.measure (ECDSAAdd.Entrant.Rolling1588.groups d j n) := by
  rw [group, distribute]
  unfold distributed ECDSAAdd.Entrant.Rolling1588.groups
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program, if_true, if_false, Bool.false_eq_true, c.append, ih,
      StairArchiveInactive.packet, StairArchiveInactive.hosts_eq, c.rename, StairGroups.packet_zero]

attribute [local irreducible] opk

theorem opk_measure (c : Cost) (d : Bool) (k : Nat) : c.measure (opk d k)=c.measure (oddPk d k) := by
  simp only [opk,StairArchiveInactive.hosts_eq,c.rename]

theorem ogroup_measure (c : Cost) (d : Bool) (j n : Nat) :
    c.measure (ogroup d j n)=c.measure (PacketSequence.program d (oddPk d) j n) := by
  unfold ogroup
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,c.append,ih,opk_measure]

private theorem gsplit (c : Cost) (d : Bool) (p : Nat→Program) (j n k : Nat) :
    c.measure (PacketSequence.program d p j (n+k))=
      c.measure (PacketSequence.program d p j n)+c.measure (PacketSequence.program d p (j+n) k) := by
  cases d
  · rw [RouteA.Rolling1588.odd45_program_false_add,c.append]; omega
  · rw [RouteA.Rolling1588.odd45_program_true_add,c.append]

private theorem oneP (c : Cost) (d : Bool) (p : Nat→Program) (j : Nat) :
    c.measure (PacketSequence.program d p j 1)=c.measure (p j) := by
  cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,List.append_nil,List.nil_append]

private theorem oseq_congr (d : Bool) (p q : Nat→Program) :
    ∀ (n j : Nat), (∀ k, j≤k → k<j+n → p k=q k) →
      PacketSequence.program d p j n=PacketSequence.program d q j n
  | 0, _, _ => rfl
  | n+1, j, h => by
    have hj := h j (Nat.le_refl j) (by omega)
    have rest := oseq_congr d p q n (j+1) (fun k a b => h k (by omega) (by omega))
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,hj,rest]

private theorem opartition (c : Cost) (d : Bool) :
    c.measure (ogroup d 1 84) = c.measure (ogroup d 1 9)+c.measure (ogroup d 10 2)+c.measure (ogroup d 12 1)+c.measure (ogroup d 13 2)+c.measure (ogroup d 15 1)+c.measure (ogroup d 16 2)+c.measure (ogroup d 18 1)+c.measure (ogroup d 19 2)+c.measure (ogroup d 21 1)+c.measure (ogroup d 22 2)+c.measure (ogroup d 24 1)+c.measure (ogroup d 25 2)+c.measure (ogroup d 27 1)+c.measure (ogroup d 28 2)+c.measure (ogroup d 30 1)+c.measure (ogroup d 31 2)+c.measure (ogroup d 33 1)+c.measure (ogroup d 34 2)+c.measure (ogroup d 36 1)+c.measure (ogroup d 37 2)+c.measure (ogroup d 39 1)+c.measure (ogroup d 40 2)+c.measure (ogroup d 42 1)+c.measure (ogroup d 43 2)+c.measure (ogroup d 45 1)+c.measure (ogroup d 46 2)+c.measure (ogroup d 48 1)+c.measure (ogroup d 49 2)+c.measure (ogroup d 51 1)+c.measure (ogroup d 52 2)+c.measure (ogroup d 54 1)+c.measure (ogroup d 55 2)+c.measure (ogroup d 57 1)+c.measure (ogroup d 58 2)+c.measure (ogroup d 60 1)+c.measure (ogroup d 61 2)+c.measure (ogroup d 63 1)+c.measure (ogroup d 64 2)+c.measure (ogroup d 66 1)+c.measure (ogroup d 67 2)+c.measure (ogroup d 69 1)+c.measure (ogroup d 70 2)+c.measure (ogroup d 72 1)+c.measure (ogroup d 73 2)+c.measure (ogroup d 75 1)+c.measure (ogroup d 76 2)+c.measure (ogroup d 78 1)+c.measure (ogroup d 79 2)+c.measure (ogroup d 81 1)+c.measure (ogroup d 82 2)+c.measure (ogroup d 84 1) := by
  have p0 := gsplit c d (opk d) 1 9 75
  have p1 := gsplit c d (opk d) 10 2 73
  have p2 := gsplit c d (opk d) 12 1 72
  have p3 := gsplit c d (opk d) 13 2 70
  have p4 := gsplit c d (opk d) 15 1 69
  have p5 := gsplit c d (opk d) 16 2 67
  have p6 := gsplit c d (opk d) 18 1 66
  have p7 := gsplit c d (opk d) 19 2 64
  have p8 := gsplit c d (opk d) 21 1 63
  have p9 := gsplit c d (opk d) 22 2 61
  have p10 := gsplit c d (opk d) 24 1 60
  have p11 := gsplit c d (opk d) 25 2 58
  have p12 := gsplit c d (opk d) 27 1 57
  have p13 := gsplit c d (opk d) 28 2 55
  have p14 := gsplit c d (opk d) 30 1 54
  have p15 := gsplit c d (opk d) 31 2 52
  have p16 := gsplit c d (opk d) 33 1 51
  have p17 := gsplit c d (opk d) 34 2 49
  have p18 := gsplit c d (opk d) 36 1 48
  have p19 := gsplit c d (opk d) 37 2 46
  have p20 := gsplit c d (opk d) 39 1 45
  have p21 := gsplit c d (opk d) 40 2 43
  have p22 := gsplit c d (opk d) 42 1 42
  have p23 := gsplit c d (opk d) 43 2 40
  have p24 := gsplit c d (opk d) 45 1 39
  have p25 := gsplit c d (opk d) 46 2 37
  have p26 := gsplit c d (opk d) 48 1 36
  have p27 := gsplit c d (opk d) 49 2 34
  have p28 := gsplit c d (opk d) 51 1 33
  have p29 := gsplit c d (opk d) 52 2 31
  have p30 := gsplit c d (opk d) 54 1 30
  have p31 := gsplit c d (opk d) 55 2 28
  have p32 := gsplit c d (opk d) 57 1 27
  have p33 := gsplit c d (opk d) 58 2 25
  have p34 := gsplit c d (opk d) 60 1 24
  have p35 := gsplit c d (opk d) 61 2 22
  have p36 := gsplit c d (opk d) 63 1 21
  have p37 := gsplit c d (opk d) 64 2 19
  have p38 := gsplit c d (opk d) 66 1 18
  have p39 := gsplit c d (opk d) 67 2 16
  have p40 := gsplit c d (opk d) 69 1 15
  have p41 := gsplit c d (opk d) 70 2 13
  have p42 := gsplit c d (opk d) 72 1 12
  have p43 := gsplit c d (opk d) 73 2 10
  have p44 := gsplit c d (opk d) 75 1 9
  have p45 := gsplit c d (opk d) 76 2 7
  have p46 := gsplit c d (opk d) 78 1 6
  have p47 := gsplit c d (opk d) 79 2 4
  have p48 := gsplit c d (opk d) 81 1 3
  have p49 := gsplit c d (opk d) 82 2 1
  simp only [ogroup]
  norm_num only [] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49
  omega


theorem ooverhead (j : Nat) (d : Bool) :
    toffoliCount (oten j (!d)) = toffoliCount (ogroup d j 2)+(if d then 106 else 101) ∧
    measurementCount (oten j (!d)) = measurementCount (ogroup d j 2)+(if d then 106 else 101) := by
  cases d <;>
    simp only [ogroup,PacketSequence.program,Bool.not_true,Bool.not_false,oten,ofirst,osecond,
      enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
      List.append_nil,toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,ReducedWindowArchives.enter0_counts.2.1,ReducedWindowArchives.switch0_counts.2.1,ReducedWindowArchives.leave0_counts.2.1,
      ReducedWindowArchives.enter1_counts.2.1,ReducedWindowArchives.switch1_counts.2.1,ReducedWindowArchives.leave1_counts.2.1,ReducedWindowArchives.enter0_counts.2.2.1,
      ReducedWindowArchives.switch0_counts.2.2.1,ReducedWindowArchives.leave0_counts.2.2.1,ReducedWindowArchives.enter1_counts.2.2.1,
      ReducedWindowArchives.switch1_counts.2.2.1,ReducedWindowArchives.leave1_counts.2.2.1] <;> constructor <;> omega

private theorem ofield_pieces (c : Cost) (d : Bool) :
    c.measure (ogroup d 1 84)=c.measure (RouteA.Rolling1588.groups d 1 83)+
      c.measure (oddPk d 84) := by
  rw [ogroup_measure]
  have b := gsplit c d (oddPk d) 1 83 1
  have p3 := oneP c d (oddPk d) 84
  have p2 := congrArg c.measure (oseq_congr d (oddPk d) (RouteA.Rolling1588.packet d) 83 1
    (fun k l u => oddPk_mid d k l (by omega)))
  norm_num only [] at b
  unfold RouteA.Rolling1588.groups
  omega

private theorem rfield_pieces (c : Cost) (d : Bool) :
    c.measure (group d 1 84)=c.measure (ECDSAAdd.Entrant.Rolling1588.groups d 1 83)+
      c.measure (ECDSAAdd.Entrant.Rolling1588.packet d 84) := by
  rw [group_measure]
  unfold ECDSAAdd.Entrant.Rolling1588.groups
  have b := gsplit c d (ECDSAAdd.Entrant.Rolling1588.packet d) 1 83 1
  have p3 := oneP c d (ECDSAAdd.Entrant.Rolling1588.packet d) 84
  norm_num only [] at b
  omega

/-- the hosted odd field packets 1..84 save 1260 T / 1680 M against the record packets 1..84. -/
theorem ofield_counts (d : Bool) :
    toffoliCount (ogroup d 1 84)+1260=toffoliCount (group d 1 84) ∧
    measurementCount (ogroup d 1 84)+1680=measurementCount (group d 1 84) := by
  have o1 := ofield_pieces tc d
  have o2 := ofield_pieces mc d
  have r1 := rfield_pieces tc d
  have r2 := rfield_pieces mc d
  rw [show tc.measure=toffoliCount from rfl] at o1 r1
  rw [show mc.measure=measurementCount from rfl] at o2 r2
  have g := RouteA.Rolling1588.groups_count_delta d 1 83 (by decide)
  rw [if_neg (by cases d <;> decide)] at g
  have h84 := OddFullPass.P1LifeLoan.packet_counts d 0 84 (by decide) (by decide)
  rw [StairGroups.packet_zero] at h84
  rw [oddPk_end] at o1 o2
  norm_num only at h84
  simp only [if_true,if_false] at h84
  exact ⟨by omega,by omega⟩

theorem half760OddLoan_zero_eq (d : Bool) :
    OddFullPass.P1LifeLoan.half760OddLoan 0 d = P1Life.half (base 760) d base (base 2409) := by
  cases d <;> simp only [OddFullPass.P1LifeLoan.half760OddLoan,P1Life.half,
    OddFullPass.P1LifeLoan.forwardLoan,P1Life.forward,
    OddFullPass.P1LifeLoan.inverseLoan,P1Life.inverse,
    OddFullPass.P1LifeLoan.p1Seed,P1Life.p1Seed,
    OddFullPass.P1LifeLoan.rawAddLoan,P1Life.rawAdd,
    OddFullPass.P1LifeLoan.foldLoan,OddFullPass.P1LifeLoan.foldAdd_zero,P1Life.fold,
    OddFullPass.P1LifeLoan.rawSubLoan,P1Life.rawSub,
    OddFullPass.P1LifeLoan.unfoldLoan,OddFullPass.P1LifeLoan.unfoldSub_zero,P1Life.unfoldStep,
    OddFullPass.P1LifeLoan.compareBlockLoan,P1Life.compare,
    OddFullPass.P1LifeLoan.short_zero,OddFullPass.P1LifeLoan.previousShort,P1Life.shortConstAdd,
    OddFullPass.P1LifeLoan.orMajor,P1Life.orMajor,
    OddFullPass.P1LifeLoan.orErase,P1Life.orErase,
    OddFullPass.P1LifeLoan.prepareCompare,P1Life.prepareCompare,
    OddFullPass.P1LifeLoan.exposure,P1Life.exposure,
    StairLoan.addPrefixLoan_zero,StairLoan.mappedAddLoan_zero,
    StairLoan.addTopLoan_zero,StairLoan.mappedSubLoan_zero,
    StairLoan.compareLoan_zero,StairLoan.literalConstAddLoan_zero,
    show (0 : Nat) < 6 by decide,if_true,if_false,Bool.false_eq_true]

/-- gate slots of the hosted odd field packets against the record packets 1..84. -/
theorem ofield_slots (d : Bool) :
    slots.measure (ogroup d 1 84)+(if d then 14280 else 11760)=
      slots.measure (group d 1 84)+(if d then 0 else 0) := by
  have o := ofield_pieces slots d
  have r := rfield_pieces slots d
  rw [show slots.measure=Challenge.gateSlots from rfl] at o r ⊢
  have g := RouteA.Rolling1588.groups_slot_delta d 1 83 (by decide)
  rw [if_neg (by cases d <;> decide)] at g
  have h0eq := half760OddLoan_zero_eq d
  have h84sl : Challenge.gateSlots (OddFullPass.P1LifeLoan.packet d 0 84) + 5 * RouteA.Rolling1588.halfSlotSaving d =
      Challenge.gateSlots (ECDSAAdd.Entrant.Rolling1588.packet d 84) := by
    have h32 := RouteA.Rolling1588.cell_slot_delta d 84 3 2
    have h42 := RouteA.Rolling1588.cell_slot_delta d 84 4 2
    have hcEq : ∀ a b, OddFullPass.P1LifeLoan.cell d 0 84 a b = RouteA.Rolling1588.cell d 84 a b := by
      intro a b; cases d <;> simp only [OddFullPass.P1LifeLoan.cell,RouteA.Rolling1588.cell,
        OddFullPass.P1LifeLoan.halfWindow,RouteA.Rolling1588.halfWindow,RouteA.Rolling1588.halfWindowWith,
        Bool.false_eq_true,if_false,if_true,h0eq]
    cases d <;> simp only [OddFullPass.P1LifeLoan.packet,ECDSAAdd.Entrant.Rolling1588.packet,
      OddFullPass.P1LifeLoan.basePacket,ECDSAAdd.Entrant.Rolling1588.basePacket,
      Bool.false_eq_true,if_false,if_true,Baselines.rename_gateSlots,Challenge.gateSlots_append,hcEq] at h32 h42 ⊢ <;> omega
  rw [oddPk_end] at o
  cases d <;> simp only [RouteA.Rolling1588.halfSlotSaving,Bool.false_eq_true,if_false,if_true] at g h84sl o ⊢ <;> omega

private theorem osolve (c : Cost) (d : Bool) (delta : Nat)
    (h : ∀j,c.measure (oten j (!d))=c.measure (ogroup d j 2)+delta) :
    c.measure (group84 d)=c.measure (ogroup d 1 84)+25*delta := by
  simp only [group84,ord,h,opartition]
  omega

/-- the field group (odd cell on packets 1..84, ten-blocks included) against the record packets 1..84. -/
theorem group_cost (d : Bool) :
    toffoliCount (group84 d)+0=toffoliCount (group d 1 84)+(if d then 1390 else 1265) ∧
    measurementCount (group84 d)+0=measurementCount (group d 1 84)+(if d then 970 else 845) := by
  have t := osolve tc d (if d then 106 else 101) (fun j => (ooverhead j d).1)
  have m := osolve mc d (if d then 106 else 101) (fun j => (ooverhead j d).2)
  have f := ofield_counts d
  rw [show tc.measure = toffoliCount from rfl] at t
  rw [show mc.measure = measurementCount from rfl] at m
  cases d <;> simp only [if_true,if_false,Bool.false_eq_true] at t m ⊢ <;> exact ⟨by omega, by omega⟩

/-- Static syntax counts include both correction lists of every measurement. -/
theorem group_slots (d : Bool) :
    slots.measure (group84 d)+(if d then 14280 else 11760)=
      slots.measure (group d 1 84)+25*(if d then 5322 else 6122)+(if d then 0 else 0) := by
  have hc := ofield_slots d
  have h (j : Nat) : slots.measure (oten j (!d)) =
      slots.measure (ogroup d j 2)+(if d then 5322 else 6122) := by
    rw [show slots.measure=Challenge.gateSlots from rfl]
    cases d <;>
      simp only [ogroup,PacketSequence.program,Bool.not_true,Bool.not_false,oten,ofirst,osecond,
        enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
        List.append_nil,Challenge.gateSlots_append,Baselines.rename_gateSlots,ReducedWindowArchives.enter0_counts.2.2.2,
        ReducedWindowArchives.switch0_counts.2.2.2,ReducedWindowArchives.leave0_counts.2.2.2,ReducedWindowArchives.enter1_counts.2.2.2,ReducedWindowArchives.switch1_counts.2.2.2,ReducedWindowArchives.leave1_counts.2.2.2] <;> omega
  have w := osolve slots d (if d then 5322 else 6122) h
  cases d <;> simp only [if_true,if_false,Bool.false_eq_true] at hc w ⊢ <;> omega

theorem group_cost_div :
    toffoliCount (group84 true) = toffoliCount (group true 1 84)+1390 ∧
    measurementCount (group84 true) = measurementCount (group true 1 84)+970 := by
  have t := (group_cost true).1
  have m := (group_cost true).2
  simp only [if_true] at t m
  exact ⟨by omega,by omega⟩

theorem group_cost_mul :
    toffoliCount (group84 false) = toffoliCount (group false 1 84)+1265 ∧
    measurementCount (group84 false) = measurementCount (group false 1 84)+845 := by
  have t := (group_cost false).1
  have m := (group_cost false).2
  simp only [Bool.false_eq_true,if_false] at t m
  exact ⟨by omega,by omega⟩
-- oddten:end WCOST


-- Static syntax counts include both correction lists of every measurement.
end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

end

section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowCosts420
open Arithmetic MappedCompressed
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount measurementCount
def due (i : Nat) := if History5.packDue i then 1 else 0
def step (i : Nat) (back measured : Bool) : Nat :=
  let pre := W.compactSkywalkTickPreWidth i - 1
  let post := W.compactSkywalkTickPostWidth i - 1
  if back then
    if measured then post + 2*due i
    else pre+post-1-(if W.trimTick i then 1 else 0)+11*due i
  else if measured then post+W.repairDue i+4*due i
  else pre+post-W.repairDue i-W.fwdDue i-TickRanges.due i+9*due i
def total (i : Nat) (back measured : Bool) : Nat → Nat
  | 0 => 0
  | n+1 => step i back measured + total (i+1) back measured n

private theorem codecs (d : Bool) (i : Nat) (lo : 6 ≤ i) :
    toffoliCount (Rolling1588.Integer.packFirst base d i)=9*due i ∧
    measurementCount (Rolling1588.Integer.packFirst base d i)=4*due i ∧
    toffoliCount (Rolling1588.unpackAtTick d i)=11*due i ∧
    measurementCount (Rolling1588.unpackAtTick d i)=2*due i := by
  have five : i ≠ 5 := by omega
  have nz : i-5 ≠ 0 := by omega
  have c := Rolling1588.code_counts d
  cases h : History5.packDue i <;>
    simp only [Rolling1588.Integer.packFirst, Rolling1588.Integer.packAfter,
      Rolling1588.Integer.encode, Rolling1588.encodeAt, Rolling1588.codeEncodeAt, Rolling1588.unpackAtTick,
      five,nz,if_false,h,Bool.false_eq_true,if_true,due,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,c.1,c.2.1,c.2.2.1,c.2.2.2] <;> simp [measurementCount,toffoliCount]

private theorem walks (d : Bool) (i n : Nat) (lo : 6 ≤ i) (hi : i+n ≤ 511) :
    toffoliCount (Rolling1588TickGap.forward d i n)=total i false false n ∧
    measurementCount (Rolling1588TickGap.forward d i n)=total i false true n ∧
    toffoliCount (Rolling1588.reverse d i n)=total i true false n ∧
    measurementCount (Rolling1588.reverse d i n)=total i true true n := by
  induction n generalizing i with
  | zero => simp [Rolling1588TickGap.forward,Rolling1588.reverse,total,toffoliCount,measurementCount]
  | succ n ih =>
    have tail := ih (i+1) (by omega) (by omega)
    have pack := codecs d i lo
    have ft := TickRanges.tick_counts base i (by omega) base_pool_nodup
    have rt := W.repairedTick_counts base i (by omega) base_pool_nodup
    have st := W.compactSkywalkTick_counts base i (by omega) base_pool_nodup
    have bt := W.ReverseCarry.compactReceiverTick_counts base i (by omega) base_pool_nodup
    have ot := W.compactSkywalkReverseTick_counts base i (by omega) base_pool_nodup
    simp only [Rolling1588TickGap.forward,Rolling1588.reverse,toffoliCount_append,
      measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
      tail.1,tail.2.1,tail.2.2.1,tail.2.2.2,pack.1,pack.2.1,pack.2.2.1,pack.2.2.2,
      total,step,if_true,if_false,Bool.false_eq_true]
    exact ⟨by omega,by omega,by omega,by omega⟩

/-- The stock walk over the ticks the 22-block shadow window (exit 420) replaces: [90,421). -/
theorem stock420 (d : Bool) :
    toffoliCount (Rolling1588TickGap.forward d 90 331)=142889 ∧
    measurementCount (Rolling1588TickGap.forward d 90 331)=71610 ∧
    toffoliCount (Rolling1588.reverse d 90 331)=142889 ∧
    measurementCount (Rolling1588.reverse d 90 331)=71309 := by
  have h := walks d 90 331 (by decide) (by decide)
  exact ⟨h.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),
    h.2.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.2.2.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))⟩

/-- The stock walk over the ticks the 23-block shadow window from tick 75 (exit 420) replaces: [75,421). -/
theorem stock420from75 (d : Bool) :
    toffoliCount (Rolling1588TickGap.forward d 75 346)=150626 ∧
    measurementCount (Rolling1588TickGap.forward d 75 346)=75477 ∧
    toffoliCount (Rolling1588.reverse d 75 346)=150617 ∧
    measurementCount (Rolling1588.reverse d 75 346)=75170 := by
  have h := walks d 75 346 (by decide) (by decide)
  exact ⟨h.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),
    h.2.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.2.2.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))⟩

/-- The stock walk over the ticks the 24-block shadow window from tick 60 (exit 420) replaces: [60,421). -/
theorem stock420from60 (d : Bool) :
    toffoliCount (Rolling1588TickGap.forward d 60 361)=158363 ∧
    measurementCount (Rolling1588TickGap.forward d 60 361)=79344 ∧
    toffoliCount (Rolling1588.reverse d 60 361)=158345 ∧
    measurementCount (Rolling1588.reverse d 60 361)=79031 := by
  have h := walks d 60 361 (by decide) (by decide)
  exact ⟨h.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),
    h.2.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.2.2.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))⟩

/-- The stock walk over the ticks the 25-block shadow window from tick 45 (exit 420) replaces: [45,421). -/
theorem stock420from45 (d : Bool) :
    toffoliCount (Rolling1588TickGap.forward d 45 376)=166100 ∧
    measurementCount (Rolling1588TickGap.forward d 45 376)=83211 ∧
    toffoliCount (Rolling1588.reverse d 45 376)=166073 ∧
    measurementCount (Rolling1588.reverse d 45 376)=82892 := by
  have h := walks d 45 376 (by decide) (by decide)
  exact ⟨h.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)),
    h.2.2.1.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)), h.2.2.2.trans (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))⟩

end ECDSAAdd.Entrant.StairPacket.StockWindowCosts420

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [45,406); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 29 ++
    TickCut.CutWindow.forwardCut d ++ Rolling1588TickGap.forward d 421 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 421 tail ++
    TickCut.CutWindow.reverseCut d ++ Rolling1588.reverse d 16 29) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (TickCut.CutWindow.forwardCut d)+f=c.measure (Rolling1588TickGap.forward d 45 376))
    (hr : c.measure (TickCut.CutWindow.reverseCut d)+r=c.measure (Rolling1588.reverse d 45 376)) :
    c.measure (forward d tail)+f=c.measure (Stair44WalkRun.forward d (405+tail)) ∧
    c.measure (backward d tail)+r=c.measure (Stair44WalkRun.backward d (405+tail)) := by
  have a := StairRestSupport.forward_append d 29 16 (376+tail)
  have b := StairRestSupport.forward_append d 376 45 tail
  have x := StairRestSupport.reverse_append d 29 16 (376+tail)
  have y := StairRestSupport.reverse_append d 376 45 tail
  change Rolling1588TickGap.forward d 16 (29+(376+tail)) =
    Rolling1588TickGap.forward d 16 29 ++ Rolling1588TickGap.forward d 45 (376+tail) at a
  change Rolling1588.reverse d 16 (29+(376+tail)) =
    Rolling1588.reverse d 45 (376+tail) ++ Rolling1588.reverse d 16 29 at x
  rw [b] at a
  rw [y] at x
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,forward,backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

attribute [local irreducible] TickCut.CutWindow.forwardCut TickCut.CutWindow.reverseCut Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 38898 else 38898)=
      toffoliCount (Stair44WalkRun.forward d (405+tail)) ∧
    toffoliCount (backward d tail)+(if d then 38804 else 38779)=
      toffoliCount (Stair44WalkRun.backward d (405+tail)) ∧
    measurementCount (forward d tail)+(if d then 17171 else 17171)=measurementCount (Stair44WalkRun.forward d (405+tail)) ∧
    measurementCount (backward d tail)+(if d then 17220 else 17195)=measurementCount (Stair44WalkRun.backward d (405+tail)) := by
  cases d
  · have sf := StockWindowCosts420.stock420from45 false
    have a : toffoliCount (TickCut.CutWindow.forwardCut false) = 127202 := TickCut.CutWindow.cut_toffoliF.2
    have b : toffoliCount (TickCut.CutWindow.reverseCut false) = 127294 := TickCut.CutWindow.cut_toffoliR.2
    have c : measurementCount (TickCut.CutWindow.forwardCut false) = 66040 := TickCut.CutWindow.cut_measureF.2
    have e : measurementCount (TickCut.CutWindow.reverseCut false) = 65697 := TickCut.CutWindow.cut_measureR.2
    have t := walk tc false tail 38898 38779
      (subEq 38898 a sf.1 (by omega)) (subEq 38779 b sf.2.2.1 (by omega))
    have m := walk mc false tail 17171 17195
      (subEq 17171 c sf.2.1 (by omega)) (subEq 17195 e sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,m⟩
  · have sf := StockWindowCosts420.stock420from45 true
    have a : toffoliCount (TickCut.CutWindow.forwardCut true) = 127202 := TickCut.CutWindow.cut_toffoliF.1
    have b : toffoliCount (TickCut.CutWindow.reverseCut true) = 127269 := TickCut.CutWindow.cut_toffoliR.1
    have c : measurementCount (TickCut.CutWindow.forwardCut true) = 66040 := TickCut.CutWindow.cut_measureF.1
    have e : measurementCount (TickCut.CutWindow.reverseCut true) = 65672 := TickCut.CutWindow.cut_measureR.1
    have t := walk tc true tail 38898 38804
      (subEq 38898 a sf.1 (by omega)) (subEq 38804 b sf.2.2.1 (by omega))
    have m := walk mc true tail 17171 17220
      (subEq 17171 c sf.2.1 (by omega)) (subEq 17220 e sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,m⟩


/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 38898 else 38898)=f) (hr : (if d then 38804 else 38779)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+(if d then 17171 else 17171)=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+(if d then 17220 else 17195)=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact exactWalks d tail

theorem instMeasurements (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 17171 else 17171)=f) (hr : (if d then 17220 else 17195)=r) :
    mc.measure (forward d tail)+f=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+r=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact (exactWalks d tail).2.2
end ECDSAAdd.Entrant.StairPacket.WindowWalkCosts

end




namespace ECDSAAdd.Entrant.PackCutExit
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutTrip

/-- The exit packet without its trailing encode tail `ep`. -/
def basePacketHeadF (d j : Nat) : Program :=
  Rolling1588.onPacket j Rolling1588.dp ++ Rolling1588.onPacket j ParityCodec5New.untwist ++
    (StairGroups.cell false d j 4 2 ++ Rolling1588.onPacket j Rolling1588.bridge5 ++
      StairGroups.cell false d j 3 2 ++ StairGroups.cell false d j 4 2 ++
      Rolling1588.onPacket j Rolling1588.bridge7inv ++
      StairGroups.cell false d j 4 2 ++ StairGroups.cell false d j 3 2) ++
    Rolling1588.onPacket j ParityCodec5New.twist

theorem basePacket_false_tail (d j : Nat) :
    StairGroups.basePacket false d j = basePacketHeadF d j ++ Rolling1588.onPacket j Rolling1588.ep := by
  simp only [StairGroups.basePacket, basePacketHeadF, Bool.false_eq_true, if_false, Rolling1588.onPacket,
    rename_app, List.append_assoc]

theorem hostedGroup_false_tail (hp : StairHostsSchedule.HostPlan) (d first c : Nat) :
    StairHostsSchedule.hostedGroup hp false d first (c + 1) =
      StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group false d first (c + 1))
        (renameProgram (OB5.sig 511) (StairGroups.groups false d (first + 1) c) ++
         renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first))) ++
      StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group false d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.ep))) := by
  simp only [StairHostsSchedule.hostedGroup, StairSchedule.placedGroups, StairConcrete.bestLoans,
    StairGroups.groups, program_false_tail, StairGroups.packet, basePacket_false_tail, rename_app,
    rebindMany_append, List.append_assoc]

theorem movedReverse_add (w : Nat → Wire) (i a b : Nat) :
    StairReplay.movedReverse w i (a + b) =
      StairReplay.movedReverse w (i + a) b ++ StairReplay.movedReverse w i a := by
  induction a generalizing i with
  | zero => simp [StairReplay.movedReverse]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [StairReplay.movedReverse, ih (i + 1), List.append_assoc]
    rw [show i + 1 + a = i + (a + 1) by omega]

/-- Expose tick `i + k` of a moved reverse run (higher ticks first). -/
theorem movedReverse_at (w : Nat → Wire) (i k b : Nat) :
    StairReplay.movedReverse w i (k + 1 + b) =
      StairReplay.movedReverse w (i + k + 1) b ++
        ((Rolling1588.Integer.unpackFirst w true (i + k) ++ W.ReverseCarry.compactReceiverTick w (i + k)) ++
          StairReplay.movedReverse w i k) := by
  rw [show k + 1 + b = k + (1 + b) by omega, movedReverse_add w i k (1 + b),
    show 1 + b = 0 + 1 + b by omega, movedReverse_add w (i + k) (0 + 1) b]
  simp only [StairReplay.movedReverse, List.nil_append, List.append_assoc, Nat.zero_add]

theorem unpackFirst_due (w : Nat → Wire) (i : Nat) (h5 : i ≠ 5) (hdue : History5.packDue i = true)
    (hs : i - 5 ≠ 0) :
    Rolling1588.Integer.unpackFirst w true i =
      Rolling1588.codeDecodeAt true (History5.historyMap w (i - 5)) := by
  simp only [Rolling1588.Integer.unpackFirst, h5, if_false, Rolling1588.Integer.decodeBefore, hdue,
    if_true, Rolling1588.Integer.decode, hs, Rolling1588.decodeAt]

/-- The due-read decode after its leading `dp`. -/
def D26 : Program := (Rolling1588.codeDecode true).drop 26

theorem dp_D26 : Rolling1588.codeDecode true = Rolling1588.dp ++ D26 := by
  unfold D26; rw [show Rolling1588.dp = (Rolling1588.codeDecode true).take 26 by decide]
  exact (List.take_append_drop _ _).symm

/-- The exit packet's shortened encode before its closing `ep`: stage-2 code then `twist`. -/
def E138x : Program := Rolling1588.stageCode false 2 ++ ParityCodec5New.twist

open MeasuredCodec5 in
/-- The exit trip on one ten-bit word. -/
def tripXOk (x : Nat) : Bool :=
  safe E138x x && safe Rolling1588.ep (bitRun E138x x) &&
    safe Rolling1588.dp (bitRun Rolling1588.ep (bitRun E138x x)) &&
    (bitRun Rolling1588.dp (bitRun Rolling1588.ep (bitRun E138x x)) == bitRun E138x x)

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c0 : ∀ y < 128, legalNat (y + 128 * 0) = true → tripXOk (y + 128 * 0) = true := by
  decide +kernel

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c1 : ∀ y < 128, legalNat (y + 128 * 1) = true → tripXOk (y + 128 * 1) = true := by
  decide +kernel

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c2 : ∀ y < 128, legalNat (y + 128 * 2) = true → tripXOk (y + 128 * 2) = true := by
  decide +kernel

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c3 : ∀ y < 128, legalNat (y + 128 * 3) = true → tripXOk (y + 128 * 3) = true := by
  decide +kernel

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c4 : ∀ y < 128, legalNat (y + 128 * 4) = true → tripXOk (y + 128 * 4) = true := by
  decide +kernel

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c5 : ∀ y < 128, legalNat (y + 128 * 5) = true → tripXOk (y + 128 * 5) = true := by
  decide +kernel

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c6 : ∀ y < 128, legalNat (y + 128 * 6) = true → tripXOk (y + 128 * 6) = true := by
  decide +kernel

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem tripX_c7 : ∀ y < 128, legalNat (y + 128 * 7) = true → tripXOk (y + 128 * 7) = true := by
  decide +kernel

theorem tripX_of_chunk (x k : Nat)
    (c : ∀ y < 128, MeasuredCodec5.legalNat (y + 128 * k) = true → tripXOk (y + 128 * k) = true)
    (h1 : 128 * k ≤ x) (h2 : x < 128 * k + 128) (lx : MeasuredCodec5.legalNat x = true) : tripXOk x = true := by
  have e : x - 128 * k + 128 * k = x := Nat.sub_add_cancel h1
  have := c (x - 128 * k) (by omega) (by rw [e]; exact lx)
  rwa [e] at this

open MeasuredCodec5 in
theorem finite_tripX : ∀ x < 1024, legalNat x = true →
    (safe E138x x && safe Rolling1588.ep (bitRun E138x x) &&
      safe Rolling1588.dp (bitRun Rolling1588.ep (bitRun E138x x)) &&
      (bitRun Rolling1588.dp (bitRun Rolling1588.ep (bitRun E138x x)) == bitRun E138x x)) = true := by
  intro x hx lx
  show tripXOk x = true
  rcases (by omega : x < 128 ∨ (128 ≤ x ∧ x < 256) ∨ (256 ≤ x ∧ x < 384) ∨ (384 ≤ x ∧ x < 512) ∨
      (512 ≤ x ∧ x < 640) ∨ (640 ≤ x ∧ x < 768) ∨ (768 ≤ x ∧ x < 896) ∨ (896 ≤ x ∧ x < 1024)) with
    h | h | h | h | h | h | h | h
  · exact tripX_of_chunk x 0 tripX_c0 (by omega) (by omega) lx
  · exact tripX_of_chunk x 1 tripX_c1 (by omega) (by omega) lx
  · exact tripX_of_chunk x 2 tripX_c2 (by omega) (by omega) lx
  · exact tripX_of_chunk x 3 tripX_c3 (by omega) (by omega) lx
  · exact tripX_of_chunk x 4 tripX_c4 (by omega) (by omega) lx
  · exact tripX_of_chunk x 5 tripX_c5 (by omega) (by omega) lx
  · exact tripX_of_chunk x 6 tripX_c6 (by omega) (by omega) lx
  · exact tripX_of_chunk x 7 tripX_c7 (by omega) (by omega) lx

open MeasuredCodec5 in
set_option maxRecDepth 100000 in
theorem suppX : wires E138x ⊆ Finset.range 10 := by decide +kernel

open MeasuredCodec5 in
theorem local_tripX (t : State) (h : legal t.basis) (m0 me md : List Bool) :
    run Rolling1588.dp md (run Rolling1588.ep me (run E138x m0 t)) = run E138x m0 t := by
  obtain ⟨x, hx, lx, hb⟩ := local_word t h
  have fin := finite_tripX x hx lx
  simp only [Bool.and_eq_true, beq_iff_eq] at fin
  obtain ⟨⟨⟨s1, s2⟩, s3⟩, e4⟩ := fin
  let u : State := ⟨t.phase, bitsOf x⟩
  have r1 : run E138x m0 u = ⟨t.phase, bitsOf (bitRun E138x x)⟩ := by
    rw [run_sim, sim_safe E138x x s1]
  have r2 : run Rolling1588.ep me (run E138x m0 u) =
      ⟨t.phase, bitsOf (bitRun Rolling1588.ep (bitRun E138x x))⟩ := by
    rw [r1, run_sim, sim_safe _ _ s2]
  have r3 : run Rolling1588.dp md (run Rolling1588.ep me (run E138x m0 u)) = run E138x m0 u := by
    rw [r2, run_sim, sim_safe _ _ s3, e4, r1]
  have agree0 : ∀ q ∈ Finset.range 10, t.basis q = u.basis q := fun q hq => hb q hq
  have l1 := run_measured_locality E138x (Finset.range 10) suppX t u m0 rfl agree0
  have l2 := run_measured_locality Rolling1588.ep (Finset.range 10) PackCutTrip.supp.2.1 _ _ me l1.1 l1.2
  have l3 := run_measured_locality Rolling1588.dp (Finset.range 10) PackCutTrip.supp.2.2 _ _ md l2.1 l2.2
  rw [r3] at l3
  apply State.extensionality
  · exact l3.1.trans l1.1.symm
  · funext q
    by_cases hq : q ∈ Finset.range 10
    · exact (l3.2 q hq).trans (l1.2 q hq).symm
    · rw [run_preserves_outside _ md _ q (fun hh => hq (PackCutTrip.supp.2.2 hh)),
        run_preserves_outside _ me _ q (fun hh => hq (PackCutTrip.supp.2.1 hh))]

open MeasuredCodec5 in
/-- Placed exit trip (any injective ten-wire placement with legal letters). -/
theorem placed_tripX (f : Fin 10 → Wire) (hf : Function.Injective f) (s : State)
    (h : legalAt f s.basis) (m0 me md : List Bool) :
    run (renameProgram (label f) Rolling1588.dp) md
      (run (renameProgram (label f) Rolling1588.ep) me (run (renameProgram (label f) E138x) m0 s)) =
      run (renameProgram (label f) E138x) m0 s := by
  have inj := FirstNonzeroCodec.label_inj' f hf
  let t : State := ⟨s.phase, fun q => s.basis (label f q)⟩
  have p1 := run_rename_pool (label f) (Finset.range 10) inj E138x suppX m0 t s rfl (fun _ _ => rfl)
  let A := run (renameProgram (label f) E138x) m0 s
  let Al := run E138x m0 t
  have p2 := run_rename_pool (label f) (Finset.range 10) inj Rolling1588.ep PackCutTrip.supp.2.1 me Al A
    p1.1.symm (fun q hq => (p1.2 q hq).symm)
  have p3 := run_rename_pool (label f) (Finset.range 10) inj Rolling1588.dp PackCutTrip.supp.2.2 md
    (run Rolling1588.ep me Al) (run (renameProgram (label f) Rolling1588.ep) me A)
    p2.1.symm (fun q hq => (p2.2 q hq).symm)
  have lt := local_tripX t h m0 me md
  have suppP := renameProgram_support (label f) Rolling1588.ep
  have suppD := renameProgram_support (label f) Rolling1588.dp
  apply State.extensionality
  · exact p3.1.trans ((congrArg State.phase lt).trans p1.1.symm)
  · funext q
    by_cases hq : q ∈ (Finset.range 10).image (label f)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact (p3.2 i hi).trans ((congrArg (fun st : State => st.basis i) lt).trans (p1.2 i hi).symm)
    · have nE : q ∉ wires (renameProgram (label f) Rolling1588.ep) := by
        rw [suppP]; intro hh; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
        exact hq (Finset.mem_image.mpr ⟨i, PackCutTrip.supp.2.1 hi, rfl⟩)
      have nD : q ∉ wires (renameProgram (label f) Rolling1588.dp) := by
        rw [suppD]; intro hh; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
        exact hq (Finset.mem_image.mpr ⟨i, PackCutTrip.supp.2.2 hi, rfl⟩)
      rw [run_preserves_outside _ md _ q nD, run_preserves_outside _ me _ q nE]

open MeasuredCodec5 in
/-- PACK-CUT exit row (generic): the group's closing encode tail `Eh` (= the placed `ep`) and the next reverse
segment's due-read head `Dh` (= the placed `dp`) cancel around the segment prefix `M`, provided `M` never touches
the packet's ten wires and, for every tape of the group prefix `A`, the state after `A` is the placed shortened
encode `E138x` of a state with legal letters. -/
theorem exit_row_cut_gen (A Eh M Dh B : Program) (F : Fin 10 → Wire) (hF : Function.Injective F)
    (hep : Eh = renameProgram (label F) Rolling1588.ep) (hdp : Dh = renameProgram (label F) Rolling1588.dp)
    (hM : ∀ q ∈ (Finset.range 10).image (label F), q ∉ wires M)
    (s : State) (m : List Bool)
    (hframe : ∀ tA, ∃ (raw : State) (m0 : List Bool), legalAt F raw.basis ∧
      run A tA s = run (renameProgram (label F) E138x) m0 raw) :
    ∃ m', run (A ++ M ++ B) m s = run (A ++ Eh ++ M ++ Dh ++ B) m' s := by
  subst hep hdp
  have hE : wires (renameProgram (label F) Rolling1588.ep) ⊆ (Finset.range 10).image (label F) := by
    rw [renameProgram_support]; exact Finset.image_subset_image PackCutTrip.supp.2.1
  have hD : wires (renameProgram (label F) Rolling1588.dp) ⊆ (Finset.range 10).image (label F) := by
    rw [renameProgram_support]; exact Finset.image_subset_image PackCutTrip.supp.2.2
  refine row_cut A _ M _ B _ hE hD hM s m ?_
  intro tA me md
  obtain ⟨raw, m0, hl, hA⟩ := hframe tA
  rw [hA]
  exact placed_tripX F hF raw hl m0 me md

open MeasuredCodec5 in
/-- The same row with the hosted group written out: the cut group drops its final hosted `ep`, the cut segment
drops the due read's leading `dp`. -/
theorem exit_row_cut (hp : StairHostsSchedule.HostPlan) (d first c : Nat) (SEG M Bx : Program)
    (F : Fin 10 → Wire) (hF : Function.Injective F)
    (hep : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group false d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.ep))) = renameProgram (label F) Rolling1588.ep)
    (hseg : SEG = M ++ renameProgram (label F) Rolling1588.dp ++ Bx)
    (hM : ∀ q ∈ (Finset.range 10).image (label F), q ∉ wires M)
    (s : State) (m : List Bool)
    (hframe : ∀ tA, ∃ (raw : State) (m0 : List Bool), legalAt F raw.basis ∧
      run (StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group false d first (c + 1))
        (renameProgram (OB5.sig 511) (StairGroups.groups false d (first + 1) c) ++
         renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first))))
        tA s = run (renameProgram (label F) E138x) m0 raw) :
    ∃ m', run (StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hp.group false d first (c + 1))
        (renameProgram (OB5.sig 511) (StairGroups.groups false d (first + 1) c) ++
         renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first)))
        ++ M ++ Bx) m s =
      run (StairHostsSchedule.hostedGroup hp false d first (c + 1) ++ SEG) m' s := by
  obtain ⟨m', h⟩ := exit_row_cut_gen _ _ M _ Bx F hF hep rfl hM s m hframe
  refine ⟨m', ?_⟩
  rw [h, hostedGroup_false_tail, hseg]
  simp only [List.append_assoc]

end ECDSAAdd.Entrant.PackCutExit

namespace ECDSAAdd.Entrant.PackCutExitRows
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutTrip PackCutExit

def cwl : List Correction → List Wire
  | [] => []
  | .Z t :: cs => t :: cwl cs
  | .CZ a b :: cs => a :: b :: cwl cs

def iwl : Instr → List Wire
  | .X t => [t]
  | .CX c t => [c, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c0 c1 => t :: (cwl c0 ++ cwl c1)

def wl : Program → List Wire
  | [] => []
  | i :: p => iwl i ++ wl p

theorem mem_cwl (q : Wire) (cs : List Correction) : q ∈ correctionWires cs ↔ q ∈ cwl cs := by
  induction cs with
  | nil => simp [correctionWires, cwl]
  | cons c cs ih => cases c <;> simp [correctionWires, cwl, ih]

theorem mem_iwl (q : Wire) (i : Instr) : q ∈ i.wires ↔ q ∈ iwl i := by
  cases i <;> simp [Instr.wires, iwl, mem_cwl]

theorem mem_wl (q : Wire) (P : Program) : q ∈ wires P ↔ q ∈ wl P := by
  induction P with
  | nil => simp [wires, wl]
  | cons i p ih => simp [wires, wl, mem_iwl, ih]

theorem avoid_list (L : List Wire) (M : Program) (h : L.all (fun q => !((wl M).contains q)) = true) :
    ∀ q ∈ L, q ∉ wires M := by
  intro q hq hm
  rw [mem_wl] at hm
  have h1 := List.all_eq_true.mp h q hq
  have h2 : q ∉ wl M := by simpa using h1
  exact h2 hm

/-- `unpack N` only touches the row sites of budget `N`, so a word that avoids those sites avoids `unpack N`. -/
theorem unpack_avoid (N : Nat) (hN : N ∈ StairPhysicalLayout.budgets) (L : List Wire)
    (h : L.all (fun q => !((StairPhysicalPrimitives.rowSitesL N).contains q)) = true) :
    L.all (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.unpack N)).contains q)) = true := by
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have h1 : q ∉ StairPhysicalPrimitives.rowSitesL N := by simpa using h q hq
  have h2 : q ∉ wl (StairConcreteAssembly.checkpointPrimitives.unpack N) := fun hw =>
    h1 (StairPhysicalPrimitives.unpack_rows N hN q ((mem_wl q _).mpr hw))
  simpa using h2

theorem avoid3 (L : List Wire) (A B C : Program)
    (ha : L.all (fun q => !((wl A).contains q)) = true)
    (hb : L.all (fun q => !((wl B).contains q)) = true)
    (hc : L.all (fun q => !((wl C).contains q)) = true) :
    L.all (fun q => !((wl (A ++ B ++ C)).contains q)) = true := by
  rw [List.all_eq_true]
  intro q hq
  have na := avoid_list L A ha q hq
  have nb := avoid_list L B hb q hq
  have nc := avoid_list L C hc q hq
  have hn : q ∉ wl (A ++ B ++ C) := by
    rw [← mem_wl, wires_append, wires_append]
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨na, nb⟩, nc⟩
  simpa using hn


theorem label_virt (w : Nat → Wire) (first : Nat) (q : Wire)
    (hq : q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap w (5 * first)))) :
    StairFirstTickV3.VWire w (5 * first + 5) q := by
  simp only [Finset.mem_image, Finset.mem_range] at hq
  obtain ⟨k, hk, rfl⟩ := hq
  refine ⟨History5.historyId (5 * first) ⟨k, hk⟩, ?_, ?_⟩
  · unfold StairFirstTickV3.Virt History5.historyId; split_ifs <;> omega
  · simp [MeasuredCodec5.label, hk, History5.historyMap]

/-- The reverse segment before its due read: unpack, the finish read, orientation, the ticks above the due tick. -/
def headX (N f : Nat) : Program :=
  StairConcreteAssembly.checkpointPrimitives.unpack N ++
    renameProgram (OB5.sig f) (Rolling1588.unpackAtTick true f) ++
    StairConcreteAssembly.checkpointPrimitives.orientR f

def segW (s : Nat) : Nat → Wire :=
  StairPhysicalPrimitivesFix505.revSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))

/-- The due tick sits at `s + 1 + k`; `b` ticks lie above it. -/
theorem seg_split (B N s k b f : Nat) (hf : f = s + 1 + k + 1 + b) (h5 : s + 1 + k ≠ 5)
    (hdue : History5.packDue (s + 1 + k) = true) (hs0 : s + 1 + k - 5 ≠ 0) :
    StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives B N s f =
      (headX N f ++ StairReplay.movedReverse (segW s) (s + 1 + k + 1) b) ++
      renameProgram (MeasuredCodec5.label (History5.historyMap (segW s) (s + 1 + k - 5))) Rolling1588.dp ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (segW s) (s + 1 + k - 5))) D26 ++
        W.ReverseCarry.compactReceiverTick (segW s) (s + 1 + k) ++
        StairReplay.movedReverse (segW s) (s + 1) k ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse s ++
        StairConcreteAssembly.checkpointPrimitives.pack B) := by
  have e : f - s - 1 = k + 1 + b := by omega
  have hm : StairConcreteAssembly.checkpointPrimitives.middleReverse (s + 1) (f - s - 1) =
      StairReplay.movedReverse (segW s) (s + 1) (f - s - 1) := rfl
  simp only [StairSchedule.reverseSegment, headX]
  rw [hm, e, movedReverse_at, unpackFirst_due _ _ h5 hdue hs0]
  simp only [Rolling1588.codeDecodeAt, dp_D26, rename_app, List.append_assoc]

theorem mid_disj (w : Nat → Wire) (hinj : Function.Injective w) (N f first : Nat)
    (hf : f ≤ 512) (hlt : 5 * first + 5 < f)
    (hhead : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap w (5 * first)))).all
      (fun q => !((wl (headX N f)).contains q)) = true) :
    ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap w (5 * first))),
      q ∉ wires (headX N f ++ StairReplay.movedReverse w (5 * first + 5 + 1) (f - (5 * first + 5) - 1)) := by
  intro q hq hm
  rw [wires_append, Finset.mem_union] at hm
  rcases hm with h1 | h2
  · have hq' : q ∈ (List.range 10).map (MeasuredCodec5.label (History5.historyMap w (5 * first))) := by
      simp only [Finset.mem_image, Finset.mem_range] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
    exact avoid_list _ _ hhead q hq' h1
  · exact StairFirstTickV3.movedReverse_clean w hinj (5 * first + 5) (by omega) (f - (5 * first + 5) - 1)
      (5 * first + 5 + 1) (by omega) (by omega) (by omega) q h2 (label_virt w first q hq)

/-! ### Row 0: group (13, 85, 5), segment (87, 62, 425, 450); due tick 430 -/

set_option maxRecDepth 200000 in
theorem hep0 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 13)
      (StairConcreteAssembly.hostPlan.group false 13 85 (4 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 85))
        (Rolling1588.onPacket 85 Rolling1588.ep))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85))) Rolling1588.ep := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head0a : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.unpack 62)).contains q)) = true :=
  unpack_avoid 62 (by decide) _ (by decide +kernel)

set_option maxRecDepth 200000 in
theorem head0b : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85)))).all
      (fun q => !((wl (renameProgram (OB5.sig 450) (Rolling1588.unpackAtTick true 450))).contains q)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head0c : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.orientR 450)).contains q)) = true := by
  decide +kernel

theorem head0 : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85)))).all
      (fun q => !((wl (headX 62 450)).contains q)) = true := by
  unfold headX
  exact avoid3 _ _ _ _ head0a head0b head0c

theorem seg0 : StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450 =
      (headX 62 450 ++ StairReplay.movedReverse (segW 425) (5 * 85 + 5 + 1) (450 - (5 * 85 + 5) - 1)) ++
      renameProgram (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85))) Rolling1588.dp ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85))) D26 ++
        W.ReverseCarry.compactReceiverTick (segW 425) 430 ++
        StairReplay.movedReverse (segW 425) 426 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 425 ++
        StairConcreteAssembly.checkpointPrimitives.pack 87) :=
  seg_split 87 62 425 4 19 450 rfl (by decide) (by decide) (by decide)

theorem inj0 : Function.Injective (History5.historyMap (segW 425) (5 * 85)) :=
  History5.historyMap_injective _ (StairPhysicalPrimitivesFix505.revSegmentMap_pool_nodup 87 (by decide))
    _ (by norm_num)

theorem segW_inj0 : Function.Injective (segW 425) :=
  StairPhysicalPrimitivesFix505.revSegmentMap_injective 87 (by decide)

theorem mid0 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85))),
    q ∉ wires (headX 62 450 ++ StairReplay.movedReverse (segW 425) (5 * 85 + 5 + 1) (450 - (5 * 85 + 5) - 1)) :=
  mid_disj (segW 425) segW_inj0 62 450 85 (by norm_num) (by norm_num) head0

/-! ### Row 1: group (22, 90, 3), segment (62, 47, 450, 465); due tick 455 -/

set_option maxRecDepth 200000 in
theorem hep1 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 22)
      (StairConcreteAssembly.hostPlan.group false 22 90 (2 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 90))
        (Rolling1588.onPacket 90 Rolling1588.ep))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90))) Rolling1588.ep := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head1a : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.unpack 47)).contains q)) = true :=
  unpack_avoid 47 (by decide) _ (by decide +kernel)

set_option maxRecDepth 200000 in
theorem head1b : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90)))).all
      (fun q => !((wl (renameProgram (OB5.sig 465) (Rolling1588.unpackAtTick true 465))).contains q)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head1c : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.orientR 465)).contains q)) = true := by
  decide +kernel

theorem head1 : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90)))).all
      (fun q => !((wl (headX 47 465)).contains q)) = true := by
  unfold headX
  exact avoid3 _ _ _ _ head1a head1b head1c

theorem seg1 : StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465 =
      (headX 47 465 ++ StairReplay.movedReverse (segW 450) (5 * 90 + 5 + 1) (465 - (5 * 90 + 5) - 1)) ++
      renameProgram (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90))) Rolling1588.dp ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90))) D26 ++
        W.ReverseCarry.compactReceiverTick (segW 450) 455 ++
        StairReplay.movedReverse (segW 450) 451 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 450 ++
        StairConcreteAssembly.checkpointPrimitives.pack 62) :=
  seg_split 62 47 450 4 9 465 rfl (by decide) (by decide) (by decide)

theorem inj1 : Function.Injective (History5.historyMap (segW 450) (5 * 90)) :=
  History5.historyMap_injective _ (StairPhysicalPrimitivesFix505.revSegmentMap_pool_nodup 62 (by decide))
    _ (by norm_num)

theorem segW_inj1 : Function.Injective (segW 450) :=
  StairPhysicalPrimitivesFix505.revSegmentMap_injective 62 (by decide)

theorem mid1 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90))),
    q ∉ wires (headX 47 465 ++ StairReplay.movedReverse (segW 450) (5 * 90 + 5 + 1) (465 - (5 * 90 + 5) - 1)) :=
  mid_disj (segW 450) segW_inj1 47 465 90 (by norm_num) (by norm_num) head1

/-! ### Row 2: group (30, 93, 3), segment (47, 32, 465, 480); due tick 470 -/

set_option maxRecDepth 200000 in
theorem hep2 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 30)
      (StairConcreteAssembly.hostPlan.group false 30 93 (2 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 93))
        (Rolling1588.onPacket 93 Rolling1588.ep))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93))) Rolling1588.ep := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head2a : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.unpack 32)).contains q)) = true :=
  unpack_avoid 32 (by decide) _ (by decide +kernel)

set_option maxRecDepth 200000 in
theorem head2b : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93)))).all
      (fun q => !((wl (renameProgram (OB5.sig 480) (Rolling1588.unpackAtTick true 480))).contains q)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head2c : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.orientR 480)).contains q)) = true := by
  decide +kernel

theorem head2 : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93)))).all
      (fun q => !((wl (headX 32 480)).contains q)) = true := by
  unfold headX
  exact avoid3 _ _ _ _ head2a head2b head2c

theorem seg2 : StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480 =
      (headX 32 480 ++ StairReplay.movedReverse (segW 465) (5 * 93 + 5 + 1) (480 - (5 * 93 + 5) - 1)) ++
      renameProgram (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93))) Rolling1588.dp ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93))) D26 ++
        W.ReverseCarry.compactReceiverTick (segW 465) 470 ++
        StairReplay.movedReverse (segW 465) 466 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 465 ++
        StairConcreteAssembly.checkpointPrimitives.pack 47) :=
  seg_split 47 32 465 4 9 480 rfl (by decide) (by decide) (by decide)

theorem inj2 : Function.Injective (History5.historyMap (segW 465) (5 * 93)) :=
  History5.historyMap_injective _ (StairPhysicalPrimitivesFix505.revSegmentMap_pool_nodup 47 (by decide))
    _ (by norm_num)

theorem segW_inj2 : Function.Injective (segW 465) :=
  StairPhysicalPrimitivesFix505.revSegmentMap_injective 47 (by decide)

theorem mid2 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93))),
    q ∉ wires (headX 32 480 ++ StairReplay.movedReverse (segW 465) (5 * 93 + 5 + 1) (480 - (5 * 93 + 5) - 1)) :=
  mid_disj (segW 465) segW_inj2 32 480 93 (by norm_num) (by norm_num) head2

/-! ### Row 3: group (36, 96, 2), segment (32, 22, 480, 490); due tick 485 -/

set_option maxRecDepth 200000 in
theorem hep3 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 36)
      (StairConcreteAssembly.hostPlan.group false 36 96 (1 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 96))
        (Rolling1588.onPacket 96 Rolling1588.ep))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96))) Rolling1588.ep := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head3a : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.unpack 22)).contains q)) = true :=
  unpack_avoid 22 (by decide) _ (by decide +kernel)

set_option maxRecDepth 200000 in
theorem head3b : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96)))).all
      (fun q => !((wl (renameProgram (OB5.sig 490) (Rolling1588.unpackAtTick true 490))).contains q)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head3c : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.orientR 490)).contains q)) = true := by
  decide +kernel

theorem head3 : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96)))).all
      (fun q => !((wl (headX 22 490)).contains q)) = true := by
  unfold headX
  exact avoid3 _ _ _ _ head3a head3b head3c

theorem seg3 : StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490 =
      (headX 22 490 ++ StairReplay.movedReverse (segW 480) (5 * 96 + 5 + 1) (490 - (5 * 96 + 5) - 1)) ++
      renameProgram (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96))) Rolling1588.dp ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96))) D26 ++
        W.ReverseCarry.compactReceiverTick (segW 480) 485 ++
        StairReplay.movedReverse (segW 480) 481 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 480 ++
        StairConcreteAssembly.checkpointPrimitives.pack 32) :=
  seg_split 32 22 480 4 4 490 rfl (by decide) (by decide) (by decide)

theorem inj3 : Function.Injective (History5.historyMap (segW 480) (5 * 96)) :=
  History5.historyMap_injective _ (StairPhysicalPrimitivesFix505.revSegmentMap_pool_nodup 32 (by decide))
    _ (by norm_num)

theorem segW_inj3 : Function.Injective (segW 480) :=
  StairPhysicalPrimitivesFix505.revSegmentMap_injective 32 (by decide)

theorem mid3 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96))),
    q ∉ wires (headX 22 490 ++ StairReplay.movedReverse (segW 480) (5 * 96 + 5 + 1) (490 - (5 * 96 + 5) - 1)) :=
  mid_disj (segW 480) segW_inj3 22 490 96 (by norm_num) (by norm_num) head3

/-! ### Row 4: group (41, 98, 2), segment (22, 12, 490, 500); due tick 495 -/

set_option maxRecDepth 200000 in
theorem hep4 : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop 41)
      (StairConcreteAssembly.hostPlan.group false 41 98 (1 + 1))
      (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi 98))
        (Rolling1588.onPacket 98 Rolling1588.ep))) =
    renameProgram (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98))) Rolling1588.ep := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head4a : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.unpack 12)).contains q)) = true :=
  unpack_avoid 12 (by decide) _ (by decide +kernel)

set_option maxRecDepth 200000 in
theorem head4b : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98)))).all
      (fun q => !((wl (renameProgram (OB5.sig 500) (Rolling1588.unpackAtTick true 500))).contains q)) = true := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem head4c : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98)))).all
      (fun q => !((wl (StairConcreteAssembly.checkpointPrimitives.orientR 500)).contains q)) = true := by
  decide +kernel

theorem head4 : ((List.range 10).map (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98)))).all
      (fun q => !((wl (headX 12 500)).contains q)) = true := by
  unfold headX
  exact avoid3 _ _ _ _ head4a head4b head4c

theorem seg4 : StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500 =
      (headX 12 500 ++ StairReplay.movedReverse (segW 490) (5 * 98 + 5 + 1) (500 - (5 * 98 + 5) - 1)) ++
      renameProgram (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98))) Rolling1588.dp ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98))) D26 ++
        W.ReverseCarry.compactReceiverTick (segW 490) 495 ++
        StairReplay.movedReverse (segW 490) 491 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 490 ++
        StairConcreteAssembly.checkpointPrimitives.pack 22) :=
  seg_split 22 12 490 4 4 500 rfl (by decide) (by decide) (by decide)

theorem inj4 : Function.Injective (History5.historyMap (segW 490) (5 * 98)) :=
  History5.historyMap_injective _ (StairPhysicalPrimitivesFix505.revSegmentMap_pool_nodup 22 (by decide))
    _ (by norm_num)

theorem segW_inj4 : Function.Injective (segW 490) :=
  StairPhysicalPrimitivesFix505.revSegmentMap_injective 22 (by decide)

theorem mid4 : ∀ q ∈ (Finset.range 10).image (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98))),
    q ∉ wires (headX 12 500 ++ StairReplay.movedReverse (segW 490) (5 * 98 + 5 + 1) (500 - (5 * 98 + 5) - 1)) :=
  mid_disj (segW 490) segW_inj4 12 500 98 (by norm_num) (by norm_num) head4

end ECDSAAdd.Entrant.PackCutExitRows

namespace ECDSAAdd.Entrant.PackCutExitFrame
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutExit

theorem run_nomeas_tape (P : Program) (h : measurementCount P = 0) (m : List Bool) (s : State) :
    run P m s = run P [] s := by
  rw [← run_take P m s, h]; rfl

theorem run_nomeas_phase (P : Program) (h : measurementCount P = 0) (m : List Bool) (s : State) :
    (run P m s).phase = s.phase := by
  induction P generalizing s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | measureX t c0 c1 => simp [measurementCount] at h
    | X t => exact ih (by simpa [measurementCount] using h) _
    | CX c t => exact ih (by simpa [measurementCount] using h) _
    | CCX a b t => exact ih (by simpa [measurementCount] using h) _

theorem twist_meas (j : Nat) : measurementCount (Rolling1588.onPacket j ParityCodec5New.twist) = 0 := by
  simp only [Rolling1588.onPacket, ParityCodec5New.twist, renameProgram, List.map, renameInstr, measurementCount]

theorem twist_frame (j : Nat) (E : Program) (origin : BasisState) (X Y : Fp) :
    Rolling1588.StateTriple (Rolling1588.CodeFrame E origin X Y) (Rolling1588.onPacket j ParityCodec5New.twist)
      (Rolling1588.CodeFrame (E ++ Rolling1588.onPacket j ParityCodec5New.twist) origin X Y) := by
  intro state records input
  obtain ⟨raw, hph, hpf, hst⟩ := input
  have hp := run_nomeas_phase _ (twist_meas j) records state
  refine ⟨hp, raw, hph.trans hp.symm, hpf, ?_⟩
  rw [run_nomeas_tape _ (twist_meas j), hst, run_append]
  simp

/-- The loaned exit packet without its closing `ep` takes the packet's A-code frame to the stage-2 code frame
followed by `twist` (the loaned cells as in `StairLoanReplay.basePacket_frame`, the closing replaced by `twist`). -/
theorem headF_frame (half : StairLoanReplay.HalfReplayHypothesis) (d j : Nat) (hd : d ≤ 68) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp) :
    Rolling1588.StateTriple
      (Rolling1588.CodeFrame (Rolling1588.codeEncodeAt false (History5.historyMap base (5 * j))) origin X Y)
      (basePacketHeadF d j)
      (fun state => ∃ X' Y' : Fp, Rolling1588.CodeFrame
        (Rolling1588.stageCodeAt false 2 (History5.historyMap base (5 * j)) ++
          Rolling1588.onPacket j ParityCodec5New.twist) origin X' Y' state) := by
  let Frame (k : Nat) (V : Fp × Fp) :=
    Rolling1588.CodeFrame (Rolling1588.stageCodeAt false k (History5.historyMap base (5 * j))) origin V.1 V.2
  have opening (V : Fp × Fp) :
      Rolling1588.StateTriple
        (Rolling1588.CodeFrame (Rolling1588.codeEncodeAt false (History5.historyMap base (5 * j))) origin V.1 V.2)
        (Rolling1588.onPacket j Rolling1588.stageOpen) (Frame 0 V) := by
    intro state records input
    exact Rolling1588.regular_open_frame false j hj origin ctx V.1 V.2 state records input
  have step (k logical physical : Nat) (hk : k < 3)
      (used : (logical, physical) ∈ Rolling1588.activeSlots false k) (V : Fp × Fp) :
      Rolling1588.StateTriple (Frame k V) (StairGroups.cell false d j physical 2)
        (Frame k (Rolling1588.regularStep false j origin logical V)) := by
    intro state records input
    exact StairLoanReplay.regularCell_frame half false d j k logical physical hd hj hk used
      origin ctx enabled V.1 V.2 state records input
  have transfer (k : Nat) (hk : k < 2) (V : Fp × Fp) :
      Rolling1588.StateTriple (Frame k V) (Rolling1588.onPacket j (Rolling1588.stageTransition false k))
        (Frame (k + 1) V) := by
    intro state records input
    exact Rolling1588.regular_transition_frame false j k hj hk origin ctx V.1 V.2 state records input
  let V1 := Rolling1588.regularStep false j origin 4 (X, Y)
  let V2 := Rolling1588.regularStep false j origin 3 V1
  let V3 := Rolling1588.regularStep false j origin 2 V2
  let V4 := Rolling1588.regularStep false j origin 1 V3
  let V5 := Rolling1588.regularStep false j origin 0 V4
  have result := (opening (X, Y)).seq
    ((step 0 4 4 (by decide) (by decide) (X, Y)).seq
    ((transfer 0 (by decide) V1).seq
    ((step 1 3 3 (by decide) (by decide) V1).seq
    ((step 1 2 4 (by decide) (by decide) V2).seq
    ((transfer 1 (by decide) V3).seq
    ((step 2 1 4 (by decide) (by decide) V3).seq
    ((step 2 0 3 (by decide) (by decide) V4).seq
      (twist_frame j _ origin V5.1 V5.2))))))))
  have hprog : Rolling1588.onPacket j Rolling1588.stageOpen ++ (StairGroups.cell false d j 4 2 ++
      (Rolling1588.onPacket j (Rolling1588.stageTransition false 0) ++ (StairGroups.cell false d j 3 2 ++
      (StairGroups.cell false d j 4 2 ++ (Rolling1588.onPacket j (Rolling1588.stageTransition false 1) ++
      (StairGroups.cell false d j 4 2 ++ (StairGroups.cell false d j 3 2 ++
        Rolling1588.onPacket j ParityCodec5New.twist))))))) = basePacketHeadF d j := by
    simp only [basePacketHeadF, Rolling1588.stageOpen, Rolling1588.stageTransition, Rolling1588.onPacket,
      rename_app, List.append_assoc, if_true, if_false, Bool.false_eq_true, show ¬(1 : Nat) = 0 from by decide]
  intro state records input
  have r := result state records input
  rw [hprog] at r
  exact ⟨r.1, V5.1, V5.2, r.2⟩

/-- Legality of the raw word under the stage-2 + twist frame (as in `Rolling1588.raw_current_legal`). -/
theorem frame_legal (j : Nat) (hj : j < 102) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (X Y : Fp) (state : State)
    (h : Rolling1588.CodeFrame (Rolling1588.stageCodeAt false 2 (History5.historyMap base (5 * j)) ++
          Rolling1588.onPacket j ParityCodec5New.twist) origin X Y state) :
    ∃ raw : State, MeasuredCodec5.legalAt (History5.historyMap base (5 * j)) raw.basis ∧
      state = run (renameProgram (MeasuredCodec5.label (History5.historyMap base (5 * j))) E138x) [] raw := by
  obtain ⟨raw, -, frame, hst⟩ := h
  refine ⟨raw, (NewHistory5.frame_history_legal base (base 2409) ctx.hn (ctx.hp _ (by simp))
    102 (by decide) origin raw.basis _ _ ctx.legal frame) j hj, ?_⟩
  rw [hst]
  simp only [E138x, Rolling1588.stageCodeAt, Rolling1588.onPacket, rename_app]

end ECDSAAdd.Entrant.PackCutExitFrame

namespace ECDSAAdd.Entrant.PackCutExitBits
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutTrip PackCutExit

open MeasuredCodec5 in
theorem local_trip_bits (t : State) (x : Nat) (hx : x < 1024) (lx : legalNat x = true)
    (hb : ∀ q ∈ Finset.range 10, t.basis q = bitsOf (bitRun E138x x) q) (me md : List Bool) :
    run Rolling1588.dp md (run Rolling1588.ep me t) = t := by
  have fin := finite_tripX x hx lx
  simp only [Bool.and_eq_true, beq_iff_eq] at fin
  obtain ⟨⟨⟨_, s2⟩, s3⟩, e4⟩ := fin
  let u : State := ⟨t.phase, bitsOf (bitRun E138x x)⟩
  have r2 : run Rolling1588.ep me u = ⟨t.phase, bitsOf (bitRun Rolling1588.ep (bitRun E138x x))⟩ := by
    rw [run_sim, sim_safe _ _ s2]
  have r3 : run Rolling1588.dp md (run Rolling1588.ep me u) = u := by
    rw [r2, run_sim, sim_safe _ _ s3, e4]
  have agree0 : ∀ q ∈ Finset.range 10, t.basis q = u.basis q := fun q hq => hb q hq
  have l2 := run_measured_locality Rolling1588.ep (Finset.range 10) PackCutTrip.supp.2.1 t u me rfl agree0
  have l3 := run_measured_locality Rolling1588.dp (Finset.range 10) PackCutTrip.supp.2.2 _ _ md l2.1 l2.2
  rw [r3] at l3
  apply State.extensionality
  · exact l3.1
  · funext q
    by_cases hq : q ∈ Finset.range 10
    · exact (l3.2 q hq).trans (agree0 q hq).symm
    · rw [run_preserves_outside _ md _ q (fun hh => hq (PackCutTrip.supp.2.2 hh)),
        run_preserves_outside _ me _ q (fun hh => hq (PackCutTrip.supp.2.1 hh))]

open MeasuredCodec5 in
/-- Placed exit trip on a state whose ten packet bits are the shortened encode of a legal word. -/
theorem placed_trip_bits (f : Fin 10 → Wire) (hf : Function.Injective f) (a : State) (x : Nat)
    (hx : x < 1024) (lx : legalNat x = true)
    (hbits : ∀ i : Fin 10, a.basis (f i) = (bitRun E138x x).testBit i) (me md : List Bool) :
    run (renameProgram (label f) Rolling1588.dp) md (run (renameProgram (label f) Rolling1588.ep) me a) = a := by
  have inj := FirstNonzeroCodec.label_inj' f hf
  let t : State := ⟨a.phase, fun q => a.basis (label f q)⟩
  have hb : ∀ q ∈ Finset.range 10, t.basis q = bitsOf (bitRun E138x x) q := by
    intro q hq
    have hq' : q < 10 := Finset.mem_range.mp hq
    show a.basis (label f q) = (bitRun E138x x).testBit q
    simp only [label, hq', dite_true]
    exact hbits ⟨q, hq'⟩
  have p2 := run_rename_pool (label f) (Finset.range 10) inj Rolling1588.ep PackCutTrip.supp.2.1 me t a
    rfl (fun _ _ => rfl)
  have p3 := run_rename_pool (label f) (Finset.range 10) inj Rolling1588.dp PackCutTrip.supp.2.2 md
    (run Rolling1588.ep me t) (run (renameProgram (label f) Rolling1588.ep) me a)
    p2.1.symm (fun q hq => (p2.2 q hq).symm)
  have lt := local_trip_bits t x hx lx hb me md
  have suppP := renameProgram_support (label f) Rolling1588.ep
  have suppD := renameProgram_support (label f) Rolling1588.dp
  apply State.extensionality
  · rw [p3.1, lt]
  · funext q
    by_cases hq : q ∈ (Finset.range 10).image (label f)
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      rw [p3.2 i hi, lt]
    · have nE : q ∉ wires (renameProgram (label f) Rolling1588.ep) := by
        rw [suppP]; intro hh; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
        exact hq (Finset.mem_image.mpr ⟨i, PackCutTrip.supp.2.1 hi, rfl⟩)
      have nD : q ∉ wires (renameProgram (label f) Rolling1588.dp) := by
        rw [suppD]; intro hh; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
        exact hq (Finset.mem_image.mpr ⟨i, PackCutTrip.supp.2.2 hi, rfl⟩)
      rw [run_preserves_outside _ md _ q nD, run_preserves_outside _ me _ q nE]

open MeasuredCodec5 in
/-- Exit row cut with the frame hypothesis on the packet bits only. -/
theorem exit_row_cut_bits (A M Dh B : Program) (F : Fin 10 → Wire) (hF : Function.Injective F)
    (hdp : Dh = renameProgram (label F) Rolling1588.dp)
    (hM : ∀ q ∈ (Finset.range 10).image (label F), q ∉ wires M)
    (s : State) (m : List Bool)
    (hbits : ∀ tA, ∃ x, x < 1024 ∧ legalNat x = true ∧
      ∀ i : Fin 10, (run A tA s).basis (F i) = (bitRun E138x x).testBit i) :
    ∃ m', run (A ++ M ++ B) m s =
      run (A ++ renameProgram (label F) Rolling1588.ep ++ M ++ Dh ++ B) m' s := by
  subst hdp
  have hE : wires (renameProgram (label F) Rolling1588.ep) ⊆ (Finset.range 10).image (label F) := by
    rw [renameProgram_support]; exact Finset.image_subset_image PackCutTrip.supp.2.1
  have hD : wires (renameProgram (label F) Rolling1588.dp) ⊆ (Finset.range 10).image (label F) := by
    rw [renameProgram_support]; exact Finset.image_subset_image PackCutTrip.supp.2.2
  refine row_cut A _ M _ B _ hE hD hM s m ?_
  intro tA me md
  obtain ⟨x, hx, lx, hb⟩ := hbits tA
  exact placed_trip_bits F hF _ x hx lx hb me md

end ECDSAAdd.Entrant.PackCutExitBits

namespace ECDSAAdd.Entrant.PackCutExitCut
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutTrip PackCutExit PackCutExitFrame

open MeasuredCodec5 in
/-- The ten letters of a placed shortened encode of a legal raw word are the bits of `bitRun E138x x`. -/
theorem placed_E138x_bits (f : Fin 10 → Wire) (hf : Function.Injective f) (raw : State)
    (h : legalAt f raw.basis) :
    ∃ x, x < 1024 ∧ legalNat x = true ∧ ∀ i : Fin 10,
      (run (renameProgram (label f) E138x) [] raw).basis (f i) = (bitRun E138x x).testBit i := by
  have inj := FirstNonzeroCodec.label_inj' f hf
  let t : State := ⟨raw.phase, fun q => raw.basis (label f q)⟩
  obtain ⟨x, hx, lx, hb⟩ := local_word t h
  have fin := finite_tripX x hx lx
  simp only [Bool.and_eq_true, beq_iff_eq] at fin
  obtain ⟨⟨⟨s1, _⟩, _⟩, _⟩ := fin
  let u : State := ⟨t.phase, bitsOf x⟩
  have r1 : run E138x [] u = ⟨t.phase, bitsOf (bitRun E138x x)⟩ := by
    rw [run_sim, sim_safe E138x x s1]
  have l1 := run_measured_locality E138x (Finset.range 10) suppX t u [] rfl hb
  have p1 := run_rename_pool (label f) (Finset.range 10) inj E138x suppX [] t raw rfl (fun _ _ => rfl)
  refine ⟨x, hx, lx, fun i => ?_⟩
  have hi : (i : Nat) ∈ Finset.range 10 := Finset.mem_range.mpr i.isLt
  have e1 : label f (i : Nat) = f i := by simp [label, i.isLt]
  rw [← e1, p1.2 _ hi, l1.2 _ hi, r1]
  rfl

theorem stage_twist_eq (j : Nat) :
    Rolling1588.stageCodeAt false 2 (History5.historyMap base (5 * j)) ++
      Rolling1588.onPacket j ParityCodec5New.twist =
    renameProgram (MeasuredCodec5.label (History5.historyMap base (5 * j))) E138x := by
  simp only [E138x, Rolling1588.stageCodeAt, Rolling1588.onPacket, rename_app]

theorem head_sub (d j : Nat) : wires (basePacketHeadF d j) ⊆ wires (StairGroups.basePacket false d j) := by
  rw [basePacket_false_tail, wires_append]
  exact Finset.subset_union_left

theorem mem_single (w : Wire) : w ∈ wires [Instr.X w] := by
  simp [wires, Instr.wires]

theorem single_sub (w : Wire) (S : Finset Wire) (h : w ∈ S) : wires [Instr.X w] ⊆ S := by
  intro q hq
  have : q = w := by simpa [wires, Instr.wires] using hq
  subst this
  exact h

open MeasuredCodec5 in
set_option maxRecDepth 20000 in
/-- On a record cut frame at `j + 1`, after the loaned head of packet `j` (everything but its closing `ep`),
the packet's ten letters are the shortened encode of a legal word. -/
theorem headF_cut_bits (half : StairLoanReplay.HalfReplayHypothesis) (d j : Nat) (hd : d ≤ 68)
    (hj1 : 1 ≤ j) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp)
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * j) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * j))
    (state : State) (records : List Bool) (input : Rolling1588.CutFrame (j + 1) origin X Y state) :
    ∃ x, x < 1024 ∧ legalNat x = true ∧ ∀ i : Fin 10,
      (run (basePacketHeadF d j) records state).basis (History5.historyMap base (5 * j) i) =
        (bitRun E138x x).testBit i := by
  have nonzero : j ≠ 0 := by omega
  obtain ⟨raw, rawPhase, rawFrame, encoded⟩ := input
  let current := run (Rolling1588.encodeGroup base (decide (j + 1 ≤ j)) j) [] raw
  have currentPhase := Rolling1588.encodeGroup_zero_phase base (decide (j + 1 ≤ j)) base_pool_nodup j
    (by omega) raw
  have cf : Rolling1588.CodeFrame (Rolling1588.encodeGroup base (decide (j + 1 ≤ j)) j) origin X Y current :=
    ⟨raw, currentPhase.symm, rawFrame, rfl⟩
  have normalized : Rolling1588.CodeFrame
      (Rolling1588.codeEncodeAt false (History5.historyMap base (5 * j))) origin X Y current := by
    simpa [Rolling1588.encodeGroup, nonzero, show ¬j + 1 ≤ j from by omega] using cf
  have res := headF_frame half d j hd hj origin ctx enabled X Y current records normalized
  obtain ⟨X', Y', raw', _, pf', enc'⟩ := res.2
  have legal' : MeasuredCodec5.legalAt (History5.historyMap base (5 * j)) raw'.basis :=
    (NewHistory5.frame_history_legal base (base 2409) ctx.hn (ctx.hp _ (by simp)) 102 (by decide) origin
      raw'.basis _ _ ctx.legal pf') j hj
  have hsub : wires (basePacketHeadF d j) ⊆ wires (StairGroups.basePacket false d j) :=
    head_sub d j
  have hsup := hsub.trans (StairLoanReplay.basePacket_read_support half false d j hd hj)
  have disj := Rolling1588.otherEncodeCut_body_disjoint (j + 1) j hj origin ctx _ hsup
  have factor := Rolling1588.allEncodeCut_factor base (j + 1) base_pool_nodup 102 j (by decide) hj raw
  have actual : run (basePacketHeadF d j) records state =
      run (Rolling1588.otherEncodeCut base (j + 1) j 102) [] (run (basePacketHeadF d j) records current) := by
    rw [encoded, factor]
    exact (Arithmetic.run_disjoint_commute (Rolling1588.otherEncodeCut base (j + 1) j 102)
      (basePacketHeadF d j) disj [] records current).symm
  have hFo : ∀ i : Fin 10, History5.historyMap base (5 * j) i ∉
      wires (Rolling1588.otherEncodeCut base (j + 1) j 102) := by
    intro i hi
    have body := Rolling1588.otherEncodeCut_body_disjoint (j + 1) j hj origin ctx
      [Instr.X (History5.historyMap base (5 * j) i)] (single_sub _ _ (Finset.mem_union_left _ (hF i)))
    exact Finset.disjoint_left.mp body hi (mem_single _)
  have inj := History5.historyMap_injective base base_pool_nodup (5 * j) (by omega)
  obtain ⟨x, hx, lx, hb⟩ := placed_E138x_bits (History5.historyMap base (5 * j)) inj raw' legal'
  refine ⟨x, hx, lx, fun i => ?_⟩
  rw [actual, run_preserves_outside _ [] _ _ (hFo i), enc', stage_twist_eq]
  exact hb i

end ECDSAAdd.Entrant.PackCutExitCut

namespace ECDSAAdd.Entrant.PackCutExitGroup
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutTrip PackCutExit PackCutExitFrame PackCutExitCut

/-- The cell placement of packet `j` moves only zero-region wires, so on a state that is zero there it leaves
the packet's ten letters exactly as the unplaced head computes them. -/
theorem shifted_head_bits (d j : Nat) (hj : j < 102) (s : State) (m : List Bool)
    (hz : ∀ q, Placement5.zeroRegion q → s.basis (base q) = false)
    (hfixF : ∀ i : Fin 10, Placement5.pi j (History5.historyId (5 * j) i) = History5.historyId (5 * j) i)
    (i : Fin 10) :
    (run (renameProgram (shifted (Placement5.pi j)) (basePacketHeadF d j)) m s).basis
        (History5.historyMap base (5 * j) i) =
      (run (basePacketHeadF d j) m s).basis (History5.historyMap base (5 * j) i) := by
  have h := run_rename (shifted (Placement5.pi j)) (shifted (Placement5.pi j)).injective
    (basePacketHeadF d j) m s
  rw [Placement5.shifted_zero_boundary (Placement5.pi j) (fun q hq => Placement5.pi_outside j q hj hq) s hz] at h
  have e := congrArg (fun st : State => st.basis (History5.historyMap base (5 * j) i)) h
  simp only [pullState] at e
  have hfix : shifted (Placement5.pi j) (History5.historyMap base (5 * j) i) =
      History5.historyMap base (5 * j) i := by
    show shifted (Placement5.pi j) (base (History5.historyId (5 * j) i)) = base (History5.historyId (5 * j) i)
    rw [shifted_base, hfixF i]
  rw [hfix] at e
  exact e

open MeasuredCodec5 in
set_option maxRecDepth 20000 in
/-- The loaned exit group of packets `first .. first + c` without its last closing `ep`, on the record cut
frame at `first + c + 1`: the last packet's letters are the shortened encode of a legal word. -/
theorem group_head_bits (half : StairLoanReplay.HalfReplayHypothesis) (d first c : Nat) (hd : d ≤ 68)
    (h1 : 1 ≤ first) (hb : first + c + 1 ≤ 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp)
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * first) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * first))
    (hfixF : ∀ i : Fin 10, Placement5.pi first (History5.historyId (5 * first) i) = History5.historyId (5 * first) i)
    (s : State) (m : List Bool) (input : Rolling1588.CutFrame (first + c + 1) origin X Y s) :
    ∃ x, x < 1024 ∧ legalNat x = true ∧ ∀ i : Fin 10,
      (run (StairGroups.groups false d (first + 1) c ++
          renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first)) m s).basis
        (History5.historyMap base (5 * first) i) = (bitRun E138x x).testBit i := by
  have gf := StairLoanReplay.groups_cut_frame half false d (first + 1) c hd (by omega) (by omega)
    origin ctx enabled X Y
  have inp : Rolling1588.CutFrame (if false = true then first + 1 else first + 1 + c) origin X Y s := by
    simpa [show first + 1 + c = first + c + 1 by omega] using input
  have r := gf s (m.take (measurementCount (StairGroups.groups false d (first + 1) c))) inp
  set s2 := run (StairGroups.groups false d (first + 1) c)
    (m.take (measurementCount (StairGroups.groups false d (first + 1) c))) s with hs2
  have f2 : Rolling1588.CutFrame (first + 1) origin
      (Replay5.groupsPayload false origin (first + 1) c (X, Y)).1
      (Replay5.groupsPayload false origin (first + 1) c (X, Y)).2 s2 := by
    have r2 := r.2
    simp only [Bool.false_eq_true, if_false] at r2
    exact r2
  have hz := Rolling1588.cutFrame_zero_region (first + 1) origin ctx _ _ s2 f2
  obtain ⟨x, hx, lx, hbits⟩ := headF_cut_bits half d first hd h1 (by omega) origin ctx enabled
    (Replay5.groupsPayload false origin (first + 1) c (X, Y)).1
    (Replay5.groupsPayload false origin (first + 1) c (X, Y)).2 hF s2
    (m.drop (measurementCount (StairGroups.groups false d (first + 1) c))) f2
  refine ⟨x, hx, lx, fun i => ?_⟩
  rw [run_append, ← hs2, shifted_head_bits d first (by omega) s2 _ hz hfixF i]
  exact hbits i

end ECDSAAdd.Entrant.PackCutExitGroup

namespace ECDSAAdd.Entrant.PackCutExitTransport
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutExit

theorem pull_swap_zero (r h : Wire) (u : State) (hr : u.basis r = false) (hh : u.basis h = false) :
    pullState (Equiv.swap r h) u = u := by
  apply State.extensionality
  · rfl
  · funext q
    show u.basis (Equiv.swap r h q) = u.basis q
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hr, hh]
    · rw [h2, hr, hh]
    · rfl

/-- Hosting (a product of role/host swaps) leaves every wire off the roles and hosts exactly as the logical
program computes it, on a state that is zero on the roles and hosts. -/
theorem hosted_bits : ∀ (rs hs : List Wire) (P : Program) (m : List Bool) (u : State),
    (∀ q ∈ rs ++ hs, u.basis q = false) → ∀ w, w ∉ rs ++ hs →
      (run (StairLoan.rebindMany rs hs P) m u).basis w = (run P m u).basis w
  | [], hs, P, m, u, _, w, _ => by cases hs <;> rfl
  | _ :: _, [], P, m, u, _, w, _ => rfl
  | r :: rs, h :: hs, P, m, u, hz, w, hw => by
    have ih := hosted_bits rs hs P m u (fun q hq => hz q (by
      simp only [List.mem_append, List.mem_cons] at hq ⊢; tauto)) w (by
      intro hm; apply hw; simp only [List.mem_append, List.mem_cons] at hm ⊢; tauto)
    have hr : u.basis r = false := hz r (by simp)
    have hh : u.basis h = false := hz h (by simp)
    have hwr : w ≠ r := fun e => hw (by simp [e])
    have hwh : w ≠ h := fun e => hw (by simp [e])
    show (run (renameProgram (Equiv.swap r h) (StairLoan.rebindMany rs hs P)) m u).basis w = _
    have e := ECDSAAdd.run_rename (Equiv.swap r h) (Equiv.swap r h).injective (StairLoan.rebindMany rs hs P) m u
    rw [pull_swap_zero r h u hr hh] at e
    have e2 := congrArg (fun st : State => st.basis w) e
    simp only [pullState] at e2
    rw [Equiv.swap_apply_of_ne_of_ne hwr hwh] at e2
    rw [e2, ih]

theorem liftF_mem (P : Program) (r : Wire) (hr : r ∈ wires P) :
    StairOuterPlacement.fieldPlace r ∈ wires (StairField2V3Entry.liftF P) := by
  unfold StairField2V3Entry.liftF StairSchedule.fieldRename StairSchedule.parityRename
  rw [renameProgram_support, renameProgram_support, renameProgram_support]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨r, hr, rfl⟩, rfl⟩, rfl⟩

theorem liftF_sub (P Q : Program) (h : wires (StairField2V3Entry.liftF P) ⊆ wires (StairField2V3Entry.liftF Q)) :
    wires P ⊆ wires Q := by
  intro r hr
  obtain ⟨r', hr', e⟩ := StairField2V3Delta.liftF_wires Q _ (h (liftF_mem P r hr))
  rw [StairField2V3Delta.fieldPlace_injective e]
  exact hr'


theorem subOff_gen (d j n : Nat) (h1 : 1 ≤ j) (h2 : j + n ≤ 102)
    (g : wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans d j n) ⊆ wires (StairField2V3ExitPlan.grpF j n)) :
    ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false d j n), StairField2V3RecScratch.Off q :=
  fun q hq => StairField2V3ExitRec.groupsF_off j n h1 h2 q (liftF_sub _ _ g hq)

theorem away_gen (B d j n : Nat) (hB : B ∈ StairPhysicalLayout.budgets) (h : j + n ≤ StairPhysicalLayout.startFor B / 5)
    (g : wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans d j n) ⊆ wires (StairField2V3ExitPlan.grpF j n)) :
    ∀ q ∈ StairField2V3Delta.Δv B, q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans d j n) :=
  StairLoanField7Transport.away_of_sub _ _ _ g (StairField2V3Delta.grpF_away B hB j n h)

end ECDSAAdd.Entrant.PackCutExitTransport

namespace ECDSAAdd.Entrant.PackCutExitRowBits
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutExit PackCutExitGroup PackCutExitTransport
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR

theorem placed_false_tail (d first c : Nat) :
    StairSchedule.placedGroups StairConcrete.bestLoans false d first (c + 1) =
      (renameProgram (OB5.sig 511) (StairGroups.groups false d (first + 1) c) ++
       renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first))) ++
      renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
        (Rolling1588.onPacket first Rolling1588.ep)) := by
  simp only [StairSchedule.placedGroups, StairConcrete.bestLoans, StairGroups.groups, program_false_tail,
    StairGroups.packet, basePacket_false_tail, rename_app, List.append_assoc]

open MeasuredCodec5 in
set_option maxRecDepth 20000 in
theorem row_bits (half : StairLoanReplay.HalfReplayHypothesis) (k x d first c B' : Nat) (Z : Program)
    (hd : d ≤ 68) (h1 : 1 ≤ first) (hb : first + c + 1 ≤ 102)
    (hreach : ∀ t, ReachBy (ExitMiddleX k x) Z t → StairField2V3ExitRec.InvE x (first + c + 1) t)
    (Fs : Fin 10 → Wire)
    (hsig : ∀ i, OB5.sig 511 (History5.historyMap base (5 * first) i) = Fs i)
    (hRH : ∀ i, Fs i ∉ StairSchedule.exclusiveRoles.drop d ++ StairConcreteAssembly.hostPlan.group false d first (c + 1))
    (hOff : ∀ i, StairField2V3RecScratch.Off (Fs i))
    (hfp : ∀ i, Fs i ∉ StairPhysicalLayout.futurePayload B')
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * first) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * first))
    (hfixF : ∀ i : Fin 10, Placement5.pi first (History5.historyId (5 * first) i) = History5.historyId (5 * first) i)
    (hsubOff : ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false d first (c + 1)),
      StairField2V3RecScratch.Off q)
    (haway : ∀ q ∈ Δv B', q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans d first (c + 1)))
    (s t : State) (hrel : StairField13V3Clean.RowRelL k x B' Z s t)
    (hz : ∀ q ∈ StairSchedule.exclusiveRoles.drop d ++ StairConcreteAssembly.hostPlan.group false d first (c + 1),
      (pullIn s).basis q = false)
    (tA : List Bool) :
    ∃ x', x' < 1024 ∧ legalNat x' = true ∧ ∀ i : Fin 10,
      (run (StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
          (StairConcreteAssembly.hostPlan.group false d first (c + 1))
          (renameProgram (OB5.sig 511) (StairGroups.groups false d (first + 1) c) ++
           renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first))))
        tA (pullIn s)).basis (Fs i) = (bitRun E138x x').testBit i := by
  obtain ⟨⟨⟨_, hout⟩, _⟩, hreachZ⟩ := hrel
  obtain ⟨origin, X, Y, srec, ctx, en, _, _, frame, agree⟩ := hreach t hreachZ
  let G : Program := StairGroups.groups false d (first + 1) c ++
    renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first)
  have hG : renameProgram (OB5.sig 511) (StairGroups.groups false d (first + 1) c) ++
      renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first)) =
      renameProgram (OB5.sig 511) G := by
    simp only [G, rename_app]
  obtain ⟨x', hx', lx', hbits⟩ := group_head_bits half d first c hd h1 hb origin ctx en X Y hF hfixF
    (pullState (OB5.sig 511) srec) tA (by simpa [show first + c + 1 = first + c + 1 from rfl] using frame)
  refine ⟨x', hx', lx', fun i => ?_⟩
  rw [hG]
  -- the logical prefix inside the placed group
  have hpre : wires (renameProgram (OB5.sig 511) G) ⊆
      wires (StairSchedule.placedGroups StairConcrete.bestLoans false d first (c + 1)) := by
    rw [placed_false_tail, hG, wires_append]
    exact Finset.subset_union_left
  -- hosted → logical
  rw [hosted_bits _ _ _ tA (pullIn s) hz (Fs i) (hRH i)]
  -- logical: selected → reference (agreement off Δv)
  have hag : ∀ r ∈ wires (renameProgram (OB5.sig 511) G), (pullIn s).basis r = (pullIn t).basis r := by
    intro r hr
    show s.basis (StairOuterPlacement.fieldPlace r) = t.basis (StairOuterPlacement.fieldPlace r)
    apply hout
    intro hΔ
    exact haway _ hΔ (liftF_mem _ r (hpre hr))
  have step1 : (run (renameProgram (OB5.sig 511) G) tA (pullIn s)).basis (Fs i) =
      (run (renameProgram (OB5.sig 511) G) tA (pullIn t)).basis (Fs i) := by
    by_cases hw : Fs i ∈ wires (renameProgram (OB5.sig 511) G)
    · exact (Arithmetic.run_local_increment _ _ _ tA hag).2 _ hw
    · rw [run_preserves_outside _ tA _ _ hw, run_preserves_outside _ tA _ _ hw]
      show s.basis (StairOuterPlacement.fieldPlace (Fs i)) = t.basis (StairOuterPlacement.fieldPlace (Fs i))
      exact hout _ (not_mem_Δv B' (Fs i) (hfp i))
  rw [step1]
  -- reference → record (agreement on Off)
  have step2 := StairField2V3RecScratch.run_agree_offP (renameProgram (OB5.sig 511) G)
    (fun q hq => hsubOff q (hpre hq)) (pullIn t) srec tA agree (Fs i) (hOff i)
  rw [step2]
  -- record: undo the 511 relabeling
  have e := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (le_refl _)) G tA srec
  have e2 := congrArg (fun st : State => st.basis (History5.historyMap base (5 * first) i)) e
  simp only [pullState] at e2
  rw [← hsig i, e2]
  exact hbits i

end ECDSAAdd.Entrant.PackCutExitRowBits

namespace ECDSAAdd.Entrant.PackCutExitFull
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutExit PackCutExitRows PackCutExitRowBits PackCutExitTransport
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR

/-- The hosted part of the exit group before its closing `ep`. -/
def Ah (d first c : Nat) : Program :=
  StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
    (StairConcreteAssembly.hostPlan.group false d first (c + 1))
    (renameProgram (OB5.sig 511) (StairGroups.groups false d (first + 1) c) ++
     renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first)) (basePacketHeadF d first)))

open MeasuredCodec5 in
set_option maxRecDepth 20000 in
theorem exit_row_full (half : StairLoanReplay.HalfReplayHypothesis) (k x d first c B' : Nat) (Z : Program)
    (hd : d ≤ 68) (h1 : 1 ≤ first) (hb : first + c + 1 ≤ 102)
    (hreach : ∀ t, ReachBy (ExitMiddleX k x) Z t → StairField2V3ExitRec.InvE x (first + c + 1) t)
    (Fs : Fin 10 → Wire) (hFinj : Function.Injective Fs)
    (hsig : ∀ i, OB5.sig 511 (History5.historyMap base (5 * first) i) = Fs i)
    (hRH : ∀ i, Fs i ∉ StairSchedule.exclusiveRoles.drop d ++ StairConcreteAssembly.hostPlan.group false d first (c + 1))
    (hOff : ∀ i, StairField2V3RecScratch.Off (Fs i))
    (hfp : ∀ i, Fs i ∉ StairPhysicalLayout.futurePayload B')
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * first) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * first))
    (hfixF : ∀ i : Fin 10, Placement5.pi first (History5.historyId (5 * first) i) = History5.historyId (5 * first) i)
    (hsubOff : ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false d first (c + 1)),
      StairField2V3RecScratch.Off q)
    (haway : ∀ q ∈ Δv B', q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans d first (c + 1)))
    (SEG M Bx : Program) (hseg : SEG = M ++ renameProgram (label Fs) Rolling1588.dp ++ Bx)
    (hM : ∀ q ∈ (Finset.range 10).image (label Fs), q ∉ wires M)
    (hep : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
        (StairConcreteAssembly.hostPlan.group false d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.ep))) = renameProgram (label Fs) Rolling1588.ep)
    (s t : State) (hrel : StairField13V3Clean.RowRelL k x B' Z s t)
    (hz : ∀ q ∈ StairSchedule.exclusiveRoles.drop d ++ StairConcreteAssembly.hostPlan.group false d first (c + 1),
      (pullIn s).basis q = false)
    (m : List Bool) :
    ∃ m', run (Ah d first c ++ M ++ Bx) m (pullIn s) =
      run (StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan false d first (c + 1) ++ SEG) m'
        (pullIn s) := by
  obtain ⟨m', h⟩ := PackCutExitBits.exit_row_cut_bits (Ah d first c) M _ Bx Fs hFinj rfl hM (pullIn s) m
    (fun tA => row_bits half k x d first c B' Z hd h1 hb hreach Fs hsig hRH hOff hfp hF hfixF hsubOff haway
      s t hrel hz tA)
  refine ⟨m', ?_⟩
  rw [h, hostedGroup_false_tail, hep, hseg]
  simp only [Ah, List.append_assoc]

end ECDSAAdd.Entrant.PackCutExitFull

namespace ECDSAAdd.Entrant.PackCutExitInst
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed
open PackCutRow PackCutShape PackCutExit PackCutExitRows PackCutExitFull PackCutExitTransport
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR


set_option maxRecDepth 100000 in
theorem rs_of_enc (j : Nat)
    (h : ∀ i : Fin 10, History5.historyMap base (5 * j) i ∈ wires (NewHistory5.encode base (5 * j))) :
    ∀ i : Fin 10, History5.historyMap base (5 * j) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * j) := by
  intro i
  unfold NewHistory5.groupReadSites
  exact Finset.mem_union_right _ (h i)

set_option maxRecDepth 200000 in
theorem sig0 : ∀ i : Fin 10, OB5.sig 511 (History5.historyMap base (5 * 85) i) =
    History5.historyMap (segW 425) (5 * 85) i := by decide +kernel

set_option maxRecDepth 200000 in
theorem rh0 : ∀ i : Fin 10, History5.historyMap (segW 425) (5 * 85) i ∉
    StairSchedule.exclusiveRoles.drop 13 ++ StairConcreteAssembly.hostPlan.group false 13 85 (4 + 1) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem off0 : ∀ i : Fin 10, StairField2V3RecScratch.Off (History5.historyMap (segW 425) (5 * 85) i) := by
  unfold StairField2V3RecScratch.Off; decide +kernel

set_option maxRecDepth 200000 in
theorem fp0 : ∀ i : Fin 10, History5.historyMap (segW 425) (5 * 85) i ∉ StairPhysicalLayout.futurePayload 62 := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem rs0 : ∀ i : Fin 10, History5.historyMap base (5 * 85) i ∈
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * 85) :=
  rs_of_enc 85 (by decide +kernel)

set_option maxRecDepth 200000 in
theorem fix0 : ∀ i : Fin 10, Placement5.pi 85 (History5.historyId (5 * 85) i) =
    History5.historyId (5 * 85) i := by decide +kernel

theorem subOff0 : ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false 13 85 (4 + 1)),
    StairField2V3RecScratch.Off q :=
  subOff_gen 13 85 (4 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.2.2.2.1

theorem away0 : ∀ q ∈ Δv 62, q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans 13 85 (4 + 1)) :=
  away_gen 62 13 85 (4 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem exit_row0 (half : StairLoanReplay.HalfReplayHypothesis) (k x : Nat) (s t : State)
    (hrel : StairField13V3Clean.RowRelL k x 62 StairLoanExitReachX.ZD s t)
    (hz : ∀ q ∈ StairSchedule.exclusiveRoles.drop 13 ++ StairConcreteAssembly.hostPlan.group false 13 85 (4 + 1),
      (pullIn s).basis q = false) (m : List Bool) :
    ∃ m', run (Ah 13 85 4 ++
        (headX 62 450 ++ StairReplay.movedReverse (segW 425) (5 * 85 + 5 + 1) (450 - (5 * 85 + 5) - 1)) ++
        (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 425) (5 * 85))) D26 ++
          W.ReverseCarry.compactReceiverTick (segW 425) 430 ++
          StairReplay.movedReverse (segW 425) 426 4 ++
          StairConcreteAssembly.checkpointPrimitives.tickReverse 425 ++
          StairConcreteAssembly.checkpointPrimitives.pack 87)) m (pullIn s) =
      run (StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan false 13 85 (4 + 1) ++
        StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) m' (pullIn s) :=
  exit_row_full half k x 13 85 4 62 StairLoanExitReachX.ZD (by norm_num) (by norm_num) (by norm_num)
    (fun t h => StairField2V3ExitRec.reach_YD k x t (StairLoanExitReachX.reachX_D half k x t h))
    _ inj0 sig0 rh0 off0 fp0 rs0 fix0 subOff0 away0 _ _ _ seg0 mid0 hep0 s t hrel hz m

set_option maxRecDepth 200000 in
theorem sig1 : ∀ i : Fin 10, OB5.sig 511 (History5.historyMap base (5 * 90) i) =
    History5.historyMap (segW 450) (5 * 90) i := by decide +kernel

set_option maxRecDepth 200000 in
theorem rh1 : ∀ i : Fin 10, History5.historyMap (segW 450) (5 * 90) i ∉
    StairSchedule.exclusiveRoles.drop 22 ++ StairConcreteAssembly.hostPlan.group false 22 90 (2 + 1) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem off1 : ∀ i : Fin 10, StairField2V3RecScratch.Off (History5.historyMap (segW 450) (5 * 90) i) := by
  unfold StairField2V3RecScratch.Off; decide +kernel

set_option maxRecDepth 200000 in
theorem fp1 : ∀ i : Fin 10, History5.historyMap (segW 450) (5 * 90) i ∉ StairPhysicalLayout.futurePayload 47 := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem rs1 : ∀ i : Fin 10, History5.historyMap base (5 * 90) i ∈
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * 90) :=
  rs_of_enc 90 (by decide +kernel)

set_option maxRecDepth 200000 in
theorem fix1 : ∀ i : Fin 10, Placement5.pi 90 (History5.historyId (5 * 90) i) =
    History5.historyId (5 * 90) i := by decide +kernel

theorem subOff1 : ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false 22 90 (2 + 1)),
    StairField2V3RecScratch.Off q :=
  subOff_gen 22 90 (2 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.2.2.1

theorem away1 : ∀ q ∈ Δv 47, q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans 22 90 (2 + 1)) :=
  away_gen 47 22 90 (2 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem exit_row1 (half : StairLoanReplay.HalfReplayHypothesis) (k x : Nat) (s t : State)
    (hrel : StairField13V3Clean.RowRelL k x 47 StairLoanExitReachX.ZC s t)
    (hz : ∀ q ∈ StairSchedule.exclusiveRoles.drop 22 ++ StairConcreteAssembly.hostPlan.group false 22 90 (2 + 1),
      (pullIn s).basis q = false) (m : List Bool) :
    ∃ m', run (Ah 22 90 2 ++
        (headX 47 465 ++ StairReplay.movedReverse (segW 450) (5 * 90 + 5 + 1) (465 - (5 * 90 + 5) - 1)) ++
        (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 450) (5 * 90))) D26 ++
          W.ReverseCarry.compactReceiverTick (segW 450) 455 ++
          StairReplay.movedReverse (segW 450) 451 4 ++
          StairConcreteAssembly.checkpointPrimitives.tickReverse 450 ++
          StairConcreteAssembly.checkpointPrimitives.pack 62)) m (pullIn s) =
      run (StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan false 22 90 (2 + 1) ++
        StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465) m' (pullIn s) :=
  exit_row_full half k x 22 90 2 47 StairLoanExitReachX.ZC (by norm_num) (by norm_num) (by norm_num)
    (fun t h => StairField2V3ExitRec.reach_YC k x t (StairLoanExitReachX.reachX_C half k x t h))
    _ inj1 sig1 rh1 off1 fp1 rs1 fix1 subOff1 away1 _ _ _ seg1 mid1 hep1 s t hrel hz m

set_option maxRecDepth 200000 in
theorem sig2 : ∀ i : Fin 10, OB5.sig 511 (History5.historyMap base (5 * 93) i) =
    History5.historyMap (segW 465) (5 * 93) i := by decide +kernel

set_option maxRecDepth 200000 in
theorem rh2 : ∀ i : Fin 10, History5.historyMap (segW 465) (5 * 93) i ∉
    StairSchedule.exclusiveRoles.drop 30 ++ StairConcreteAssembly.hostPlan.group false 30 93 (2 + 1) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem off2 : ∀ i : Fin 10, StairField2V3RecScratch.Off (History5.historyMap (segW 465) (5 * 93) i) := by
  unfold StairField2V3RecScratch.Off; decide +kernel

set_option maxRecDepth 200000 in
theorem fp2 : ∀ i : Fin 10, History5.historyMap (segW 465) (5 * 93) i ∉ StairPhysicalLayout.futurePayload 32 := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem rs2 : ∀ i : Fin 10, History5.historyMap base (5 * 93) i ∈
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * 93) :=
  rs_of_enc 93 (by decide +kernel)

set_option maxRecDepth 200000 in
theorem fix2 : ∀ i : Fin 10, Placement5.pi 93 (History5.historyId (5 * 93) i) =
    History5.historyId (5 * 93) i := by decide +kernel

theorem subOff2 : ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false 30 93 (2 + 1)),
    StairField2V3RecScratch.Off q :=
  subOff_gen 30 93 (2 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.2.1

theorem away2 : ∀ q ∈ Δv 32, q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans 30 93 (2 + 1)) :=
  away_gen 32 30 93 (2 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem exit_row2 (half : StairLoanReplay.HalfReplayHypothesis) (k x : Nat) (s t : State)
    (hrel : StairField13V3Clean.RowRelL k x 32 StairLoanExitReachX.ZB s t)
    (hz : ∀ q ∈ StairSchedule.exclusiveRoles.drop 30 ++ StairConcreteAssembly.hostPlan.group false 30 93 (2 + 1),
      (pullIn s).basis q = false) (m : List Bool) :
    ∃ m', run (Ah 30 93 2 ++
        (headX 32 480 ++ StairReplay.movedReverse (segW 465) (5 * 93 + 5 + 1) (480 - (5 * 93 + 5) - 1)) ++
        (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 465) (5 * 93))) D26 ++
          W.ReverseCarry.compactReceiverTick (segW 465) 470 ++
          StairReplay.movedReverse (segW 465) 466 4 ++
          StairConcreteAssembly.checkpointPrimitives.tickReverse 465 ++
          StairConcreteAssembly.checkpointPrimitives.pack 47)) m (pullIn s) =
      run (StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan false 30 93 (2 + 1) ++
        StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480) m' (pullIn s) :=
  exit_row_full half k x 30 93 2 32 StairLoanExitReachX.ZB (by norm_num) (by norm_num) (by norm_num)
    (fun t h => StairField2V3ExitRec.reach_YB k x t (StairLoanExitReachX.reachX_B half k x t h))
    _ inj2 sig2 rh2 off2 fp2 rs2 fix2 subOff2 away2 _ _ _ seg2 mid2 hep2 s t hrel hz m

set_option maxRecDepth 200000 in
theorem sig3 : ∀ i : Fin 10, OB5.sig 511 (History5.historyMap base (5 * 96) i) =
    History5.historyMap (segW 480) (5 * 96) i := by decide +kernel

set_option maxRecDepth 200000 in
theorem rh3 : ∀ i : Fin 10, History5.historyMap (segW 480) (5 * 96) i ∉
    StairSchedule.exclusiveRoles.drop 36 ++ StairConcreteAssembly.hostPlan.group false 36 96 (1 + 1) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem off3 : ∀ i : Fin 10, StairField2V3RecScratch.Off (History5.historyMap (segW 480) (5 * 96) i) := by
  unfold StairField2V3RecScratch.Off; decide +kernel

set_option maxRecDepth 200000 in
theorem fp3 : ∀ i : Fin 10, History5.historyMap (segW 480) (5 * 96) i ∉ StairPhysicalLayout.futurePayload 22 := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem rs3 : ∀ i : Fin 10, History5.historyMap base (5 * 96) i ∈
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * 96) :=
  rs_of_enc 96 (by decide +kernel)

set_option maxRecDepth 200000 in
theorem fix3 : ∀ i : Fin 10, Placement5.pi 96 (History5.historyId (5 * 96) i) =
    History5.historyId (5 * 96) i := by decide +kernel

theorem subOff3 : ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false 36 96 (1 + 1)),
    StairField2V3RecScratch.Off q :=
  subOff_gen 36 96 (1 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.1

theorem away3 : ∀ q ∈ Δv 22, q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans 36 96 (1 + 1)) :=
  away_gen 22 36 96 (1 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem exit_row3 (half : StairLoanReplay.HalfReplayHypothesis) (k x : Nat) (s t : State)
    (hrel : StairField13V3Clean.RowRelL k x 22 StairLoanExitReachX.ZA s t)
    (hz : ∀ q ∈ StairSchedule.exclusiveRoles.drop 36 ++ StairConcreteAssembly.hostPlan.group false 36 96 (1 + 1),
      (pullIn s).basis q = false) (m : List Bool) :
    ∃ m', run (Ah 36 96 1 ++
        (headX 22 490 ++ StairReplay.movedReverse (segW 480) (5 * 96 + 5 + 1) (490 - (5 * 96 + 5) - 1)) ++
        (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 480) (5 * 96))) D26 ++
          W.ReverseCarry.compactReceiverTick (segW 480) 485 ++
          StairReplay.movedReverse (segW 480) 481 4 ++
          StairConcreteAssembly.checkpointPrimitives.tickReverse 480 ++
          StairConcreteAssembly.checkpointPrimitives.pack 32)) m (pullIn s) =
      run (StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan false 36 96 (1 + 1) ++
        StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490) m' (pullIn s) :=
  exit_row_full half k x 36 96 1 22 StairLoanExitReachX.ZA (by norm_num) (by norm_num) (by norm_num)
    (fun t h => StairField2V3ExitRec.reach_YA k x t (StairLoanExitReachX.reachX_A half k x t h))
    _ inj3 sig3 rh3 off3 fp3 rs3 fix3 subOff3 away3 _ _ _ seg3 mid3 hep3 s t hrel hz m

set_option maxRecDepth 200000 in
theorem sig4 : ∀ i : Fin 10, OB5.sig 511 (History5.historyMap base (5 * 98) i) =
    History5.historyMap (segW 490) (5 * 98) i := by decide +kernel

set_option maxRecDepth 200000 in
theorem rh4 : ∀ i : Fin 10, History5.historyMap (segW 490) (5 * 98) i ∉
    StairSchedule.exclusiveRoles.drop 41 ++ StairConcreteAssembly.hostPlan.group false 41 98 (1 + 1) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem off4 : ∀ i : Fin 10, StairField2V3RecScratch.Off (History5.historyMap (segW 490) (5 * 98) i) := by
  unfold StairField2V3RecScratch.Off; decide +kernel

set_option maxRecDepth 200000 in
theorem fp4 : ∀ i : Fin 10, History5.historyMap (segW 490) (5 * 98) i ∉ StairPhysicalLayout.futurePayload 12 := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem rs4 : ∀ i : Fin 10, History5.historyMap base (5 * 98) i ∈
    NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * 98) :=
  rs_of_enc 98 (by decide +kernel)

set_option maxRecDepth 200000 in
theorem fix4 : ∀ i : Fin 10, Placement5.pi 98 (History5.historyId (5 * 98) i) =
    History5.historyId (5 * 98) i := by decide +kernel

theorem subOff4 : ∀ q ∈ wires (StairSchedule.placedGroups StairConcrete.bestLoans false 41 98 (1 + 1)),
    StairField2V3RecScratch.Off q :=
  subOff_gen 41 98 (1 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.1

theorem away4 : ∀ q ∈ Δv 12, q ∉ wires (StairLoanField7Transport.grpFL StairConcrete.bestLoans 41 98 (1 + 1)) :=
  away_gen 12 41 98 (1 + 1) (by decide) (by decide) StairLoanField7Transport.exitGroupSub_best.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem exit_row4 (half : StairLoanReplay.HalfReplayHypothesis) (k x : Nat) (s t : State)
    (hrel : StairField13V3Clean.RowRelL k x 12 StairLoanExitReachX.ZH s t)
    (hz : ∀ q ∈ StairSchedule.exclusiveRoles.drop 41 ++ StairConcreteAssembly.hostPlan.group false 41 98 (1 + 1),
      (pullIn s).basis q = false) (m : List Bool) :
    ∃ m', run (Ah 41 98 1 ++
        (headX 12 500 ++ StairReplay.movedReverse (segW 490) (5 * 98 + 5 + 1) (500 - (5 * 98 + 5) - 1)) ++
        (renameProgram (MeasuredCodec5.label (History5.historyMap (segW 490) (5 * 98))) D26 ++
          W.ReverseCarry.compactReceiverTick (segW 490) 495 ++
          StairReplay.movedReverse (segW 490) 491 4 ++
          StairConcreteAssembly.checkpointPrimitives.tickReverse 490 ++
          StairConcreteAssembly.checkpointPrimitives.pack 22)) m (pullIn s) =
      run (StairHostsSchedule.hostedGroup StairConcreteAssembly.hostPlan false 41 98 (1 + 1) ++
        StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500) m' (pullIn s) :=
  exit_row_full half k x 41 98 1 12 StairLoanExitReachX.ZH (by norm_num) (by norm_num) (by norm_num)
    (fun t h => StairField2V3ExitRec.reach_head k x t (StairLoanExitReachX.reachX_head half k x t h))
    _ inj4 sig4 rh4 off4 fp4 rs4 fix4 subOff4 away4 _ _ _ seg4 mid4 hep4 s t hrel hz m

end ECDSAAdd.Entrant.PackCutExitInst


/-! ## PACK-CUT odd exit: programs and per-row bookkeeping (early) -/

section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.PackCutOddExit
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 BalancedField


/-- The odd exit packet without its closing `ep` (base coordinates). -/
def oddHeadF (d j : Nat) : Program :=
  Rolling1588.onPacket j (Rolling1588.dp ++ ParityCodec5New.untwist) ++
    (RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 4 2 ++
      Rolling1588.onPacket j Rolling1588.bridge5 ++
      RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 3 2 ++
      RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 4 2 ++
      Rolling1588.onPacket j Rolling1588.bridge7inv ++
      RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 4 2 ++
      RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 3 2) ++
    Rolling1588.onPacket j ParityCodec5New.twist

theorem oddCell_eq (d j active hole : Nat) :
    OddFullPass.P1LifeLoan.cell false d j active hole =
      RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j active hole := by
  unfold OddFullPass.P1LifeLoan.cell OddFullPass.P1LifeLoan.halfWindow
    RouteA.Rolling1588.cellWith RouteA.Rolling1588.halfWindowWith
  rfl

/-- The odd exit packet is its head followed by the closing `ep`. -/
theorem basePacket_false_tail (d j : Nat) :
    OddFullPass.P1LifeLoan.basePacket false d j = oddHeadF d j ++ Rolling1588.onPacket j Rolling1588.ep := by
  simp only [OddFullPass.P1LifeLoan.basePacket, oddHeadF, oddCell_eq, Bool.false_eq_true, ↓reduceIte,
    Rolling1588.onPacket, PackCutShape.rename_app, List.append_assoc]

theorem twist_meas (j : Nat) : measurementCount (Rolling1588.onPacket j ParityCodec5New.twist) = 0 := by
  simp only [Rolling1588.onPacket, ParityCodec5New.twist, renameProgram, List.map, renameInstr, measurementCount]

theorem run_nomeas_tape (P : Program) (h : measurementCount P = 0) (m : List Bool) (s : State) :
    run P m s = run P [] s := by
  rw [← run_take P m s, h]; rfl

theorem run_nomeas_phase (P : Program) (h : measurementCount P = 0) (m : List Bool) (s : State) :
    (run P m s).phase = s.phase := by
  induction P generalizing s with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | measureX t c0 c1 => simp [measurementCount] at h
    | X t => exact ih (by simpa [measurementCount] using h) _
    | CX c t => exact ih (by simpa [measurementCount] using h) _
    | CCX a b t => exact ih (by simpa [measurementCount] using h) _

theorem twist_frame (j : Nat) (E : Program) (origin : BasisState) (X Y : Fp) :
    Rolling1588.StateTriple (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord E origin X Y)
      (Rolling1588.onPacket j ParityCodec5New.twist)
      (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
        (E ++ Rolling1588.onPacket j ParityCodec5New.twist) origin X Y) := by
  intro state records input
  obtain ⟨raw, hph, hpf, hst⟩ := input
  have hp := run_nomeas_phase _ (twist_meas j) records state
  refine ⟨hp, raw, hph.trans hp.symm, hpf, ?_⟩
  rw [run_nomeas_tape _ (twist_meas j), hst, run_append]
  simp


end ECDSAAdd.Entrant.PackCutOddExit

namespace ECDSAAdd.Entrant.PackCutOddExit
open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout

attribute [local irreducible] run measurementCount wires renameProgram toffoliCount Challenge.gateSlots

theorem program_false_tail' (p : Nat → Program) (j c : Nat) :
    PacketSequence.program false p j (c + 1) = PacketSequence.program false p (j + 1) c ++ p j := by
  simp [PacketSequence.program]

theorem rename_app' (f : Wire → Wire) (P Q : Program) :
    renameProgram f (P ++ Q) = renameProgram f P ++ renameProgram f Q := by
  simp [renameProgram, List.map_append]

/-- The placed odd exit group = its placed head (all but the last closing `ep`) ++ the placed `ep`. -/
theorem oddPlaced_false_tail (d first c : Nat) :
    renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups false d first (c + 1)) =
      renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups false d (first + 1) c ++
        renameProgram (shifted (Placement5.pi first)) (oddHeadF d first)) ++
      renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
        (Rolling1588.onPacket first Rolling1588.ep)) := by
  simp only [OddFullPass.P1LifeLoan.groups, program_false_tail', OddFullPass.P1LifeLoan.packet,
    basePacket_false_tail, rename_app', List.append_assoc]


/-- The hosted part of the odd exit group before its closing `ep`. -/
def AhOdd (d first c : Nat) : Program :=
  StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hostPlan.group false d first (c + 1))
    (renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups false d (first + 1) c ++
      renameProgram (shifted (Placement5.pi first)) (oddHeadF d first)))

theorem oddHostedGroup_false_tail (d first c : Nat) :
    OddFullPass.P1LifeLoan.hostedGroup hostPlan false d first (c + 1) =
      AhOdd d first c ++ StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d) (hostPlan.group false d first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.ep))) := by
  rw [OddFullPass.P1LifeLoan.hostedGroup, OddFullPass.P1LifeLoan.placedGroups, oddPlaced_false_tail,
    PackCutShape.rebindMany_append]
  rfl

/-- PACK-CUT odd exit row: the hosted odd group without its last closing `ep`, then the reverse segment
without its due-read `dp`. -/
def cutRowOddPk (B N s f d first c : Nat) : Program :=
  AhOdd d first c ++
    (PackCutExitRows.headX N f ++
      StairReplay.movedReverse (PackCutExitRows.segW s) (5 * first + 5 + 1) (f - (5 * first + 5) - 1)) ++
    (renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW s) (5 * first))) PackCutExit.D26 ++
      W.ReverseCarry.compactReceiverTick (PackCutExitRows.segW s) (5 * first + 5) ++
      StairReplay.movedReverse (PackCutExitRows.segW s) (s + 1) (5 * first + 5 - (s + 1)) ++
      StairConcreteAssembly.checkpointPrimitives.tickReverse s ++
      StairConcreteAssembly.checkpointPrimitives.pack B)

theorem cutRow_count_split (A Eh M Dh Bx : Program)
    (hEt : toffoliCount Eh = 6) (hDt : toffoliCount Dh = 7) (hEm : measurementCount Eh = 3) (hDm : measurementCount Dh = 2) :
    toffoliCount (A ++ M ++ Bx) + 13 = toffoliCount (A ++ Eh) + toffoliCount (M ++ Dh ++ Bx) ∧
    measurementCount (A ++ M ++ Bx) + 5 = measurementCount (A ++ Eh) + measurementCount (M ++ Dh ++ Bx) := by
  simp only [toffoliCount_append, measurementCount_append]
  omega

theorem cutRow_wires_split (A Eh M Dh Bx : Program) :
    wires (A ++ M ++ Bx) ⊆ wires (A ++ Eh) ∪ wires (M ++ Dh ++ Bx) := by
  intro q hq
  simp only [wires_append, Finset.mem_union] at hq ⊢
  tauto

theorem ep_counts (f : Wire → Wire) :
    toffoliCount (renameProgram f Rolling1588.ep) = 6 ∧ measurementCount (renameProgram f Rolling1588.ep) = 3 := by
  rw [(renameProgram_counts f _).1, (renameProgram_counts f _).2]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem dp_counts (f : Wire → Wire) :
    toffoliCount (renameProgram f Rolling1588.dp) = 7 ∧ measurementCount (renameProgram f Rolling1588.dp) = 2 := by
  rw [(renameProgram_counts f _).1, (renameProgram_counts f _).2]
  exact ⟨by decide +kernel, by decide +kernel⟩

theorem cutRow_sound_split (A Eh M Dh Bx : Program)
    (h1 : StairPhysicalV3.Sound (A ++ Eh)) (h2 : StairPhysicalV3.Sound (M ++ Dh ++ Bx)) :
    StairPhysicalV3.Sound (A ++ M ++ Bx) := by
  refine ⟨?_, ?_⟩
  · have p1 := h1.physical
    have p2 := h2.physical
    simp only [gatePhysical_append] at p1 p2 ⊢
    exact ⟨⟨p1.1, p2.1.1⟩, p2.2⟩
  · intro q hq
    rcases Finset.mem_union.mp (cutRow_wires_split A Eh M Dh Bx hq) with h | h
    · exact h1.good q h
    · exact h2.good q h

theorem cutRow_slots_split (A Eh M Dh Bx : Program) :
    Challenge.gateSlots (A ++ M ++ Bx) ≤ Challenge.gateSlots (A ++ Eh) + Challenge.gateSlots (M ++ Dh ++ Bx) := by
  simp only [Challenge.gateSlots_append]
  omega


theorem cutRow_counts_gen (A Eh M Dh Bx HG SEG CR : Program)
    (hHG : HG = A ++ Eh) (hSEG : SEG = M ++ Dh ++ Bx) (hCR : CR = A ++ M ++ Bx)
    (hEt : toffoliCount Eh = 6) (hDt : toffoliCount Dh = 7) (hEm : measurementCount Eh = 3) (hDm : measurementCount Dh = 2) :
    toffoliCount CR + 13 = toffoliCount HG + toffoliCount SEG ∧
    measurementCount CR + 5 = measurementCount HG + measurementCount SEG := by
  subst hHG hSEG hCR
  exact cutRow_count_split A Eh M Dh Bx hEt hDt hEm hDm

theorem cutRow_slots_gen (A Eh M Dh Bx HG SEG CR : Program)
    (hHG : HG = A ++ Eh) (hSEG : SEG = M ++ Dh ++ Bx) (hCR : CR = A ++ M ++ Bx) :
    Challenge.gateSlots CR ≤ Challenge.gateSlots HG + Challenge.gateSlots SEG := by
  subst hHG hSEG hCR
  exact cutRow_slots_split A Eh M Dh Bx

theorem cutRow_wires_gen (A Eh M Dh Bx HG SEG CR : Program)
    (hHG : HG = A ++ Eh) (hSEG : SEG = M ++ Dh ++ Bx) (hCR : CR = A ++ M ++ Bx) :
    wires CR ⊆ wires HG ∪ wires SEG := by
  subst hHG hSEG hCR
  intro q hq
  have h := cutRow_wires_split A Eh M Dh Bx hq
  simpa [wires_append] using h

theorem cutRow_sound_gen (A Eh M Dh Bx HG SEG CR : Program)
    (hHG : HG = A ++ Eh) (hSEG : SEG = M ++ Dh ++ Bx) (hCR : CR = A ++ M ++ Bx)
    (h1 : StairPhysicalV3.Sound HG) (h2 : StairPhysicalV3.Sound SEG) : StairPhysicalV3.Sound CR := by
  subst hHG hSEG hCR
  exact cutRow_sound_split A Eh M Dh Bx h1 h2

theorem cutRowOddPk_eq0 : cutRowOddPk 87 62 425 450 13 85 4 = AhOdd 13 85 4 ++ (PackCutExitRows.headX 62 450 ++ StairReplay.movedReverse (PackCutExitRows.segW 425) (5 * 85 + 5 + 1) (450 - (5 * 85 + 5) - 1)) ++ (renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 425) (5 * 85))) PackCutExit.D26 ++
        W.ReverseCarry.compactReceiverTick (PackCutExitRows.segW 425) 430 ++
        StairReplay.movedReverse (PackCutExitRows.segW 425) 426 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 425 ++
        StairConcreteAssembly.checkpointPrimitives.pack 87) := rfl

theorem hostedGroup_eq0 : OddFullPass.P1LifeLoan.hostedGroup hostPlan false 13 85 5 = AhOdd 13 85 4 ++ renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 425) (5 * 85))) Rolling1588.ep :=
  (oddHostedGroup_false_tail 13 85 4).trans (congrArg (AhOdd 13 85 4 ++ ·) PackCutExitRows.hep0)

theorem cutRow0_counts :
    toffoliCount (cutRowOddPk 87 62 425 450 13 85 4) + 13 = toffoliCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 13 85 5) + toffoliCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) ∧
    measurementCount (cutRowOddPk 87 62 425 450 13 85 4) + 5 = measurementCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 13 85 5) + measurementCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) :=
  cutRow_counts_gen _ _ _ _ _ _ _ _ hostedGroup_eq0 PackCutExitRows.seg0 cutRowOddPk_eq0
    (ep_counts _).1 (dp_counts _).1 (ep_counts _).2 (dp_counts _).2

theorem cutRow0_slots :
    Challenge.gateSlots (cutRowOddPk 87 62 425 450 13 85 4) ≤ Challenge.gateSlots (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 13 85 5) + Challenge.gateSlots (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) :=
  cutRow_slots_gen _ _ _ _ _ _ _ _ hostedGroup_eq0 PackCutExitRows.seg0 cutRowOddPk_eq0

theorem cutRow0_wires :
    wires (cutRowOddPk 87 62 425 450 13 85 4) ⊆ wires (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 13 85 5) ∪ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) :=
  cutRow_wires_gen _ _ _ _ _ _ _ _ hostedGroup_eq0 PackCutExitRows.seg0 cutRowOddPk_eq0

theorem cutRow0_sound (h1 : StairPhysicalV3.Sound (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 13 85 5))
    (h2 : StairPhysicalV3.Sound (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450)) : StairPhysicalV3.Sound (cutRowOddPk 87 62 425 450 13 85 4) :=
  cutRow_sound_gen _ _ _ _ _ _ _ _ hostedGroup_eq0 PackCutExitRows.seg0 cutRowOddPk_eq0 h1 h2

theorem cutRow0_stock_mem (q : Wire) (h : q ∈ wires (cutRowOddPk 87 62 425 450 13 85 4)) :
    q ∈ wires (StairHostsSchedule.hostedGroup hostPlan false 13 85 5) ∨ q ∈ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) := by
  rcases Finset.mem_union.mp (cutRow0_wires h) with h' | h'
  · exact Or.inl (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan false 13 85 5 (by decide) (by decide) h')
  · exact Or.inr h'

theorem cutRowOddPk_eq1 : cutRowOddPk 62 47 450 465 22 90 2 = AhOdd 22 90 2 ++ (PackCutExitRows.headX 47 465 ++ StairReplay.movedReverse (PackCutExitRows.segW 450) (5 * 90 + 5 + 1) (465 - (5 * 90 + 5) - 1)) ++ (renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 450) (5 * 90))) PackCutExit.D26 ++
        W.ReverseCarry.compactReceiverTick (PackCutExitRows.segW 450) 455 ++
        StairReplay.movedReverse (PackCutExitRows.segW 450) 451 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 450 ++
        StairConcreteAssembly.checkpointPrimitives.pack 62) := rfl

theorem hostedGroup_eq1 : OddFullPass.P1LifeLoan.hostedGroup hostPlan false 22 90 3 = AhOdd 22 90 2 ++ renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 450) (5 * 90))) Rolling1588.ep :=
  (oddHostedGroup_false_tail 22 90 2).trans (congrArg (AhOdd 22 90 2 ++ ·) PackCutExitRows.hep1)

theorem cutRow1_counts :
    toffoliCount (cutRowOddPk 62 47 450 465 22 90 2) + 13 = toffoliCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 22 90 3) + toffoliCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465) ∧
    measurementCount (cutRowOddPk 62 47 450 465 22 90 2) + 5 = measurementCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 22 90 3) + measurementCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465) :=
  cutRow_counts_gen _ _ _ _ _ _ _ _ hostedGroup_eq1 PackCutExitRows.seg1 cutRowOddPk_eq1
    (ep_counts _).1 (dp_counts _).1 (ep_counts _).2 (dp_counts _).2

theorem cutRow1_slots :
    Challenge.gateSlots (cutRowOddPk 62 47 450 465 22 90 2) ≤ Challenge.gateSlots (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 22 90 3) + Challenge.gateSlots (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465) :=
  cutRow_slots_gen _ _ _ _ _ _ _ _ hostedGroup_eq1 PackCutExitRows.seg1 cutRowOddPk_eq1

theorem cutRow1_wires :
    wires (cutRowOddPk 62 47 450 465 22 90 2) ⊆ wires (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 22 90 3) ∪ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465) :=
  cutRow_wires_gen _ _ _ _ _ _ _ _ hostedGroup_eq1 PackCutExitRows.seg1 cutRowOddPk_eq1

theorem cutRow1_sound (h1 : StairPhysicalV3.Sound (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 22 90 3))
    (h2 : StairPhysicalV3.Sound (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465)) : StairPhysicalV3.Sound (cutRowOddPk 62 47 450 465 22 90 2) :=
  cutRow_sound_gen _ _ _ _ _ _ _ _ hostedGroup_eq1 PackCutExitRows.seg1 cutRowOddPk_eq1 h1 h2

theorem cutRow1_stock_mem (q : Wire) (h : q ∈ wires (cutRowOddPk 62 47 450 465 22 90 2)) :
    q ∈ wires (StairHostsSchedule.hostedGroup hostPlan false 22 90 3) ∨ q ∈ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465) := by
  rcases Finset.mem_union.mp (cutRow1_wires h) with h' | h'
  · exact Or.inl (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan false 22 90 3 (by decide) (by decide) h')
  · exact Or.inr h'

theorem cutRowOddPk_eq2 : cutRowOddPk 47 32 465 480 30 93 2 = AhOdd 30 93 2 ++ (PackCutExitRows.headX 32 480 ++ StairReplay.movedReverse (PackCutExitRows.segW 465) (5 * 93 + 5 + 1) (480 - (5 * 93 + 5) - 1)) ++ (renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 465) (5 * 93))) PackCutExit.D26 ++
        W.ReverseCarry.compactReceiverTick (PackCutExitRows.segW 465) 470 ++
        StairReplay.movedReverse (PackCutExitRows.segW 465) 466 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 465 ++
        StairConcreteAssembly.checkpointPrimitives.pack 47) := rfl

theorem hostedGroup_eq2 : OddFullPass.P1LifeLoan.hostedGroup hostPlan false 30 93 3 = AhOdd 30 93 2 ++ renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 465) (5 * 93))) Rolling1588.ep :=
  (oddHostedGroup_false_tail 30 93 2).trans (congrArg (AhOdd 30 93 2 ++ ·) PackCutExitRows.hep2)

theorem cutRow2_counts :
    toffoliCount (cutRowOddPk 47 32 465 480 30 93 2) + 13 = toffoliCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 30 93 3) + toffoliCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480) ∧
    measurementCount (cutRowOddPk 47 32 465 480 30 93 2) + 5 = measurementCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 30 93 3) + measurementCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480) :=
  cutRow_counts_gen _ _ _ _ _ _ _ _ hostedGroup_eq2 PackCutExitRows.seg2 cutRowOddPk_eq2
    (ep_counts _).1 (dp_counts _).1 (ep_counts _).2 (dp_counts _).2

theorem cutRow2_slots :
    Challenge.gateSlots (cutRowOddPk 47 32 465 480 30 93 2) ≤ Challenge.gateSlots (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 30 93 3) + Challenge.gateSlots (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480) :=
  cutRow_slots_gen _ _ _ _ _ _ _ _ hostedGroup_eq2 PackCutExitRows.seg2 cutRowOddPk_eq2

theorem cutRow2_wires :
    wires (cutRowOddPk 47 32 465 480 30 93 2) ⊆ wires (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 30 93 3) ∪ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480) :=
  cutRow_wires_gen _ _ _ _ _ _ _ _ hostedGroup_eq2 PackCutExitRows.seg2 cutRowOddPk_eq2

theorem cutRow2_sound (h1 : StairPhysicalV3.Sound (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 30 93 3))
    (h2 : StairPhysicalV3.Sound (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480)) : StairPhysicalV3.Sound (cutRowOddPk 47 32 465 480 30 93 2) :=
  cutRow_sound_gen _ _ _ _ _ _ _ _ hostedGroup_eq2 PackCutExitRows.seg2 cutRowOddPk_eq2 h1 h2

theorem cutRow2_stock_mem (q : Wire) (h : q ∈ wires (cutRowOddPk 47 32 465 480 30 93 2)) :
    q ∈ wires (StairHostsSchedule.hostedGroup hostPlan false 30 93 3) ∨ q ∈ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480) := by
  rcases Finset.mem_union.mp (cutRow2_wires h) with h' | h'
  · exact Or.inl (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan false 30 93 3 (by decide) (by decide) h')
  · exact Or.inr h'

theorem cutRowOddPk_eq3 : cutRowOddPk 32 22 480 490 36 96 1 = AhOdd 36 96 1 ++ (PackCutExitRows.headX 22 490 ++ StairReplay.movedReverse (PackCutExitRows.segW 480) (5 * 96 + 5 + 1) (490 - (5 * 96 + 5) - 1)) ++ (renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 480) (5 * 96))) PackCutExit.D26 ++
        W.ReverseCarry.compactReceiverTick (PackCutExitRows.segW 480) 485 ++
        StairReplay.movedReverse (PackCutExitRows.segW 480) 481 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 480 ++
        StairConcreteAssembly.checkpointPrimitives.pack 32) := rfl

theorem hostedGroup_eq3 : OddFullPass.P1LifeLoan.hostedGroup hostPlan false 36 96 2 = AhOdd 36 96 1 ++ renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 480) (5 * 96))) Rolling1588.ep :=
  (oddHostedGroup_false_tail 36 96 1).trans (congrArg (AhOdd 36 96 1 ++ ·) PackCutExitRows.hep3)

theorem cutRow3_counts :
    toffoliCount (cutRowOddPk 32 22 480 490 36 96 1) + 13 = toffoliCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 36 96 2) + toffoliCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490) ∧
    measurementCount (cutRowOddPk 32 22 480 490 36 96 1) + 5 = measurementCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 36 96 2) + measurementCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490) :=
  cutRow_counts_gen _ _ _ _ _ _ _ _ hostedGroup_eq3 PackCutExitRows.seg3 cutRowOddPk_eq3
    (ep_counts _).1 (dp_counts _).1 (ep_counts _).2 (dp_counts _).2

theorem cutRow3_slots :
    Challenge.gateSlots (cutRowOddPk 32 22 480 490 36 96 1) ≤ Challenge.gateSlots (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 36 96 2) + Challenge.gateSlots (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490) :=
  cutRow_slots_gen _ _ _ _ _ _ _ _ hostedGroup_eq3 PackCutExitRows.seg3 cutRowOddPk_eq3

theorem cutRow3_wires :
    wires (cutRowOddPk 32 22 480 490 36 96 1) ⊆ wires (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 36 96 2) ∪ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490) :=
  cutRow_wires_gen _ _ _ _ _ _ _ _ hostedGroup_eq3 PackCutExitRows.seg3 cutRowOddPk_eq3

theorem cutRow3_sound (h1 : StairPhysicalV3.Sound (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 36 96 2))
    (h2 : StairPhysicalV3.Sound (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490)) : StairPhysicalV3.Sound (cutRowOddPk 32 22 480 490 36 96 1) :=
  cutRow_sound_gen _ _ _ _ _ _ _ _ hostedGroup_eq3 PackCutExitRows.seg3 cutRowOddPk_eq3 h1 h2

theorem cutRow3_stock_mem (q : Wire) (h : q ∈ wires (cutRowOddPk 32 22 480 490 36 96 1)) :
    q ∈ wires (StairHostsSchedule.hostedGroup hostPlan false 36 96 2) ∨ q ∈ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490) := by
  rcases Finset.mem_union.mp (cutRow3_wires h) with h' | h'
  · exact Or.inl (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan false 36 96 2 (by decide) (by decide) h')
  · exact Or.inr h'

theorem cutRowOddPk_eq4 : cutRowOddPk 22 12 490 500 41 98 1 = AhOdd 41 98 1 ++ (PackCutExitRows.headX 12 500 ++ StairReplay.movedReverse (PackCutExitRows.segW 490) (5 * 98 + 5 + 1) (500 - (5 * 98 + 5) - 1)) ++ (renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 490) (5 * 98))) PackCutExit.D26 ++
        W.ReverseCarry.compactReceiverTick (PackCutExitRows.segW 490) 495 ++
        StairReplay.movedReverse (PackCutExitRows.segW 490) 491 4 ++
        StairConcreteAssembly.checkpointPrimitives.tickReverse 490 ++
        StairConcreteAssembly.checkpointPrimitives.pack 22) := rfl

theorem hostedGroup_eq4 : OddFullPass.P1LifeLoan.hostedGroup hostPlan false 41 98 2 = AhOdd 41 98 1 ++ renameProgram (MeasuredCodec5.label (History5.historyMap (PackCutExitRows.segW 490) (5 * 98))) Rolling1588.ep :=
  (oddHostedGroup_false_tail 41 98 1).trans (congrArg (AhOdd 41 98 1 ++ ·) PackCutExitRows.hep4)

theorem cutRow4_counts :
    toffoliCount (cutRowOddPk 22 12 490 500 41 98 1) + 13 = toffoliCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 41 98 2) + toffoliCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500) ∧
    measurementCount (cutRowOddPk 22 12 490 500 41 98 1) + 5 = measurementCount (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 41 98 2) + measurementCount (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500) :=
  cutRow_counts_gen _ _ _ _ _ _ _ _ hostedGroup_eq4 PackCutExitRows.seg4 cutRowOddPk_eq4
    (ep_counts _).1 (dp_counts _).1 (ep_counts _).2 (dp_counts _).2

theorem cutRow4_slots :
    Challenge.gateSlots (cutRowOddPk 22 12 490 500 41 98 1) ≤ Challenge.gateSlots (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 41 98 2) + Challenge.gateSlots (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500) :=
  cutRow_slots_gen _ _ _ _ _ _ _ _ hostedGroup_eq4 PackCutExitRows.seg4 cutRowOddPk_eq4

theorem cutRow4_wires :
    wires (cutRowOddPk 22 12 490 500 41 98 1) ⊆ wires (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 41 98 2) ∪ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500) :=
  cutRow_wires_gen _ _ _ _ _ _ _ _ hostedGroup_eq4 PackCutExitRows.seg4 cutRowOddPk_eq4

theorem cutRow4_sound (h1 : StairPhysicalV3.Sound (OddFullPass.P1LifeLoan.hostedGroup hostPlan false 41 98 2))
    (h2 : StairPhysicalV3.Sound (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500)) : StairPhysicalV3.Sound (cutRowOddPk 22 12 490 500 41 98 1) :=
  cutRow_sound_gen _ _ _ _ _ _ _ _ hostedGroup_eq4 PackCutExitRows.seg4 cutRowOddPk_eq4 h1 h2

theorem cutRow4_stock_mem (q : Wire) (h : q ∈ wires (cutRowOddPk 22 12 490 500 41 98 1)) :
    q ∈ wires (StairHostsSchedule.hostedGroup hostPlan false 41 98 2) ∨ q ∈ wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500) := by
  rcases Finset.mem_union.mp (cutRow4_wires h) with h' | h'
  · exact Or.inl (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan false 41 98 2 (by decide) (by decide) h')
  · exact Or.inr h'

/-- The cut exit rows' wires sit inside the stock rows' wires. -/
theorem cutRows_sub :
    wires (StairSchedule.reverseLast StairConcreteAssembly.checkpointPrimitives ++
      cutRowOddPk 22 12 490 500 41 98 1 ++
      cutRowOddPk 32 22 480 490 36 96 1 ++
      cutRowOddPk 47 32 465 480 30 93 2 ++
      cutRowOddPk 62 47 450 465 22 90 2 ++
      cutRowOddPk 87 62 425 450 13 85 4) ⊆
    wires (StairSchedule.reverseLast StairConcreteAssembly.checkpointPrimitives ++
      StairHostsSchedule.hostedGroup hostPlan false 41 98 2 ++ StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500 ++
      StairHostsSchedule.hostedGroup hostPlan false 36 96 2 ++ StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490 ++
      StairHostsSchedule.hostedGroup hostPlan false 30 93 3 ++ StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480 ++
      StairHostsSchedule.hostedGroup hostPlan false 22 90 3 ++ StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465 ++
      StairHostsSchedule.hostedGroup hostPlan false 13 85 5 ++ StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) := by
  intro q hq
  simp only [wires_append, Finset.mem_union] at hq ⊢
  rcases hq with (((((h | h) | h) | h) | h) | h)
  · tauto
  · have := cutRow4_stock_mem q h
    tauto
  · have := cutRow3_stock_mem q h
    tauto
  · have := cutRow2_stock_mem q h
    tauto
  · have := cutRow1_stock_mem q h
    tauto
  · have := cutRow0_stock_mem q h
    tauto

end ECDSAAdd.Entrant.PackCutOddExit
end


section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

def entryTailPrefix (p : StairSchedule.StairPrimitives)
     : Program :=
  WindowFieldCosts.group84 true ++
    StairSchedule.forwardSegment p 87 62 425 450 ++
    OddFullPass.P1LifeLoan.hostedGroup hostPlan true 13 85 5 ++
    StairSchedule.forwardSegment p 62 47 450 465 ++
    OddFullPass.P1LifeLoan.hostedGroup hostPlan true 22 90 3 ++
    StairSchedule.forwardSegment p 47 32 465 480 ++
    OddFullPass.P1LifeLoan.hostedGroup hostPlan true 30 93 3 ++
    StairSchedule.forwardSegment p 32 22 480 490 ++
    OddFullPass.P1LifeLoan.hostedGroup hostPlan true 36 96 2 ++
    StairSchedule.forwardSegment p 22 12 490 500 ++
    OddFullPass.P1LifeLoan.hostedGroup hostPlan true 41 98 2 ++ StairSchedule.forwardLast p

def exitHeadSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.reverseLast p ++
    PackCutOddExit.cutRowOddPk 22 12 490 500 41 98 1 ++
    PackCutOddExit.cutRowOddPk 32 22 480 490 36 96 1 ++
    PackCutOddExit.cutRowOddPk 47 32 465 480 30 93 2 ++
    PackCutOddExit.cutRowOddPk 62 47 450 465 22 90 2 ++
    PackCutOddExit.cutRowOddPk 87 62 425 450 13 85 4 ++
    WindowFieldCosts.group84 false

/-- Odd-word half-cell on `base 760` used for cells 2, 3, 4 of `placedFirstPacketOdd`. -/
def oddFirstHalf (divide : Bool) : Program :=
  P1Life.half (base 760) divide base (base 2409)

theorem oddFirstHalf_physical (divide : Bool) : GatePhysical (oddFirstHalf divide) :=
  (P1Life.half_resources (base 760) divide base (base 2409)
    Rolling1588Lifetime.half_ports_nodup RouteA.Rolling1588.route_retired_member).1

theorem oddFirstHalf_support (divide : Bool) :
    JointOdd1588.OddHalfSupport (oddFirstHalf divide) := by
  have hchk : (base 2409 :: base 768 :: base 1797 :: base 1027 ::
      (wireBlock base 2056 256 ++ wireBlock base 770 256 ++ (wireBlock base 512 253 ++ [base 1540]))).all
      (fun q => decide (q = base 760 ∨ (q ∈ StairFirstPacketKernel.LT48T.env ∧ q ∉ StairFirstPacketKernel.LT48T.bad))) = true := by
    decide +kernel
  intro q hq
  have hsub := (P1Life.half_resources (base 760) divide base (base 2409)
    Rolling1588Lifetime.half_ports_nodup RouteA.Rolling1588.route_retired_member).2 hq
  have hne := (Finset.mem_erase.mp hsub).1
  have hmem := Finset.mem_of_mem_erase hsub
  rw [P1Life.junction_footprint_ports, List.mem_toFinset] at hmem
  exact (of_decide_eq_true (List.all_eq_true.mp hchk q hmem)).resolve_left hne

theorem oddFirstHalf_slots_le (divide : Bool) :
    Challenge.gateSlots (oddFirstHalf divide) ≤ Challenge.gateSlots (R2Life760.half760 divide) := by
  have h1 := RouteA.slot_half (base 760) divide base (base 2409)
  have h2 := RouteA.slot_record_half divide
  cases divide <;> simp only [oddFirstHalf, Bool.false_eq_true, if_false, if_true] at h1 h2 ⊢ <;> omega

theorem fpSup_bounds (w : Wire) (h : StairWireCheck.fpSup w = true) :
    (16 ≤ w ∧ w < 2330) ∨ w = 2425 := by
  have hlt : w < 2426 := StairWireCheck.fpSup_lt w h
  have hchk : (List.range 2426).all (fun x : Nat =>
      !StairWireCheck.fpSup x || (decide (16 ≤ x ∧ x < 2330) || decide (x = 2425))) = true := by
    decide +kernel
  have hw := List.all_eq_true.mp hchk w (List.mem_range.mpr hlt)
  simp only [h, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hw
  exact hw

private theorem rebindMany_slots_eq (roles hosts : List Wire) (P : Program) :
    Challenge.gateSlots (StairLoan.rebindMany roles hosts P) = Challenge.gateSlots P := by
  induction roles generalizing hosts with
  | nil => rfl
  | cons r roles ih =>
    cases hosts with
    | nil => rfl
    | cons h hosts => simp only [StairLoan.rebindMany, Baselines.rename_gateSlots, ih]

def entryLowPrefix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
      (JointOdd1588.placedFirstPacketOdd oddFirstHalf true) ++
    FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (entryTailPrefix p) ++
    FourScratchWindow.unprefix

def exitLowSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (exitHeadSuffix p) ++
    FourScratchWindow.unprefix ++
    StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
      (JointOdd1588.placedFirstPacketOdd oddFirstHalf false)

def entryFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.fieldRename (entryLowPrefix p) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd hostPlan) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd hostPlan) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowSuffix p)

/-- The division field's tail prefix with the five packet-cut odd rows. -/
def entryTailPrefixCut : Program :=
  WindowFieldCosts.group84 true ++
    (PackCutOdd.cutRowOdd 87 62 425 450 13 85 4 ++
    (PackCutOdd.cutRowOdd 62 47 450 465 22 90 2 ++
    (PackCutOdd.cutRowOdd 47 32 465 480 30 93 2 ++
    (PackCutOdd.cutRowOdd 32 22 480 490 36 96 1 ++
    (PackCutOdd.cutRowOdd 22 12 490 500 41 98 1 ++ StairSchedule.forwardLast checkpointPrimitives)))))

def entryLowPrefixCut : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
      (JointOdd1588.placedFirstPacketOdd oddFirstHalf true) ++
    FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow entryTailPrefixCut ++
    FourScratchWindow.unprefix

def entryFieldHostedCut : Program :=
  StairSchedule.fieldRename entryLowPrefixCut ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd hostPlan) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

theorem field_delta_tc_div (n : Nat)
    (h : tc.measure (WindowFieldCosts.group84 true)=tc.measure (WindowFieldCosts.group true 1 84)+n) :
    tc.measure (entryFieldHosted checkpointPrimitives)+953 =
      tc.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 13 85 5 (by decide) (by decide)).1
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 22 90 3 (by decide) (by decide)).1
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 30 93 3 (by decide) (by decide)).1
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 36 96 2 (by decide) (by decide)).1
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 41 98 2 (by decide) (by decide)).1
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 43 100 2 (by decide) (by decide)).1
  have hc := OddFullPass.HalfConvertOdd.canon760OddLoan_counts.1
  have hcn := StairBoundaryLoan.canon760Loan_counts.1
  have hcb : toffoliCount R2SqEp760.canon760 = 254 := by
    rw [StairBoundaryLoan.canon760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).2.2.1
  have hde := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_counts.1
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf true
    (P1Life.half_counts (base 760) true base (base 2409)).1
    (P1Life.half_counts (base 760) true base (base 2409)).2).1
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf true)).1
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (Rolling1588.placedFirstPacket true)).1
  rw [show tc.measure=toffoliCount from rfl] at h ⊢
  simp only [if_true,WindowFieldCosts.group,entryFieldHosted,entryLowPrefix,entryTailPrefix,
    OddFullPass.P1LifeLoan.entryLowSuffixOdd,OddFullPass.P1LifeLoan.entryTailSuffixOdd,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.entryLowPrefix,
    StairHostsSchedule.entryTailPrefix,StairHostsSchedule.entryLowSuffix,
    StairHostsSchedule.entryTailSuffix,StairConcrete.bestLoans_divEndpoint,
    StairConcrete.bestLoans,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,toffoliCount_append] at *
  norm_num only at g13 g22 g30 g36 g41 g43
  simp only [if_false,if_true] at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_tc_mul (n : Nat)
    (h : tc.measure (WindowFieldCosts.group84 false)=tc.measure (WindowFieldCosts.group false 1 84)+n) :
    tc.measure (exitFieldHosted checkpointPrimitives)+1020 =
      tc.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 13 85 5 (by decide) (by decide)).1
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 22 90 3 (by decide) (by decide)).1
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 30 93 3 (by decide) (by decide)).1
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 36 96 2 (by decide) (by decide)).1
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 41 98 2 (by decide) (by decide)).1
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 43 100 2 (by decide) (by decide)).1
  have hct := OddFullPass.HalfConvertOdd.center760OddLoan_counts.1
  have hctn := StairBoundaryLoan.center760Loan_counts.1
  have hctb : toffoliCount R2SqEp760.center760 = 254 := by
    rw [StairBoundaryLoan.center760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).1
  have hme := OddFullPass.InverseTailCOdd.endPacket760OddLoan44_counts.1
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf false
    (P1Life.half_counts (base 760) false base (base 2409)).1
    (P1Life.half_counts (base 760) false base (base 2409)).2).1
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf false)).1
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (Rolling1588.placedFirstPacket false)).1
  have cr0 := PackCutOddExit.cutRow0_counts.1
  have cr1 := PackCutOddExit.cutRow1_counts.1
  have cr2 := PackCutOddExit.cutRow2_counts.1
  have cr3 := PackCutOddExit.cutRow3_counts.1
  have cr4 := PackCutOddExit.cutRow4_counts.1
  rw [show tc.measure=toffoliCount from rfl] at h ⊢
  simp only [WindowFieldCosts.group,exitFieldHosted,exitLowSuffix,exitHeadSuffix,
    OddFullPass.P1LifeLoan.exitLowPrefixOdd,OddFullPass.P1LifeLoan.exitHeadPrefixOdd,
    StairHostsSchedule.exitFieldHosted,StairHostsSchedule.exitLowSuffix,
    StairHostsSchedule.exitHeadSuffix,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.exitHeadPrefix,StairHostsSchedule.hostedEndpoint,
    StairSchedule.placedEndPacket,StairConcrete.bestLoans,StairConcrete.endPacket,
    Bool.false_eq_true,if_false,if_true,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,toffoliCount_append] at *
  norm_num only at g13 g22 g30 g36 g41 g43
  simp only [if_false,if_true] at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_mc_div (n : Nat)
    (h : mc.measure (WindowFieldCosts.group84 true)=mc.measure (WindowFieldCosts.group true 1 84)+n) :
    mc.measure (entryFieldHosted checkpointPrimitives)+1718 =
      mc.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 13 85 5 (by decide) (by decide)).2
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 22 90 3 (by decide) (by decide)).2
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 30 93 3 (by decide) (by decide)).2
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 36 96 2 (by decide) (by decide)).2
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 41 98 2 (by decide) (by decide)).2
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan true 43 100 2 (by decide) (by decide)).2
  have hc := OddFullPass.HalfConvertOdd.canon760OddLoan_counts.2
  have hcn := StairBoundaryLoan.canon760Loan_counts.2
  have hcb : measurementCount R2SqEp760.canon760 = 254 := by
    rw [StairBoundaryLoan.canon760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).2.2.2
  have hde := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_counts.2
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf true
    (P1Life.half_counts (base 760) true base (base 2409)).1
    (P1Life.half_counts (base 760) true base (base 2409)).2).2
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf true)).2
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
    (Rolling1588.placedFirstPacket true)).2
  rw [show mc.measure=measurementCount from rfl] at h ⊢
  simp only [WindowFieldCosts.group,entryFieldHosted,entryLowPrefix,entryTailPrefix,
    OddFullPass.P1LifeLoan.entryLowSuffixOdd,OddFullPass.P1LifeLoan.entryTailSuffixOdd,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.entryLowPrefix,
    StairHostsSchedule.entryTailPrefix,StairHostsSchedule.entryLowSuffix,
    StairHostsSchedule.entryTailSuffix,StairConcrete.bestLoans_divEndpoint,
    StairConcrete.bestLoans,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,measurementCount_append] at *
  norm_num only at g13 g22 g30 g36 g41 g43
  simp only [if_false,if_true] at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_mc_mul (n : Nat)
    (h : mc.measure (WindowFieldCosts.group84 false)=mc.measure (WindowFieldCosts.group false 1 84)+n) :
    mc.measure (exitFieldHosted checkpointPrimitives)+1744 =
      mc.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 13 85 5 (by decide) (by decide)).2
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 22 90 3 (by decide) (by decide)).2
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 30 93 3 (by decide) (by decide)).2
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 36 96 2 (by decide) (by decide)).2
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 41 98 2 (by decide) (by decide)).2
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts hostPlan false 43 100 2 (by decide) (by decide)).2
  have hct := OddFullPass.HalfConvertOdd.center760OddLoan_counts.2
  have hctn := StairBoundaryLoan.center760Loan_counts.2
  have hctb : measurementCount R2SqEp760.center760 = 254 := by
    rw [StairBoundaryLoan.center760_eq]
    exact (HalfConvert.counts StairBoundaryLoan.converterLayout760 StairBoundaryLoan.converterLayout760_facts.widths).2.1
  have hme := OddFullPass.InverseTailCOdd.endPacket760OddLoan44_counts.2
  have hfp := (JointOdd1588.placedFirstPacketOdd_counts_delta oddFirstHalf false
    (P1Life.half_counts (base 760) false base (base 2409)).1
    (P1Life.half_counts (base 760) false base (base 2409)).2).2
  have hrNew := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf false)).2
  have hrOld := (StairLoan.rebindMany_counts StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (Rolling1588.placedFirstPacket false)).2
  have cr0 := PackCutOddExit.cutRow0_counts.2
  have cr1 := PackCutOddExit.cutRow1_counts.2
  have cr2 := PackCutOddExit.cutRow2_counts.2
  have cr3 := PackCutOddExit.cutRow3_counts.2
  have cr4 := PackCutOddExit.cutRow4_counts.2
  rw [show mc.measure=measurementCount from rfl] at h ⊢
  simp only [WindowFieldCosts.group,exitFieldHosted,exitLowSuffix,exitHeadSuffix,
    OddFullPass.P1LifeLoan.exitLowPrefixOdd,OddFullPass.P1LifeLoan.exitHeadPrefixOdd,
    StairHostsSchedule.exitFieldHosted,StairHostsSchedule.exitLowSuffix,
    StairHostsSchedule.exitHeadSuffix,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.exitHeadPrefix,StairHostsSchedule.hostedEndpoint,
    StairSchedule.placedEndPacket,StairConcrete.bestLoans,StairConcrete.endPacket,
    Bool.false_eq_true,if_false,if_true,StairSchedule.fieldRename,StairSchedule.parityRename,
    renameProgram_counts,measurementCount_append] at *
  norm_num only at g13 g22 g30 g36 g41 g43
  simp only [if_false,if_true] at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_slots (d : Bool) (n : Nat)
    (h : slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n) :
    (if d then slots.measure (entryFieldHosted checkpointPrimitives)
     else slots.measure (exitFieldHosted checkpointPrimitives)) ≤
    (if d then slots.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
     else slots.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan))+n+
      (if d then 7900 else 8160) := by
  have g13 := OddFullPass.P1LifeLoan.hostedGroup_slots_le hostPlan d 13 85 5 (by decide) (by decide) (by decide)
  have g22 := OddFullPass.P1LifeLoan.hostedGroup_slots_le hostPlan d 22 90 3 (by decide) (by decide) (by decide)
  have g30 := OddFullPass.P1LifeLoan.hostedGroup_slots_le hostPlan d 30 93 3 (by decide) (by decide) (by decide)
  have g36 := OddFullPass.P1LifeLoan.hostedGroup_slots_le hostPlan d 36 96 2 (by decide) (by decide) (by decide)
  have g41 := OddFullPass.P1LifeLoan.hostedGroup_slots_le hostPlan d 41 98 2 (by decide) (by decide) (by decide)
  have g43 := OddFullPass.P1LifeLoan.hostedGroup_slots_le hostPlan d 43 100 2 (by decide) (by decide) (by decide)
  have hc := OddFullPass.HalfConvertOdd.canon760OddLoan_slots_le
  have hct := OddFullPass.HalfConvertOdd.center760OddLoan_slots_le
  have hde := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_slots_le
  have hme := OddFullPass.InverseTailCOdd.endPacket760OddLoan44_slots_le
  have hfp := JointOdd1588.placedFirstPacketOdd_slots_le oddFirstHalf d (oddFirstHalf_slots_le d)
  have hrNew := rebindMany_slots_eq StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (JointOdd1588.placedFirstPacketOdd oddFirstHalf d)
  have hrOld := rebindMany_slots_eq StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (Rolling1588.placedFirstPacket d)
  have cs0 := PackCutOddExit.cutRow0_slots
  have cs1 := PackCutOddExit.cutRow1_slots
  have cs2 := PackCutOddExit.cutRow2_slots
  have cs3 := PackCutOddExit.cutRow3_slots
  have cs4 := PackCutOddExit.cutRow4_slots
  rw [show slots.measure=Challenge.gateSlots from rfl] at h ⊢
  cases d <;> simp only [Bool.false_eq_true,if_true,if_false,WindowFieldCosts.group,
    entryFieldHosted,exitFieldHosted,entryLowPrefix,exitLowSuffix,
    entryTailPrefix,exitHeadSuffix,OddFullPass.P1LifeLoan.entryLowSuffixOdd,
    OddFullPass.P1LifeLoan.exitLowPrefixOdd,OddFullPass.P1LifeLoan.entryTailSuffixOdd,
    OddFullPass.P1LifeLoan.exitHeadPrefixOdd,
    StairHostsSchedule.entryFieldHosted,StairHostsSchedule.exitFieldHosted,
    StairHostsSchedule.entryLowPrefix,StairHostsSchedule.exitLowSuffix,
    StairHostsSchedule.entryTailPrefix,StairHostsSchedule.exitHeadSuffix,
    StairHostsSchedule.entryLowSuffix,StairHostsSchedule.exitLowPrefix,
    StairHostsSchedule.entryTailSuffix,StairHostsSchedule.exitHeadPrefix,
    StairHostsSchedule.hostedEndpoint,StairSchedule.placedEndPacket,
    StairConcrete.bestLoans_divEndpoint,StairConcrete.bestLoans,StairConcrete.endPacket,
    StairSchedule.fieldRename,StairSchedule.parityRename,
    Baselines.rename_gateSlots,Challenge.gateSlots_append] at * <;> omega

open Stair44Outer

def divide : Program :=
  phasePlace (WindowWalkCosts.forward true 4) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace entryFieldHostedCut ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 85) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 84) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 4) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

def generic (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (EntryFuseOdd.entryYAllOdd layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (EntryFuseOdd.exitYAllOdd layout cy)

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

theorem tailPrefix_rows : entryTailPrefix checkpointPrimitives = WindowFieldCosts.group84 true ++
      ((StairSchedule.forwardSegment checkpointPrimitives 87 62 425 450 ++ OddFullPass.P1LifeLoan.hostedGroup hostPlan true 13 85 (4 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 62 47 450 465 ++ OddFullPass.P1LifeLoan.hostedGroup hostPlan true 22 90 (2 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 47 32 465 480 ++ OddFullPass.P1LifeLoan.hostedGroup hostPlan true 30 93 (2 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 32 22 480 490 ++ OddFullPass.P1LifeLoan.hostedGroup hostPlan true 36 96 (1 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 22 12 490 500 ++ OddFullPass.P1LifeLoan.hostedGroup hostPlan true 41 98 (1 + 1)) ++
        StairSchedule.forwardLast checkpointPrimitives))))) := by
  simp only [entryTailPrefix, List.append_assoc]

theorem tail_sublist : entryTailPrefixCut.Sublist (entryTailPrefix checkpointPrimitives) := by
  rw [tailPrefix_rows]
  unfold entryTailPrefixCut
  exact (List.Sublist.refl _).append ((PackCutOdd.row_subOdd 87 62 425 450 13 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp1).append
    ((PackCutOdd.row_subOdd 62 47 450 465 22 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp2).append
    ((PackCutOdd.row_subOdd 47 32 465 480 30 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp3).append
    ((PackCutOdd.row_subOdd 32 22 480 490 36 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp4).append
    ((PackCutOdd.row_subOdd 22 12 490 500 41 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp5).append
    (List.Sublist.refl _))))))

theorem low_sublist : entryLowPrefixCut.Sublist (entryLowPrefix checkpointPrimitives) := by
  unfold entryLowPrefixCut entryLowPrefix
  exact ((List.Sublist.refl _).append (PackCutSub.rename_sub _ tail_sublist)).append (List.Sublist.refl _)

theorem field_sublist : entryFieldHostedCut.Sublist (entryFieldHosted checkpointPrimitives) := by
  have f : (StairSchedule.fieldRename entryLowPrefixCut).Sublist
      (StairSchedule.fieldRename (entryLowPrefix checkpointPrimitives)) :=
    PackCutSub.rename_sub _ (PackCutSub.rename_sub _ low_sublist)
  unfold entryFieldHostedCut entryFieldHosted
  exact ((((f.append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append
    (List.Sublist.refl _)).append (List.Sublist.refl _)

/-- One cut odd row costs the placed `ep` and `dp` less, for every additive renaming-invariant cost. -/
theorem rowOdd_cost (c : Cost) (B N s f d first cc : Nat)
    (h1 : s + 1 ≤ 5 * first + 5) (h2 : 5 * first + 5 + 1 ≤ f)
    (h5 : 5 * first + 5 ≠ 5) (hdue : History5.packDue (5 * first + 5) = true) (hf0 : first ≠ 0)
    (hdp : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop d)
        (StairConcreteAssembly.hostPlan.group true d first (cc + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) =
      renameProgram (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
        Rolling1588.dp) :
    c.measure (StairSchedule.forwardSegment checkpointPrimitives B N s f ++
        OddFullPass.P1LifeLoan.hostedGroup StairConcreteAssembly.hostPlan true d first (cc + 1)) =
      c.measure (PackCutOdd.cutRowOdd B N s f d first cc) + (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  obtain ⟨X, M, Y, ho, hc⟩ := PackCutOdd.row_shapeOdd B N s f d first cc h1 h2 h5 hdue hf0 hdp
  rw [ho, hc]
  simp only [c.append, c.rename]
  omega

theorem rows_cost (c : Cost) :
    c.measure (entryTailPrefix checkpointPrimitives) =
      c.measure entryTailPrefixCut + 5 * (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  have r1 := rowOdd_cost c 87 62 425 450 13 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp1
  have r2 := rowOdd_cost c 62 47 450 465 22 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp2
  have r3 := rowOdd_cost c 47 32 465 480 30 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp3
  have r4 := rowOdd_cost c 32 22 480 490 36 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp4
  have r5 := rowOdd_cost c 22 12 490 500 41 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutRows.hdp5
  rw [tailPrefix_rows]
  simp only [entryTailPrefixCut, c.append] at r1 r2 r3 r4 r5 ⊢
  omega

theorem field_cut (c : Cost) :
    c.measure (entryFieldHosted checkpointPrimitives) =
      c.measure entryFieldHostedCut + 5 * (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  have hr := rows_cost c
  simp only [entryFieldHosted, entryFieldHostedCut, entryLowPrefix, entryLowPrefixCut,
    StairSchedule.fieldRename, StairSchedule.parityRename, c.rename, c.append]
  omega

theorem kernels (c : Cost) (gainF gainR tailSave fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 4)+gainF=c.measure (Stair44WalkRun.forward true 409))
    (dR : c.measure (WindowWalkCosts.backward false 85)+gainR=c.measure (Stair44WalkRun.backward false 490))
    (h : c.measure (entryFieldHosted checkpointPrimitives)+tailSave=
      c.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+fieldExtra) :
    c.measure divide+gainF+gainR+tailSave+5 * (c.measure Rolling1588.ep + c.measure Rolling1588.dp)=
      c.measure Stair44Outer.divide+fieldExtra := by
  have hc := field_cut c
  simp only [divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

theorem kernelsM (c : Cost) (k gainF gainR tailSave fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 84)+gainF=c.measure (Stair44WalkRun.forward false 489))
    (mR : c.measure (WindowWalkCosts.backward true 4)+gainR=c.measure (Stair44WalkRun.backward true 409))
    (h : c.measure (exitFieldHosted checkpointPrimitives)+tailSave=
      c.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+fieldExtra) :
    c.measure (multiply k)+gainF+gainR+tailSave=c.measure (Stair44Outer.multiply k)+fieldExtra := by
  simp only [multiply,Stair44Outer.multiply,phasePlace,kernelPlace,c.append,c.rename,Stair44PointMap.switchX]
  omega

theorem finite_delta (c : Cost) (C : Point) (cx cy : Fp) (gain : Nat)
    (hEn : c.measure (EntryFuseOdd.entryYAllOdd layout (-cy)) = c.measure (ParityUniform.entryYAll layout (-cy)))
    (hEx : c.measure (EntryFuseOdd.exitYAllOdd layout cy) = c.measure (ParityUniform.exitYAll layout cy))
    (h : c.measure divide+c.measure (multiply cx.val)+gain =
      c.measure Stair44Outer.divide+c.measure (Stair44Outer.multiply cx.val)) :
    c.measure (finite C cx cy)+gain=c.measure (Stair44Outer.finite C cx cy) := by
  simp only [finite,Stair44Outer.finite,borrowGeneric,Stair44Outer.borrowGeneric,
    generic,Stair44Outer.generic,Stair44PointMap.encodeY,c.append,c.rename,hEn,hEx]
  omega

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open ArchiveFieldScratch StairArchiveRelease StairArchiveNativeCut StairArchiveTen

def reserved : List Wire := List.range' 4836 39 ++ List.range' 4876 4
private theorem subset {q : Wire} (h : q∈reserved) : q∈StairPhysicalInventory.physicalHoles := by
  rw [StairPhysicalLayout.physicalHoles_eq_nat]
  simp only [reserved,StairPhysicalLayout.newHolesNat,List.mem_append,List.mem_range'_1] at *
  omega

theorem weaken {P : Program} {f : Wire → Wire} (h : PieceOK StairPhysicalInventory.physicalHoles f P) :
    PieceOK reserved f P := ⟨h.1,fun x hx bad => h.2 x hx (subset bad)⟩

theorem app {a b : Program} {f : Wire → Wire} {hs : List Wire} :
    PieceOK hs f (a++b) ↔ PieceOK hs f a ∧ PieceOK hs f b := by
  refine ⟨fun h => ⟨?_,?_⟩,fun h => h.1.append h.2⟩ <;>
    constructor <;> intro q hq
  · exact h.1 q (wires_append a b ▸ Finset.mem_union_left _ hq)
  · exact h.2 q (wires_append a b ▸ Finset.mem_union_left _ hq)
  · exact h.1 q (wires_append a b ▸ Finset.mem_union_right _ hq)
  · exact h.2 q (wires_append a b ▸ Finset.mem_union_right _ hq)

theorem ren {a : Program} {f g : Wire → Wire} {hs : List Wire} :
    PieceOK hs f (renameProgram g a) ↔ PieceOK hs (fun q => f (g q)) a := by
  refine ⟨fun h => ⟨?_,?_⟩,PieceOK.rename⟩ <;> intro x hx
  · exact h.1 (g x) (renameProgram_support g a ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩)
  · exact h.2 (g x) (renameProgram_support g a ▸ Finset.mem_image.mpr ⟨x,hx,rfl⟩)

private theorem singleton_ok {q : Wire} (h : Stair44OuterSites.fit q=true) :
    q∈StairHoleSupport.recordArena ∧ q∉StairHoleSupport.oldHoles ∧ q∉reserved := by
  let P : Program := [.X q]
  have inv : PieceOK StairPhysicalInventory.physicalHoles id P := Stair44OuterSites.fits
    (fun x hx => by
      have eq : x=q := by simpa [P,wires,Instr.wires] using hx
      exact eq ▸ h)
  have here : q∈wires P := by simp [P,wires,Instr.wires]
  exact ⟨(inv.1 q here).1,(inv.1 q here).2,(weaken inv).2 q here⟩

private theorem tagOK : 4835∈StairHoleSupport.recordArena ∧ 4835∉StairHoleSupport.oldHoles ∧
    4835∉reserved := by
  rw [StairPhysicalLayout.recordArena_eq,StairPhysicalLayout.oldHoles_eq]
  decide +kernel

private theorem addresses (j : Nat) (hj : j∈List.range' 1 83) (q : Wire) (hq : q∈layout j) :
    Stair44OuterSites.fit q=true ∨ q=4835 := by
  have p := List.all_eq_true.mp packets_exact j hj
  dsimp only [packetOK,Id.run,pure] at p
  simp only [Bool.and_eq_true] at p
  simp only [layout,transient_exact,List.mem_append,List.mem_cons] at hq
  rcases hq with a | a | a
  · have z := List.all_eq_true.mp p.2 q a
    simp only [Bool.and_eq_true] at z
    exact Or.inl z.1
  · exact Or.inr a
  · exact Or.inl (List.all_eq_true.mp permanent_exact.2 q a)

theorem hook (j : Nat) (hj : j∈List.range' 1 83) (op : Stage) :
    PieceOK reserved TP (fieldHook j op) := by
  rw [fieldHook,ren]
  have cover (x : Wire) (hx : x∈wires (program op)) :
      TP (fieldPort j x)∈StairHoleSupport.recordArena ∧
      TP (fieldPort j x)∉StairHoleSupport.oldHoles ∧ TP (fieldPort j x)∉reserved := by
    have lt := Finset.mem_range.mp (sub op hx)
    have sl := (layout_frame j hj).2
    have small : x < (layout j).length := sl ▸ lt
    have member : port j x ∈ layout j := by
      simp only [port,List.getElem?_eq_getElem small,Option.getD_some,List.getElem_mem]
    change StairOuterPlacement.outerPlace _ ∈ _ ∧ _ ∧ _
    simp only [show TP=StairOuterPlacement.outerPlace from rfl,StairPlaceFast.outerPlace_eqB,placed_port j hj x lt]
    rcases addresses j hj _ member with p|e
    · exact singleton_ok p
    · rw [e]; exact tagOK
  exact ⟨fun x hx => ⟨(cover x hx).1,(cover x hx).2.1⟩,fun x hx => (cover x hx).2.2⟩

theorem width {P : Program} (h : PieceOK reserved id P) : Challenge.qubits P ≤ 1543 := by
  have listOK := StairCertificate.holeList_of_physical_sub reserved (by decide +kernel) (fun _ hx => subset hx)
  exact StairCertificate.qubits_le_holes reserved listOK P (holePlacement_of_ok h)
end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

attribute [local irreducible] wires domain

theorem forward45plus1_domain (d : Bool) : Covered (TickCut.CutWindow.forwardCut d) := by
  intro q h
  rw [domain_eq]
  exact (TickCut.CutWindow.cut_covered d).1 q h
theorem reverse45plus1_domain (d : Bool) : Covered (TickCut.CutWindow.reverseCut d) := by
  intro q h
  rw [domain_eq]
  exact (TickCut.CutWindow.cut_covered d).2 q h

theorem forward45plus1_fits (d : Bool) : ∀ q ∈ wires (TickCut.CutWindow.forwardCut d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (forward45plus1_domain d q h)

theorem reverse45plus1_fits (d : Bool) : ∀ q ∈ wires (TickCut.CutWindow.reverseCut d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (reverse45plus1_domain d q h)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

private theorem fieldTcDiv :
    tc.measure (WindowFieldCosts.group84 true)=tc.measure (WindowFieldCosts.group true 1 84)+1390 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_div.1
private theorem fieldMcDiv :
    mc.measure (WindowFieldCosts.group84 true)=mc.measure (WindowFieldCosts.group true 1 84)+970 := by
  rw [show mc.measure=measurementCount from rfl]
  exact WindowFieldCosts.group_cost_div.2
private theorem fieldTcMul :
    tc.measure (WindowFieldCosts.group84 false)=tc.measure (WindowFieldCosts.group false 1 84)+1265 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_mul.1
private theorem fieldMcMul :
    mc.measure (WindowFieldCosts.group84 false)=mc.measure (WindowFieldCosts.group false 1 84)+845 := by
  rw [show mc.measure=measurementCount from rfl]
  exact WindowFieldCosts.group_cost_mul.2
private theorem pair_delta2 {a b x y g h i j t1 t2 f1 f2 r : Nat}
    (l : a+g+h+t1=x+f1) (rr : b+i+j+t2=y+f2) (v : g+h+t1+i+j+t2=r+f1+f2) : a+b+r=x+y := by omega
attribute [local irreducible] Stair44Outer.divide Stair44Outer.multiply divide multiply
  finite Stair44Outer.finite WindowWalkCosts.forward WindowWalkCosts.backward
  WindowFieldCosts.group84 WindowFieldCosts.group Stair44WalkRun.forward Stair44WalkRun.backward
  toffoliCount measurementCount

theorem tc_div : tc.measure divide+38898+38779+1018=tc.measure Stair44Outer.divide+1390 := by
  have k := kernels tc 38898 38779 953 1390 (WindowWalkCosts.inst true 4 409 38898 38804 rfl rfl rfl).1
    (WindowWalkCosts.inst false 85 490 38898 38779 rfl rfl rfl).2.1 (field_delta_tc_div 1390 fieldTcDiv)
  have e : tc.measure Rolling1588.ep + tc.measure Rolling1588.dp = 13 := by
    show toffoliCount Rolling1588.ep + toffoliCount Rolling1588.dp = 13
    rw [PackCutCounts.tc_ep, PackCutCounts.tc_dp]
  omega

theorem tc_mul (k : Nat) : tc.measure (multiply k)+38898+38804+1020=tc.measure (Stair44Outer.multiply k)+1265 :=
  kernelsM tc k 38898 38804 1020 1265 (WindowWalkCosts.inst false 84 489 38898 38779 rfl rfl rfl).1
    (WindowWalkCosts.inst true 4 409 38898 38804 rfl rfl rfl).2.1 (field_delta_tc_mul 1265 fieldTcMul)

theorem mc_div : mc.measure divide+17171+17195+1743=mc.measure Stair44Outer.divide+970 := by
  have k := kernels mc 17171 17195 1718 970 (WindowWalkCosts.instMeasurements true 4 409 17171 17220 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements false 85 490 17171 17195 rfl rfl rfl).2 (field_delta_mc_div 970 fieldMcDiv)
  have e : mc.measure Rolling1588.ep + mc.measure Rolling1588.dp = 5 := by
    show measurementCount Rolling1588.ep + measurementCount Rolling1588.dp = 5
    exact PackCutCounts.mc_epdp
  omega

theorem mc_mul (k : Nat) : mc.measure (multiply k)+17171+17220+1744=mc.measure (Stair44Outer.multiply k)+845 :=
  kernelsM mc k 17171 17220 1744 845 (WindowWalkCosts.instMeasurements false 84 489 17171 17195 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements true 4 409 17171 17220 rfl rfl rfl).2 (field_delta_mc_mul 845 fieldMcMul)

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+154762=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+70429=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 154762
      (OddOuterBridge.entryYAllOdd_tc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_tc_eq layout layout_widths cy)
      (pair_delta2 tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 70429
      (OddOuterBridge.entryYAllOdd_mc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_mc_eq layout layout_widths cy)
      (pair_delta2 mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2013078 ∧
    measurementCount (program C) ≤ 1449468 := by
  have h := Stair44Resources.totals C
  cases C with
  | zero => change toffoliCount [] ≤ _ ∧ measurementCount [] ≤ _; simp [toffoliCount,measurementCount]
  | @some cx cy hc =>
    have d := deltas (.some hc) cx cy
    simp only [program,Stair44Outer.program,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2] at h ⊢
    exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44Resources Stair44Outer
open StairConcreteAssembly WindowWalkCosts
set_option maxHeartbeats 1400000
set_option maxRecDepth 14000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount gateSlots measurementCount wires renameProgram
  Rolling1588TickGap.forward Rolling1588.reverse TickCut.CutWindow.forwardCut TickCut.CutWindow.reverseCut

theorem walk (c : Cost) (d : Bool) (tail f r n : Nat) (hn : 405+tail=n)
    (hf : c.measure (TickCut.CutWindow.forwardCut d) ≤ f) (hr : c.measure (TickCut.CutWindow.reverseCut d) ≤ r) :
    c.measure (WindowWalkCosts.forward d tail) ≤ c.measure (Stair44WalkRun.forward d n)+f ∧
    c.measure (WindowWalkCosts.backward d tail) ≤ c.measure (Stair44WalkRun.backward d n)+r := by
  subst n
  have a := StairRestSupport.forward_append d 29 16 (376+tail)
  have b := StairRestSupport.forward_append d 376 45 tail
  have x := StairRestSupport.reverse_append d 29 16 (376+tail)
  have y := StairRestSupport.reverse_append d 376 45 tail
  change Rolling1588TickGap.forward d 16 (29+(376+tail)) =
    Rolling1588TickGap.forward d 16 29 ++ Rolling1588TickGap.forward d 45 (376+tail) at a
  change Rolling1588.reverse d 16 (29+(376+tail)) =
    Rolling1588.reverse d 45 (376+tail) ++ Rolling1588.reverse d 16 29 at x
  rw [b] at a
  rw [y] at x
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,WindowWalkCosts.forward,WindowWalkCosts.backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

private theorem kernels (gainF gainR fieldExtra : Nat)
    (dF : slots.measure (WindowWalkCosts.forward true 4) ≤ slots.measure (Stair44WalkRun.forward true 409)+gainF)
    (dR : slots.measure (WindowWalkCosts.backward false 85) ≤ slots.measure (Stair44WalkRun.backward false 490)+gainR)
    (g : slots.measure (WindowFieldCosts.group84 true)=slots.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    slots.measure WindowCallerCosts.divide ≤ slots.measure Stair44Outer.divide+gainF+gainR+fieldExtra+7900 := by
  have h := WindowCallerCosts.field_delta_slots true _ g
  have hc := WindowCallerCosts.field_cut slots
  simp only [if_true] at h
  simp only [WindowCallerCosts.divide,Stair44Outer.divide,phasePlace,kernelPlace,
    Stair44Resources.slots.append,Stair44Resources.slots.rename]
  omega

private theorem kernelsM (k gainF gainR fieldExtra : Nat)
    (mF : slots.measure (WindowWalkCosts.forward false 84) ≤ slots.measure (Stair44WalkRun.forward false 489)+gainF)
    (mR : slots.measure (WindowWalkCosts.backward true 4) ≤ slots.measure (Stair44WalkRun.backward true 409)+gainR)
    (g : slots.measure (WindowFieldCosts.group84 false)=slots.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
    slots.measure (WindowCallerCosts.multiply k) ≤ slots.measure (Stair44Outer.multiply k)+gainF+gainR+fieldExtra+8160 := by
  have h := WindowCallerCosts.field_delta_slots false _ g
  simp only [Bool.false_eq_true,if_false] at h
  simp only [WindowCallerCosts.multiply,Stair44Outer.multiply,phasePlace,kernelPlace,
    Stair44Resources.slots.append,Stair44Resources.slots.rename,Stair44PointMap.switchX]
  omega

private theorem finite_upper (C : Point) (cx cy : Fp) (gain : Nat)
    (h : slots.measure WindowCallerCosts.divide+slots.measure (WindowCallerCosts.multiply cx.val)+7144 ≤
      slots.measure Stair44Outer.divide+slots.measure (Stair44Outer.multiply cx.val)+gain) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤ slots.measure (Stair44Outer.finite C cx cy)+gain := by
  have hy := OddOuterBridge.outerY_slots_delta cy
  rw [show slots.measure=Challenge.gateSlots from rfl] at h ⊢
  simp only [WindowCallerCosts.finite,Stair44Outer.finite,WindowCallerCosts.borrowGeneric,Stair44Outer.borrowGeneric,
    WindowCallerCosts.generic,Stair44Outer.generic,Challenge.gateSlots_append,Baselines.rename_gateSlots] at *
  omega


private theorem casts {P : Program} {n : Nat} (h : gateSlots P ≤ n) : slots.measure P ≤ n := h
private theorem groupCap (d : Bool) (n : Nat)
    (hn : 25*(if d then 5322 else 6122)+(if d then 0 else 0)=n+(if d then 14280 else 11760)) :
    slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  have h := WindowFieldCosts.group_slots d
  omega
theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+2419094+2403571+118770+7900 :=
  kernels 2419094 2403571 118770
    (walk slots true 4 2419094 2403571 409 rfl (casts TickCut.CutWindow.cut_slotsF.1) (casts TickCut.CutWindow.cut_slotsR.1)).1
    (walk slots false 85 2419094 2403571 490 rfl (casts TickCut.CutWindow.cut_slotsF.2) (casts TickCut.CutWindow.cut_slotsR.2)).2
    (groupCap true 118770 rfl)

theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+2419094+2403571+141290+8160 :=
  kernelsM k 2419094 2403571 141290
    (walk slots false 84 2419094 2403571 489 rfl (casts TickCut.CutWindow.cut_slotsF.2) (casts TickCut.CutWindow.cut_slotsR.2)).1
    (walk slots true 4 2419094 2403571 409 rfl (casts TickCut.CutWindow.cut_slotsF.1) (casts TickCut.CutWindow.cut_slotsR.1)).2
    (groupCap false 141290 rfl)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+2419094+2403571+118770+7900)
    (hm : b ≤ y+2419094+2403571+141290+8160) : a+b+7144 ≤ x+y+9928594 := by omega

theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+9928594 :=
  finite_upper C cx cy 9928594 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 66279181 := by
  have h := Stair44Resources.slotBound C
  cases C with
  | zero => change gateSlots [] ≤ _; simp [gateSlots]
  | @some cx cy hc =>
    have f := cap (.some hc) cx cy
    rw [show slots.measure=gateSlots from rfl] at f
    simp only [WindowCallerCosts.program,Stair44Outer.program,rename_gateSlots] at h ⊢
    omega
end ECDSAAdd.Entrant.StairPacket.WindowSlots

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open StairRestSupport StairPhysicalV3 ArchiveFieldScratch StairArchiveRelease StairArchiveGates Baselines
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet


theorem app {p q : Program} : Sound (p++q) ↔ Sound p ∧ Sound q :=
  ⟨fun h => ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩,
    fun h => sound_append h.1 h.2⟩

private theorem emitted (op : Stage) : GatePhysical (StairArchiveRelease.program op) := by
  cases op
  exacts [ReducedWindowArchives.enter0_counts.1,ReducedWindowArchives.switch0_counts.1,ReducedWindowArchives.leave0_counts.1,
    ReducedWindowArchives.enter1_counts.1,ReducedWindowArchives.switch1_counts.1,ReducedWindowArchives.leave1_counts.1]

theorem hook (j : Nat) (hj : j∈[10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82]) (op : Stage) :
    Sound (fieldHook j op) := by
  have span : j∈List.range' 1 83 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; apply List.mem_range'_1.mpr; omega
  have chk : (fieldSites j).all (fun q => decide (InDom q))=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  refine ⟨gatePhysical_rename_support _ _ (fun a ha b hb eq => field_inj j span a (sub op ha) b (sub op hb) eq) (emitted op),?_⟩
  intro q hq
  rw [fieldHook,renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  have len : (fieldSites j).length=121 := by
    have hh := (layout_frame j span).2
    rwa [←field_layout,List.length_map] at hh
  have lt : x < (fieldSites j).length := len ▸ (Finset.mem_range.mp (sub op hx))
  apply of_decide_eq_true (List.all_eq_true.mp chk _ ?_)
  simp only [fieldPort,List.getElem?_eq_getElem lt,Option.getD_some,List.getElem_mem]

private theorem distributed_ok (d : Bool) (j n : Nat) :
    Sound (distributed d j n) ↔
    ∀ (i : Nat), j ≤ i → i < j+n → Sound (packet d i) := by
  induction n generalizing j with
  | zero =>
    change Sound [] ↔ _
    exact ⟨fun _ i lo hi => False.elim (by omega),fun _ => ⟨by simp [GatePhysical],fun _ h => by simp [wires] at h⟩⟩
  | succ n ih =>
    change Sound (if d then packet d j ++ distributed d (j+1) n
      else distributed d (j+1) n ++ packet d j) ↔ _
    have both : (Sound (packet d j) ∧ Sound (distributed d (j+1) n)) ↔
        ∀ (i : Nat), j ≤ i → i < j+(n+1) → Sound (packet d i) := by
      rw [ih]
      refine ⟨fun h i l u => ?_,fun h => ⟨h j (by omega) (by omega),?_⟩⟩
      · by_cases e : j=i
        · exact e ▸ h.1
        · exact h.2 i (by omega) (by omega)
      · exact fun i l u => h i (by omega) (by omega)
    cases d <;> simp only [Bool.false_eq_true,if_false,if_true,app]
    · exact and_comm.trans both
    · exact both

private theorem whole (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → Sound (packet d i) := by
  apply (distributed_ok d 1 84).mp
  rw [←distribute]
  exact sound_hostedGroup StairOpenWiring.half760 hostSlots_v3 d 0 1 84 (by decide) (by decide) (by decide) (by decide)

/-- oddten: the field group's own packets are sound (record footprint, odd packets physical). -/
private theorem ot_opk_sound (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) : Sound (opk d k) := by
  by_cases big : 84<k
  · rw [WindowFieldCosts.ot_opk_std d k big]; exact whole d k lo (by omega)
  · refine ⟨?_,good_of_subset (WindowFieldCosts.ot_opk_sub d k) (whole d k lo (by omega)).good⟩
    simp only [opk,StairArchiveInactive.hosts_eq]
    exact gatePhysical_rename _ (Equiv.injective _) _
      (gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _ (WindowFieldCosts.oddPk_physical d k lo (by omega)))

private theorem ot_ogroup_sound (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) : Sound (ogroup d j n) := by
  unfold ogroup
  induction n generalizing j with
  | zero =>
    show Sound []
    exact ⟨by simp [GatePhysical],fun _ h => by simp [wires] at h⟩
  | succ n ih =>
    have head := ot_opk_sound d j lo (by omega)
    have tail := ih (j+1) (by omega) (by omega)
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true]
    · exact sound_append tail head
    · exact sound_append head tail

private theorem ot_pair (d : Bool) (j : Nat) (pick : j∈[10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82]) (lo : 1≤j) (hi : j≤83) :
    Sound (oten j (!d)) := by
  have here := ot_opk_sound d j lo (by omega)
  have next := ot_opk_sound d (j+1) (by omega) (by omega)
  have firstOK : Sound (ofirst j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (osecond j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))

theorem group84_ok (d : Bool) : Sound (group84 d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  have c40 := ord (ot_pair d 76 (by decide) (by decide) (by decide)) (ord (ot_ogroup_sound d 78 1 (by decide) (by decide)) (ord (ot_pair d 79 (by decide) (by decide) (by decide)) (ord (ot_ogroup_sound d 81 1 (by decide) (by decide)) (ord (ot_pair d 82 (by decide) (by decide) (by decide)) (ot_ogroup_sound d 84 1 (by decide) (by decide))))))
  have c39 := ord (ot_ogroup_sound d 75 1 (by decide) (by decide)) c40
  have c38 := ord (ot_pair d 73 (by decide) (by decide) (by decide)) c39
  have c37 := ord (ot_ogroup_sound d 72 1 (by decide) (by decide)) c38
  have c36 := ord (ot_pair d 70 (by decide) (by decide) (by decide)) c37
  have c35 := ord (ot_ogroup_sound d 69 1 (by decide) (by decide)) c36
  have c34 := ord (ot_pair d 67 (by decide) (by decide) (by decide)) c35
  have c33 := ord (ot_ogroup_sound d 66 1 (by decide) (by decide)) c34
  have c32 := ord (ot_pair d 64 (by decide) (by decide) (by decide)) c33
  have c31 := ord (ot_ogroup_sound d 63 1 (by decide) (by decide)) c32
  have c30 := ord (ot_pair d 61 (by decide) (by decide) (by decide)) c31
  have c29 := ord (ot_ogroup_sound d 60 1 (by decide) (by decide)) c30
  have c28 := ord (ot_pair d 58 (by decide) (by decide) (by decide)) c29
  have c27 := ord (ot_ogroup_sound d 57 1 (by decide) (by decide)) c28
  have c26 := ord (ot_pair d 55 (by decide) (by decide) (by decide)) c27
  have c25 := ord (ot_ogroup_sound d 54 1 (by decide) (by decide)) c26
  have c24 := ord (ot_pair d 52 (by decide) (by decide) (by decide)) c25
  have c23 := ord (ot_ogroup_sound d 51 1 (by decide) (by decide)) c24
  have c22 := ord (ot_pair d 49 (by decide) (by decide) (by decide)) c23
  have c21 := ord (ot_ogroup_sound d 48 1 (by decide) (by decide)) c22
  have c20 := ord (ot_pair d 46 (by decide) (by decide) (by decide)) c21
  have c19 := ord (ot_ogroup_sound d 45 1 (by decide) (by decide)) c20
  have c18 := ord (ot_pair d 43 (by decide) (by decide) (by decide)) c19
  have c17 := ord (ot_ogroup_sound d 42 1 (by decide) (by decide)) c18
  have c16 := ord (ot_pair d 40 (by decide) (by decide) (by decide)) c17
  have c15 := ord (ot_ogroup_sound d 39 1 (by decide) (by decide)) c16
  have c14 := ord (ot_pair d 37 (by decide) (by decide) (by decide)) c15
  have c13 := ord (ot_ogroup_sound d 36 1 (by decide) (by decide)) c14
  have c12 := ord (ot_pair d 34 (by decide) (by decide) (by decide)) c13
  have c11 := ord (ot_ogroup_sound d 33 1 (by decide) (by decide)) c12
  have c10 := ord (ot_pair d 31 (by decide) (by decide) (by decide)) c11
  have c9 := ord (ot_ogroup_sound d 30 1 (by decide) (by decide)) c10
  have c8 := ord (ot_pair d 28 (by decide) (by decide) (by decide)) c9
  have c7 := ord (ot_ogroup_sound d 27 1 (by decide) (by decide)) c8
  have c6 := ord (ot_pair d 25 (by decide) (by decide) (by decide)) c7
  have c5 := ord (ot_ogroup_sound d 24 1 (by decide) (by decide)) c6
  have c4 := ord (ot_pair d 22 (by decide) (by decide) (by decide)) c5
  have c3 := ord (ot_ogroup_sound d 21 1 (by decide) (by decide)) c4
  have c2 := ord (ot_pair d 19 (by decide) (by decide) (by decide)) c3
  have cq16a := ord (ot_ogroup_sound d 18 1 (by decide) (by decide)) c2
  have cq16b := ord (ot_pair d 16 (by decide) (by decide) (by decide)) cq16a
  have cq13a := ord (ot_ogroup_sound d 15 1 (by decide) (by decide)) cq16b
  have cq13b := ord (ot_pair d 13 (by decide) (by decide) (by decide)) cq13a
  have cq10a := ord (ot_ogroup_sound d 12 1 (by decide) (by decide)) cq13b
  have cq10b := ord (ot_pair d 10 (by decide) (by decide) (by decide)) cq10a
  exact ord (ot_ogroup_sound d 1 9 (by decide) (by decide)) cq10b

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet

private theorem distributed_ok (d : Bool) (j n : Nat) :
    PieceOK reserved TP (distributed d j n) ↔
    ∀ (i : Nat), j ≤ i → i < j+n → PieceOK reserved TP (packet d i) := by
  induction n generalizing j with
  | zero =>
    change PieceOK _ _ [] ↔ _
    exact ⟨fun _ i lo hi => False.elim (by omega),fun _ => pieceOK_nil _ _⟩
  | succ n ih =>
    change PieceOK _ _ (if d then packet d j ++ distributed d (j+1) n
      else distributed d (j+1) n ++ packet d j) ↔ _
    have both : (PieceOK reserved TP (packet d j) ∧ PieceOK reserved TP (distributed d (j+1) n)) ↔
        ∀ (i : Nat), j ≤ i → i < j+(n+1) → PieceOK reserved TP (packet d i) := by
      rw [ih]
      refine ⟨fun h i l u => ?_,fun h => ⟨h j (by omega) (by omega),?_⟩⟩
      · by_cases e : j=i
        · exact e ▸ h.1
        · exact h.2 i (by omega) (by omega)
      · exact fun i l u => h i (by omega) (by omega)
    cases d <;> simp only [Bool.false_eq_true,if_false,if_true,app]
    · exact and_comm.trans both
    · exact both

private theorem whole (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → PieceOK reserved TP (packet d i) := by
  apply (distributed_ok d 1 84).mp
  rw [←distribute]
  exact Stair44Groups.hostedGroup44 d 0 1 84 (by decide)

theorem ordinary (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK reserved TP (group d j n) := by
  rw [group,distribute,distributed_ok]
  exact fun i l u => whole d i (by omega) (by omega)

theorem pair (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) :
    PieceOK reserved TP (ten j (!d)) := by
  have jmem : j∈List.range' 1 83 := List.mem_range'_1.mpr ⟨lo,by omega⟩
  have here := whole d j lo (by omega)
  have next := whole d (j+1) (by omega) (by omega)
  have firstOK : PieceOK reserved TP (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : PieceOK reserved TP (second j (!d)) := by cases d <;> first | exact here | exact next
  exact (hook j jmem _).append (firstOK.append ((hook j jmem _).append (lastOK.append (hook j jmem _))))


-- oddten:begin SITES
/-- oddten: the field group's own packets avoid the reserved holes (their wires are record wires). -/
private theorem ot_ogroup_piece (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK reserved TP (ogroup d j n) := by
  have hrec := ordinary d j n lo hi
  exact ⟨fun x hx => hrec.1 x (WindowFieldCosts.ot_ogroup_sub d j n hx),
    fun x hx => hrec.2 x (WindowFieldCosts.ot_ogroup_sub d j n hx)⟩

private theorem ot_oten_piece (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) : PieceOK reserved TP (oten j (!d)) := by
  have hrec := pair d j lo hi
  exact ⟨fun x hx => hrec.1 x (WindowFieldCosts.ot_oten_sub j (!d) hx),
    fun x hx => hrec.2 x (WindowFieldCosts.ot_oten_sub j (!d) hx)⟩

theorem group84_ok (d : Bool) : PieceOK reserved TP (group84 d) := by
  have ord {a b : Program} (ha : PieceOK reserved TP a) (hb : PieceOK reserved TP b) :
      PieceOK reserved TP (ordered d a b) := by cases d <;> first | exact ha.append hb | exact hb.append ha
  have c40 := ord (ot_oten_piece d 76 (by decide) (by decide)) (ord (ot_ogroup_piece d 78 1 (by decide) (by decide)) (ord (ot_oten_piece d 79 (by decide) (by decide)) (ord (ot_ogroup_piece d 81 1 (by decide) (by decide)) (ord (ot_oten_piece d 82 (by decide) (by decide)) (ot_ogroup_piece d 84 1 (by decide) (by decide))))))
  have c39 := ord (ot_ogroup_piece d 75 1 (by decide) (by decide)) c40
  have c38 := ord (ot_oten_piece d 73 (by decide) (by decide)) c39
  have c37 := ord (ot_ogroup_piece d 72 1 (by decide) (by decide)) c38
  have c36 := ord (ot_oten_piece d 70 (by decide) (by decide)) c37
  have c35 := ord (ot_ogroup_piece d 69 1 (by decide) (by decide)) c36
  have c34 := ord (ot_oten_piece d 67 (by decide) (by decide)) c35
  have c33 := ord (ot_ogroup_piece d 66 1 (by decide) (by decide)) c34
  have c32 := ord (ot_oten_piece d 64 (by decide) (by decide)) c33
  have c31 := ord (ot_ogroup_piece d 63 1 (by decide) (by decide)) c32
  have c30 := ord (ot_oten_piece d 61 (by decide) (by decide)) c31
  have c29 := ord (ot_ogroup_piece d 60 1 (by decide) (by decide)) c30
  have c28 := ord (ot_oten_piece d 58 (by decide) (by decide)) c29
  have c27 := ord (ot_ogroup_piece d 57 1 (by decide) (by decide)) c28
  have c26 := ord (ot_oten_piece d 55 (by decide) (by decide)) c27
  have c25 := ord (ot_ogroup_piece d 54 1 (by decide) (by decide)) c26
  have c24 := ord (ot_oten_piece d 52 (by decide) (by decide)) c25
  have c23 := ord (ot_ogroup_piece d 51 1 (by decide) (by decide)) c24
  have c22 := ord (ot_oten_piece d 49 (by decide) (by decide)) c23
  have c21 := ord (ot_ogroup_piece d 48 1 (by decide) (by decide)) c22
  have c20 := ord (ot_oten_piece d 46 (by decide) (by decide)) c21
  have c19 := ord (ot_ogroup_piece d 45 1 (by decide) (by decide)) c20
  have c18 := ord (ot_oten_piece d 43 (by decide) (by decide)) c19
  have c17 := ord (ot_ogroup_piece d 42 1 (by decide) (by decide)) c18
  have c16 := ord (ot_oten_piece d 40 (by decide) (by decide)) c17
  have c15 := ord (ot_ogroup_piece d 39 1 (by decide) (by decide)) c16
  have c14 := ord (ot_oten_piece d 37 (by decide) (by decide)) c15
  have c13 := ord (ot_ogroup_piece d 36 1 (by decide) (by decide)) c14
  have c12 := ord (ot_oten_piece d 34 (by decide) (by decide)) c13
  have c11 := ord (ot_ogroup_piece d 33 1 (by decide) (by decide)) c12
  have c10 := ord (ot_oten_piece d 31 (by decide) (by decide)) c11
  have c9 := ord (ot_ogroup_piece d 30 1 (by decide) (by decide)) c10
  have c8 := ord (ot_oten_piece d 28 (by decide) (by decide)) c9
  have c7 := ord (ot_ogroup_piece d 27 1 (by decide) (by decide)) c8
  have c6 := ord (ot_oten_piece d 25 (by decide) (by decide)) c7
  have c5 := ord (ot_ogroup_piece d 24 1 (by decide) (by decide)) c6
  have c4 := ord (ot_oten_piece d 22 (by decide) (by decide)) c5
  have c3 := ord (ot_ogroup_piece d 21 1 (by decide) (by decide)) c4
  have c2 := ord (ot_oten_piece d 19 (by decide) (by decide)) c3
  have cq16a := ord (ot_ogroup_piece d 18 1 (by decide) (by decide)) c2
  have cq16b := ord (ot_oten_piece d 16 (by decide) (by decide)) cq16a
  have cq13a := ord (ot_ogroup_piece d 15 1 (by decide) (by decide)) cq16b
  have cq13b := ord (ot_oten_piece d 13 (by decide) (by decide)) cq13a
  have cq10a := ord (ot_ogroup_piece d 12 1 (by decide) (by decide)) cq13b
  have cq10b := ord (ot_oten_piece d 10 (by decide) (by decide)) cq10a
  exact ord (ot_ogroup_piece d 1 9 (by decide) (by decide)) cq10b

end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open Arithmetic MappedCompressed Baselines StairPhysicalV3 StairRestSupport StairConcreteAssembly
variable {p : StairSchedule.StairPrimitives}
set_option maxRecDepth 14000
set_option maxHeartbeats 1200000
theorem sound_entryTailPrefix (H : LoanHyp) (P : PrimitiveSlots p) (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryTailPrefix p) := by
  have g0 := group84_ok true
  have oddSound (d f c : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) (hfc : f + c ≤ 102)
      (ho : Sound (StairHostsSchedule.hostedGroup hostPlan true d f c)) :
      Sound (OddFullPass.P1LifeLoan.hostedGroup hostPlan true d f c) :=
    ⟨OddFullPass.P1LifeLoan.hostedGroup_physical hostPlan true d f c hfc,
     good_of_subset (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan true d f c hd h42) ho.good⟩
  have g14 := oddSound 13 85 5 (by decide) (by decide) (by decide) (sound_hostedGroup H hs true 13 85 5 (by decide) (by omega) (by omega) (by omega))
  have g23 := oddSound 22 90 3 (by decide) (by decide) (by decide) (sound_hostedGroup H hs true 22 90 3 (by decide) (by omega) (by omega) (by omega))
  have g31 := oddSound 30 93 3 (by decide) (by decide) (by decide) (sound_hostedGroup H hs true 30 93 3 (by decide) (by omega) (by omega) (by omega))
  have g37 := oddSound 36 96 2 (by decide) (by decide) (by decide) (sound_hostedGroup H hs true 36 96 2 (by decide) (by omega) (by omega) (by omega))
  have g42 := oddSound 41 98 2 (by decide) (by decide) (by decide) (sound_hostedGroup H hs true 41 98 2 (by decide) (by omega) (by omega) (by omega))
  have s1 := sound_forwardSegment P 87 62 425 450 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s2 := sound_forwardSegment P 62 47 450 465 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s3 := sound_forwardSegment P 47 32 465 480 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s4 := sound_forwardSegment P 32 22 480 490 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s5 := sound_forwardSegment P 22 12 490 500 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have sl := sound_forwardLast P
  unfold WindowCallerCosts.entryTailPrefix
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append g0 s1) g14) s2) g23) s3) g31) s4) g37) s5) g42) sl

theorem sound_exitHeadSuffix (H : LoanHyp) (P : PrimitiveSlots p) (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitHeadSuffix p) := by
  have g0 := group84_ok false
  have oddSound (d f c : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) (hfc : f + c ≤ 102)
      (ho : Sound (StairHostsSchedule.hostedGroup hostPlan false d f c)) :
      Sound (OddFullPass.P1LifeLoan.hostedGroup hostPlan false d f c) :=
    ⟨OddFullPass.P1LifeLoan.hostedGroup_physical hostPlan false d f c hfc,
     good_of_subset (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan false d f c hd h42) ho.good⟩
  let Pc := StairPhysicalV3.primitiveSlots_v3 StairPhysicalV3.primitiveChecks
  have cut0 := PackCutOddExit.cutRow0_sound
    (oddSound 13 85 5 (by decide) (by decide) (by decide) (sound_hostedGroup H hs false 13 85 5 (by decide) (by omega) (by omega) (by omega)))
    (sound_reverseSegment Pc 87 62 425 450 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut1 := PackCutOddExit.cutRow1_sound
    (oddSound 22 90 3 (by decide) (by decide) (by decide) (sound_hostedGroup H hs false 22 90 3 (by decide) (by omega) (by omega) (by omega)))
    (sound_reverseSegment Pc 62 47 450 465 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut2 := PackCutOddExit.cutRow2_sound
    (oddSound 30 93 3 (by decide) (by decide) (by decide) (sound_hostedGroup H hs false 30 93 3 (by decide) (by omega) (by omega) (by omega)))
    (sound_reverseSegment Pc 47 32 465 480 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut3 := PackCutOddExit.cutRow3_sound
    (oddSound 36 96 2 (by decide) (by decide) (by decide) (sound_hostedGroup H hs false 36 96 2 (by decide) (by omega) (by omega) (by omega)))
    (sound_reverseSegment Pc 32 22 480 490 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut4 := PackCutOddExit.cutRow4_sound
    (oddSound 41 98 2 (by decide) (by decide) (by decide) (sound_hostedGroup H hs false 41 98 2 (by decide) (by omega) (by omega) (by omega)))
    (sound_reverseSegment Pc 22 12 490 500 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have rl := sound_reverseLast P
  unfold WindowCallerCosts.exitHeadSuffix
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append rl cut4) cut3) cut2) cut1) cut0) g0

private theorem sound_firstPacketOdd (divide : Bool) :
    Sound (JointOdd1588.placedFirstPacketOdd WindowCallerCosts.oddFirstHalf divide) := by
  refine ⟨JointOdd1588.placedFirstPacketOdd_physical WindowCallerCosts.oddFirstHalf divide
      (WindowCallerCosts.oddFirstHalf_physical divide), ?_⟩
  intro q hq
  have hsup := StairWireCheck.allSites_sound StairWireCheck.fpSup _
    (JointOdd1588.placedFirstPacketOdd_passSup WindowCallerCosts.oddFirstHalf divide
      (WindowCallerCosts.oddFirstHalf_support divide)) q hq
  rcases WindowCallerCosts.fpSup_bounds q hsup with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (by rw [h2]; decide)

theorem sound_entryFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryFieldHosted p) := by
  have first := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket true)
    (sound_firstPacketOdd true)
  have pre : Sound (WindowCallerCosts.entryLowPrefix p) := by
    unfold WindowCallerCosts.entryLowPrefix
    exact sound_append (sound_append (sound_append first sound_clearProgram)
      (sound_borrow (sound_entryTailPrefix H P hs))) sound_unprefix
  have tailStd : Sound (StairHostsSchedule.entryTailSuffix hostPlan) := by
    have g := sound_hostedGroup H hs true 43 100 2 (by decide) (by omega) (by omega) (by omega)
    unfold StairHostsSchedule.entryTailSuffix
    exact sound_append (sound_append (sound_append g
      (sound_sig 511 (by omega) B.divEndpoint)) sound_copyN) B.canon
  have tail : Sound (OddFullPass.P1LifeLoan.entryTailSuffixOdd hostPlan) := by
    refine ⟨?_, good_of_subset (OddFullPass.P1LifeLoan.entryTailSuffixOdd_wires_sub hostPlan) tailStd.good⟩
    unfold OddFullPass.P1LifeLoan.entryTailSuffixOdd
    simp only [gatePhysical_append]
    exact ⟨⟨⟨OddFullPass.P1LifeLoan.hostedGroup_physical hostPlan true 43 100 2 (by decide),
      gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
        OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_physical⟩,
      sound_copyN.physical⟩, OddFullPass.HalfConvertOdd.canon760OddLoan_physical⟩
  have suf : Sound (OddFullPass.P1LifeLoan.entryLowSuffixOdd hostPlan) := by
    unfold OddFullPass.P1LifeLoan.entryLowSuffixOdd
    exact sound_append (sound_append sound_clearProgram (sound_borrow tail)) sound_unprefix
  unfold WindowCallerCosts.entryFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_fieldRename pre) sound_paritySetup) sound_hostedX)
    (sound_fieldRename suf)) sound_hostedX) sound_paritySetup

theorem sound_exitFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitFieldHosted p) := by
  have headStd : Sound (StairHostsSchedule.exitHeadPrefix hostPlan) := by
    have g := sound_hostedGroup H hs false 43 100 2 (by decide) (by omega) (by omega) (by omega)
    unfold StairHostsSchedule.exitHeadPrefix StairHostsSchedule.hostedEndpoint
      StairSchedule.placedEndPacket
    exact sound_append (sound_append (sound_append B.center sound_copyN)
      (sound_sig 511 (by omega) B.multEndpoint)) g
  have head : Sound (OddFullPass.P1LifeLoan.exitHeadPrefixOdd hostPlan) := by
    refine ⟨?_, good_of_subset (OddFullPass.P1LifeLoan.exitHeadPrefixOdd_wires_sub hostPlan) headStd.good⟩
    unfold OddFullPass.P1LifeLoan.exitHeadPrefixOdd
    simp only [gatePhysical_append]
    exact ⟨⟨⟨OddFullPass.HalfConvertOdd.center760OddLoan_physical, sound_copyN.physical⟩,
      gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
        OddFullPass.InverseTailCOdd.endPacket760OddLoan44_physical⟩,
      OddFullPass.P1LifeLoan.hostedGroup_physical hostPlan false 43 100 2 (by decide)⟩
  have pre : Sound (OddFullPass.P1LifeLoan.exitLowPrefixOdd hostPlan) := by
    unfold OddFullPass.P1LifeLoan.exitLowPrefixOdd
    exact sound_append (sound_append sound_clearProgram (sound_borrow head)) sound_unprefix
  have last := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket false)
    (sound_firstPacketOdd false)
  have suf : Sound (WindowCallerCosts.exitLowSuffix p) := by
    unfold WindowCallerCosts.exitLowSuffix
    exact sound_append (sound_append (sound_append sound_clearProgram
      (sound_borrow (sound_exitHeadSuffix H P hs))) sound_unprefix) last
  unfold WindowCallerCosts.exitFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    sound_paritySetup sound_hostedX) (sound_fieldRename pre)) sound_paritySetup)
    sound_hostedX) (sound_fieldRename suf)

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairRestSupport
set_option maxRecDepth 14000
set_option maxHeartbeats 1000000
attribute [local irreducible] wires renameProgram TickCut.CutWindow.forwardCut TickCut.CutWindow.reverseCut
  Rolling1588TickGap.forward Rolling1588.reverse Stair44WalkMap.rest Stair44WalkMap.first

abbrev GoodWindow (p : Program) :=
  ∀ q∈wires p, Stair44PhaseSites.valid (Stair44WalkMap.rest q)=true

theorem native {p : Program} (h : GoodWindow p) :
    PieceOK reserved (fun x => PP (Stair44WalkMap.rest x)) p := by
  apply weaken
  apply Stair44OuterSites.fits
  intro x hx
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace (Stair44WalkMap.rest x))=true
  rw [StairPlaceFast.phasePlace_eqB]
  exact h x hx

theorem walkF (d : Bool) (tail : Nat) (bound : 16+(405+tail)≤506)
    (new : GoodWindow (TickCut.CutWindow.forwardCut d)) :
    PieceOK reserved PP (WindowWalkCosts.forward d tail) := by
  have old := weaken (Stair44PhaseSites.forward d (405+tail) bound)
  have a := StairRestSupport.forward_append d 29 16 (376+tail)
  have b := StairRestSupport.forward_append d 376 45 tail
  change Rolling1588TickGap.forward d 16 (29+(376+tail)) =
    Rolling1588TickGap.forward d 16 29 ++ Rolling1588TickGap.forward d 45 (376+tail) at a
  rw [b] at a
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.forward,num,a,app,ren] at old
  simp only [WindowWalkCosts.forward,app,ren]
  exact ⟨old.1,⟨old.2.1,native new⟩,old.2.2.2⟩

theorem walkR (d : Bool) (tail : Nat) (bound : 16+(405+tail)≤506)
    (new : GoodWindow (TickCut.CutWindow.reverseCut d)) :
    PieceOK reserved PP (WindowWalkCosts.backward d tail) := by
  have old := weaken (Stair44PhaseSites.backward d (405+tail) bound)
  have a := StairRestSupport.reverse_append d 29 16 (376+tail)
  have b := StairRestSupport.reverse_append d 376 45 tail
  change Rolling1588.reverse d 16 (29+(376+tail)) =
    Rolling1588.reverse d 45 (376+tail) ++ Rolling1588.reverse d 16 29 at a
  rw [b] at a
  have num : 405+tail=29+(376+tail) := by omega
  simp only [Stair44WalkRun.backward,num,a,app,ren] at old
  simp only [WindowWalkCosts.backward,app,ren]
  exact ⟨⟨⟨old.1.1.1,native new⟩,old.1.2⟩,old.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open Arithmetic MappedCompressed Secp256k1 Baselines StairPhysicalV3 StairRestSupport
open Stair44Outer StairConcreteAssembly Stair44WalkMap
set_option maxHeartbeats 1400000
set_option maxRecDepth 20000
attribute [local irreducible] wires GatePhysical
theorem parts {P Q : Program} (h : Sound (P ++ Q)) : Sound P ∧ Sound Q :=
  ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩

private theorem firstDom (q : Wire) (h : InDom q) : InDom (first q) := by
  unfold first shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))

private theorem restDom (q : Wire) (h : InDom q) : InDom (rest q) := by
  unfold rest shared
  simp only [Equiv.trans_apply]
  exact indom_swap _ _ (by decide) (by decide) _
    (indom_swap _ _ (by decide) (by decide) _ (indom_swap _ _ (by decide) (by decide) _ h))


theorem dom {p : Program} (cover : PartialSites.Covered p) : Good p := by
  intro q hq
  have h := cover q hq
  simp only [PartialSites.domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  unfold InDom InDomN
  left
  constructor
  all_goals omega

private theorem fw (d : Bool) (tail n : Nat) (hn : 15+(405+tail)=n)
    (ref_ : Sound (Rolling1588TickGap.forward d 1 n))
    (p : GatePhysical (TickCut.CutWindow.forwardCut d)) : Sound (WindowWalkCosts.forward d tail) := by
  subst n
  rw [forward_append d 15 1 (405+tail)] at ref_
  obtain ⟨early,late⟩ := parts ref_
  change Sound (Rolling1588TickGap.forward d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,forward_append d 29 16 (376+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 45 (376+tail)) at ms
  rw [forward_append d 376 45 tail] at ms
  have patch : Sound (TickCut.CutWindow.forwardCut d) := ⟨p,dom (PartialSites.forward45plus1_domain d)⟩
  have last : Sound (Rolling1588TickGap.forward d 421 tail) := (parts ms).2
  exact sound_append (sound_rename _ first.injective firstDom early)
    (sound_rename _ rest.injective restDom (sound_append (sound_append pre patch) last))

private theorem bw (d : Bool) (tail n : Nat) (hn : 15+(405+tail)=n)
    (ref_ : Sound (Rolling1588.reverse d 1 n))
    (p : GatePhysical (TickCut.CutWindow.reverseCut d)) : Sound (WindowWalkCosts.backward d tail) := by
  subst n
  rw [reverse_append d 15 1 (405+tail)] at ref_
  obtain ⟨late,early⟩ := parts ref_
  change Sound (Rolling1588.reverse d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,reverse_append d 29 16 (376+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 45 (376+tail)) at ms
  rw [reverse_append d 376 45 tail] at ms
  have patch : Sound (TickCut.CutWindow.reverseCut d) := ⟨p,dom (PartialSites.reverse45plus1_domain d)⟩
  have last : Sound (Rolling1588.reverse d 421 tail) := (parts ms).1
  exact sound_append (sound_rename _ rest.injective restDom (sound_append (sound_append last patch) pre))
    (sound_rename _ first.injective firstDom early)
theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

variable (ff : ∀d,GatePhysical (TickCut.CutWindow.forwardCut d)) (rr : ∀d,GatePhysical (TickCut.CutWindow.reverseCut d))

include ff rr in
theorem dividePhysical : GatePhysical WindowCallerCosts.divide := by
  have eq : InverseFive23.lastPhase15 false = reverseEnd ++
      Rolling1588.reverse false 1 505 ++ FrontierEntry1591NativeH.inverse base := by
    simp only [InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
      reverseEnd,List.append_assoc]
  have h := sound_lastPhase15
  rw [eq] at h
  have ⟨a,native⟩ := parts h
  have ⟨tail,walk⟩ := parts a
  let P := primitiveSlots_v3 primitiveChecks
  have field := PackCutSub.sound_sub WindowCallerCosts.field_sublist
    (sound_entryFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3)
  simp only [WindowCallerCosts.divide,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw true 4 424 rfl sound_forward424 (ff _)),phase P.firstPack⟩,rest_physical _ field⟩,
    phase tail⟩,phase (bw false 85 505 rfl walk (rr _))⟩,phase (sound_rename _ first.injective firstDom native)⟩

include ff rr in
theorem multiplyPhysical (k : Nat) : GatePhysical (WindowCallerCosts.multiply k) := by
  have eq : Rolling1588TickGap.tailPhase false = Rolling1588TickGap.forward false 1 504 ++ forwardEnd := by
    simp only [Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,
      forwardEnd,List.append_assoc]
  have h := sound_tailPhase
  rw [eq] at h
  have ⟨walk,tail⟩ := parts h
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_exitFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [WindowCallerCosts.multiply,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw false 84 504 rfl walk (ff _)),phase tail⟩,rest_physical _ field⟩,phase P.firstUnpack⟩,
    phase (bw true 4 424 rfl sound_reverse424 (rr _))⟩,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ (phase (sound_x1N k))⟩

include ff rr in
theorem genericPhysical (cx cy : Fp) : GatePhysical (WindowCallerCosts.generic cx cy) := by
  have g := FlagTop2.genericN_physical cx cy
  simp only [FlagExit.genericN,FlagExit.secondStageN,gatePhysical_append] at g
  simp only [WindowCallerCosts.generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨gatePhysical_rename _ Stair44PointMap.duringY.injective _
      (EntryFuseOdd.entryYAllOdd_physical layout layout_widths layout_nodup (-cy)),
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ g.1.1.2⟩,dividePhysical ff rr⟩,
    Stair44Square.physical _⟩,multiplyPhysical ff rr _⟩,
    gatePhysical_rename _ Stair44PointMap.duringY.injective _
      (EntryFuseOdd.exitYAllOdd_physical layout layout_widths layout_nodup cy)⟩

include ff rr in
theorem physical (C : Point) : GatePhysical (WindowCallerCosts.program C) := by
  cases C with
  | zero => simp [WindowCallerCosts.program,GatePhysical]
  | @some cx cy hc =>
    let C : Point := .some hc
    have m := AboveFieldPointDevelop.middle_physical C cx cy
    simp only [AboveFieldPointDevelop.middle,gatePhysical_append] at m
    apply gatePhysical_rename _ (Wrapper5.U layout).injective
    simp only [WindowCallerCosts.finite,gatePhysical_append]
    refine ⟨⟨gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_,?_⟩,
      gatePhysical_rename _ Stair44PointMap.outer.injective _ ?_⟩
    · simp only [gatePhysical_append]
      exact ⟨⟨FlagTop.stageNew_physical hc,m.1.1.1.1⟩,m.1.1.1.2⟩
    · exact gatePhysical_rename _ (Equiv.swap _ _).injective _
        (gatePhysical_rename _ FlagTop.rho_injective _ (genericPhysical ff rr cx cy))
    · simp only [gatePhysical_append]
      exact ⟨⟨m.1.2,m.2⟩,ControlPointEncodingDevelop.borrowOut_physical hc⟩
end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed Secp256k1 Baselines StairSiteAvoidance StairSiteEasy
open StairConcreteAssembly Stair44Outer
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires renameProgram

/-- Replacing a child leaves the safety contract on the other children intact. -/
private def SafeChange (f : Wire → Wire) (old new : Program) :=
  PieceOK reserved f old → PieceOK reserved f new
theorem same (f : Wire → Wire) (p : Program) : SafeChange f p p := id
theorem fresh {f : Wire → Wire} {p q : Program} (h : PieceOK reserved f q) :
    SafeChange f p q := fun _ => h
private theorem appendChange {f : Wire → Wire} {a b x y : Program}
    (l : SafeChange f a x) (r : SafeChange f b y) : SafeChange f (a++b) (x++y) :=
  fun old => (l (app.mp old).1).append (r (app.mp old).2)
private theorem renameChange {f g : Wire → Wire} {a b : Program}
    (h : SafeChange (fun x => f (g x)) a b) : SafeChange f (renameProgram g a) (renameProgram g b) :=
  fun old => ren.mpr (h (ren.mp old))

theorem tail (p : StairSchedule.StairPrimitives) :
    SafeChange TP (StairHostsSchedule.entryTailPrefix p hostPlan)
      (WindowCallerCosts.entryTailPrefix p) := by
  have subCh (d f c : Nat) (hd : d ≤ 43) (h42 : d ≠ 42) :
      SafeChange TP (StairHostsSchedule.hostedGroup hostPlan true d f c)
        (OddFullPass.P1LifeLoan.hostedGroup hostPlan true d f c) :=
    fun h => ⟨fun q hq => h.1 q (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan true d f c hd h42 hq),
              fun q hq => h.2 q (OddFullPass.P1LifeLoan.hostedGroup_wires_sub hostPlan true d f c hd h42 hq)⟩
  unfold StairHostsSchedule.entryTailPrefix WindowCallerCosts.entryTailPrefix
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (subCh 41 98 2 (by decide) (by decide))
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (subCh 36 96 2 (by decide) (by decide))
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (subCh 30 93 3 (by decide) (by decide))
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (subCh 22 90 3 (by decide) (by decide))
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (subCh 13 85 5 (by decide) (by decide))
  refine appendChange ?_ (same _ _)
  exact fresh (group84_ok true)

theorem head (p : StairSchedule.StairPrimitives) (hp : p = StairConcreteAssembly.checkpointPrimitives) :
    SafeChange TP (StairHostsSchedule.exitHeadSuffix p hostPlan)
      (WindowCallerCosts.exitHeadSuffix p) := by
  subst hp
  unfold StairHostsSchedule.exitHeadSuffix WindowCallerCosts.exitHeadSuffix
  refine appendChange ?_ (fresh (group84_ok false))
  intro h
  exact ⟨fun q hq => h.1 q (PackCutOddExit.cutRows_sub hq), fun q hq => h.2 q (PackCutOddExit.cutRows_sub hq)⟩

private theorem entryField : PieceOK reserved KP
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) := by
  have h : PieceOK reserved KP (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan) :=
    Stair44FieldSites.entry
  apply (show SafeChange KP (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) from ?_) h
  have fpOk : PieceOK reserved lowPlace (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true) :=
    weaken (JointOdd1588.hostedFirstPacketOdd_pieceOK WindowCallerCosts.oddFirstHalf
      StairPhysicalInventory.physicalHoles (fun _ h => h) true
      (WindowCallerCosts.oddFirstHalf_support true))
  have low : SafeChange lowPlace (StairHostsSchedule.entryLowPrefix checkpointPrimitives hostPlan)
      (WindowCallerCosts.entryLowPrefix checkpointPrimitives) :=
    appendChange (appendChange (appendChange (fresh fpOk) (same _ _)) (renameChange (tail _))) (same _ _)
  have field : SafeChange KP (StairSchedule.fieldRename (StairHostsSchedule.entryLowPrefix checkpointPrimitives hostPlan))
      (StairSchedule.fieldRename (WindowCallerCosts.entryLowPrefix checkpointPrimitives)) :=
    renameChange (renameChange low)
  have sufLow : SafeChange lowPlace (StairHostsSchedule.entryLowSuffix hostPlan)
      (OddFullPass.P1LifeLoan.entryLowSuffixOdd hostPlan) :=
    fun ok => ⟨fun q hq => ok.1 q (OddFullPass.P1LifeLoan.entryLowSuffixOdd_wires_sub hostPlan hq),
      fun q hq => ok.2 q (OddFullPass.P1LifeLoan.entryLowSuffixOdd_wires_sub hostPlan hq)⟩
  have sufCh : SafeChange KP (StairSchedule.fieldRename (StairHostsSchedule.entryLowSuffix hostPlan))
      (StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd hostPlan)) :=
    renameChange (renameChange sufLow)
  exact appendChange (appendChange (appendChange (appendChange (appendChange field
    (same _ _)) (same _ _)) sufCh) (same _ _)) (same _ _)

private theorem exitField : PieceOK reserved KP
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) := by
  have h : PieceOK reserved KP (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) :=
    Stair44FieldSites.exit
  apply (show SafeChange KP (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) from ?_) h
  have preLow : SafeChange lowPlace (StairHostsSchedule.exitLowPrefix hostPlan)
      (OddFullPass.P1LifeLoan.exitLowPrefixOdd hostPlan) :=
    fun ok => ⟨fun q hq => ok.1 q (OddFullPass.P1LifeLoan.exitLowPrefixOdd_wires_sub hostPlan hq),
      fun q hq => ok.2 q (OddFullPass.P1LifeLoan.exitLowPrefixOdd_wires_sub hostPlan hq)⟩
  have preCh : SafeChange KP (StairSchedule.fieldRename (StairHostsSchedule.exitLowPrefix hostPlan))
      (StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd hostPlan)) :=
    renameChange (renameChange preLow)
  have fpOk : PieceOK reserved lowPlace (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false) :=
    weaken (JointOdd1588.hostedFirstPacketOdd_pieceOK WindowCallerCosts.oddFirstHalf
      StairPhysicalInventory.physicalHoles (fun _ h => h) false
      (WindowCallerCosts.oddFirstHalf_support false))
  have low : SafeChange lowPlace (StairHostsSchedule.exitLowSuffix checkpointPrimitives hostPlan)
      (WindowCallerCosts.exitLowSuffix checkpointPrimitives) :=
    appendChange (appendChange (appendChange (same _ _) (renameChange (head _ rfl))) (same _ _)) (fresh fpOk)
  exact appendChange (appendChange (appendChange (appendChange (appendChange (same _ _) (same _ _))
    preCh) (same _ _)) (same _ _)) (renameChange (renameChange low))

section
private theorem pieceOK_sub {holes : List Wire} {f : Wire → Wire} {P Q : Program}
    (h : ∀ q ∈ wires P, q ∈ wires Q) (hq : PieceOK holes f Q) : PieceOK holes f P :=
  ⟨fun x hx => hq.1 x (h x hx), fun x hx => hq.2 x (h x hx)⟩
private theorem entryFieldCut : PieceOK reserved KP WindowCallerCosts.entryFieldHostedCut :=
  pieceOK_sub (PackCutSub.wires_sub WindowCallerCosts.field_sublist) entryField
end

theorem phase {P : Program} (v : PieceOK reserved PP P) :
    PieceOK reserved UG (Stair44Outer.phasePlace P) := ok_kernel (ok_phase v)

theorem division (f : GoodWindow (TickCut.CutWindow.forwardCut true))
    (r : GoodWindow (TickCut.CutWindow.reverseCut false)) :
    PieceOK reserved UG WindowCallerCosts.divide :=
  (((((phase (walkF true 4 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.pack)))).append
    (ok_kernel entryFieldCut)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.reverseTail)))).append
    (phase (walkR false 85 (by decide) r))).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.native)))

theorem multiplication (k : Nat) (f : GoodWindow (TickCut.CutWindow.forwardCut false))
    (r : GoodWindow (TickCut.CutWindow.reverseCut true)) :
    PieceOK reserved UG (WindowCallerCosts.multiply k) :=
  (((((phase (walkF false 84 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.forwardTail)))).append
    (ok_kernel exitField)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.unpack)))).append
    (phase (walkR true 4 (by decide) r))).append (weaken (Stair44PhaseSites.exitX k))

theorem program_width (C : Point) (f : ∀d, GoodWindow (TickCut.CutWindow.forwardCut d))
    (r : ∀d,GoodWindow (TickCut.CutWindow.reverseCut d)) :
    Challenge.qubits (WindowCallerCosts.program C) ≤ 1543 := by
  apply width
  cases C with
  | zero => exact pieceOK_nil _ _
  | @some cx cy hc =>
    apply ok_wrapper
    exact ((weaken (Stair44OuterSites.initial hc)).append (ok_generic
      ((((((weaken (Stair44OuterSites.entryY (-cy))).append (weaken (Stair44OuterSites.entryX (-cx)))).append
        (division (f _) (r _))).append (weaken (Stair44Release.squareSites (ReflectionE1.correction cx)))).append
          (multiplication cx.val (f _) (r _))).append (weaken (Stair44OuterSites.exitY cy))))).append
      (weaken (Stair44OuterSites.finalPart hc))
end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic Secp256k1

theorem physical (C : Point) : GatePhysical (program C) :=
  WindowPhysical.physical (fun d => (TickCut.CutWindow.cut_physical d).1) (fun d => (TickCut.CutWindow.cut_physical d).2) C

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Secp256k1

theorem qubitBound (C : Point) : Challenge.qubits (program C) ≤ 1543 :=
  WindowSites.program_width C PartialSites.forward45plus1_fits PartialSites.reverse45plus1_fits

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowRelease
open Arithmetic Secp256k1 Challenge Baselines

end ECDSAAdd.Entrant.StairPacket.WindowRelease

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen

def mask (bank : Finset Wire) (archive stock : State) : State :=
  ⟨stock.phase, fun q => if q ∈ bank then archive.basis q else stock.basis q⟩

def avoids (P : Program) (bank : Finset Wire) : Prop := ∀ q ∈ bank, q ∉ wires P

theorem mask_run (P : Program) (bank : Finset Wire) (m : List Bool) (a r : State)
    (safe : avoids P bank) :
    run P m (mask bank a r) = mask bank a (run P m r) := by
  have h := Arithmetic.run_local_increment P (mask bank a r) r m (fun q used => by
    have off : q ∉ bank := fun x => safe q x used
    simp [mask, off])
  apply congrArg₂ State.mk
  · have hh := h.1
    change ((run P m (mask bank a r)).phase ^^ r.phase) = ((run P m r).phase ^^ r.phase) at hh
    change (run P m (mask bank a r)).phase = (run P m r).phase
    cases r.phase <;> simp_all
  · funext q
    by_cases used : q ∈ wires P
    · have off : q ∉ bank := fun x => safe q x used
      simpa [mask, off] using h.2 q used
    · rw [run_preserves_outside P m (mask bank a r) q used]
      change (if q ∈ bank then a.basis q else r.basis q) =
        (if q ∈ bank then a.basis q else (run P m r).basis q)
      rw [run_preserves_outside P m r q used]

theorem mask_frame (j row : Nat) (cs : CodecBitSliceVerify.Cols) (bank : Finset Wire)
    (a r : State) (off : ∀ q∈inside j, q∉bank) (h : frame j row cs r) :
    frame j row cs (mask bank a r) := by
  intro q hq
  have hk := off (fieldPort j q) (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  simpa [mask,hk] using h q hq

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section
namespace ECDSAAdd.Entrant.StairArchiveRelease
theorem packetSites_length (j : Nat) : (ArchiveFieldScratch.packetSites j).length = 16 := by
  simp [ArchiveFieldScratch.packetSites, List.range, List.range.loop]
/-- The field ports from 16 on (the tag and the 104 holes) do not depend on the bank. -/
theorem fieldPort_tail (j q : Nat) (h : 16 ≤ q) : fieldPort j q = fieldPort 0 q := by
  have a : (ArchiveFieldScratch.packetSites j).length ≤ q := by rw [packetSites_length]; exact h
  have b : (ArchiveFieldScratch.packetSites 0).length ≤ q := by rw [packetSites_length]; exact h
  simp only [fieldPort, fieldSites, List.getElem?_append_right a, List.getElem?_append_right b, packetSites_length]
end ECDSAAdd.Entrant.StairArchiveRelease
end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
open Arithmetic MappedCompressed ArchiveFieldScratch StairArchiveInactive StairArchiveNativeCut StairArchiveRelease
def slots (j : Nat) := (List.range 16).map (fieldPort j)
def banks := [10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82]
private def fixedCover (q : Wire) : Bool := decide (
  q ∈ [base 2400,base 2409,base 2410] ∨
  q ∈ [base 765,base 768,base 767,base 766,base 2312,base 1797,base 1027,base 2311,
       base 1025,base 2056,base 1540,base 1541,base 1026] ∨
  base 2057 ≤ q ∧ q < base 2311 ∨ base 770 ≤ q ∧ q < base 1025 ∨
  base 512 ≤ q ∧ q < base 765)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1200000 in
private theorem fixedCover_of_id {i : Nat} (h : i ∈ Q6EndpointCell.ids) :
    fixedCover (base i) = true := by
  simp only [Q6EndpointCell.ids, List.mem_append, List.mem_cons, List.not_mem_nil,
    List.mem_range'_1, or_false] at h
  simp only [fixedCover, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false,
    MappedCompressed.base]
  simp only [Nat.add_left_inj, Nat.add_le_add_iff_right, Nat.add_lt_add_iff_right]
  change _ ∨ _ ∨ 2057 ≤ i ∧ i < 2057+254 ∨ 770 ≤ i ∧ i < 770+255 ∨ 512 ≤ i ∧ i < 512+253
  tauto
def compactCover (k : Nat) (q : Wire) : Bool := fixedCover q ||
  ((List.finRange 10).map (History5.historyMap base (5*k))).contains q
theorem compactCover_present {k : Nat} {q : Wire} (h : q ∈ cover k) :
    compactCover k q = true := by
  rw [compactCover, Bool.or_eq_true]
  simp only [cover, List.mem_append, or_assoc] at h
  rcases h with small | fixed | dynamic
  · exact Or.inl (by simp only [fixedCover, decide_eq_true_eq]; exact Or.inl small)
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp fixed
    exact Or.inl (fixedCover_of_id hi)
  · exact Or.inr (List.contains_iff_mem.mpr dynamic)


def allowed (j k : Nat) := k=j || k=j+1 || (slots j).all (fun q => !compactCover k (preimage k q))
def part (h offset count : Nat) := (List.range' offset count).all (allowed h)
/-- `allowed` with the bank's `host.symm` images as a list: the tick-independent half of `preimage` (build-chain). -/
def allowedW (w : List Nat) (j k : Nat) := k=j || k=j+1 ||
  w.all (fun x => !compactCover k ((MappedCompressed.shifted (Placement5.pi k)).symm x))
def partW (w : List Nat) (h offset count : Nat) := (List.range' offset count).all (allowedW w h)
theorem part_eq_W (h offset count : Nat) (w : List Nat)
    (hw : (slots h).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) = w) :
    part h offset count = partW w h offset count := by
  subst hw
  have key : allowed h = allowedW ((slots h).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q))) h := by
    funext k
    have e : ((fun x => !compactCover k ((MappedCompressed.shifted (Placement5.pi k)).symm x)) ∘
        (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q))) = (fun q => !compactCover k (preimage k q)) := by
      funext q; simp only [Function.comp_apply, preimage]
    simp only [allowed, allowedW, List.all_map, e]
  unfold part partW
  rw [key]
-- build-chain: the h-chunk check generic in the bank and the tick (helpers/build-chain/box/gen/BankGen.lean)
/-- Bank `h`'s sixteen packet cells after `sig 511 ∘ host.symm` (ticks `5h..5h+9`, B-sides at offsets 0,1,3,5,6,8). -/
def cellsW (h : Nat) : List Nat :=
  [base (5*h), base (1028+5*h), base (5*h+1), base (1028+5*h+1), base (5*h+2), base (5*h+3), base (1028+5*h+3),
   base (5*h+4), base (5*h+5), base (1028+5*h+5), base (5*h+6), base (1028+5*h+6), base (5*h+7), base (5*h+8),
   base (1028+5*h+8), base (5*h+9)]

theorem shifted_symm_base (e : Equiv.Perm Nat) (n : Nat) :
    (MappedCompressed.shifted e).symm (base n) = base (e.symm n) :=
  MappedCompressed.shiftedFn_base e.symm n

theorem pi_symm_fix (k n : Nat) (hk : k ≤ 100) (hw : n < 515 ∨ 719 ≤ n)
    (hh : n < 1030 ∨ 1537 < n ∨ ((n-1030)%5 ≠ 0 ∧ (n-1030)%5 ≠ 2)) :
    (Placement5.pi k).symm n = n := by
  have z : Placement5.pi0.symm n = n := by
    rw [Equiv.symm_apply_eq]
    exact (Placement5.pi0_outside n (by
      simp only [Placement5.zeroRegion, Placement5.workRegion, Placement5.holeRegion]; omega)).symm
  have a1 : n ≠ Placement5.H (2*k+1) := by simp only [Placement5.H]; omega
  have a2 : n ≠ Placement5.H 203 := by simp only [Placement5.H]; omega
  have a3 : n ≠ Placement5.H (2*k) := by simp only [Placement5.H]; omega
  have a4 : n ≠ Placement5.H 202 := by simp only [Placement5.H]; omega
  have a5 : n ≠ Placement5.W (2*k+1) := by simp only [Placement5.W]; omega
  have a7 : n ≠ Placement5.W (2*k) := by simp only [Placement5.W]; omega
  simp only [Placement5.pi, Equiv.symm_trans_apply, Equiv.symm_swap, z,
    Equiv.swap_apply_of_ne_of_ne a1 a2, Equiv.swap_apply_of_ne_of_ne a3 a4,
    Equiv.swap_apply_of_ne_of_ne a5 a1, Equiv.swap_apply_of_ne_of_ne a7 a3]

private theorem fixed_false (n : Nat) (hn : n < 512 ∨ (1028 ≤ n ∧ n < 1540)) : fixedCover (base n) = false := by
  unfold fixedCover
  rw [decide_eq_false_iff_not]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, base]
  try simp only [Wire] at *
  omega

theorem hist_false (k n : Nat) (hn : ∀ i, i < 5 → n ≠ 5*k+i ∧ n ≠ 1028+5*k+i) :
    ((List.finRange 10).map (History5.historyMap base (5*k))).contains (base n) = false := by
  rw [Bool.eq_false_iff]
  intro hc
  obtain ⟨q, -, hq⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
  simp only [History5.historyMap, History5.historyId, base] at hq
  try simp only [Wire] at hq
  have hq5 : q.val / 2 < 5 := by omega
  split_ifs at hq
  · exact (hn (q.val/2) hq5).1 (by omega)
  · exact (hn (q.val/2) hq5).2 (by omega)

theorem cell_good (k n : Nat) (hk : k ≤ 100) (hw : n < 515 ∨ 719 ≤ n)
    (hh : n < 1030 ∨ 1537 < n ∨ ((n-1030)%5 ≠ 0 ∧ (n-1030)%5 ≠ 2))
    (hf : n < 512 ∨ (1028 ≤ n ∧ n < 1540)) (hi : ∀ i, i < 5 → n ≠ 5*k+i ∧ n ≠ 1028+5*k+i) :
    (!compactCover k ((MappedCompressed.shifted (Placement5.pi k)).symm (base n))) = true := by
  rw [shifted_symm_base, pi_symm_fix k n hk hw hh, compactCover, fixed_false n hf, hist_false k n hi]
  rfl

theorem cells_good (h k : Nat) (h1 : 1 ≤ h) (hh : h ≤ 100) (hk : k ≤ 100) (e0 : k ≠ h) (e1 : k ≠ h+1) :
    ∀ x ∈ cellsW h, (!compactCover k ((MappedCompressed.shifted (Placement5.pi k)).symm x)) = true := by
  intro x hx
  simp only [cellsW, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact cell_good k _ hk (by omega) (by omega) (by omega) (fun i hi => ⟨by omega, by omega⟩)

theorem allowedW_cells (h k : Nat) (h1 : 1 ≤ h) (hh : h ≤ 100) (hk : k ≤ 100) :
    allowedW (cellsW h) h k = true := by
  by_cases e0 : k = h
  · simp [allowedW, e0]
  by_cases e1 : k = h+1
  · simp [allowedW, e1]
  simp only [allowedW, List.all_eq_true.mpr (cells_good h k h1 hh hk e0 e1), Bool.or_true]

theorem partW_cells (h offset count : Nat) (h1 : 1 ≤ h) (hh : h ≤ 100) (hk : offset+count ≤ 101) :
    (List.range' offset count).all (allowedW (cellsW h) h) = true :=
  List.all_eq_true.mpr fun k hk' => allowedW_cells h k h1 hh (by have := List.mem_range'_1.mp hk'; omega)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify

def bank (j : Nat) := (Finset.range 16).image (fieldPort j)

def offBanks (persistent other : Finset Wire) (a r : State) : Prop :=
  ∀ q, q ∉ persistent → q ∉ other → a.basis q = r.basis q

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 100000

theorem restored (rev : Bool) :
    (List.range' 16 105).all (fun q => get (outputCols (leave rev)) q == get (StairArchiveNativeCut.canonical rev rev) q) = true := by
  cases rev <;> decide +kernel

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem wl10 : (slots 10).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 10 := by
  decide +kernel
theorem wl13 : (slots 13).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 13 := by
  decide +kernel
theorem wl16 : (slots 16).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 16 := by
  decide +kernel
theorem wl19 : (slots 19).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 19 := by
  decide +kernel
theorem wl22 : (slots 22).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 22 := by
  decide +kernel
theorem wl25 : (slots 25).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 25 := by
  decide +kernel
theorem wl28 : (slots 28).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 28 := by
  decide +kernel
theorem wl31 : (slots 31).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 31 := by
  decide +kernel
theorem wl34 : (slots 34).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 34 := by
  decide +kernel
theorem wl37 : (slots 37).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 37 := by
  decide +kernel
theorem wl40 : (slots 40).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 40 := by
  decide +kernel
theorem wl43 : (slots 43).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 43 := by
  decide +kernel
theorem wl46 : (slots 46).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 46 := by
  decide +kernel
theorem wl49 : (slots 49).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 49 := by
  decide +kernel
theorem wl52 : (slots 52).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 52 := by
  decide +kernel
theorem wl55 : (slots 55).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 55 := by
  decide +kernel
theorem wl58 : (slots 58).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 58 := by
  decide +kernel
theorem wl61 : (slots 61).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 61 := by
  decide +kernel
theorem wl64 : (slots 64).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 64 := by
  decide +kernel
theorem wl67 : (slots 67).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 67 := by
  decide +kernel
theorem wl70 : (slots 70).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 70 := by
  decide +kernel
theorem wl73 : (slots 73).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 73 := by
  decide +kernel
theorem wl76 : (slots 76).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 76 := by
  decide +kernel
theorem wl79 : (slots 79).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 79 := by
  decide +kernel
theorem wl82 : (slots 82).map (fun q => OB5.sig 511 (StairArchiveInactive.host.symm q)) =
    cellsW 82 := by
  decide +kernel
theorem h25_1 : part 25 1 7 = true := by
  rw [part_eq_W 25 1 7 _ wl25]
  exact partW_cells 25 1 7 (by decide) (by decide) (by decide)
theorem h25_8 : part 25 8 7 = true := by
  rw [part_eq_W 25 8 7 _ wl25]
  exact partW_cells 25 8 7 (by decide) (by decide) (by decide)
theorem h25_15 : part 25 15 7 = true := by
  rw [part_eq_W 25 15 7 _ wl25]
  exact partW_cells 25 15 7 (by decide) (by decide) (by decide)
theorem h25_22 : part 25 22 7 = true := by
  rw [part_eq_W 25 22 7 _ wl25]
  exact partW_cells 25 22 7 (by decide) (by decide) (by decide)
theorem h25_29 : part 25 29 7 = true := by
  rw [part_eq_W 25 29 7 _ wl25]
  exact partW_cells 25 29 7 (by decide) (by decide) (by decide)
theorem h25_36 : part 25 36 7 = true := by
  rw [part_eq_W 25 36 7 _ wl25]
  exact partW_cells 25 36 7 (by decide) (by decide) (by decide)
theorem h25_43 : part 25 43 7 = true := by
  rw [part_eq_W 25 43 7 _ wl25]
  exact partW_cells 25 43 7 (by decide) (by decide) (by decide)
theorem h25_50 : part 25 50 7 = true := by
  rw [part_eq_W 25 50 7 _ wl25]
  exact partW_cells 25 50 7 (by decide) (by decide) (by decide)
theorem h25_57 : part 25 57 7 = true := by
  rw [part_eq_W 25 57 7 _ wl25]
  exact partW_cells 25 57 7 (by decide) (by decide) (by decide)
theorem h25_64 : part 25 64 7 = true := by
  rw [part_eq_W 25 64 7 _ wl25]
  exact partW_cells 25 64 7 (by decide) (by decide) (by decide)
theorem h25_71 : part 25 71 7 = true := by
  rw [part_eq_W 25 71 7 _ wl25]
  exact partW_cells 25 71 7 (by decide) (by decide) (by decide)
theorem h25_78 : part 25 78 7 = true := by
  rw [part_eq_W 25 78 7 _ wl25]
  exact partW_cells 25 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h28_1 : part 28 1 7 = true := by
  rw [part_eq_W 28 1 7 _ wl28]
  exact partW_cells 28 1 7 (by decide) (by decide) (by decide)
theorem h28_8 : part 28 8 7 = true := by
  rw [part_eq_W 28 8 7 _ wl28]
  exact partW_cells 28 8 7 (by decide) (by decide) (by decide)
theorem h28_15 : part 28 15 7 = true := by
  rw [part_eq_W 28 15 7 _ wl28]
  exact partW_cells 28 15 7 (by decide) (by decide) (by decide)
theorem h28_22 : part 28 22 7 = true := by
  rw [part_eq_W 28 22 7 _ wl28]
  exact partW_cells 28 22 7 (by decide) (by decide) (by decide)
theorem h28_29 : part 28 29 7 = true := by
  rw [part_eq_W 28 29 7 _ wl28]
  exact partW_cells 28 29 7 (by decide) (by decide) (by decide)
theorem h28_36 : part 28 36 7 = true := by
  rw [part_eq_W 28 36 7 _ wl28]
  exact partW_cells 28 36 7 (by decide) (by decide) (by decide)
theorem h28_43 : part 28 43 7 = true := by
  rw [part_eq_W 28 43 7 _ wl28]
  exact partW_cells 28 43 7 (by decide) (by decide) (by decide)
theorem h28_50 : part 28 50 7 = true := by
  rw [part_eq_W 28 50 7 _ wl28]
  exact partW_cells 28 50 7 (by decide) (by decide) (by decide)
theorem h28_57 : part 28 57 7 = true := by
  rw [part_eq_W 28 57 7 _ wl28]
  exact partW_cells 28 57 7 (by decide) (by decide) (by decide)
theorem h28_64 : part 28 64 7 = true := by
  rw [part_eq_W 28 64 7 _ wl28]
  exact partW_cells 28 64 7 (by decide) (by decide) (by decide)
theorem h28_71 : part 28 71 7 = true := by
  rw [part_eq_W 28 71 7 _ wl28]
  exact partW_cells 28 71 7 (by decide) (by decide) (by decide)
theorem h28_78 : part 28 78 7 = true := by
  rw [part_eq_W 28 78 7 _ wl28]
  exact partW_cells 28 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h31_1 : part 31 1 7 = true := by
  rw [part_eq_W 31 1 7 _ wl31]
  exact partW_cells 31 1 7 (by decide) (by decide) (by decide)
theorem h31_8 : part 31 8 7 = true := by
  rw [part_eq_W 31 8 7 _ wl31]
  exact partW_cells 31 8 7 (by decide) (by decide) (by decide)
theorem h31_15 : part 31 15 7 = true := by
  rw [part_eq_W 31 15 7 _ wl31]
  exact partW_cells 31 15 7 (by decide) (by decide) (by decide)
theorem h31_22 : part 31 22 7 = true := by
  rw [part_eq_W 31 22 7 _ wl31]
  exact partW_cells 31 22 7 (by decide) (by decide) (by decide)
theorem h31_29 : part 31 29 7 = true := by
  rw [part_eq_W 31 29 7 _ wl31]
  exact partW_cells 31 29 7 (by decide) (by decide) (by decide)
theorem h31_36 : part 31 36 7 = true := by
  rw [part_eq_W 31 36 7 _ wl31]
  exact partW_cells 31 36 7 (by decide) (by decide) (by decide)
theorem h31_43 : part 31 43 7 = true := by
  rw [part_eq_W 31 43 7 _ wl31]
  exact partW_cells 31 43 7 (by decide) (by decide) (by decide)
theorem h31_50 : part 31 50 7 = true := by
  rw [part_eq_W 31 50 7 _ wl31]
  exact partW_cells 31 50 7 (by decide) (by decide) (by decide)
theorem h31_57 : part 31 57 7 = true := by
  rw [part_eq_W 31 57 7 _ wl31]
  exact partW_cells 31 57 7 (by decide) (by decide) (by decide)
theorem h31_64 : part 31 64 7 = true := by
  rw [part_eq_W 31 64 7 _ wl31]
  exact partW_cells 31 64 7 (by decide) (by decide) (by decide)
theorem h31_71 : part 31 71 7 = true := by
  rw [part_eq_W 31 71 7 _ wl31]
  exact partW_cells 31 71 7 (by decide) (by decide) (by decide)
theorem h31_78 : part 31 78 7 = true := by
  rw [part_eq_W 31 78 7 _ wl31]
  exact partW_cells 31 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h34_1 : part 34 1 7 = true := by
  rw [part_eq_W 34 1 7 _ wl34]
  exact partW_cells 34 1 7 (by decide) (by decide) (by decide)
theorem h34_8 : part 34 8 7 = true := by
  rw [part_eq_W 34 8 7 _ wl34]
  exact partW_cells 34 8 7 (by decide) (by decide) (by decide)
theorem h34_15 : part 34 15 7 = true := by
  rw [part_eq_W 34 15 7 _ wl34]
  exact partW_cells 34 15 7 (by decide) (by decide) (by decide)
theorem h34_22 : part 34 22 7 = true := by
  rw [part_eq_W 34 22 7 _ wl34]
  exact partW_cells 34 22 7 (by decide) (by decide) (by decide)
theorem h34_29 : part 34 29 7 = true := by
  rw [part_eq_W 34 29 7 _ wl34]
  exact partW_cells 34 29 7 (by decide) (by decide) (by decide)
theorem h34_36 : part 34 36 7 = true := by
  rw [part_eq_W 34 36 7 _ wl34]
  exact partW_cells 34 36 7 (by decide) (by decide) (by decide)
theorem h34_43 : part 34 43 7 = true := by
  rw [part_eq_W 34 43 7 _ wl34]
  exact partW_cells 34 43 7 (by decide) (by decide) (by decide)
theorem h34_50 : part 34 50 7 = true := by
  rw [part_eq_W 34 50 7 _ wl34]
  exact partW_cells 34 50 7 (by decide) (by decide) (by decide)
theorem h34_57 : part 34 57 7 = true := by
  rw [part_eq_W 34 57 7 _ wl34]
  exact partW_cells 34 57 7 (by decide) (by decide) (by decide)
theorem h34_64 : part 34 64 7 = true := by
  rw [part_eq_W 34 64 7 _ wl34]
  exact partW_cells 34 64 7 (by decide) (by decide) (by decide)
theorem h34_71 : part 34 71 7 = true := by
  rw [part_eq_W 34 71 7 _ wl34]
  exact partW_cells 34 71 7 (by decide) (by decide) (by decide)
theorem h34_78 : part 34 78 7 = true := by
  rw [part_eq_W 34 78 7 _ wl34]
  exact partW_cells 34 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h37_1 : part 37 1 7 = true := by
  rw [part_eq_W 37 1 7 _ wl37]
  exact partW_cells 37 1 7 (by decide) (by decide) (by decide)
theorem h37_8 : part 37 8 7 = true := by
  rw [part_eq_W 37 8 7 _ wl37]
  exact partW_cells 37 8 7 (by decide) (by decide) (by decide)
theorem h37_15 : part 37 15 7 = true := by
  rw [part_eq_W 37 15 7 _ wl37]
  exact partW_cells 37 15 7 (by decide) (by decide) (by decide)
theorem h37_22 : part 37 22 7 = true := by
  rw [part_eq_W 37 22 7 _ wl37]
  exact partW_cells 37 22 7 (by decide) (by decide) (by decide)
theorem h37_29 : part 37 29 7 = true := by
  rw [part_eq_W 37 29 7 _ wl37]
  exact partW_cells 37 29 7 (by decide) (by decide) (by decide)
theorem h37_36 : part 37 36 7 = true := by
  rw [part_eq_W 37 36 7 _ wl37]
  exact partW_cells 37 36 7 (by decide) (by decide) (by decide)
theorem h37_43 : part 37 43 7 = true := by
  rw [part_eq_W 37 43 7 _ wl37]
  exact partW_cells 37 43 7 (by decide) (by decide) (by decide)
theorem h37_50 : part 37 50 7 = true := by
  rw [part_eq_W 37 50 7 _ wl37]
  exact partW_cells 37 50 7 (by decide) (by decide) (by decide)
theorem h37_57 : part 37 57 7 = true := by
  rw [part_eq_W 37 57 7 _ wl37]
  exact partW_cells 37 57 7 (by decide) (by decide) (by decide)
theorem h37_64 : part 37 64 7 = true := by
  rw [part_eq_W 37 64 7 _ wl37]
  exact partW_cells 37 64 7 (by decide) (by decide) (by decide)
theorem h37_71 : part 37 71 7 = true := by
  rw [part_eq_W 37 71 7 _ wl37]
  exact partW_cells 37 71 7 (by decide) (by decide) (by decide)
theorem h37_78 : part 37 78 7 = true := by
  rw [part_eq_W 37 78 7 _ wl37]
  exact partW_cells 37 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h40_1 : part 40 1 7 = true := by
  rw [part_eq_W 40 1 7 _ wl40]
  exact partW_cells 40 1 7 (by decide) (by decide) (by decide)
theorem h40_8 : part 40 8 7 = true := by
  rw [part_eq_W 40 8 7 _ wl40]
  exact partW_cells 40 8 7 (by decide) (by decide) (by decide)
theorem h40_15 : part 40 15 7 = true := by
  rw [part_eq_W 40 15 7 _ wl40]
  exact partW_cells 40 15 7 (by decide) (by decide) (by decide)
theorem h40_22 : part 40 22 7 = true := by
  rw [part_eq_W 40 22 7 _ wl40]
  exact partW_cells 40 22 7 (by decide) (by decide) (by decide)
theorem h40_29 : part 40 29 7 = true := by
  rw [part_eq_W 40 29 7 _ wl40]
  exact partW_cells 40 29 7 (by decide) (by decide) (by decide)
theorem h40_36 : part 40 36 7 = true := by
  rw [part_eq_W 40 36 7 _ wl40]
  exact partW_cells 40 36 7 (by decide) (by decide) (by decide)
theorem h40_43 : part 40 43 7 = true := by
  rw [part_eq_W 40 43 7 _ wl40]
  exact partW_cells 40 43 7 (by decide) (by decide) (by decide)
theorem h40_50 : part 40 50 7 = true := by
  rw [part_eq_W 40 50 7 _ wl40]
  exact partW_cells 40 50 7 (by decide) (by decide) (by decide)
theorem h40_57 : part 40 57 7 = true := by
  rw [part_eq_W 40 57 7 _ wl40]
  exact partW_cells 40 57 7 (by decide) (by decide) (by decide)
theorem h40_64 : part 40 64 7 = true := by
  rw [part_eq_W 40 64 7 _ wl40]
  exact partW_cells 40 64 7 (by decide) (by decide) (by decide)
theorem h40_71 : part 40 71 7 = true := by
  rw [part_eq_W 40 71 7 _ wl40]
  exact partW_cells 40 71 7 (by decide) (by decide) (by decide)
theorem h40_78 : part 40 78 7 = true := by
  rw [part_eq_W 40 78 7 _ wl40]
  exact partW_cells 40 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h43_1 : part 43 1 7 = true := by
  rw [part_eq_W 43 1 7 _ wl43]
  exact partW_cells 43 1 7 (by decide) (by decide) (by decide)
theorem h43_8 : part 43 8 7 = true := by
  rw [part_eq_W 43 8 7 _ wl43]
  exact partW_cells 43 8 7 (by decide) (by decide) (by decide)
theorem h43_15 : part 43 15 7 = true := by
  rw [part_eq_W 43 15 7 _ wl43]
  exact partW_cells 43 15 7 (by decide) (by decide) (by decide)
theorem h43_22 : part 43 22 7 = true := by
  rw [part_eq_W 43 22 7 _ wl43]
  exact partW_cells 43 22 7 (by decide) (by decide) (by decide)
theorem h43_29 : part 43 29 7 = true := by
  rw [part_eq_W 43 29 7 _ wl43]
  exact partW_cells 43 29 7 (by decide) (by decide) (by decide)
theorem h43_36 : part 43 36 7 = true := by
  rw [part_eq_W 43 36 7 _ wl43]
  exact partW_cells 43 36 7 (by decide) (by decide) (by decide)
theorem h43_43 : part 43 43 7 = true := by
  rw [part_eq_W 43 43 7 _ wl43]
  exact partW_cells 43 43 7 (by decide) (by decide) (by decide)
theorem h43_50 : part 43 50 7 = true := by
  rw [part_eq_W 43 50 7 _ wl43]
  exact partW_cells 43 50 7 (by decide) (by decide) (by decide)
theorem h43_57 : part 43 57 7 = true := by
  rw [part_eq_W 43 57 7 _ wl43]
  exact partW_cells 43 57 7 (by decide) (by decide) (by decide)
theorem h43_64 : part 43 64 7 = true := by
  rw [part_eq_W 43 64 7 _ wl43]
  exact partW_cells 43 64 7 (by decide) (by decide) (by decide)
theorem h43_71 : part 43 71 7 = true := by
  rw [part_eq_W 43 71 7 _ wl43]
  exact partW_cells 43 71 7 (by decide) (by decide) (by decide)
theorem h43_78 : part 43 78 7 = true := by
  rw [part_eq_W 43 78 7 _ wl43]
  exact partW_cells 43 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h46_1 : part 46 1 7 = true := by
  rw [part_eq_W 46 1 7 _ wl46]
  exact partW_cells 46 1 7 (by decide) (by decide) (by decide)
theorem h46_8 : part 46 8 7 = true := by
  rw [part_eq_W 46 8 7 _ wl46]
  exact partW_cells 46 8 7 (by decide) (by decide) (by decide)
theorem h46_15 : part 46 15 7 = true := by
  rw [part_eq_W 46 15 7 _ wl46]
  exact partW_cells 46 15 7 (by decide) (by decide) (by decide)
theorem h46_22 : part 46 22 7 = true := by
  rw [part_eq_W 46 22 7 _ wl46]
  exact partW_cells 46 22 7 (by decide) (by decide) (by decide)
theorem h46_29 : part 46 29 7 = true := by
  rw [part_eq_W 46 29 7 _ wl46]
  exact partW_cells 46 29 7 (by decide) (by decide) (by decide)
theorem h46_36 : part 46 36 7 = true := by
  rw [part_eq_W 46 36 7 _ wl46]
  exact partW_cells 46 36 7 (by decide) (by decide) (by decide)
theorem h46_43 : part 46 43 7 = true := by
  rw [part_eq_W 46 43 7 _ wl46]
  exact partW_cells 46 43 7 (by decide) (by decide) (by decide)
theorem h46_50 : part 46 50 7 = true := by
  rw [part_eq_W 46 50 7 _ wl46]
  exact partW_cells 46 50 7 (by decide) (by decide) (by decide)
theorem h46_57 : part 46 57 7 = true := by
  rw [part_eq_W 46 57 7 _ wl46]
  exact partW_cells 46 57 7 (by decide) (by decide) (by decide)
theorem h46_64 : part 46 64 7 = true := by
  rw [part_eq_W 46 64 7 _ wl46]
  exact partW_cells 46 64 7 (by decide) (by decide) (by decide)
theorem h46_71 : part 46 71 7 = true := by
  rw [part_eq_W 46 71 7 _ wl46]
  exact partW_cells 46 71 7 (by decide) (by decide) (by decide)
theorem h46_78 : part 46 78 7 = true := by
  rw [part_eq_W 46 78 7 _ wl46]
  exact partW_cells 46 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h49_1 : part 49 1 7 = true := by
  rw [part_eq_W 49 1 7 _ wl49]
  exact partW_cells 49 1 7 (by decide) (by decide) (by decide)
theorem h49_8 : part 49 8 7 = true := by
  rw [part_eq_W 49 8 7 _ wl49]
  exact partW_cells 49 8 7 (by decide) (by decide) (by decide)
theorem h49_15 : part 49 15 7 = true := by
  rw [part_eq_W 49 15 7 _ wl49]
  exact partW_cells 49 15 7 (by decide) (by decide) (by decide)
theorem h49_22 : part 49 22 7 = true := by
  rw [part_eq_W 49 22 7 _ wl49]
  exact partW_cells 49 22 7 (by decide) (by decide) (by decide)
theorem h49_29 : part 49 29 7 = true := by
  rw [part_eq_W 49 29 7 _ wl49]
  exact partW_cells 49 29 7 (by decide) (by decide) (by decide)
theorem h49_36 : part 49 36 7 = true := by
  rw [part_eq_W 49 36 7 _ wl49]
  exact partW_cells 49 36 7 (by decide) (by decide) (by decide)
theorem h49_43 : part 49 43 7 = true := by
  rw [part_eq_W 49 43 7 _ wl49]
  exact partW_cells 49 43 7 (by decide) (by decide) (by decide)
theorem h49_50 : part 49 50 7 = true := by
  rw [part_eq_W 49 50 7 _ wl49]
  exact partW_cells 49 50 7 (by decide) (by decide) (by decide)
theorem h49_57 : part 49 57 7 = true := by
  rw [part_eq_W 49 57 7 _ wl49]
  exact partW_cells 49 57 7 (by decide) (by decide) (by decide)
theorem h49_64 : part 49 64 7 = true := by
  rw [part_eq_W 49 64 7 _ wl49]
  exact partW_cells 49 64 7 (by decide) (by decide) (by decide)
theorem h49_71 : part 49 71 7 = true := by
  rw [part_eq_W 49 71 7 _ wl49]
  exact partW_cells 49 71 7 (by decide) (by decide) (by decide)
theorem h49_78 : part 49 78 7 = true := by
  rw [part_eq_W 49 78 7 _ wl49]
  exact partW_cells 49 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h52_1 : part 52 1 7 = true := by
  rw [part_eq_W 52 1 7 _ wl52]
  exact partW_cells 52 1 7 (by decide) (by decide) (by decide)
theorem h52_8 : part 52 8 7 = true := by
  rw [part_eq_W 52 8 7 _ wl52]
  exact partW_cells 52 8 7 (by decide) (by decide) (by decide)
theorem h52_15 : part 52 15 7 = true := by
  rw [part_eq_W 52 15 7 _ wl52]
  exact partW_cells 52 15 7 (by decide) (by decide) (by decide)
theorem h52_22 : part 52 22 7 = true := by
  rw [part_eq_W 52 22 7 _ wl52]
  exact partW_cells 52 22 7 (by decide) (by decide) (by decide)
theorem h52_29 : part 52 29 7 = true := by
  rw [part_eq_W 52 29 7 _ wl52]
  exact partW_cells 52 29 7 (by decide) (by decide) (by decide)
theorem h52_36 : part 52 36 7 = true := by
  rw [part_eq_W 52 36 7 _ wl52]
  exact partW_cells 52 36 7 (by decide) (by decide) (by decide)
theorem h52_43 : part 52 43 7 = true := by
  rw [part_eq_W 52 43 7 _ wl52]
  exact partW_cells 52 43 7 (by decide) (by decide) (by decide)
theorem h52_50 : part 52 50 7 = true := by
  rw [part_eq_W 52 50 7 _ wl52]
  exact partW_cells 52 50 7 (by decide) (by decide) (by decide)
theorem h52_57 : part 52 57 7 = true := by
  rw [part_eq_W 52 57 7 _ wl52]
  exact partW_cells 52 57 7 (by decide) (by decide) (by decide)
theorem h52_64 : part 52 64 7 = true := by
  rw [part_eq_W 52 64 7 _ wl52]
  exact partW_cells 52 64 7 (by decide) (by decide) (by decide)
theorem h52_71 : part 52 71 7 = true := by
  rw [part_eq_W 52 71 7 _ wl52]
  exact partW_cells 52 71 7 (by decide) (by decide) (by decide)
theorem h52_78 : part 52 78 7 = true := by
  rw [part_eq_W 52 78 7 _ wl52]
  exact partW_cells 52 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

end


section

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h55_1 : part 55 1 7 = true := by
  rw [part_eq_W 55 1 7 _ wl55]
  exact partW_cells 55 1 7 (by decide) (by decide) (by decide)
theorem h55_8 : part 55 8 7 = true := by
  rw [part_eq_W 55 8 7 _ wl55]
  exact partW_cells 55 8 7 (by decide) (by decide) (by decide)
theorem h55_15 : part 55 15 7 = true := by
  rw [part_eq_W 55 15 7 _ wl55]
  exact partW_cells 55 15 7 (by decide) (by decide) (by decide)
theorem h55_22 : part 55 22 7 = true := by
  rw [part_eq_W 55 22 7 _ wl55]
  exact partW_cells 55 22 7 (by decide) (by decide) (by decide)
theorem h55_29 : part 55 29 7 = true := by
  rw [part_eq_W 55 29 7 _ wl55]
  exact partW_cells 55 29 7 (by decide) (by decide) (by decide)
theorem h55_36 : part 55 36 7 = true := by
  rw [part_eq_W 55 36 7 _ wl55]
  exact partW_cells 55 36 7 (by decide) (by decide) (by decide)
theorem h55_43 : part 55 43 7 = true := by
  rw [part_eq_W 55 43 7 _ wl55]
  exact partW_cells 55 43 7 (by decide) (by decide) (by decide)
theorem h55_50 : part 55 50 7 = true := by
  rw [part_eq_W 55 50 7 _ wl55]
  exact partW_cells 55 50 7 (by decide) (by decide) (by decide)
theorem h55_57 : part 55 57 7 = true := by
  rw [part_eq_W 55 57 7 _ wl55]
  exact partW_cells 55 57 7 (by decide) (by decide) (by decide)
theorem h55_64 : part 55 64 7 = true := by
  rw [part_eq_W 55 64 7 _ wl55]
  exact partW_cells 55 64 7 (by decide) (by decide) (by decide)
theorem h55_71 : part 55 71 7 = true := by
  rw [part_eq_W 55 71 7 _ wl55]
  exact partW_cells 55 71 7 (by decide) (by decide) (by decide)
theorem h55_78 : part 55 78 7 = true := by
  rw [part_eq_W 55 78 7 _ wl55]
  exact partW_cells 55 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h58_1 : part 58 1 7 = true := by
  rw [part_eq_W 58 1 7 _ wl58]
  exact partW_cells 58 1 7 (by decide) (by decide) (by decide)
theorem h58_8 : part 58 8 7 = true := by
  rw [part_eq_W 58 8 7 _ wl58]
  exact partW_cells 58 8 7 (by decide) (by decide) (by decide)
theorem h58_15 : part 58 15 7 = true := by
  rw [part_eq_W 58 15 7 _ wl58]
  exact partW_cells 58 15 7 (by decide) (by decide) (by decide)
theorem h58_22 : part 58 22 7 = true := by
  rw [part_eq_W 58 22 7 _ wl58]
  exact partW_cells 58 22 7 (by decide) (by decide) (by decide)
theorem h58_29 : part 58 29 7 = true := by
  rw [part_eq_W 58 29 7 _ wl58]
  exact partW_cells 58 29 7 (by decide) (by decide) (by decide)
theorem h58_36 : part 58 36 7 = true := by
  rw [part_eq_W 58 36 7 _ wl58]
  exact partW_cells 58 36 7 (by decide) (by decide) (by decide)
theorem h58_43 : part 58 43 7 = true := by
  rw [part_eq_W 58 43 7 _ wl58]
  exact partW_cells 58 43 7 (by decide) (by decide) (by decide)
theorem h58_50 : part 58 50 7 = true := by
  rw [part_eq_W 58 50 7 _ wl58]
  exact partW_cells 58 50 7 (by decide) (by decide) (by decide)
theorem h58_57 : part 58 57 7 = true := by
  rw [part_eq_W 58 57 7 _ wl58]
  exact partW_cells 58 57 7 (by decide) (by decide) (by decide)
theorem h58_64 : part 58 64 7 = true := by
  rw [part_eq_W 58 64 7 _ wl58]
  exact partW_cells 58 64 7 (by decide) (by decide) (by decide)
theorem h58_71 : part 58 71 7 = true := by
  rw [part_eq_W 58 71 7 _ wl58]
  exact partW_cells 58 71 7 (by decide) (by decide) (by decide)
theorem h58_78 : part 58 78 7 = true := by
  rw [part_eq_W 58 78 7 _ wl58]
  exact partW_cells 58 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h61_1 : part 61 1 7 = true := by
  rw [part_eq_W 61 1 7 _ wl61]
  exact partW_cells 61 1 7 (by decide) (by decide) (by decide)
theorem h61_8 : part 61 8 7 = true := by
  rw [part_eq_W 61 8 7 _ wl61]
  exact partW_cells 61 8 7 (by decide) (by decide) (by decide)
theorem h61_15 : part 61 15 7 = true := by
  rw [part_eq_W 61 15 7 _ wl61]
  exact partW_cells 61 15 7 (by decide) (by decide) (by decide)
theorem h61_22 : part 61 22 7 = true := by
  rw [part_eq_W 61 22 7 _ wl61]
  exact partW_cells 61 22 7 (by decide) (by decide) (by decide)
theorem h61_29 : part 61 29 7 = true := by
  rw [part_eq_W 61 29 7 _ wl61]
  exact partW_cells 61 29 7 (by decide) (by decide) (by decide)
theorem h61_36 : part 61 36 7 = true := by
  rw [part_eq_W 61 36 7 _ wl61]
  exact partW_cells 61 36 7 (by decide) (by decide) (by decide)
theorem h61_43 : part 61 43 7 = true := by
  rw [part_eq_W 61 43 7 _ wl61]
  exact partW_cells 61 43 7 (by decide) (by decide) (by decide)
theorem h61_50 : part 61 50 7 = true := by
  rw [part_eq_W 61 50 7 _ wl61]
  exact partW_cells 61 50 7 (by decide) (by decide) (by decide)
theorem h61_57 : part 61 57 7 = true := by
  rw [part_eq_W 61 57 7 _ wl61]
  exact partW_cells 61 57 7 (by decide) (by decide) (by decide)
theorem h61_64 : part 61 64 7 = true := by
  rw [part_eq_W 61 64 7 _ wl61]
  exact partW_cells 61 64 7 (by decide) (by decide) (by decide)
theorem h61_71 : part 61 71 7 = true := by
  rw [part_eq_W 61 71 7 _ wl61]
  exact partW_cells 61 71 7 (by decide) (by decide) (by decide)
theorem h61_78 : part 61 78 7 = true := by
  rw [part_eq_W 61 78 7 _ wl61]
  exact partW_cells 61 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h64_1 : part 64 1 7 = true := by
  rw [part_eq_W 64 1 7 _ wl64]
  exact partW_cells 64 1 7 (by decide) (by decide) (by decide)
theorem h64_8 : part 64 8 7 = true := by
  rw [part_eq_W 64 8 7 _ wl64]
  exact partW_cells 64 8 7 (by decide) (by decide) (by decide)
theorem h64_15 : part 64 15 7 = true := by
  rw [part_eq_W 64 15 7 _ wl64]
  exact partW_cells 64 15 7 (by decide) (by decide) (by decide)
theorem h64_22 : part 64 22 7 = true := by
  rw [part_eq_W 64 22 7 _ wl64]
  exact partW_cells 64 22 7 (by decide) (by decide) (by decide)
theorem h64_29 : part 64 29 7 = true := by
  rw [part_eq_W 64 29 7 _ wl64]
  exact partW_cells 64 29 7 (by decide) (by decide) (by decide)
theorem h64_36 : part 64 36 7 = true := by
  rw [part_eq_W 64 36 7 _ wl64]
  exact partW_cells 64 36 7 (by decide) (by decide) (by decide)
theorem h64_43 : part 64 43 7 = true := by
  rw [part_eq_W 64 43 7 _ wl64]
  exact partW_cells 64 43 7 (by decide) (by decide) (by decide)
theorem h64_50 : part 64 50 7 = true := by
  rw [part_eq_W 64 50 7 _ wl64]
  exact partW_cells 64 50 7 (by decide) (by decide) (by decide)
theorem h64_57 : part 64 57 7 = true := by
  rw [part_eq_W 64 57 7 _ wl64]
  exact partW_cells 64 57 7 (by decide) (by decide) (by decide)
theorem h64_64 : part 64 64 7 = true := by
  rw [part_eq_W 64 64 7 _ wl64]
  exact partW_cells 64 64 7 (by decide) (by decide) (by decide)
theorem h64_71 : part 64 71 7 = true := by
  rw [part_eq_W 64 71 7 _ wl64]
  exact partW_cells 64 71 7 (by decide) (by decide) (by decide)
theorem h64_78 : part 64 78 7 = true := by
  rw [part_eq_W 64 78 7 _ wl64]
  exact partW_cells 64 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h67_1 : part 67 1 7 = true := by
  rw [part_eq_W 67 1 7 _ wl67]
  exact partW_cells 67 1 7 (by decide) (by decide) (by decide)
theorem h67_8 : part 67 8 7 = true := by
  rw [part_eq_W 67 8 7 _ wl67]
  exact partW_cells 67 8 7 (by decide) (by decide) (by decide)
theorem h67_15 : part 67 15 7 = true := by
  rw [part_eq_W 67 15 7 _ wl67]
  exact partW_cells 67 15 7 (by decide) (by decide) (by decide)
theorem h67_22 : part 67 22 7 = true := by
  rw [part_eq_W 67 22 7 _ wl67]
  exact partW_cells 67 22 7 (by decide) (by decide) (by decide)
theorem h67_29 : part 67 29 7 = true := by
  rw [part_eq_W 67 29 7 _ wl67]
  exact partW_cells 67 29 7 (by decide) (by decide) (by decide)
theorem h67_36 : part 67 36 7 = true := by
  rw [part_eq_W 67 36 7 _ wl67]
  exact partW_cells 67 36 7 (by decide) (by decide) (by decide)
theorem h67_43 : part 67 43 7 = true := by
  rw [part_eq_W 67 43 7 _ wl67]
  exact partW_cells 67 43 7 (by decide) (by decide) (by decide)
theorem h67_50 : part 67 50 7 = true := by
  rw [part_eq_W 67 50 7 _ wl67]
  exact partW_cells 67 50 7 (by decide) (by decide) (by decide)
theorem h67_57 : part 67 57 7 = true := by
  rw [part_eq_W 67 57 7 _ wl67]
  exact partW_cells 67 57 7 (by decide) (by decide) (by decide)
theorem h67_64 : part 67 64 7 = true := by
  rw [part_eq_W 67 64 7 _ wl67]
  exact partW_cells 67 64 7 (by decide) (by decide) (by decide)
theorem h67_71 : part 67 71 7 = true := by
  rw [part_eq_W 67 71 7 _ wl67]
  exact partW_cells 67 71 7 (by decide) (by decide) (by decide)
theorem h67_78 : part 67 78 7 = true := by
  rw [part_eq_W 67 78 7 _ wl67]
  exact partW_cells 67 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h70_1 : part 70 1 7 = true := by
  rw [part_eq_W 70 1 7 _ wl70]
  exact partW_cells 70 1 7 (by decide) (by decide) (by decide)
theorem h70_8 : part 70 8 7 = true := by
  rw [part_eq_W 70 8 7 _ wl70]
  exact partW_cells 70 8 7 (by decide) (by decide) (by decide)
theorem h70_15 : part 70 15 7 = true := by
  rw [part_eq_W 70 15 7 _ wl70]
  exact partW_cells 70 15 7 (by decide) (by decide) (by decide)
theorem h70_22 : part 70 22 7 = true := by
  rw [part_eq_W 70 22 7 _ wl70]
  exact partW_cells 70 22 7 (by decide) (by decide) (by decide)
theorem h70_29 : part 70 29 7 = true := by
  rw [part_eq_W 70 29 7 _ wl70]
  exact partW_cells 70 29 7 (by decide) (by decide) (by decide)
theorem h70_36 : part 70 36 7 = true := by
  rw [part_eq_W 70 36 7 _ wl70]
  exact partW_cells 70 36 7 (by decide) (by decide) (by decide)
theorem h70_43 : part 70 43 7 = true := by
  rw [part_eq_W 70 43 7 _ wl70]
  exact partW_cells 70 43 7 (by decide) (by decide) (by decide)
theorem h70_50 : part 70 50 7 = true := by
  rw [part_eq_W 70 50 7 _ wl70]
  exact partW_cells 70 50 7 (by decide) (by decide) (by decide)
theorem h70_57 : part 70 57 7 = true := by
  rw [part_eq_W 70 57 7 _ wl70]
  exact partW_cells 70 57 7 (by decide) (by decide) (by decide)
theorem h70_64 : part 70 64 7 = true := by
  rw [part_eq_W 70 64 7 _ wl70]
  exact partW_cells 70 64 7 (by decide) (by decide) (by decide)
theorem h70_71 : part 70 71 7 = true := by
  rw [part_eq_W 70 71 7 _ wl70]
  exact partW_cells 70 71 7 (by decide) (by decide) (by decide)
theorem h70_78 : part 70 78 7 = true := by
  rw [part_eq_W 70 78 7 _ wl70]
  exact partW_cells 70 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h73_1 : part 73 1 7 = true := by
  rw [part_eq_W 73 1 7 _ wl73]
  exact partW_cells 73 1 7 (by decide) (by decide) (by decide)
theorem h73_8 : part 73 8 7 = true := by
  rw [part_eq_W 73 8 7 _ wl73]
  exact partW_cells 73 8 7 (by decide) (by decide) (by decide)
theorem h73_15 : part 73 15 7 = true := by
  rw [part_eq_W 73 15 7 _ wl73]
  exact partW_cells 73 15 7 (by decide) (by decide) (by decide)
theorem h73_22 : part 73 22 7 = true := by
  rw [part_eq_W 73 22 7 _ wl73]
  exact partW_cells 73 22 7 (by decide) (by decide) (by decide)
theorem h73_29 : part 73 29 7 = true := by
  rw [part_eq_W 73 29 7 _ wl73]
  exact partW_cells 73 29 7 (by decide) (by decide) (by decide)
theorem h73_36 : part 73 36 7 = true := by
  rw [part_eq_W 73 36 7 _ wl73]
  exact partW_cells 73 36 7 (by decide) (by decide) (by decide)
theorem h73_43 : part 73 43 7 = true := by
  rw [part_eq_W 73 43 7 _ wl73]
  exact partW_cells 73 43 7 (by decide) (by decide) (by decide)
theorem h73_50 : part 73 50 7 = true := by
  rw [part_eq_W 73 50 7 _ wl73]
  exact partW_cells 73 50 7 (by decide) (by decide) (by decide)
theorem h73_57 : part 73 57 7 = true := by
  rw [part_eq_W 73 57 7 _ wl73]
  exact partW_cells 73 57 7 (by decide) (by decide) (by decide)
theorem h73_64 : part 73 64 7 = true := by
  rw [part_eq_W 73 64 7 _ wl73]
  exact partW_cells 73 64 7 (by decide) (by decide) (by decide)
theorem h73_71 : part 73 71 7 = true := by
  rw [part_eq_W 73 71 7 _ wl73]
  exact partW_cells 73 71 7 (by decide) (by decide) (by decide)
theorem h73_78 : part 73 78 7 = true := by
  rw [part_eq_W 73 78 7 _ wl73]
  exact partW_cells 73 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h76_1 : part 76 1 7 = true := by
  rw [part_eq_W 76 1 7 _ wl76]
  exact partW_cells 76 1 7 (by decide) (by decide) (by decide)
theorem h76_8 : part 76 8 7 = true := by
  rw [part_eq_W 76 8 7 _ wl76]
  exact partW_cells 76 8 7 (by decide) (by decide) (by decide)
theorem h76_15 : part 76 15 7 = true := by
  rw [part_eq_W 76 15 7 _ wl76]
  exact partW_cells 76 15 7 (by decide) (by decide) (by decide)
theorem h76_22 : part 76 22 7 = true := by
  rw [part_eq_W 76 22 7 _ wl76]
  exact partW_cells 76 22 7 (by decide) (by decide) (by decide)
theorem h76_29 : part 76 29 7 = true := by
  rw [part_eq_W 76 29 7 _ wl76]
  exact partW_cells 76 29 7 (by decide) (by decide) (by decide)
theorem h76_36 : part 76 36 7 = true := by
  rw [part_eq_W 76 36 7 _ wl76]
  exact partW_cells 76 36 7 (by decide) (by decide) (by decide)
theorem h76_43 : part 76 43 7 = true := by
  rw [part_eq_W 76 43 7 _ wl76]
  exact partW_cells 76 43 7 (by decide) (by decide) (by decide)
theorem h76_50 : part 76 50 7 = true := by
  rw [part_eq_W 76 50 7 _ wl76]
  exact partW_cells 76 50 7 (by decide) (by decide) (by decide)
theorem h76_57 : part 76 57 7 = true := by
  rw [part_eq_W 76 57 7 _ wl76]
  exact partW_cells 76 57 7 (by decide) (by decide) (by decide)
theorem h76_64 : part 76 64 7 = true := by
  rw [part_eq_W 76 64 7 _ wl76]
  exact partW_cells 76 64 7 (by decide) (by decide) (by decide)
theorem h76_71 : part 76 71 7 = true := by
  rw [part_eq_W 76 71 7 _ wl76]
  exact partW_cells 76 71 7 (by decide) (by decide) (by decide)
theorem h76_78 : part 76 78 7 = true := by
  rw [part_eq_W 76 78 7 _ wl76]
  exact partW_cells 76 78 7 (by decide) (by decide) (by decide)
theorem h79_1 : part 79 1 7 = true := by
  rw [part_eq_W 79 1 7 _ wl79]
  exact partW_cells 79 1 7 (by decide) (by decide) (by decide)
theorem h79_8 : part 79 8 7 = true := by
  rw [part_eq_W 79 8 7 _ wl79]
  exact partW_cells 79 8 7 (by decide) (by decide) (by decide)
theorem h79_15 : part 79 15 7 = true := by
  rw [part_eq_W 79 15 7 _ wl79]
  exact partW_cells 79 15 7 (by decide) (by decide) (by decide)
theorem h79_22 : part 79 22 7 = true := by
  rw [part_eq_W 79 22 7 _ wl79]
  exact partW_cells 79 22 7 (by decide) (by decide) (by decide)
theorem h79_29 : part 79 29 7 = true := by
  rw [part_eq_W 79 29 7 _ wl79]
  exact partW_cells 79 29 7 (by decide) (by decide) (by decide)
theorem h79_36 : part 79 36 7 = true := by
  rw [part_eq_W 79 36 7 _ wl79]
  exact partW_cells 79 36 7 (by decide) (by decide) (by decide)
theorem h79_43 : part 79 43 7 = true := by
  rw [part_eq_W 79 43 7 _ wl79]
  exact partW_cells 79 43 7 (by decide) (by decide) (by decide)
theorem h79_50 : part 79 50 7 = true := by
  rw [part_eq_W 79 50 7 _ wl79]
  exact partW_cells 79 50 7 (by decide) (by decide) (by decide)
theorem h79_57 : part 79 57 7 = true := by
  rw [part_eq_W 79 57 7 _ wl79]
  exact partW_cells 79 57 7 (by decide) (by decide) (by decide)
theorem h79_64 : part 79 64 7 = true := by
  rw [part_eq_W 79 64 7 _ wl79]
  exact partW_cells 79 64 7 (by decide) (by decide) (by decide)
theorem h79_71 : part 79 71 7 = true := by
  rw [part_eq_W 79 71 7 _ wl79]
  exact partW_cells 79 71 7 (by decide) (by decide) (by decide)
theorem h79_78 : part 79 78 7 = true := by
  rw [part_eq_W 79 78 7 _ wl79]
  exact partW_cells 79 78 7 (by decide) (by decide) (by decide)
theorem h82_1 : part 82 1 7 = true := by
  rw [part_eq_W 82 1 7 _ wl82]
  exact partW_cells 82 1 7 (by decide) (by decide) (by decide)
theorem h82_8 : part 82 8 7 = true := by
  rw [part_eq_W 82 8 7 _ wl82]
  exact partW_cells 82 8 7 (by decide) (by decide) (by decide)
theorem h82_15 : part 82 15 7 = true := by
  rw [part_eq_W 82 15 7 _ wl82]
  exact partW_cells 82 15 7 (by decide) (by decide) (by decide)
theorem h82_22 : part 82 22 7 = true := by
  rw [part_eq_W 82 22 7 _ wl82]
  exact partW_cells 82 22 7 (by decide) (by decide) (by decide)
theorem h82_29 : part 82 29 7 = true := by
  rw [part_eq_W 82 29 7 _ wl82]
  exact partW_cells 82 29 7 (by decide) (by decide) (by decide)
theorem h82_36 : part 82 36 7 = true := by
  rw [part_eq_W 82 36 7 _ wl82]
  exact partW_cells 82 36 7 (by decide) (by decide) (by decide)
theorem h82_43 : part 82 43 7 = true := by
  rw [part_eq_W 82 43 7 _ wl82]
  exact partW_cells 82 43 7 (by decide) (by decide) (by decide)
theorem h82_50 : part 82 50 7 = true := by
  rw [part_eq_W 82 50 7 _ wl82]
  exact partW_cells 82 50 7 (by decide) (by decide) (by decide)
theorem h82_57 : part 82 57 7 = true := by
  rw [part_eq_W 82 57 7 _ wl82]
  exact partW_cells 82 57 7 (by decide) (by decide) (by decide)
theorem h82_64 : part 82 64 7 = true := by
  rw [part_eq_W 82 64 7 _ wl82]
  exact partW_cells 82 64 7 (by decide) (by decide) (by decide)
theorem h82_71 : part 82 71 7 = true := by
  rw [part_eq_W 82 71 7 _ wl82]
  exact partW_cells 82 71 7 (by decide) (by decide) (by decide)
theorem h82_78 : part 82 78 7 = true := by
  rw [part_eq_W 82 78 7 _ wl82]
  exact partW_cells 82 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h10_1 : part 10 1 7 = true := by
  rw [part_eq_W 10 1 7 _ wl10]
  exact partW_cells 10 1 7 (by decide) (by decide) (by decide)
theorem h10_8 : part 10 8 7 = true := by
  rw [part_eq_W 10 8 7 _ wl10]
  exact partW_cells 10 8 7 (by decide) (by decide) (by decide)
theorem h10_15 : part 10 15 7 = true := by
  rw [part_eq_W 10 15 7 _ wl10]
  exact partW_cells 10 15 7 (by decide) (by decide) (by decide)
theorem h10_22 : part 10 22 7 = true := by
  rw [part_eq_W 10 22 7 _ wl10]
  exact partW_cells 10 22 7 (by decide) (by decide) (by decide)
theorem h10_29 : part 10 29 7 = true := by
  rw [part_eq_W 10 29 7 _ wl10]
  exact partW_cells 10 29 7 (by decide) (by decide) (by decide)
theorem h10_36 : part 10 36 7 = true := by
  rw [part_eq_W 10 36 7 _ wl10]
  exact partW_cells 10 36 7 (by decide) (by decide) (by decide)
theorem h10_43 : part 10 43 7 = true := by
  rw [part_eq_W 10 43 7 _ wl10]
  exact partW_cells 10 43 7 (by decide) (by decide) (by decide)
theorem h10_50 : part 10 50 7 = true := by
  rw [part_eq_W 10 50 7 _ wl10]
  exact partW_cells 10 50 7 (by decide) (by decide) (by decide)
theorem h10_57 : part 10 57 7 = true := by
  rw [part_eq_W 10 57 7 _ wl10]
  exact partW_cells 10 57 7 (by decide) (by decide) (by decide)
theorem h10_64 : part 10 64 7 = true := by
  rw [part_eq_W 10 64 7 _ wl10]
  exact partW_cells 10 64 7 (by decide) (by decide) (by decide)
theorem h10_71 : part 10 71 7 = true := by
  rw [part_eq_W 10 71 7 _ wl10]
  exact partW_cells 10 71 7 (by decide) (by decide) (by decide)
theorem h10_78 : part 10 78 7 = true := by
  rw [part_eq_W 10 78 7 _ wl10]
  exact partW_cells 10 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h13_1 : part 13 1 7 = true := by
  rw [part_eq_W 13 1 7 _ wl13]
  exact partW_cells 13 1 7 (by decide) (by decide) (by decide)
theorem h13_8 : part 13 8 7 = true := by
  rw [part_eq_W 13 8 7 _ wl13]
  exact partW_cells 13 8 7 (by decide) (by decide) (by decide)
theorem h13_15 : part 13 15 7 = true := by
  rw [part_eq_W 13 15 7 _ wl13]
  exact partW_cells 13 15 7 (by decide) (by decide) (by decide)
theorem h13_22 : part 13 22 7 = true := by
  rw [part_eq_W 13 22 7 _ wl13]
  exact partW_cells 13 22 7 (by decide) (by decide) (by decide)
theorem h13_29 : part 13 29 7 = true := by
  rw [part_eq_W 13 29 7 _ wl13]
  exact partW_cells 13 29 7 (by decide) (by decide) (by decide)
theorem h13_36 : part 13 36 7 = true := by
  rw [part_eq_W 13 36 7 _ wl13]
  exact partW_cells 13 36 7 (by decide) (by decide) (by decide)
theorem h13_43 : part 13 43 7 = true := by
  rw [part_eq_W 13 43 7 _ wl13]
  exact partW_cells 13 43 7 (by decide) (by decide) (by decide)
theorem h13_50 : part 13 50 7 = true := by
  rw [part_eq_W 13 50 7 _ wl13]
  exact partW_cells 13 50 7 (by decide) (by decide) (by decide)
theorem h13_57 : part 13 57 7 = true := by
  rw [part_eq_W 13 57 7 _ wl13]
  exact partW_cells 13 57 7 (by decide) (by decide) (by decide)
theorem h13_64 : part 13 64 7 = true := by
  rw [part_eq_W 13 64 7 _ wl13]
  exact partW_cells 13 64 7 (by decide) (by decide) (by decide)
theorem h13_71 : part 13 71 7 = true := by
  rw [part_eq_W 13 71 7 _ wl13]
  exact partW_cells 13 71 7 (by decide) (by decide) (by decide)
theorem h13_78 : part 13 78 7 = true := by
  rw [part_eq_W 13 78 7 _ wl13]
  exact partW_cells 13 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h16_1 : part 16 1 7 = true := by
  rw [part_eq_W 16 1 7 _ wl16]
  exact partW_cells 16 1 7 (by decide) (by decide) (by decide)
theorem h16_8 : part 16 8 7 = true := by
  rw [part_eq_W 16 8 7 _ wl16]
  exact partW_cells 16 8 7 (by decide) (by decide) (by decide)
theorem h16_15 : part 16 15 7 = true := by
  rw [part_eq_W 16 15 7 _ wl16]
  exact partW_cells 16 15 7 (by decide) (by decide) (by decide)
theorem h16_22 : part 16 22 7 = true := by
  rw [part_eq_W 16 22 7 _ wl16]
  exact partW_cells 16 22 7 (by decide) (by decide) (by decide)
theorem h16_29 : part 16 29 7 = true := by
  rw [part_eq_W 16 29 7 _ wl16]
  exact partW_cells 16 29 7 (by decide) (by decide) (by decide)
theorem h16_36 : part 16 36 7 = true := by
  rw [part_eq_W 16 36 7 _ wl16]
  exact partW_cells 16 36 7 (by decide) (by decide) (by decide)
theorem h16_43 : part 16 43 7 = true := by
  rw [part_eq_W 16 43 7 _ wl16]
  exact partW_cells 16 43 7 (by decide) (by decide) (by decide)
theorem h16_50 : part 16 50 7 = true := by
  rw [part_eq_W 16 50 7 _ wl16]
  exact partW_cells 16 50 7 (by decide) (by decide) (by decide)
theorem h16_57 : part 16 57 7 = true := by
  rw [part_eq_W 16 57 7 _ wl16]
  exact partW_cells 16 57 7 (by decide) (by decide) (by decide)
theorem h16_64 : part 16 64 7 = true := by
  rw [part_eq_W 16 64 7 _ wl16]
  exact partW_cells 16 64 7 (by decide) (by decide) (by decide)
theorem h16_71 : part 16 71 7 = true := by
  rw [part_eq_W 16 71 7 _ wl16]
  exact partW_cells 16 71 7 (by decide) (by decide) (by decide)
theorem h16_78 : part 16 78 7 = true := by
  rw [part_eq_W 16 78 7 _ wl16]
  exact partW_cells 16 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h19_1 : part 19 1 7 = true := by
  rw [part_eq_W 19 1 7 _ wl19]
  exact partW_cells 19 1 7 (by decide) (by decide) (by decide)
theorem h19_8 : part 19 8 7 = true := by
  rw [part_eq_W 19 8 7 _ wl19]
  exact partW_cells 19 8 7 (by decide) (by decide) (by decide)
theorem h19_15 : part 19 15 7 = true := by
  rw [part_eq_W 19 15 7 _ wl19]
  exact partW_cells 19 15 7 (by decide) (by decide) (by decide)
theorem h19_22 : part 19 22 7 = true := by
  rw [part_eq_W 19 22 7 _ wl19]
  exact partW_cells 19 22 7 (by decide) (by decide) (by decide)
theorem h19_29 : part 19 29 7 = true := by
  rw [part_eq_W 19 29 7 _ wl19]
  exact partW_cells 19 29 7 (by decide) (by decide) (by decide)
theorem h19_36 : part 19 36 7 = true := by
  rw [part_eq_W 19 36 7 _ wl19]
  exact partW_cells 19 36 7 (by decide) (by decide) (by decide)
theorem h19_43 : part 19 43 7 = true := by
  rw [part_eq_W 19 43 7 _ wl19]
  exact partW_cells 19 43 7 (by decide) (by decide) (by decide)
theorem h19_50 : part 19 50 7 = true := by
  rw [part_eq_W 19 50 7 _ wl19]
  exact partW_cells 19 50 7 (by decide) (by decide) (by decide)
theorem h19_57 : part 19 57 7 = true := by
  rw [part_eq_W 19 57 7 _ wl19]
  exact partW_cells 19 57 7 (by decide) (by decide) (by decide)
theorem h19_64 : part 19 64 7 = true := by
  rw [part_eq_W 19 64 7 _ wl19]
  exact partW_cells 19 64 7 (by decide) (by decide) (by decide)
theorem h19_71 : part 19 71 7 = true := by
  rw [part_eq_W 19 71 7 _ wl19]
  exact partW_cells 19 71 7 (by decide) (by decide) (by decide)
theorem h19_78 : part 19 78 7 = true := by
  rw [part_eq_W 19 78 7 _ wl19]
  exact partW_cells 19 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h22_1 : part 22 1 7 = true := by
  rw [part_eq_W 22 1 7 _ wl22]
  exact partW_cells 22 1 7 (by decide) (by decide) (by decide)
theorem h22_8 : part 22 8 7 = true := by
  rw [part_eq_W 22 8 7 _ wl22]
  exact partW_cells 22 8 7 (by decide) (by decide) (by decide)
theorem h22_15 : part 22 15 7 = true := by
  rw [part_eq_W 22 15 7 _ wl22]
  exact partW_cells 22 15 7 (by decide) (by decide) (by decide)
theorem h22_22 : part 22 22 7 = true := by
  rw [part_eq_W 22 22 7 _ wl22]
  exact partW_cells 22 22 7 (by decide) (by decide) (by decide)
theorem h22_29 : part 22 29 7 = true := by
  rw [part_eq_W 22 29 7 _ wl22]
  exact partW_cells 22 29 7 (by decide) (by decide) (by decide)
theorem h22_36 : part 22 36 7 = true := by
  rw [part_eq_W 22 36 7 _ wl22]
  exact partW_cells 22 36 7 (by decide) (by decide) (by decide)
theorem h22_43 : part 22 43 7 = true := by
  rw [part_eq_W 22 43 7 _ wl22]
  exact partW_cells 22 43 7 (by decide) (by decide) (by decide)
theorem h22_50 : part 22 50 7 = true := by
  rw [part_eq_W 22 50 7 _ wl22]
  exact partW_cells 22 50 7 (by decide) (by decide) (by decide)
theorem h22_57 : part 22 57 7 = true := by
  rw [part_eq_W 22 57 7 _ wl22]
  exact partW_cells 22 57 7 (by decide) (by decide) (by decide)
theorem h22_64 : part 22 64 7 = true := by
  rw [part_eq_W 22 64 7 _ wl22]
  exact partW_cells 22 64 7 (by decide) (by decide) (by decide)
theorem h22_71 : part 22 71 7 = true := by
  rw [part_eq_W 22 71 7 _ wl22]
  exact partW_cells 22 71 7 (by decide) (by decide) (by decide)
theorem h22_78 : part 22 78 7 = true := by
  rw [part_eq_W 22 78 7 _ wl22]
  exact partW_cells 22 78 7 (by decide) (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify

attribute [local irreducible] run StairArchiveInactive.packet StairArchiveRelease.fieldHook
  StairArchiveTen.first StairArchiveTen.second StairArchiveTen.ten
  StairArchiveRelease.fieldPort StairArchiveRelease.outputCols StairArchiveRelease.inputCols
  StairArchiveNativeCut.canonical CodecBitSliceVerify.get
set_option maxRecDepth 1200
set_option maxHeartbeats 360000
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
open Arithmetic MappedCompressed ArchiveFieldScratch StairArchiveInactive StairArchiveNativeCut StairArchiveRelease WindowFieldMask
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 100000
private theorem splitRange : List.range' 1 84 = List.range' 1 7 ++ List.range' 8 7 ++ List.range' 15 7 ++ List.range' 22 7 ++ List.range' 29 7 ++ List.range' 36 7 ++ List.range' 43 7 ++ List.range' 50 7 ++ List.range' 57 7 ++ List.range' 64 7 ++ List.range' 71 7 ++ List.range' 78 7 := by decide +kernel
attribute [local irreducible] allowed fieldPort packet cover preimage
private theorem pass55 : (List.range' 1 84).all (allowed 55)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h55_1,h55_8⟩,h55_15⟩,h55_22⟩,h55_29⟩,h55_36⟩,h55_43⟩,h55_50⟩,h55_57⟩,h55_64⟩,h55_71⟩,h55_78⟩
private theorem pass58 : (List.range' 1 84).all (allowed 58)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h58_1,h58_8⟩,h58_15⟩,h58_22⟩,h58_29⟩,h58_36⟩,h58_43⟩,h58_50⟩,h58_57⟩,h58_64⟩,h58_71⟩,h58_78⟩
private theorem pass61 : (List.range' 1 84).all (allowed 61)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h61_1,h61_8⟩,h61_15⟩,h61_22⟩,h61_29⟩,h61_36⟩,h61_43⟩,h61_50⟩,h61_57⟩,h61_64⟩,h61_71⟩,h61_78⟩
private theorem pass64 : (List.range' 1 84).all (allowed 64)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h64_1,h64_8⟩,h64_15⟩,h64_22⟩,h64_29⟩,h64_36⟩,h64_43⟩,h64_50⟩,h64_57⟩,h64_64⟩,h64_71⟩,h64_78⟩
private theorem pass67 : (List.range' 1 84).all (allowed 67)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h67_1,h67_8⟩,h67_15⟩,h67_22⟩,h67_29⟩,h67_36⟩,h67_43⟩,h67_50⟩,h67_57⟩,h67_64⟩,h67_71⟩,h67_78⟩
private theorem pass70 : (List.range' 1 84).all (allowed 70)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h70_1,h70_8⟩,h70_15⟩,h70_22⟩,h70_29⟩,h70_36⟩,h70_43⟩,h70_50⟩,h70_57⟩,h70_64⟩,h70_71⟩,h70_78⟩
private theorem pass73 : (List.range' 1 84).all (allowed 73)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h73_1,h73_8⟩,h73_15⟩,h73_22⟩,h73_29⟩,h73_36⟩,h73_43⟩,h73_50⟩,h73_57⟩,h73_64⟩,h73_71⟩,h73_78⟩
private theorem pass76 : (List.range' 1 84).all (allowed 76)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h76_1,h76_8⟩,h76_15⟩,h76_22⟩,h76_29⟩,h76_36⟩,h76_43⟩,h76_50⟩,h76_57⟩,h76_64⟩,h76_71⟩,h76_78⟩
private theorem pass79 : (List.range' 1 84).all (allowed 79)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h79_1,h79_8⟩,h79_15⟩,h79_22⟩,h79_29⟩,h79_36⟩,h79_43⟩,h79_50⟩,h79_57⟩,h79_64⟩,h79_71⟩,h79_78⟩
private theorem pass82 : (List.range' 1 84).all (allowed 82)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h82_1,h82_8⟩,h82_15⟩,h82_22⟩,h82_29⟩,h82_36⟩,h82_43⟩,h82_50⟩,h82_57⟩,h82_64⟩,h82_71⟩,h82_78⟩
private theorem pass10 : (List.range' 1 84).all (allowed 10)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h10_1,h10_8⟩,h10_15⟩,h10_22⟩,h10_29⟩,h10_36⟩,h10_43⟩,h10_50⟩,h10_57⟩,h10_64⟩,h10_71⟩,h10_78⟩
private theorem pass13 : (List.range' 1 84).all (allowed 13)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h13_1,h13_8⟩,h13_15⟩,h13_22⟩,h13_29⟩,h13_36⟩,h13_43⟩,h13_50⟩,h13_57⟩,h13_64⟩,h13_71⟩,h13_78⟩
private theorem pass16 : (List.range' 1 84).all (allowed 16)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h16_1,h16_8⟩,h16_15⟩,h16_22⟩,h16_29⟩,h16_36⟩,h16_43⟩,h16_50⟩,h16_57⟩,h16_64⟩,h16_71⟩,h16_78⟩
private theorem pass19 : (List.range' 1 84).all (allowed 19)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h19_1,h19_8⟩,h19_15⟩,h19_22⟩,h19_29⟩,h19_36⟩,h19_43⟩,h19_50⟩,h19_57⟩,h19_64⟩,h19_71⟩,h19_78⟩
private theorem pass22 : (List.range' 1 84).all (allowed 22)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h22_1,h22_8⟩,h22_15⟩,h22_22⟩,h22_29⟩,h22_36⟩,h22_43⟩,h22_50⟩,h22_57⟩,h22_64⟩,h22_71⟩,h22_78⟩
private theorem pass25 : (List.range' 1 84).all (allowed 25)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h25_1,h25_8⟩,h25_15⟩,h25_22⟩,h25_29⟩,h25_36⟩,h25_43⟩,h25_50⟩,h25_57⟩,h25_64⟩,h25_71⟩,h25_78⟩
private theorem pass28 : (List.range' 1 84).all (allowed 28)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h28_1,h28_8⟩,h28_15⟩,h28_22⟩,h28_29⟩,h28_36⟩,h28_43⟩,h28_50⟩,h28_57⟩,h28_64⟩,h28_71⟩,h28_78⟩
private theorem pass31 : (List.range' 1 84).all (allowed 31)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h31_1,h31_8⟩,h31_15⟩,h31_22⟩,h31_29⟩,h31_36⟩,h31_43⟩,h31_50⟩,h31_57⟩,h31_64⟩,h31_71⟩,h31_78⟩
private theorem pass34 : (List.range' 1 84).all (allowed 34)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h34_1,h34_8⟩,h34_15⟩,h34_22⟩,h34_29⟩,h34_36⟩,h34_43⟩,h34_50⟩,h34_57⟩,h34_64⟩,h34_71⟩,h34_78⟩
private theorem pass37 : (List.range' 1 84).all (allowed 37)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h37_1,h37_8⟩,h37_15⟩,h37_22⟩,h37_29⟩,h37_36⟩,h37_43⟩,h37_50⟩,h37_57⟩,h37_64⟩,h37_71⟩,h37_78⟩
private theorem pass40 : (List.range' 1 84).all (allowed 40)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h40_1,h40_8⟩,h40_15⟩,h40_22⟩,h40_29⟩,h40_36⟩,h40_43⟩,h40_50⟩,h40_57⟩,h40_64⟩,h40_71⟩,h40_78⟩
private theorem pass43 : (List.range' 1 84).all (allowed 43)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h43_1,h43_8⟩,h43_15⟩,h43_22⟩,h43_29⟩,h43_36⟩,h43_43⟩,h43_50⟩,h43_57⟩,h43_64⟩,h43_71⟩,h43_78⟩
private theorem pass46 : (List.range' 1 84).all (allowed 46)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h46_1,h46_8⟩,h46_15⟩,h46_22⟩,h46_29⟩,h46_36⟩,h46_43⟩,h46_50⟩,h46_57⟩,h46_64⟩,h46_71⟩,h46_78⟩
private theorem pass49 : (List.range' 1 84).all (allowed 49)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h49_1,h49_8⟩,h49_15⟩,h49_22⟩,h49_29⟩,h49_36⟩,h49_43⟩,h49_50⟩,h49_57⟩,h49_64⟩,h49_71⟩,h49_78⟩
private theorem pass52 : (List.range' 1 84).all (allowed 52)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h52_1,h52_8⟩,h52_15⟩,h52_22⟩,h52_29⟩,h52_36⟩,h52_43⟩,h52_50⟩,h52_57⟩,h52_64⟩,h52_71⟩,h52_78⟩
theorem pass (h : Nat) (hm : h ∈ banks) : (List.range' 1 84).all (allowed h) = true := by
  simp only [banks,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact pass10
  · exact pass13
  · exact pass16
  · exact pass19
  · exact pass22
  · exact pass25
  · exact pass28
  · exact pass31
  · exact pass34
  · exact pass37
  · exact pass40
  · exact pass43
  · exact pass46
  · exact pass49
  · exact pass52
  · exact pass55
  · exact pass58
  · exact pass61
  · exact pass64
  · exact pass67
  · exact pass70
  · exact pass73
  · exact pass76
  · exact pass79
  · exact pass82

theorem packet_free (h k : Nat) (hm : h∈banks) (km : k∈List.range' 1 84)
    (not0 : k≠h) (not1 : k≠h+1) (d : Bool) : avoids (packet d k) (bank h) := by
  have once := List.all_eq_true.mp (pass h hm) k km
  simp only [allowed, decide_eq_false not0, decide_eq_false not1, Bool.false_or] at once
  intro q member used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp member
  have qmem : fieldPort h i ∈ slots h := List.mem_map.mpr ⟨i,List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩
  have outside := List.all_eq_true.mp once _ qmem
  have limit := (List.mem_range'_1.mp km).2
  have inside := original d k (by omega) used
  simp [compactCover_present inside] at outside

/-- Bit mask of a wire list (kernel-cheap: `Nat.lor`/`Nat.shiftLeft` are GMP-accelerated). -/
def maskOf (l : List Wire) : Nat := l.foldl (fun acc q => acc ||| (1 <<< (q:Nat))) 0

theorem testBit_maskFold (l : List Wire) (acc q : Nat) :
    (l.foldl (fun acc q => acc ||| (1 <<< (q:Nat))) acc).testBit q = (acc.testBit q || l.contains q) := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.contains_cons]
    by_cases h : (a:Nat) = q
    · subst h; simp
    · have h' : (q == a) = false := by simp only [beq_eq_false_iff_ne]; exact fun e => h e.symm
      simp [h, h']

theorem testBit_maskOf {l : List Wire} {q : Wire} (h : q ∈ l) : (maskOf l).testBit q = true := by
  rw [maskOf, testBit_maskFold]
  simp [h]

/-- Banks `j ≠ h`: no slot of `h` is a field port of `j` (one `&&&` of two masks per pair). -/
def distinct (j h : Nat) := j=h ||
  ((maskOf (slots h)) &&& (maskOf ((List.range 121).map (fieldPort j))) == 0)
private theorem distinct_ok : banks.all (fun j=>banks.all (distinct j))=true := by decide +kernel

theorem separate (j h : Nat) (jm : j∈banks) (hm : h∈banks) (ne : j≠h) :
    ∀ q∈inside j, q∉bank h := by
  have ok := List.all_eq_true.mp (List.all_eq_true.mp distinct_ok j jm) h hm
  simp only [distinct, decide_eq_false ne, Bool.false_or, beq_iff_eq] at ok
  intro q own other
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp other
  have qmem : fieldPort h i ∈ slots h := List.mem_map.mpr ⟨i,List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩
  have inside' : fieldPort h i ∈ (List.range 121).map (fieldPort j) := by
    obtain ⟨t,ht,eq⟩ := Finset.mem_image.mp own
    exact List.mem_map.mpr ⟨t,List.mem_range.mpr (Finset.mem_range.mp ht),eq⟩
  have b := congrArg (fun n : Nat => n.testBit (fieldPort h i)) ok
  simp only [Nat.testBit_and, testBit_maskOf qmem, testBit_maskOf inside', Bool.and_self, Nat.zero_testBit] at b
  exact Bool.noConfusion b
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify
def bankIds : Finset Nat := {10,13,16,19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73,76,79,82}
def allBanks : Finset Wire := bankIds.biUnion bank
def others (j : Nat) : Finset Wire := (bankIds.erase j).biUnion bank
def byteFrame (j row : Nat) (cs : Cols) (a : State) := ∀ q∈Finset.range 16,
  a.basis (fieldPort j q) = (get cs q).testBit row
structure Fits (rows : Nat → Nat) (code : Nat → Cols) (a r : State) : Prop where
  phase : a.phase = r.phase
  outside : ∀ q∉allBanks, a.basis q=r.basis q
  bytes : ∀ j∈bankIds, byteFrame j (rows j) (code j) a

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 100000

theorem decompose (j : Nat) (hj : j∈bankIds) : allBanks=bank j ∪ others j := by
  ext q
  simp only [allBanks,others,Finset.mem_union,Finset.mem_biUnion,Finset.mem_erase]
  constructor
  · rintro ⟨k,hk,hq⟩
    by_cases same : k=j
    · subst k; exact Or.inl hq
    · exact Or.inr ⟨k,⟨same,hk⟩,hq⟩
  · rintro (own|⟨k,⟨_,hk⟩,hq⟩)
    · exact ⟨j,hj,own⟩
    · exact ⟨k,hk,hq⟩

theorem plain (P : Program) (rows : Nat→Nat) (code : Nat→Cols) (m : List Bool) (a r : State)
    (h : Fits rows code a r) (safe : avoids P allBanks) : Fits rows code (run P m a) (run P m r) := by
  have eq : a=mask allBanks a r := by
    apply congrArg₂ State.mk h.phase
    funext q
    by_cases qmem : q∈allBanks
    · simp [qmem]
    · simpa [mask,qmem] using h.outside q qmem
  have result := mask_run P allBanks m a r safe
  rw [←eq] at result
  refine ⟨?_,?_,?_⟩
  · rw [result]; rfl
  · intro q out
    rw [result]
    simp [mask,out]
  · intro j hj q hq
    have mem : fieldPort j q∈allBanks := Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
    rw [result]
    simpa [mask,mem] using h.bytes j hj q hq

private theorem initRest (rev : Bool) :
    (List.range' 16 105).all (fun q => get (inputCols (enter rev)) q == get (StairArchiveNativeCut.canonical (!rev) (!rev)) q) = true := by
  cases rev <;> decide +kernel

attribute [local irreducible] run fieldPort StairArchiveNativeCut.canonical inputCols enter CodecBitSliceVerify.get

theorem beforeFrame (j : Nat) (hj : j∈bankIds) (rows : Nat→Nat) (code : Nat→Cols) (rev : Bool) (a r : State)
    (h : Fits rows code a r) (active : code j=inputCols (enter rev))
    (apart : ∀ q∈inside j, q∉others j) (before_ : frame j (rows j) (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (nd : ∀ i∈Finset.range 121,∀ k∈Finset.range 121, fieldPort j i=fieldPort j k→i=k) :
    frame j (rows j) (inputCols (enter rev)) a := by
  intro q hq
  by_cases lo : q<16
  · rw [←active]
    exact h.bytes j hj q (Finset.mem_range.mpr lo)
  · have lq := Finset.mem_range.mp hq
    have own : fieldPort j q ∉ bank j := by
      intro mem
      obtain ⟨k,hk,heq⟩ := Finset.mem_image.mp mem
      have lk := Finset.mem_range.mp hk
      have eq := nd k (Finset.mem_range.mpr (by omega)) q hq heq
      omega
    have outsider : fieldPort j q ∉ allBanks := by
      rw [decompose j hj,Finset.mem_union]
      exact fun hit => hit.elim own (apart _ (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
    have range : q∈List.range' 16 105 := List.mem_range'_1.mpr ⟨by omega,by omega⟩
    have c := beq_iff_eq.mp (List.all_eq_true.mp (initRest rev) q range)
    rw [h.outside _ outsider, before_ q hq, c]
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveInactive WindowFieldCosts
attribute [local irreducible] packet run allBanks
def nativeRanges (j n : Nat) := (j=1 ∧ n=9) ∨ (j=12 ∧ n=1) ∨ (j=15 ∧ n=1) ∨ (j=18 ∧ n=1) ∨ (j=21 ∧ n=1) ∨ (j=24 ∧ n=1) ∨ (j=27 ∧ n=1) ∨ (j=30 ∧ n=1) ∨ (j=33 ∧ n=1) ∨ (j=36 ∧ n=1) ∨ (j=39 ∧ n=1) ∨ (j=42 ∧ n=1) ∨ (j=45 ∧ n=1) ∨ (j=48 ∧ n=1) ∨ (j=51 ∧ n=1) ∨ (j=54 ∧ n=1) ∨ (j=57 ∧ n=1) ∨ (j=60 ∧ n=1) ∨ (j=63 ∧ n=1) ∨ (j=66 ∧ n=1) ∨ (j=69 ∧ n=1) ∨ (j=72 ∧ n=1) ∨ (j=75 ∧ n=1) ∨ (j=78 ∧ n=1) ∨ (j=81 ∧ n=1) ∨ (j=84 ∧ n=1)
private theorem disjointRange {j n k h : Nat} (valid : nativeRanges j n) (hk : j≤k ∧ k<j+n)
    (isBank : h∈bankIds) : k∈List.range' 1 84 ∧ k≠h ∧ k≠h+1 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at isBank
  unfold nativeRanges at valid
  rw [List.mem_range'_1]; omega
private theorem seqSafe (d : Bool) (j n : Nat)
    (h : ∀ k, j≤k → k<j+n → avoids (packet d k) allBanks) :
    avoids (PacketSequence.program d (packet d) j n) allBanks := by
  induction n generalizing j with
  | zero =>
    intro q _ used; simp [PacketSequence.program,wires] at used
  | succ n ih =>
    have head := h j (by omega) (by omega)
    have tail := ih (j+1) (fun k l u=>h k (by omega) (by omega))
    intro q inbank used
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at used
    · exact used.elim (tail q inbank) (head q inbank)
    · exact used.elim (head q inbank) (tail q inbank)
theorem groupSafe (d : Bool) (j n : Nat) (valid : nativeRanges j n) : avoids (group d j n) allBanks := by
  rw [group,distribute]
  apply seqSafe
  intro k lower upper q mem used
  rw [allBanks] at mem
  obtain ⟨h,hm,hq⟩ := Finset.mem_biUnion.mp mem
  have triple := disjointRange valid ⟨lower,upper⟩ hm
  have hlist : h∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using hm
  exact WindowBankCheck.packet_free h k hlist triple.1 triple.2.1 triple.2.2 d q hq used
end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify
set_option maxRecDepth 1600
set_option maxHeartbeats 400000
attribute [local irreducible] run packet fieldPort StairArchiveNativeCut.canonical inputCols outputCols CodecBitSliceVerify.get

private theorem memberList {j : Nat} (h : j∈bankIds) : j∈WindowBankCheck.banks := by
  simpa [bankIds,WindowBankCheck.banks] using h
theorem geometry {j : Nat} (h : j∈bankIds) : j∈starts10 ∧ j∈List.range' 1 83 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
theorem apart {j : Nat} (hj : j∈bankIds) : ∀ q∈inside j, q∉others j := by
  intro q hi ho
  obtain ⟨k,hk,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,kid⟩ := Finset.mem_erase.mp hk
  exact WindowBankCheck.separate j k (memberList hj) (memberList kid) ne.symm q hi mem
private theorem native_safe (j k : Nat) (hj : j∈bankIds) (which : k=j ∨ k=j+1) (d : Bool) :
    avoids (packet d k) (others j) := by
  intro q ho used
  obtain ⟨h,hm,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,hid⟩ := Finset.mem_erase.mp hm
  apply WindowBankCheck.packet_free h k (memberList hid) _ _ _ d q mem used
  all_goals simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at hj hid
  · apply List.mem_range'_1.mpr; omega
  all_goals omega
private theorem hook_safe (j : Nat) (hj : j∈bankIds) (s : Stage) :
    avoids (fieldHook j s) (others j) := by
  intro q ho used
  rw [fieldHook,renameProgram_support] at used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  exact apart hj _ (Finset.mem_image.mpr ⟨i,sub s hi,rfl⟩) ho
private theorem append_safe {P Q : Program} {W : Finset Wire} (p : avoids P W) (q : avoids Q W) :
    avoids (P++Q) W := by
  intro i hi used
  rw [wires_append, Finset.mem_union] at used
  exact used.elim (p i hi) (q i hi)

def update (code : Nat→Cols) (j : Nat) (out : Cols) := fun k => if k=j then out else code k
attribute [local irreducible] inside StairArchiveRelease.fieldHook
  StairArchiveTen.first StairArchiveTen.second StairArchiveTen.ten

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open CodecBitSliceVerify WindowFieldMask WindowFieldCosts ArchiveFieldScratch
attribute [local irreducible] run measurementCount WindowFieldCosts.group StairArchiveTen.ten refExit
  inputCols outputCols StairArchiveNativeCut.canonical enter leave
inductive Leg where
  | native (j n : Nat)
  | paired (j : Nat)
def emitted (d : Bool) : Leg → Program
  | .native j n => group d j n
  | .paired j => ten j (!d)
def stock (d : Bool) (m : List Bool) (r : State) : Leg → State
  | .native j n => run (group d j n) m r
  | .paired j => refExit j (!d) m r
def codes (d : Bool) (c : Nat→Cols) : Leg → Nat→Cols
  | .native _ _ => c
  | .paired j => update c j (outputCols (leave (!d)))
def nextTape (d : Bool) (l : Leg) (m : List Bool) := m.drop (measurementCount (emitted d l))
def concatenate (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => emitted d l ++ concatenate d ls
def destination (d : Bool) : List Leg → List Bool → State → State
  | [],_,r => r
  | l::ls,m,r => destination d ls (nextTape d l m) (stock d m r l)
def finalCode (d : Bool) : List Leg → (Nat→Cols) → Nat→Cols
  | [],c => c
  | l::ls,c => finalCode d ls (codes d c l)
def validLeg (d : Bool) (c : Nat→Cols) : Leg → Prop
  | .native j n => nativeRanges j n
  | .paired j => j∈bankIds ∧ c j=inputCols (enter (!d))
def valid (d : Bool) : List Leg → (Nat→Cols) → Prop
  | [],_ => True
  | l::ls,c => validLeg d c l ∧ valid d ls (codes d c l)
def plan : Bool→List Leg
  | true => [.native 1 9,.paired 10,.native 12 1,.paired 13,.native 15 1,.paired 16,.native 18 1,.paired 19,.native 21 1,.paired 22,.native 24 1,.paired 25,.native 27 1,.paired 28,.native 30 1,.paired 31,.native 33 1,.paired 34,.native 36 1,.paired 37,.native 39 1,.paired 40,.native 42 1,.paired 43,.native 45 1,.paired 46,.native 48 1,.paired 49,.native 51 1,.paired 52,.native 54 1,.paired 55,.native 57 1,.paired 58,.native 60 1,.paired 61,.native 63 1,.paired 64,.native 66 1,.paired 67,.native 69 1,.paired 70,.native 72 1,.paired 73,.native 75 1,.paired 76,.native 78 1,.paired 79,.native 81 1,.paired 82,.native 84 1]
  | false => [.native 84 1,.paired 82,.native 81 1,.paired 79,.native 78 1,.paired 76,.native 75 1,.paired 73,.native 72 1,.paired 70,.native 69 1,.paired 67,.native 66 1,.paired 64,.native 63 1,.paired 61,.native 60 1,.paired 58,.native 57 1,.paired 55,.native 54 1,.paired 52,.native 51 1,.paired 49,.native 48 1,.paired 46,.native 45 1,.paired 43,.native 42 1,.paired 40,.native 39 1,.paired 37,.native 36 1,.paired 34,.native 33 1,.paired 31,.native 30 1,.paired 28,.native 27 1,.paired 25,.native 24 1,.paired 22,.native 21 1,.paired 19,.native 18 1,.paired 16,.native 15 1,.paired 13,.native 12 1,.paired 10,.native 1 9]
def initialCode (d : Bool) : Nat→Cols := fun _=>inputCols (enter (!d))
private theorem valid_plan (d : Bool) : valid d (plan d) (initialCode d) := by
  cases d <;> simp [valid,plan,validLeg,nativeRanges,bankIds,codes,update,initialCode]
end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney

end

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

theorem pool (i : Nat) (hi : cleanIndex i) : pmapR layout (base i) ∈ layout.dialogPool := by
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

theorem direct (s : State) (m : List Bool) (X : Nat) (hx : regValue layout.point.x s.basis=X)
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
namespace NativePack270
open ArchiveBoundary270
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

end ECDSAAdd.Entrant.StairPacket.WideReference

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

theorem frame_key (j:Fin 26) (ps:Ports) (chron:∀i:Fin 20,ps ⟨i,by omega⟩=nativeRawPort j i)
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

theorem off (d:Bool) (k i n:Nat) (lo:k < i) (hi:i+n≤512):
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
def referenceTape0 (d : Bool) : List Leg → List Bool → List Bool
  | [],_ => []
  | l::ls,m => joinTapes (referenceLeg d l) (legTape d m l) (referenceTape0 d ls (nextTape d l m))
/-- the reference tape of the record run, seen from the actual tape `m` of the field group. -/
def referenceTape (d : Bool) (ls : List Leg) (m : List Bool) : List Bool :=
  referenceTape0 d ls (WindowFieldCosts.cellTape d m)

set_option maxRecDepth 8000
set_option maxHeartbeats 900000
private theorem shape' (d : Bool) (p : Nat→Program) : PacketSequence.program d p 1 84 =
  let seq := PacketSequence.program d p
  if d then seq 1 9 ++ ((p 10 ++ p 11) ++ (seq 12 1 ++ ((p 13 ++ p 14) ++ (seq 15 1 ++ ((p 16 ++ p 17) ++ (seq 18 1 ++ ((p 19 ++ p 20) ++ (seq 21 1 ++ ((p 22 ++ p 23) ++ (seq 24 1 ++ ((p 25 ++ p 26) ++ (seq 27 1 ++ ((p 28 ++ p 29) ++ (seq 30 1 ++ ((p 31 ++ p 32) ++ (seq 33 1 ++ ((p 34 ++ p 35) ++ (seq 36 1 ++ ((p 37 ++ p 38) ++ (seq 39 1 ++ ((p 40 ++ p 41) ++ (seq 42 1 ++ ((p 43 ++ p 44) ++ (seq 45 1 ++ ((p 46 ++ p 47) ++ (seq 48 1 ++ ((p 49 ++ p 50) ++ (seq 51 1 ++ ((p 52 ++ p 53) ++ (seq 54 1 ++ ((p 55 ++ p 56) ++ (seq 57 1 ++ ((p 58 ++ p 59) ++ (seq 60 1 ++ ((p 61 ++ p 62) ++ (seq 63 1 ++ ((p 64 ++ p 65) ++ (seq 66 1 ++ ((p 67 ++ p 68) ++ (seq 69 1 ++ ((p 70 ++ p 71) ++ (seq 72 1 ++ ((p 73 ++ p 74) ++ (seq 75 1 ++ ((p 76 ++ p 77) ++ (seq 78 1 ++ ((p 79 ++ p 80) ++ (seq 81 1 ++ ((p 82 ++ p 83) ++ (seq 84 1 ++ []))))))))))))))))))))))))))))))))))))))))))))))))))
  else seq 84 1 ++ ((p 83 ++ p 82) ++ (seq 81 1 ++ ((p 80 ++ p 79) ++ (seq 78 1 ++ ((p 77 ++ p 76) ++ (seq 75 1 ++ ((p 74 ++ p 73) ++ (seq 72 1 ++ ((p 71 ++ p 70) ++ (seq 69 1 ++ ((p 68 ++ p 67) ++ (seq 66 1 ++ ((p 65 ++ p 64) ++ (seq 63 1 ++ ((p 62 ++ p 61) ++ (seq 60 1 ++ ((p 59 ++ p 58) ++ (seq 57 1 ++ ((p 56 ++ p 55) ++ (seq 54 1 ++ ((p 53 ++ p 52) ++ (seq 51 1 ++ ((p 50 ++ p 49) ++ (seq 48 1 ++ ((p 47 ++ p 46) ++ (seq 45 1 ++ ((p 44 ++ p 43) ++ (seq 42 1 ++ ((p 41 ++ p 40) ++ (seq 39 1 ++ ((p 38 ++ p 37) ++ (seq 36 1 ++ ((p 35 ++ p 34) ++ (seq 33 1 ++ ((p 32 ++ p 31) ++ (seq 30 1 ++ ((p 29 ++ p 28) ++ (seq 27 1 ++ ((p 26 ++ p 25) ++ (seq 24 1 ++ ((p 23 ++ p 22) ++ (seq 21 1 ++ ((p 20 ++ p 19) ++ (seq 18 1 ++ ((p 17 ++ p 16) ++ (seq 15 1 ++ ((p 14 ++ p 13) ++ (seq 12 1 ++ ((p 11 ++ p 10) ++ (seq 1 9 ++ [])))))))))))))))))))))))))))))))))))))))))))))))))) := by
  cases d <;> simp [PacketSequence.program,List.append_assoc]
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
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed WindowParityDirty
def region : Program := []
def site (j i : Nat) := OB5.sig 511 (NewHistory5.payloadWire base (8*j+i))
def other (j : Nat) := if j=46 then 49 else 46
def port (j q : Nat) : Wire :=
  if q<16 then site j q else if q=16 then FrontierEntry1591Field.host else site (other j) (q-17)
def bankCorrection (j : Nat) := renameProgram (port j) region
def correction := bankCorrection 10 ++ (bankCorrection 13 ++ (bankCorrection 16 ++ (bankCorrection 19 ++ (bankCorrection 22 ++ (bankCorrection 25 ++ (bankCorrection 28 ++ (bankCorrection 31 ++ (bankCorrection 34 ++ (bankCorrection 37 ++ (bankCorrection 40 ++ (bankCorrection 43 ++ (bankCorrection 46 ++ (bankCorrection 49 ++ (bankCorrection 52 ++ (bankCorrection 55 ++ (bankCorrection 58 ++ (bankCorrection 61 ++ (bankCorrection 64 ++ (bankCorrection 67 ++ (bankCorrection 70 ++ (bankCorrection 73 ++ (bankCorrection 76 ++ (bankCorrection 79 ++ bankCorrection 82)))))))))))))))))))))))
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

def plain (kx ky : Fp) := OddOuterBridge.plainOdd kx ky
def routed (kx ky : Fp) := OddOuterBridge.routedOdd kx ky

theorem unpull (f : Equiv.Perm Wire) (s : State) : pullState f.symm (pullState f s)=s := by
  apply State.extensionality
  · rfl
  · funext q; exact congrArg s.basis (f.apply_symm_apply q)

theorem encoded_head (X Y kx ky : Fp) (s : State) (m : List Bool)
    (hx : regValue layout.point.x s.basis=X.val) (hy : regValue layout.point.y s.basis=Y.val)
    (clean : regValue layout.dialogPool s.basis=0) :
    let flag := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+kx.val) else false
    let initial := put s (pkW layout) flag
    run (routed kx ky) m (pullState outer.symm initial)=pullState integerFirst.symm (run (plain kx ky) m initial) :=
  OddOuterBridge.encoded_head_odd X Y kx ky s m hx hy clean
    (fun sY mX xc pc => Stair44OuterX.execute X kx sY mX xc pc)

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
theorem geom (d:Bool):wires (codeEncode d)=Finset.range 10:=by cases d <;> decide +kernel
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



-- ==== w4: build-w4b B2-b selected_receipt (b2b/Main_SelectedReceipt.lean) ====
-- BEGIN build-w4b NativeJ.selected_receipt (B2-b part 4)
-- Main (w4r): next to dadon's `NativePack{240,255}.selected_receipt` (after `StockCanonicalRow`, Main ~5436).
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ7
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction StairArchiveTrace StockCanonicalRow Partial
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run Shadow7.onRails Shadow7.routed measurementCount Shadow7.body

/-- dadon's `NativePack{s}.selected_receipt`, generic: block `j` keeps the previous block's archive at the row
`select` picks from the recorded key. -/
theorem selected_receipt (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    let v:=key (Shadow7.sbP (start (prev j))) past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    select v<63145 ∧ Encodes v (select v) ∧ Kept (ArchiveJ7.codePorts (prev j)) d (select v) out:=by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity
    ready.2.1 scratch past pg ps cross po pm prior
  have held:=bank_kept j (by omega) (by omega) d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1
  have all:=frame_key (prev j) (ArchiveJ7.rawPorts (prev j))
    (ArchiveJ7.chronological_all (prev j) (by simp only [prev]; omega)) row (Shadow7.sbP (start (prev j))) past pg ps cross s _
    prior held frame
  have spec:=select_spec ⟨row,limit,all⟩
  have final:=receipt j (by omega) (by omega) d pre tape _ spec.1 (reframe limit all (ArchiveJ7.rawPorts (prev j)) _ frame)
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨spec.1,spec.2,final.1⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ7

end
-- END build-w4b NativeJ.selected_receipt
-- ==== w4: end selected_receipt ====

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack270
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary270
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open StockCanonicalRow ArchiveBoundary270 ParkEndpoint Portal270Flag Secp256k1 SkywalkRails StairArchiveTrace
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
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd hostPlan) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd hostPlan) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (WindowCallerCosts.exitLowSuffix p)

def entryFieldHostedCut : Program :=
  StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd hostPlan) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

theorem field_sublist : entryFieldHostedCut.Sublist (entryFieldHosted checkpointPrimitives) := by
  have f : (StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut).Sublist
      (StairSchedule.fieldRename (WindowCallerCosts.entryLowPrefix checkpointPrimitives)) :=
    PackCutSub.rename_sub _ (PackCutSub.rename_sub _ WindowCallerCosts.low_sublist)
  unfold entryFieldHostedCut entryFieldHosted
  exact ((((f.append (List.Sublist.refl _)).append (List.Sublist.refl _)).append (List.Sublist.refl _)).append
    (List.Sublist.refl _)).append (List.Sublist.refl _)

open Stair44Outer

def divide : Program :=
  phasePlace (WindowWalkCosts.forward true 4) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace entryFieldHostedCut ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 85) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 84) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 4) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

def generic (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (EntryFuseOdd.entryYAllOdd layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (EntryFuseOdd.exitYAllOdd layout cy)

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
def outside (q last : Wire) (xs : Hops) := q≠last ∧ ∀ e∈xs,q≠e.1 ∧ q≠e.2
def safe (last target : Wire) : Wire→Hops→Prop
  | src,[] => src≠target ∧ last≠target
  | src,(c,b)::xs => src≠target ∧ c≠target ∧ b≠target ∧ src≠b ∧ c≠b ∧ outside b last xs ∧ safe last target b xs

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

end ECDSAAdd.Entrant.StairPacket.StockArchiveTruth

end

end
section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryJ
open Arithmetic MappedCompressed IntegerPacket Partial WideReference
set_option maxRecDepth 25000
set_option maxHeartbeats 2800000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.body Shadow7.routed measurementCount

/-! Generic history hand-off of an interior window block `j` (par-c2; dadon's `Ordinary{s}Exit`, `Ordinary{s}Native`,
`Logical{s}Exit`). The block's pack re-encodes the cells of ticks `s-15..s-11` exactly as the stock encoder of
group `s-15` does, and the logical end state differs from the stock run only on the archived cells of ticks
`s-10..s-1` (`newBank`). Interior: `oldStart s = s-15` (par-a's `oldStart_interior`). Blocks `1 ≤ j ≤ 21`. -/

def plain (j : Fin 26) : Fin 10 → Wire := History5.historyMap base (start j-15)
def newBank (j : Fin 26) : List Wire := (List.range' (start j-10) 10).flatMap (fun r=>[base r,base (1028+r)])

theorem plain_cell (j : Fin 26) (i : Fin 10) :
    (i.val%2=0 ∧ (plain j i:Nat)=start j-15+i.val/2+16) ∨ (i.val%2≠0 ∧ (plain j i:Nat)=start j-15+i.val/2+1044) := by
  simp only [plain,History5.historyMap,History5.historyId,base,Wire]
  split
  · left; constructor; assumption; omega
  · right; constructor; assumption; omega
theorem plain_inj (j : Fin 26) : Function.Injective (plain j) := by
  intro a b e
  have ha:=a.isLt; have hb:=b.isLt
  have ca:=plain_cell j a; have cb:=plain_cell j b
  have e':(plain j a:Nat)=plain j b:=e
  apply Fin.ext
  simp only [Wire] at ca cb e'
  omega
/-- `OB5.sig s` and `OB5.sig (s+14)` agree on these cells (both swap the moved history cells). -/
theorem sig_same (j : Fin 26) (i : Fin 10) :
    (OB5.sig (start j) (plain j i):Nat)=OB5.sig (start j+14) (plain j i) := by
  have c:=plain_cell j i
  have hj:=j.isLt; have hi:=i.isLt
  simp only [OB5.sig,Wire]
  simp only [start,Wire] at *
  split <;> split <;> omega

/-- Cells of the stock encoder of group `t`: ticks `t..t+4`. -/
theorem encode_cells (d:Bool) (t:Nat) : ∀q∈wires (Rolling1588.encodeAt base d t),
    ∃r,t≤r ∧ r≤t+4 ∧ (q=r+16 ∨ q=r+1044) := by
  intro q h
  change q∈wires (renameProgram (MeasuredCodec5.label (History5.historyMap base t)) (Rolling1588.codeEncode d)) at h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
  rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
  refine ⟨t+a/2,by omega,by omega,?_⟩
  simp only [MeasuredCodec5.label,ha,dif_pos,History5.historyMap,History5.historyId,base,Wire]
  split <;> omega

theorem heads_all : ∀ j : Fin 26, 1≤j.val → j.val≤24 → ∀i:Fin 10,
    oldRange (start j+1) (windowNet j (NativeJ7.history j i)) ∧
    NativeJ7.history j i∉ArchiveJ7.rawHead (NativeJ7.prev j) ∧ ArchiveJ7.Band (start (NativeJ7.prev j)+15) (NativeJ7.history j i) ∧
    NativeJ7.history j i∉EnterJ7.pending j ∧ NativeJ7.history j i≠EnterJ7.flagN j ∧ NativeJ7.history j i≠EnterJ7.flagF j ∧
    NativeJ7.history j i≠EnterJ7.flagU j ∧ NativeJ7.history j i∉RailPair.sites (EnterJ7.upperPairs j) ∧
    EnterJ7.pull j (NativeJ7.history j i)=plain j i := by
  decide +kernel

theorem kept (j:Fin 26) (admin:Program) (m:List Bool) (s:State) (q:Wire) (early:oldRange (start j+1) (windowNet j q)) :
    (run (Shadow7.body j admin) m s).basis q=
      (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)).basis q := by
  simp only [Shadow7.body,run_append,run_take]
  exact Shadow7.route_outside j 1 14 (by decide) q (Shadow7.old_clear (by decide) early) _ _

theorem pastInput (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (x p:Nat) (good:Bounds x p) (raw:State)
    (dom:Domain (start j) x p raw) (i:Fin 10) :
    raw.basis (plain j i)=(run (span (start j) 15) [] raw).basis (plain j i) := by
  have pp:=preservePast (start j) 15 x p (start j-15+i.val/2) (by simp only [start]; omega) good raw dom
    (by simp only [start]; omega) []
  rcases plain_cell j i with ⟨-,e⟩|⟨-,e⟩
  · rw [e]; exact pp.1.symm
  · rw [e,show start j-15+i.val/2+1044=base (1028+(start j-15+i.val/2)) by simp only [base]; omega]; exact pp.2.symm

theorem encode (j : Fin 26) (h1 : 1≤j.val) (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (NativeJ7.history j i)=b.basis (plain j i)) (i:Fin 10) :
    (run (NativeJ7.program j d) tape a).basis (NativeJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] b).basis (plain j i) := by
  rw [(NativeJ7.equals j (by omega) d).1]
  exact ArchiveOrdinaryFive.stock_relocated d (NativeJ7.history j) (plain j) (NativeJ7.histInj j) (plain_inj j) a b tape [] agree i

theorem readback (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw pre wide out:State) (tape:List Bool)
    (input:∀i,pre.basis (NativeJ7.history j i)=raw.basis (plain j i))
    (stable:∀i,raw.basis (plain j i)=wide.basis (plain j i))
    (last:∀i,out.basis (NativeJ7.history j i)=(run (NativeJ7.withArchive j d) tape pre).basis (NativeJ7.history j i)) (i:Fin 10) :
    out.basis (NativeJ7.history j i)=(run (Rolling1588.encodeAt base d (start j-15)) [] wide).basis (plain j i) := by
  apply (last i).trans
  rw [NativeJ7.withArchive,run_append,run_take]
  have hp:(NativeJ7.prev j).val≤23:=by simp only [NativeJ7.prev]; omega
  obtain ⟨-,offHead,band,-⟩:=heads_all j (by omega) h21 i
  have off:NativeJ7.history j i∉ArchiveJ7.rawPortsList (NativeJ7.prev j):=by
    rw [ArchiveJ7.raw_split,List.mem_append]
    rintro (h|h)
    · exact offHead h
    · obtain ⟨k,hk,eq⟩:=List.mem_map.mp h
      exact ArchiveJ7.band_off _ (ArchiveJ.tick_lt _) (List.mem_range.mp hk) band eq
  rw [run_preserves_outside (Shadow7.archiveLoadP (NativeJ7.prev j) d) _ _ _
    (fun h=>off (List.mem_toFinset.mp (ArchiveJ7.load_cover (NativeJ7.prev j) (by omega) d h)))]
  exact encode j (by omega) d pre wide tape (fun k=>(input k).trans (stable k)) i

/-- `Ordinary{s}Exit.result` for every interior block. -/
theorem result (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool) (x p:Nat)
    (good:Bounds x p) (dom:Domain (start j) x p raw)
    (input:∀i,(run (Shadow7.routed j 0 1) m s).basis (NativeJ7.history j i)=raw.basis (plain j i)) :
    ∀i,(run (Shadow7.body j (NativeJ7.withArchive j d)) m s).basis (NativeJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)).basis (plain j i) :=
  readback j (by omega) h21 d raw (run (Shadow7.routed j 0 1) m s) (run (span (start j) 15) [] raw) _ _ input
    (pastInput j (by omega) h21 x p good raw dom) (fun i=>kept j _ m s _ (heads_all j (by omega) h21 i).1)

/-- `Logical{s}Exit.window` for every interior block (par-a's `Fixed`-free `endRaw_*_gen`). -/
theorem window (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24)
    (interior:oldStart (start j)=start j-15 ∧ oldCount (start j)=15) (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,historyState.basis (NativeJ7.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)).basis (plain j i))
    (q:Wire) (ordinarySite:q∉newBank j) :
    (endRaw (start j) raw historyState).basis q=
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)).basis q := by
  have bound:start j+14≤511:=by simp only [start]; omega
  have s15:15≤start j:=by simp only [start]; omega
  by_cases inside:q∈oldSites (start j)
  · obtain ⟨r,r1,r2,hq⟩:=old_cell inside
    rw [interior.1] at r1 r2
    rw [interior.2] at r2
    have young:r<start j-10:=by
      by_contra hr
      apply ordinarySite
      simp only [newBank,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false,base]
      simp only [Wire] at *
      exact ⟨r,⟨by omega,by omega⟩,by omega⟩
    have ex:∃i:Fin 10,q=plain j i:=by
      simp only [Wire] at *
      rcases hq with hq|hq
      · refine ⟨⟨2*(r-(start j-15)),by omega⟩,?_⟩
        rcases plain_cell j ⟨2*(r-(start j-15)),by omega⟩ with ⟨-,e⟩|⟨od,-⟩
        · rw [e]; dsimp only; omega
        · exfalso; simp only at od; omega
      · refine ⟨⟨2*(r-(start j-15))+1,by omega⟩,?_⟩
        rcases plain_cell j ⟨2*(r-(start j-15))+1,by omega⟩ with ⟨ev,-⟩|⟨-,e⟩
        · exfalso; simp only at ev; omega
        · rw [e]; dsimp only; omega
    obtain ⟨i,rfl⟩:=ex
    rw [endRaw_inside_gen _ bound _ _ _ inside,← sig_same j i]
    exact ordinaryBits i
  · rw [endRaw_outside_gen _ bound _ _ _ inside]
    apply (run_preserves_outside _ _ _ q _).symm
    intro used
    obtain ⟨r,r1,r2,hq⟩:=encode_cells d _ q used
    apply inside
    simp only [oldSites,interior.1,interior.2,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
      or_false,base]
    simp only [Wire] at *
    exact ⟨r,⟨by omega,by omega⟩,by omega⟩

/-- `Ordinary{s}Native.result`: block `j`'s window agrees with the stock run except on `newBank j`
(par-d2's `OrdinaryChainW` step for an interior block). -/
theorem native (j : Fin 26) (h1 : 1≤j.val) (h21 : j.val≤24)
    (interior:oldStart (start j)=start j-15 ∧ oldCount (start j)=15) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (domain:Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) neg far long (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:Shadow7.onRails j 0 z (run (Shadow7.enterP j) a s).basis) :
    let historyState:=run (Shadow7.body j (NativeJ7.withArchive j d)) b (run (Shadow7.enterP j) a s)
    ArchiveHistoryCompare.Except (newBank j) (endRaw (start j) raw historyState)
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)) := by
  let e:=run (Shadow7.enterP j) a s
  have input:∀i,(run (Shadow7.routed j 0 1) b e).basis (NativeJ7.history j i)=raw.basis (plain j i) := by
    intro i
    have kept0:=NativeJ7.prefix_kept j (by omega) h21 s a b z odd active i
    obtain ⟨-,-,-,notTag,hn,hf,hu,hi,same⟩:=heads_all j (by omega) h21 i
    exact kept0.trans (by simpa only [eraseSites,if_neg notTag,pullState,same] using cut.unchanged _ hn hf hu hi)
  exact fun q hq=>window j (by omega) h21 interior d raw _ (result j (by omega) h21 d raw e b x p good domain input) q hq

end ECDSAAdd.Entrant.StairPacket.OrdinaryJ

end

-- ==== end PrizeTail8dd9f9e60 ====

-- ==== begin PrizeTail05e06b1e9 ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.StockStrongChain
open Arithmetic MappedCompressed Secp256k1 IntegerPacket WideReference StockWindowTicket StockCanonicalRow Partial ArchivePortAction ArchiveStockRows
set_option maxRecDepth 16000
set_option maxHeartbeats 4500000
attribute [local irreducible] run measurementCount Partial.leave225 Partial.leave240 Partial.leave255
  NativePack270.lastWindow
noncomputable def value (x p i b:Nat) (c:SkywalkNat.State→Bool):Nat→Bool:=
  key b (unsigned i x p) (c (unsigned i x p)) (SkywalkTrace.trace 15 (WideReference.canonical i x p))
def SavedKey (v:Nat→Bool) (ps:Ports) (d:Bool) (s:State):Prop:= select v<63145 ∧ Encodes v (select v) ∧ Kept ps d (select v) s

attribute [local irreducible] key select WideReference.canonical
theorem kept_frame (ps:Ports) (d:Bool) (r:Nat) (s:State) (h:Frame ps (code d) r s):
    Kept ps d r s:=fun j=>h ⟨j,by omega⟩
end ECDSAAdd.Entrant.StairPacket.StockStrongChain

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44Resources Stair44Outer
open StairConcreteAssembly WindowFieldParity
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
private theorem setup_eq : setup = StairSchedule.paritySetup := by
  have empty : correction = [] := rfl
  rw [setup, empty, List.append_nil]

theorem program_eq (C : Point) : program C = WindowCallerCosts.program C := by
  cases C with
  | zero => rfl
  | @some cx cy hc =>
    simp only [program, WindowCallerCosts.program, finite, WindowCallerCosts.finite,
      borrowGeneric, WindowCallerCosts.borrowGeneric, generic, WindowCallerCosts.generic,
      divide, WindowCallerCosts.divide, multiply, WindowCallerCosts.multiply,
      entryFieldHosted, WindowCallerCosts.entryFieldHosted, entryFieldHostedCut,
      WindowCallerCosts.entryFieldHostedCut, exitFieldHosted,
      WindowCallerCosts.exitFieldHosted, setup_eq]

theorem metrics (C : Point) : toffoliCount (program C) ≤ 2013078 ∧
    measurementCount (program C) ≤ 1449468 ∧ gateSlots (program C) ≤ 66279181 := by
  rw [program_eq]
  exact ⟨(WindowCallerCosts.totals C).1, (WindowCallerCosts.totals C).2, WindowSlots.slotBound C⟩
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
attribute [local irreducible] run chain

end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Baselines Stair44Outer StairConcreteAssembly WindowFieldParity
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem physical (C : Point) : GatePhysical (program C) := by
  rw [program_eq]
  exact WindowCallerCosts.physical C
end ECDSAAdd.Entrant.StairPacket.WindowParityCaller

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityCaller
open Arithmetic MappedCompressed Secp256k1 Challenge Baselines Stair44Outer WindowFieldParity
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
theorem width (C : Point) : qubits (program C) ≤ 1543 := by
  rw [program_eq]
  exact WindowCallerCosts.qubitBound C
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

namespace ECDSAAdd.Entrant.StairPacket.Ordinary270Terminal
open Arithmetic MappedCompressed NativePack270 ArchivePortAction ArchiveBoundary270 ParkEndpoint CodecBitSliceVerify
set_option maxRecDepth 40000
set_option maxHeartbeats 3800000
attribute [local irreducible] run
end ECDSAAdd.Entrant.StairPacket.Ordinary270Terminal

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

end ECDSAAdd.Entrant.StairPacket.WindowFieldHistory

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option linter.unusedSimpArgs false
def lawful (t : Wire) : Aff→Prop
  | .x w => w≠t
  | .cx c w => c≠w ∧ c≠t ∧ w≠t
end ECDSAAdd.Entrant.StairPacket.WindowParityDirty

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityRelease
open Arithmetic Secp256k1 Challenge Baselines

def entry : Challenge.Entry := fun C => normalizeProgram (WindowParityCaller.program C)
def bounds : Challenge.Bounds := ⟨2013078,1449468,1543,66279181⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowParityCaller.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowParityCaller.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowParityCaller.metrics C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1449468
    rw [normalize_measurements]
    exact (WindowParityCaller.metrics C).2.1
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1543
    rw [normalize_qubits]
    exact WindowParityCaller.width C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 66279181
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

namespace ECDSAAdd.Entrant.StairPacket.StockBaseline
open Arithmetic MappedCompressed WideReference Secp256k1
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward
theorem forward_phase (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:1 ≤ i) (hi:i+n≤512) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p i s.basis):
    (run (Rolling1588TickGap.forward d i n) m (pullState (OB5.sig (i-1)) s)).phase=s.phase:=by
  have spec:=Rolling1588TickGap.forward_gen d x good.nonzero good.small n i lo hi s m stage
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have ph:=(Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p i n hp0 good.nonzero odd cap (by norm_num [p]) good.small cop hi s m stage).1
  exact (congrArg State.phase spec).trans ph
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
private theorem physicalHead :
    WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q=>fieldPort j q == wire (histPort j q)))=true := by
  decide +kernel
private theorem physicalTail : ((fieldPort 0 16 == base 720) &&
    (List.range' 17 104).all (fun q=>fieldPort 0 q == wire (base (Placement5.H (8+(q-17))))))=true := by
  decide +kernel
private theorem physical_ok : WindowBankCheck.banks.all physical=true := by
  rw [List.all_eq_true]
  intro j hj
  have hh := List.all_eq_true.mp physicalHead j hj
  have tl := physicalTail
  simp only [physical, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hh tl ⊢
  refine ⟨⟨hh, by rw [fieldPort_tail j 16 (le_refl _)]; exact tl.1⟩, fun q hq => ?_⟩
  rw [fieldPort_tail j q (by have := List.mem_range'_1.mp hq; omega)]
  exact tl.2 q hq
def lookup (l h : Bool) := (List.range 16).all (fun q=>
  CodecBitSliceVerify.get (StairArchiveNativeCut.canonical l h) q == CodecBitSliceVerify.get (storage (native (if high q then h else l) (high q))) (lane q))
private theorem lookup_ok (l h : Bool) : lookup l h=true := by cases l <;> cases h <;> decide +kernel
private theorem upper_zero (l h : Bool) : (List.range' 16 105).all (fun q=>CodecBitSliceVerify.get (StairArchiveNativeCut.canonical l h) q == 0)=true := by
  cases l <;> cases h <;> decide +kernel
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
attribute [local irreducible] run wire StairArchiveNativeCut.canonical StairArchiveRelease.fieldPort CodecBitSliceVerify.get
def boundaryCols (j c : Nat) := StairArchiveNativeCut.canonical (decide (c≤j)) (decide (c≤j+1))

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowParityDirty
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run mcx chain

instance (t : Wire) (g : Aff) : Decidable (lawful t g) := by cases g <;> unfold lawful <;> infer_instance
instance (q j : Wire) (xs : Hops) : Decidable (outside q j xs) := by unfold outside; infer_instance
instance dsafe (last target src : Wire) (xs : Hops) : Decidable (safe last target src xs) := by
  cases xs with
  | nil => unfold safe; infer_instance
  | cons pair tail =>
    obtain ⟨c,b⟩ := pair
    letI := dsafe last target b tail
    unfold safe; infer_instance

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
theorem fixed (s : State) (z : ∀j∈firstSites,s.basis (base j)=false) : pullState first s=s := by
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

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 20000
attribute [local irreducible] wires domain
theorem reverse_domain (d : Bool) : ∀ q ∈ wires (TickCut.CutWindow.reverseCut d), domain q = true := by
  intro q h
  rw [domain_eq]
  exact (TickCut.CutWindow.cut_covered d).2 q h

theorem inside (n:Nat) (use:domain n=true):(16:Nat)≤n ∧ n≤1812:=by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at use
  rcases use with ⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩
  all_goals exact ⟨Nat.le_trans (by decide) lo,Nat.le_trans hi (by decide)⟩
theorem range_pool (n:Nat) (lo:16 ≤ n) (hi:n≤1812):n∈skywalkPoolWires base:=by
  have hit:=StackOB5Base.base_pool (n-16) (by omega)
  simpa only [base,Nat.sub_add_cancel lo] using hit
theorem pool_partial (d:Bool):wires (TickCut.CutWindow.reverseCut d)⊆(skywalkPoolWires base).toFinset:=by
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
open Arithmetic MappedCompressed Secp256k1 StockCanonicalRow StockStrongChain
open StairArchiveRaw WideReference ArchiveStockSuffix ArchivePortAction
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

theorem historical (b i x p:Nat) (c:SkywalkNat.State→Bool) (r:Nat)
    (labels:Encodes (value x p i b c) r):ArchiveStockRows.Chronology i x p r:=by
  intro j
  have bit:=labels ⟨j,by omega⟩
  simpa only [value,key,rawBit,j.isLt,if_true] using bit

end ECDSAAdd.Entrant.StairPacket.StockRowVector

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkPrefix
open Arithmetic MappedCompressed Secp256k1 WideReference
set_option maxRecDepth 8500
set_option maxHeartbeats 2000000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount renameProgram
def first (d:Bool):Program:=Stair44WalkRun.forward d 29
def regular (d:Bool) (s:State) (m:List Bool):State:=run (Rolling1588.Integer.regularForward base d 1 44) m s
theorem cut120 (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Rolling1588.Integer.Stage base d x p 45 (regular d s m).basis ∧
    pullState Stair44WalkMap.rest (run (first d) m a)=pullState (OB5.sig 44) (regular d s m):=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have spec:=Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p 1 44 hp0 good.nonzero odd cap (by norm_num [p]) good.small cop (by decide) s m stage
  refine ⟨spec.2,?_⟩
  have entry:=Stair44WalkRun.forward_run d 29 x good.nonzero good.small s a m stage input
  have logical:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 44 1 (by decide) (by decide) s m stage
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  rw [show 1-1=0 from rfl,init] at logical
  exact entry.trans logical

def forwardEnd (d:Bool) (n:Nat):Program:=TickCut.CutWindow.forwardCut d++Rolling1588TickGap.forward d 421 n
theorem split (d:Bool) (n:Nat):WindowWalkCosts.forward d n=first d++renameProgram Stair44WalkMap.rest (forwardEnd d n):=by
  simp only [WindowWalkCosts.forward,first,Stair44WalkRun.forward,forwardEnd,renameProgram,List.map_append,List.append_assoc]
theorem placed (d:Bool) (n x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    pullState Stair44WalkMap.rest (run (WindowWalkCosts.forward d n) m a)=
      run (forwardEnd d n) (m.drop (measurementCount (first d))) (pullState (OB5.sig 44) (regular d s m)):=by
  rw [split,run_append,run_take,run_rename _ Stair44WalkMap.rest.injective,(cut120 d x good s a m stage input).2]
end ECDSAAdd.Entrant.StairPacket.StockWalkPrefix

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg
attribute [local irreducible] run wires measurementCount wire group StairArchiveInactive.packet
set_option maxRecDepth 2600
set_option maxHeartbeats 500000

def surface : Finset Wire := ((Finset.Icc 1 84).biUnion (fun j=>wires (packet false j) ∪ wires (packet true j))) ∪ bankIds.biUnion inside
def tracks (actual ideal : State) := ∀q∈surface,q≠base 720→actual.basis q=ideal.basis q
def StockCut (c : Nat) (origin : BasisState) (r : State) : Prop :=
  r.basis (base 720)=false ∧ ∃ (X Y : Fp) (ideal : State),
    Rolling1588.CutFrame c origin X Y (pullState wire ideal) ∧ tracks r ideal

private def allowedTag (k : Nat) := !(cover k).contains (preimage k (base 720))
theorem tagged : (List.range' 1 84).all allowedTag=true := by decide +kernel
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

end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify StairArchiveNativeRows WindowParityDirty
set_option maxRecDepth 8000
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 100000
set_option linter.unusedSimpArgs false
def parity (cs : Cols) := ((List.range 16).map (get cs)).foldr (· ^^^ ·) 0
theorem matchedParity (d : Bool) :
    parity (ArchivePortAction.code d) = parity (StairArchiveNativeCut.canonical d d) := by
  cases d <;> decide +kernel
theorem region_run (d : Bool) (row : Nat) (_rb : row<63145) (m : List Bool) (s : State)
    (_data : ∀i<16,s.basis i=(get (ArchivePortAction.code d) i).testBit row) :
    run region m s = flip 16 (((parity (ArchivePortAction.code d)).testBit row) ^^
      ((parity (StairArchiveNativeCut.canonical d d)).testBit row)) s := by
  simp [region, run, matchedParity]
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

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic MappedCompressed BalancedField Secp256k1 StairArchiveRelease StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask StairField2V3RecScratch StairPhysicalLayout
set_option maxRecDepth 2200
set_option maxHeartbeats 500000

def regular (z : Wire) := !(EP.contains z) && !((futurePayload 87).contains z)
private def archiveGood (j : Nat) := (List.range 121).all (fun q => q==16 || regular (host.symm (fieldPort j q)))
private theorem portsHead :
    WindowBankCheck.banks.all (fun j => (List.range 16).all (fun q => regular (host.symm (fieldPort j q))))=true := by
  decide +kernel
private theorem portsTail :
    (List.range' 16 105).all (fun q => q==16 || regular (host.symm (fieldPort 0 q)))=true := by
  decide +kernel
private theorem portsCheck : WindowBankCheck.banks.all archiveGood=true := by
  rw [List.all_eq_true]
  intro j hj
  have hh := List.all_eq_true.mp portsHead j hj
  rw [archiveGood, List.all_eq_true]
  intro q hq
  have hq' := List.mem_range.mp hq
  by_cases lo : q < 16
  · have e := List.all_eq_true.mp hh q (List.mem_range.mpr lo)
    simp only [e, Bool.or_true]
  · have e := List.all_eq_true.mp portsTail q (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
    rw [fieldPort_tail j q (by omega)]
    exact e
private theorem cleanPort (j q : Nat) (jb : j∈bankIds) (qb : q<121) (ne : fieldPort j q≠base 720) :
    Off (host.symm (fieldPort j q)) ∧ host.symm (fieldPort j q)∉futurePayload 87 := by
  have jm : j∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using jb
  have ok := List.all_eq_true.mp (List.all_eq_true.mp portsCheck _ jm) q (List.mem_range.mpr qb)
  have eq16 : fieldPort j 16=base 720 := by
    simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at jb
    rcases jb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
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
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

-- oddten:begin SEM
section

namespace ECDSAAdd.Entrant.StairArchiveInactive
set_option maxHeartbeats 900000
set_option maxRecDepth 22000
attribute [local irreducible] StairPacket.WindowFieldCosts.opk wires preimage cover savedSites

/-- oddten: dadon's `packet_avoids` for the field group's own packets (through the record footprint). -/
theorem ot_packet_avoids (j : Nat) (hj : j∈starts10) (d second : Bool)
    (q : Wire) (save : q∈savedSites j second) :
    q∉wires (StairPacket.WindowFieldCosts.opk d (if second then j+1 else j)) :=
  fun used => packet_avoids10 j hj d second q save (StairPacket.WindowFieldCosts.ot_opk_sub d _ used)

/-- oddten: dadon's `advance`, packet := the field group's own packet. -/
theorem ot_advance (start : Nat) (hs : start∈starts10) (d second : Bool) (m : List Bool)
    (reference actual : State)
    (same : ∀ q ∉ savedSites start second, actual.basis q = reference.basis q) :
    let p := StairPacket.WindowFieldCosts.opk d (if second then start+1 else start)
    ((run p m actual).phase ^^ actual.phase) = ((run p m reference).phase ^^ reference.phase) ∧
    (∀ q ∉ savedSites start second, (run p m actual).basis q = (run p m reference).basis q) ∧
    (∀ q ∈ savedSites start second, (run p m actual).basis q = actual.basis q) := by
  let p := StairPacket.WindowFieldCosts.opk d (if second then start+1 else start)
  have unchanged := ot_packet_avoids start hs d second
  have act := Arithmetic.run_local_increment p actual reference m
    (fun q hq => same q (fun h => unchanged q h hq))
  refine ⟨act.1, ?_, fun q hq => run_preserves_outside p m actual q (unchanged q hq)⟩
  intro q keep
  by_cases used : q∈wires p
  · exact act.2 q used
  · exact (run_preserves_outside p m actual q used).trans ((same q keep).trans
      (run_preserves_outside p m reference q used).symm)

end ECDSAAdd.Entrant.StairArchiveInactive
end

section
namespace ECDSAAdd.Entrant.StairArchiveNativeCut
open Arithmetic CodecBitSliceVerify StairArchiveRelease StairArchiveSlots StairArchiveNativeRows
open StairArchiveInactive
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
attribute [local irreducible] run StairPacket.WindowFieldCosts.opk fieldHook fieldPort inputCols outputCols CodecBitSliceVerify.get savedSites

theorem ot_xor_cancel (a b c : Bool) (h : (a ^^ c)=(b ^^ c)) : a=b := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- oddten: dadon's `stage_packet` (one hook, then the field group's own packet). -/
theorem ot_stage_packet (j : Nat) (hstart : j∈starts10) (hj : j∈List.range' 1 83)
    (rev last : Bool) (row : Nat) (hr : row<63145) (m n : List Bool) (a ref : State)
    (change : frame j row (inputCols (fromStage rev last)) a)
    (out : exterior j a ref) (phase : a.phase=ref.phase)
    (entryFrame : frame j row (before rev last) ref)
    (endFrame : frame j row (after rev last)
      (run (StairPacket.WindowFieldCosts.opk (!rev) (if rev ^^ last then j+1 else j)) n ref)) :
    let c := run (fieldHook j (fromStage rev last)) m a
    let p := StairPacket.WindowFieldCosts.opk (!rev) (if rev ^^ last then j+1 else j)
    let s := run p n c
    let t := run p n ref
    s.phase=t.phase ∧ exterior j s t ∧ frame j row (inputCols (toStage rev last)) s := by
  let active := rev ^^ last
  let fromC := outputCols (fromStage rev last)
  let toC := inputCols (toStage rev last)
  let c := run (fieldHook j (fromStage rev last)) m a
  let p := StairPacket.WindowFieldCosts.opk (!rev) (if active then j+1 else j)
  have admin := StairArchiveAllPorts.field_run j hj _ row hr m a change
  have hchecks := all_checks rev last
  change (agrees active false fromC (before rev last) &&
    agrees active false toC (after rev last) && agrees active true fromC toC)=true at hchecks
  simp only [Bool.and_eq_true] at hchecks
  have same : ∀ z∉savedSites j active, c.basis z=ref.basis z := by
    intro z hz
    by_cases hz' : z∈inside j
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz'
      have hh : q∉held active := fun h => hz ((held_at j hj active q hq).mpr h)
      exact (admin.2.1 q hq).trans ((congrArg (fun v : Nat => v.testBit row)
        (column _ _ _ _ hchecks.1.1 q hq (decide_eq_false hh))).trans (entryFrame q hq).symm)
    · exact (admin.2.2 z hz').trans (out z hz')
  have body :
      ((run p n c).phase ^^ c.phase) = ((run p n ref).phase ^^ ref.phase) ∧
      (∀ z ∉ savedSites j active, (run p n c).basis z = (run p n ref).basis z) ∧
      (∀ z ∈ savedSites j active, (run p n c).basis z = c.basis z) :=
    ot_advance j hstart (!rev) active n ref c same
  have cphase : c.phase=ref.phase := admin.1.trans phase
  change (run p n c).phase = (run p n ref).phase ∧ exterior j (run p n c) (run p n ref) ∧ frame j row toC (run p n c)
  refine ⟨?_, ?_, ?_⟩
  · have v := body.1
    change ((run p n c).phase ^^ c.phase) = ((run p n ref).phase ^^ ref.phase) at v
    rw [cphase] at v
    exact ot_xor_cancel _ _ _ v
  · intro z hz
    apply body.2.1 z
    intro h
    rw [held_eq j hj active] at h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact hz (Finset.mem_image.mpr ⟨q,held_bounded _ hq,rfl⟩)
  · intro q hq
    by_cases hold : q∈held active
    · exact (body.2.2 _ ((held_at j hj active q hq).mpr hold)).trans
        ((admin.2.1 q hq).trans (congrArg (fun v : Nat => v.testBit row)
          (column _ _ _ _ hchecks.2 q hq (decide_eq_true hold))))
    · exact (body.2.1 _ (fun z => hold ((held_at j hj active q hq).mp z))).trans
        ((endFrame q hq).trans (congrArg (fun v : Nat => v.testBit row)
          (column _ _ _ _ hchecks.1.2 q hq (decide_eq_false hold))).symm)

end ECDSAAdd.Entrant.StairArchiveNativeCut
end

section
namespace ECDSAAdd.Entrant.StairArchiveTen
open CodecBitSliceVerify StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairPacket.WindowFieldCosts

def otapeS (j : Nat) (rev : Bool) (m : List Bool) := (tapeA j rev m).drop (measurementCount (ofirst j rev))
def otapeB (j : Nat) (rev : Bool) (m : List Bool) := (otapeS j rev m).drop (measurementCount (fieldHook j (shift rev)))
def otapeL (j : Nat) (rev : Bool) (m : List Bool) := (otapeB j rev m).drop (measurementCount (osecond j rev))
def orefMiddle (j : Nat) (rev : Bool) (m : List Bool) (s : State) :=
  run (ofirst j rev) (tapeA j rev m) s
def orefExit (j : Nat) (rev : Bool) (m : List Bool) (s : State) :=
  run (osecond j rev) (otapeB j rev m) (orefMiddle j rev m s)

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

/-- oddten: dadon's `ten_run` around the field group's own packets. -/
theorem ot_ten_run (j : Nat) (hs : j∈starts10) (hj : j∈List.range' 1 83)
    (rev : Bool) (row : Nat) (hr : row<63145) (m : List Bool) (a r : State)
    (arch : frame j row (inputCols (enter rev)) a)
    (same : exterior j a r) (ph : a.phase = r.phase)
    (before_ : frame j row (canonical (!rev) (!rev)) r)
    (middle_ : frame j row middle (orefMiddle j rev m r))
    (after_ : frame j row (canonical rev rev) (orefExit j rev m r)) :
    let actual := run (oten j rev) m a
    let final := orefExit j rev m r
    actual.phase=final.phase ∧ exterior j actual final ∧ frame j row (outputCols (leave rev)) actual := by
  let a0 := run (fieldHook j (enter rev)) m a
  let a1 := run (ofirst j rev) (tapeA j rev m) a0
  let a2 := run (fieldHook j (shift rev)) (otapeS j rev m) a1
  let a3 := run (osecond j rev) (otapeB j rev m) a2
  let a4 := run (fieldHook j (leave rev)) (otapeL j rev m) a3
  have f : a1.phase=(orefMiddle j rev m r).phase ∧ exterior j a1 (orefMiddle j rev m r) ∧
      frame j row (inputCols (shift rev)) a1 := by
    simpa only [fromStage, toStage, before, after, Bool.false_eq_true, if_false, Bool.xor_false,
      ofirst, orefMiddle] using ot_stage_packet j hs hj rev false row hr m (tapeA j rev m) a r
        arch same ph before_ (by simpa only [after, Bool.false_eq_true, if_false, Bool.xor_false, ofirst, orefMiddle] using middle_)
  have z : a3.phase=(orefExit j rev m r).phase ∧ exterior j a3 (orefExit j rev m r) ∧
      frame j row (inputCols (leave rev)) a3 := by
    have eq : (if rev ^^ true then j+1 else j) = (if rev then j else j+1) := by cases rev <;> rfl
    simpa only [fromStage, toStage, before, after, if_true, eq, osecond, orefExit] using
      ot_stage_packet j hs hj rev true row hr (otapeS j rev m) (otapeB j rev m) a1 (orefMiddle j rev m r)
        f.2.2 f.2.1 f.1 middle_ (by simpa only [after, if_true, eq, osecond, orefExit] using after_)
  have last := StairArchiveAllPorts.field_run j hj (leave rev) row hr (otapeL j rev m) a3 z.2.2
  have shape : run (oten j rev) m a = a4 := by
    simp only [oten, run_append, run_take]
    rfl
  rw [shape]
  exact ⟨last.1.trans z.1, fun q hq => (last.2.2 q hq).trans (z.2.1 q hq), last.2.1⟩

end ECDSAAdd.Entrant.StairArchiveTen
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify WindowFieldCosts

attribute [local irreducible] run StairArchiveInactive.packet StairArchiveRelease.fieldHook
  WindowFieldCosts.ofirst WindowFieldCosts.osecond WindowFieldCosts.oten
  StairArchiveRelease.fieldPort StairArchiveRelease.outputCols StairArchiveRelease.inputCols
  StairArchiveNativeCut.canonical CodecBitSliceVerify.get
set_option maxRecDepth 1200
set_option maxHeartbeats 360000
set_option linter.constructorNameAsVariable false
/-- oddten: dadon's `ten_masked` around the field group's own packets. -/
theorem ot_ten_masked (j : Nat) (hs : j ∈ starts10) (hj : j ∈ List.range' 1 83)
    (rev : Bool) (row : Nat) (hr : row < 63145) (m : List Bool) (a r : State)
    (other : Finset Wire) (apart : ∀ q ∈ inside j, q ∉ other)
    (ha : avoids (ofirst j rev) other) (hb : avoids (osecond j rev) other)
    (arch : frame j row (inputCols (enter rev)) a) (same : offBanks (bank j) other a r)
    (ph : a.phase = r.phase)
    (before_ : frame j row (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j row middle (orefMiddle j rev m r))
    (after_ : frame j row (StairArchiveNativeCut.canonical rev rev) (orefExit j rev m r)) :
    let next := run (oten j rev) m a
    let final := orefExit j rev m r
    next.phase = final.phase ∧ offBanks (bank j) other next final ∧
      frame j row (outputCols (leave rev)) next := by
  let shadow := mask other a r
  have mid : orefMiddle j rev m shadow = mask other a (orefMiddle j rev m r) := by
    exact mask_run (ofirst j rev) other _ a r ha
  have fin : orefExit j rev m shadow = mask other a (orefExit j rev m r) := by
    unfold orefExit
    rw [mid, mask_run]
    exact hb
  have outer : exterior j a shadow := by
    intro q hq
    by_cases qmem : q ∈ other
    · simp [shadow, mask, qmem]
    · have qbank : q ∉ bank j := by
        intro bad
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp bad
        exact hq (Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega),rfl⟩)
      simpa [shadow,mask,qmem] using same q qbank qmem
  have mm : frame j row middle (orefMiddle j rev m shadow) := mid ▸ mask_frame _ _ _ _ _ _ apart middle_
  have ff : frame j row (StairArchiveNativeCut.canonical rev rev) (orefExit j rev m shadow) := fin ▸ mask_frame _ _ _ _ _ _ apart after_
  have result := ot_ten_run j hs hj rev row hr m a shadow arch outer ph
    (mask_frame _ _ _ _ _ _ apart before_) mm ff
  obtain ⟨phase,ext,stored⟩ := result
  refine ⟨?_,?_,stored⟩
  · rw [fin] at phase
    exact phase
  · intro q notbank notother
    by_cases qin : q ∈ inside j
    · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp qin
      have lower : 16 ≤ k := by
        by_contra! h
        exact notbank (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr h, rfl⟩)
      have upper := Finset.mem_range.mp hk
      have kn : k ∈ List.range' 16 105 := List.mem_range'_1.mpr ⟨lower,by omega⟩
      have col := beq_iff_eq.mp (List.all_eq_true.mp (restored rev) k kn)
      rw [stored k hk,after_ k hk,col]
    · have x := ext q qin
      rw [fin] at x
      simpa [mask, notother] using x

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify WindowFieldCosts
set_option maxRecDepth 1600
set_option maxHeartbeats 400000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run packet fieldPort StairArchiveNativeCut.canonical inputCols outputCols CodecBitSliceVerify.get
attribute [local irreducible] inside StairArchiveRelease.fieldHook WindowFieldCosts.ofirst WindowFieldCosts.osecond
  WindowFieldCosts.oten WindowFieldCosts.opk WindowFieldCosts.ogroup WindowFieldCosts.group allBanks wires

private theorem ot_native_safe (j k : Nat) (hj : j∈bankIds) (which : k=j ∨ k=j+1) (d : Bool) :
    avoids (opk d k) (others j) :=
  fun q ho used => native_safe j k hj which d q ho (WindowFieldCosts.ot_opk_sub d k used)

/-- oddten: dadon's `stepTen` around the field group's own packets. -/
theorem ot_stepTen (j : Nat) (hj : j∈bankIds) (rows : Nat→Nat) (code : Nat→Cols) (rev : Bool)
    (bound : rows j < 63145) (m : List Bool) (a r : State) (h : Fits rows code a r)
    (active : code j=inputCols (enter rev))
    (before_ : frame j (rows j) (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j (rows j) middle (orefMiddle j rev m r))
    (after_ : frame j (rows j) (StairArchiveNativeCut.canonical rev rev) (orefExit j rev m r)) :
    Fits rows (update code j (outputCols (leave rev))) (run (oten j rev) m a) (orefExit j rev m r) := by
  have ⟨hs,hr⟩ := geometry hj
  have fa : avoids (ofirst j rev) (others j) := by
    rw [ofirst]; apply ot_native_safe _ _ hj; cases rev <;> simp
  have sa : avoids (osecond j rev) (others j) := by
    rw [osecond]; apply ot_native_safe _ _ hj; cases rev <;> simp
  have ea : avoids (oten j rev) (others j) := by
    rw [oten]; exact append_safe (hook_safe j hj _)
      (append_safe fa (append_safe (hook_safe j hj _) (append_safe sa (hook_safe j hj _))))
  have same : offBanks (bank j) (others j) a r := by
    intro q a0 a1; apply h.outside; rw [decompose j hj,Finset.mem_union]; exact fun hit => hit.elim a0 a1
  have result := ot_ten_masked j hs hr rev (rows j) bound m a r (others j) (apart hj) fa sa
    (beforeFrame j hj rows code rev a r h active (apart hj) before_ (field_inj j hr)) same h.phase before_ middle_ after_
  refine ⟨result.1,?_,?_⟩
  · intro q off
    rw [decompose j hj,Finset.mem_union] at off
    exact result.2.1 q (fun a=>off (Or.inl a)) (fun b=>off (Or.inr b))
  · intro k hk i hi
    by_cases eq : k=j
    · subst k
      simpa only [update,if_pos rfl] using result.2.2 i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega))
    · have ho : fieldPort k i∈others j := Finset.mem_biUnion.mpr
        ⟨k,Finset.mem_erase.mpr ⟨eq,hk⟩,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
      rw [run_preserves_outside _ m a _ (ea _ ho)]
      simpa only [update,if_neg eq] using h.bytes k hk i hi

theorem ot_groupSafe (d : Bool) (j n : Nat) (valid : nativeRanges j n) : avoids (ogroup d j n) allBanks :=
  fun q hq used => groupSafe d j n valid q hq (WindowFieldCosts.ot_ogroup_sub d j n used)

end ECDSAAdd.Entrant.StairPacket.WindowFieldMask
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldHistory
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairField2V3Seg
attribute [local irreducible] run wires rawCol CodecBitSliceVerify.get SkywalkTrace.next
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1400
set_option maxHeartbeats 400000

/-- oddten: `cut_byte` for any word code of the field registers (the bytes are history letters). -/
theorem ot_cut_byte (w : Fp → Nat) (cut j x row : Nat) (positive : 1≤j) (bound : j+2≤102)
    (rowBound : row<63145) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (tr : TraceOK x origin) (record : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (X Y : Fp) (s : State) (fr : RouteA.Rolling1588.CutFrame w w cut origin X Y s) (hi : Bool) (q : Fin 10) :
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
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField Rolling1588 StairArchiveRaw StairArchiveTrace
open CodecBitSliceVerify StairArchiveNativeRows StairArchiveNativeCut StairArchiveRelease
open WindowFieldMask ArchiveFieldScratch StairField2V3Seg
set_option maxRecDepth 4000
set_option maxHeartbeats 600000
attribute [local irreducible] run wire StairArchiveNativeCut.canonical StairArchiveRelease.fieldPort CodecBitSliceVerify.get

/-- oddten: `observed` for any word code of the field registers. -/
theorem oobserved (w : Fp → Nat) (j c x row : Nat) (hj : j∈WindowBankCheck.banks) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (X Y : Fp) (ideal actual : State) (cf : RouteA.Rolling1588.CutFrame w w c origin X Y (pullState wire ideal))
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
      have byte := WindowFieldHistory.ot_cut_byte w c j x row jBounds.1 jBounds.2 rb origin ctx tr history X Y
        (pullState wire ideal) cf (high q) (lane q)
      change ideal.basis (wire (histPort j q))=_ at byte
      rw [byte]
      have col := beq_iff_eq.mp (List.all_eq_true.mp (lookup_ok (decide (c≤j)) (decide (c≤j+1))) q (List.mem_range.mpr low))
      unfold boundaryCols; rw [col]
      cases high q <;> simp
    · have member : q∈List.range' 17 104 := List.mem_range'_1.mpr ⟨by omega,by omega⟩
      have loc := beq_iff_eq.mp (List.all_eq_true.mp geometry.2 q member)
      rw [loc]
      have clean := RouteA.Rolling1588.cutFrame_zero_region w w c origin ctx X Y _ cf (Placement5.H (8+(q-17)))
        (Or.inr (Placement5.H_region (8+(q-17)) (by omega)))
      change ideal.basis (wire (base (Placement5.H (8+(q-17)))))=false at clean
      have zero := beq_iff_eq.mp (List.all_eq_true.mp (upper_zero (decide (c≤j)) (decide (c≤j+1))) q
        (List.mem_range'_1.mpr ⟨by omega,by omega⟩))
      simp only [boundaryCols,zero,clean,Nat.zero_testBit]
end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run wires measurementCount StairArchiveInactive.packet WindowFieldCosts.opk
  WindowFieldCosts.ogroup

/-- the word code of the field registers at cut `c` (odd words on cuts 1..85). -/
def oddCutWord (c : Nat) : Fp → Nat := if 1≤c ∧ c≤85 then P1Life.oddWord else centerWord
theorem oddCutWord_odd {c : Nat} (h1 : 1≤c) (h2 : c≤85) : oddCutWord c=P1Life.oddWord := if_pos ⟨h1,h2⟩
theorem oddCutWord_center {c : Nat} (h : c<1 ∨ 85<c) : oddCutWord c=centerWord := if_neg (by omega)

/-- `StockCut` with the cut's word code. -/
def OCut (c : Nat) (origin : BasisState) (r : State) : Prop :=
  r.basis (base 720)=false ∧ ∃ (X Y : Fp) (ideal : State),
    RouteA.Rolling1588.CutFrame (oddCutWord c) (oddCutWord c) c origin X Y (pullState wire ideal) ∧ tracks r ideal

theorem ocut_of_stock (c : Nat) (hc : c<1 ∨ 85<c) (origin : BasisState) (r : State)
    (h : StockCut c origin r) : OCut c origin r := by
  obtain ⟨zero,X,Y,ideal,cf,view⟩ := h
  refine ⟨zero,X,Y,ideal,?_,view⟩
  rw [oddCutWord_center hc]
  exact cf

/-- division-kernel packet `k` of the family between its cut frames. -/
theorem pk_frame_div (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple (RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin X Y)
      (oddPk true k)
      (fun state => let V := directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord (k+1)) (oddCutWord (k+1)) (k+1) origin V.1 V.2 state) := by
  rcases (show (1≤k ∧ k<84) ∨ k=84 ∨ 84<k by omega) with ⟨h1,h2⟩|h|h
  · rw [oddPk_mid true k h1 h2,oddCutWord_odd h1 (by omega),oddCutWord_odd (c := k+1) (by omega) (by omega)]
    exact RouteA.Rolling1588.packet_cut_frame true k lo (by omega) (fun _ => by omega) origin ctx enabled X Y
  · subst h
    rw [oddPk_end,oddCutWord_odd (c := 84) (by omega) (by omega),oddCutWord_odd (c := 84+1) (by omega) (by omega)]
    have h0eq := WindowFieldCosts.half760OddLoan_zero_eq true
    intro state records input
    have raw := RouteA.Rolling1588.cut_window_frame P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord 84 85 84 (by decide) origin X Y _ _
      (OddFullPass.P1LifeLoan.basePacket true 0 84) (ECDSAAdd.Entrant.Rolling1588.otherEncodeCut_step base 84 102)
      (ECDSAAdd.Entrant.Rolling1588.otherEncodeCut_body_disjoint 84 84 (by decide) origin ctx _
        (by
          have hsub : wires (OddFullPass.P1LifeLoan.basePacket true 0 84) ⊆ wires (ECDSAAdd.Entrant.Rolling1588.basePacket true 84) := by
            have hp := OddFullPass.P1LifeLoan.packet_wires_sub true 0 84 (by decide) (by decide)
            rw [OddFullPass.P1LifeLoan.packet,StairGroups.packet_zero,ECDSAAdd.Entrant.Rolling1588.packet,
              renameProgram_support,renameProgram_support] at hp
            intro q hq
            have hi := Finset.mem_image.mp (hp (Finset.mem_image.mpr ⟨q,hq,rfl⟩))
            obtain ⟨v,hv,eq⟩ := hi; exact (Equiv.injective _ eq) ▸ hv
          exact hsub.trans (ECDSAAdd.Entrant.Rolling1588.basePacket_read_support true 84 (by decide))))
      (fun current tape frame => by
        have hcEq : ∀ a b, OddFullPass.P1LifeLoan.cell true 0 84 a b = RouteA.Rolling1588.cell true 84 a b := by
          intro a b; simp only [OddFullPass.P1LifeLoan.cell,RouteA.Rolling1588.cell,
            OddFullPass.P1LifeLoan.halfWindow,RouteA.Rolling1588.halfWindow,RouteA.Rolling1588.halfWindowWith,if_true,h0eq]
        have normalized : RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
            (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt true (History5.historyMap base (5*84))) origin X Y current := by
          simpa [ECDSAAdd.Entrant.Rolling1588.encodeGroup] using frame
        let Frame (k : Nat) (V : Fp×Fp) :=
          RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
            (ECDSAAdd.Entrant.Rolling1588.stageCodeAt true k (History5.historyMap base (5*84))) origin V.1 V.2
        have opening (V : Fp×Fp) : ECDSAAdd.Entrant.Rolling1588.StateTriple
            (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
              (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt true (History5.historyMap base (5*84))) origin V.1 V.2)
            (ECDSAAdd.Entrant.Rolling1588.onPacket 84 ECDSAAdd.Entrant.Rolling1588.stageOpen) (Frame 0 V) :=
          fun s r h => RouteA.Rolling1588.regular_open_frame P1Life.oddWord P1Life.oddWord true 84 (by decide) origin ctx V.1 V.2 s r h
        have step (k logical physical : Nat) (hk : k<3) (used : (logical,physical)∈ECDSAAdd.Entrant.Rolling1588.activeSlots true k) (V : Fp×Fp) :
            ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame k V) (RouteA.Rolling1588.cell true 84 physical 2)
              (Frame k (ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin logical V)) :=
          fun s r h => RouteA.Rolling1588.regular_cell_frame true 84 k logical physical (by decide) hk used origin ctx enabled V.1 V.2 s r h
        have transfer (k : Nat) (hk : k<2) (V : Fp×Fp) :
            ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame k V)
              (ECDSAAdd.Entrant.Rolling1588.onPacket 84 (ECDSAAdd.Entrant.Rolling1588.stageTransition true k)) (Frame (k+1) V) :=
          fun s r h => RouteA.Rolling1588.regular_transition_frame P1Life.oddWord P1Life.oddWord true 84 k (by decide) hk origin ctx V.1 V.2 s r h
        have closing (V : Fp×Fp) : ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame 2 V)
            (ECDSAAdd.Entrant.Rolling1588.onPacket 84 ECDSAAdd.Entrant.Rolling1588.stageClose)
            (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
              (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt false (History5.historyMap base (5*84))) origin V.1 V.2) :=
          fun s r h => RouteA.Rolling1588.regular_close_frame P1Life.oddWord P1Life.oddWord true 84 (by decide) origin ctx V.1 V.2 s r h
        let V1 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 0 (X,Y)
        let V2 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 1 V1
        let V3 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 2 V2
        let V4 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 3 V3
        let V5 := ECDSAAdd.Entrant.Rolling1588.regularStep true 84 origin 4 V4
        have hres := (opening (X,Y)).seq
          ((step 0 0 3 (by decide) (by decide) (X,Y)).seq
          ((step 0 1 4 (by decide) (by decide) V1).seq
          ((transfer 0 (by decide) V2).seq
          ((step 1 2 4 (by decide) (by decide) V2).seq
          ((step 1 3 3 (by decide) (by decide) V3).seq
          ((transfer 1 (by decide) V4).seq
          ((step 2 4 4 (by decide) (by decide) V4).seq (closing V5))))))))
        have hstep := hres current tape normalized
        rw [show V5 = ECDSAAdd.Entrant.Rolling1588.regularPayload true 84 origin (X,Y) from by
              simp only [V5,V4,V3,V2,V1,ECDSAAdd.Entrant.Rolling1588.regularPayload,if_true],
            ECDSAAdd.Entrant.Rolling1588.regularPayload_eq true 84 (by decide) origin enabled] at hstep
        simpa only [OddFullPass.P1LifeLoan.basePacket,hcEq,ECDSAAdd.Entrant.Rolling1588.stageOpen,
          ECDSAAdd.Entrant.Rolling1588.stageClose,ECDSAAdd.Entrant.Rolling1588.stageTransition,
          if_true,if_false,List.append_assoc,ECDSAAdd.Entrant.Rolling1588.encodeGroup] using hstep)
      state records input
    have same := Replay5.placed_eq (Placement5.pi 84) (OddFullPass.P1LifeLoan.basePacket true 0 84)
      (fun q hq => Placement5.pi_outside 84 q (by decide) hq) state records
      (RouteA.Rolling1588.cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
      (RouteA.Rolling1588.cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
    change run (OddFullPass.P1LifeLoan.packet true 0 84) records state = run (OddFullPass.P1LifeLoan.basePacket true 0 84) records state at same
    rw [same]; exact raw
  · rw [oddPk_std true k h,oddCutWord_center (c := k) (by omega),oddCutWord_center (c := k+1) (by omega)]
    exact ECDSAAdd.Entrant.Rolling1588.packet_cut_frame true k lo (by omega) origin ctx enabled X Y

/-- multiplication-kernel packet `k` of the family between its cut frames. -/
theorem pk_frame_mul (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple (RouteA.Rolling1588.CutFrame (oddCutWord (k+1)) (oddCutWord (k+1)) (k+1) origin X Y)
      (oddPk false k)
      (fun state => let V := directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2 state) := by
  rcases (show (1≤k ∧ k<84) ∨ k=84 ∨ 84<k by omega) with ⟨h1,h2⟩|h|h
  · rw [oddPk_mid false k h1 h2,oddCutWord_odd (c := k+1) (by omega) (by omega),oddCutWord_odd h1 (by omega)]
    exact RouteA.Rolling1588.packet_cut_frame false k lo (by omega) (fun e => absurd e Bool.false_ne_true) origin ctx enabled X Y
  · subst h
    rw [oddPk_end,oddCutWord_odd (c := 84+1) (by omega) (by omega),oddCutWord_odd (c := 84) (by omega) (by omega)]
    have h0eq : OddFullPass.P1LifeLoan.packet false 0 84 = RouteA.Rolling1588.packet false 84 := by
      have hh := WindowFieldCosts.half760OddLoan_zero_eq false
      simp only [OddFullPass.P1LifeLoan.packet,RouteA.Rolling1588.packet,
        OddFullPass.P1LifeLoan.basePacket,RouteA.Rolling1588.basePacket,
        OddFullPass.P1LifeLoan.cell,RouteA.Rolling1588.cell,
        OddFullPass.P1LifeLoan.halfWindow,RouteA.Rolling1588.halfWindow,RouteA.Rolling1588.halfWindowWith,
        hh,Bool.false_eq_true,if_false,if_true]
    rw [h0eq]
    exact RouteA.Rolling1588.packet_cut_frame false 84 (by decide) (by decide) (fun e => absurd e Bool.false_ne_true) origin ctx enabled X Y
  · rw [oddPk_std false k h,oddCutWord_center (c := k+1) (by omega),oddCutWord_center (c := k) (by omega)]
    exact ECDSAAdd.Entrant.Rolling1588.packet_cut_frame false k lo (by omega) origin ctx enabled X Y

private theorem ofield_cut_frame_mul' (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin X Y)
      (PacketSequence.program false (oddPk false) j n)
      (fun state => let V := PacketSequence.payload false (fun k V => directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin V.1 V.2 state) :=
  RouteA.Rolling1588.route_cut_sequence_frame false (oddPk false)
    (fun k V => directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) 85
    (fun k hk kb V => pk_frame_mul k hk (by omega) origin ctx enabled V.1 V.2) j n first bound (X,Y)

/-- the multiplication field packets `j+n-1..j` between cut frames. -/
theorem ofield_cut_frame_mul (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin X Y)
      (PacketSequence.program false (oddPk false) j n)
      (fun state => let V := Replay5.groupsPayload false origin j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin V.1 V.2 state) :=
  ofield_cut_frame_mul' j n first bound origin ctx enabled X Y

/-- the division packet law in the exact shape `route_cut_sequence_frame` instantiates (payload as a redex). -/
private theorem lawDiv (k : Nat) (hk : 1≤k) (kb : k<85) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (V : Fp×Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      ((fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) (if true then k else k+1) V)
      (oddPk true k)
      ((fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) (if true then k+1 else k)
        ((fun k (V : Fp×Fp) => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) k V)) := by
  have h : (fun k (V : Fp×Fp) => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) k V =
      directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (V.1,V.2) := rfl
  rw [h]
  exact pk_frame_div k hk (by omega) origin ctx enabled V.1 V.2

private theorem ofield_cut_frame_div' (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin X Y)
      (PacketSequence.program true (oddPk true) j n)
      (fun state => let V := PacketSequence.payload true (fun k V => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V) j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin V.1 V.2 state) :=
  RouteA.Rolling1588.route_cut_sequence_frame true (oddPk true)
    (fun k (V : Fp×Fp) => directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun k (V : Fp×Fp) => RouteA.Rolling1588.CutFrame (oddCutWord k) (oddCutWord k) k origin V.1 V.2) 85
    (fun k hk kb V => lawDiv k hk kb origin ctx enabled V) j n first bound (X,Y)

/-- the division field packets `j..j+n-1` between cut frames. -/
theorem ofield_cut_frame_div (j n : Nat) (first : 1≤j) (bound : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame (oddCutWord j) (oddCutWord j) j origin X Y)
      (PacketSequence.program true (oddPk true) j n)
      (fun state => let V := Replay5.groupsPayload true origin j n (X,Y)
        RouteA.Rolling1588.CutFrame (oddCutWord (j+n)) (oddCutWord (j+n)) (j+n) origin V.1 V.2 state) :=
  ofield_cut_frame_div' j n first bound origin ctx enabled X Y

/-- the odd field packets 1..84 run directly between odd-word cut frames at cuts 1 and 85. -/
theorem ofield_cut_frame_odd (d : Bool) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400)=true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if d then 1 else 85) origin X Y)
      (PacketSequence.program d (oddPk d) 1 84)
      (fun state => let V := Replay5.groupsPayload d origin 1 84 (X,Y)
        RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if d then 85 else 1) origin V.1 V.2 state) := by
  have c1 : oddCutWord 1=P1Life.oddWord := oddCutWord_odd (by decide) (by decide)
  have c85 : oddCutWord (1+84)=P1Life.oddWord := oddCutWord_odd (by decide) (by decide)
  cases d
  · simpa only [Bool.false_eq_true,if_false,c1,c85] using
      ofield_cut_frame_mul 1 84 (by decide) (by decide) origin ctx enabled X Y
  · simpa only [if_true,c1,c85] using
      ofield_cut_frame_div 1 84 (by decide) (by decide) origin ctx enabled X Y

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 2600
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run wires measurementCount wire group StairArchiveInactive.packet WindowFieldCosts.opk
  WindowFieldCosts.ogroup

theorem ot_opk_map (d : Bool) (k : Nat) : opk d k=renameProgram wire (oddPk d k) := by
  unfold opk
  calc
    _ = renameProgram StairArchiveInactive.host (renameProgram (OB5.sig 511) (oddPk d k)) :=
      StairArchiveInactive.hosts_eq _ _ _
    _ = _ := by rw [renameProgram_comp]; unfold wire; rfl

/-- oddten: dadon's `step` for the field group's own packet, multiplication kernel (packet `k`: cut `k+1` to cut `k`). -/
theorem ostep_mul (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut (k+1) origin r) :
    OCut k origin (run (opk false k) m r) := by
  have uses : ∀ q∈wires (opk false k), q∈surface ∧ q≠base 720 :=
    fun q h => packetUses false k lo hi (WindowFieldCosts.ot_opk_sub false k h)
  obtain ⟨zero,X,Y,b,fr,match_⟩ := initial
  obtain ⟨same,afterZero⟩ := follow _ m r b match_ zero uses
  have actual := pk_frame_mul k lo hi origin ctx enabled X Y _ m fr
  refine ⟨afterZero,(directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).1,
    (directionalPayload true (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).2,
    run (opk false k) m b,?_,same⟩
  rw [ot_opk_map,run_rename wire injective]; exact actual.2

/-- oddten: dadon's `step` for the field group's own packet, division kernel (packet `k`: cut `k` to cut `k+1`). -/
theorem ostep_div (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut k origin r) :
    OCut (k+1) origin (run (opk true k) m r) := by
  have uses : ∀ q∈wires (opk true k), q∈surface ∧ q≠base 720 :=
    fun q h => packetUses true k lo hi (WindowFieldCosts.ot_opk_sub true k h)
  obtain ⟨zero,X,Y,b,fr,match_⟩ := initial
  obtain ⟨same,afterZero⟩ := follow _ m r b match_ zero uses
  have actual := pk_frame_div k lo hi origin ctx enabled X Y _ m fr
  refine ⟨afterZero,(directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).1,
    (directionalPayload false (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X,Y)).2,
    run (opk true k) m b,?_,same⟩
  rw [ot_opk_map,run_rename wire injective]; exact actual.2

/-- oddten: dadon's `step` for the field group's own packet. -/
theorem ostep (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut (if d then k else k+1) origin r) :
    OCut (if d then k+1 else k) origin (run (opk d k) m r) := by
  cases d
  · exact ostep_mul k lo hi origin ctx enabled r m initial
  · exact ostep_div k lo hi origin ctx enabled r m initial

/-- oddten: dadon's `selected` for the field group's own packets. -/
theorem oselected (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (enabled : origin (base 2400)=true)
    (r : State) (m : List Bool) (initial : OCut (if d then j else j+n) origin r) :
    OCut (if d then j+n else j) origin (run (ogroup d j n) m r) := by
  rw [ogroup]
  induction n generalizing j r m with
  | zero =>
    simpa only [PacketSequence.program,run,Nat.add_zero] using initial
  | succ n ih =>
    cases d with
    | false =>
      simp only [Bool.false_eq_true,if_false] at initial ⊢
      simp only [PacketSequence.program,Bool.false_eq_true,if_false,run_append,run_take]
      apply ostep false j lo (by omega) origin ctx enabled
      apply ih (j+1) (by omega) (by omega) r m
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using initial
    | true =>
      simp only [if_true] at initial ⊢
      simp only [PacketSequence.program,if_true,run_append,run_take]
      have first := ostep true j lo (by omega) origin ctx enabled r m initial
      have last := ih (j+1) (by omega) (by omega) _ (m.drop (measurementCount (opk true j))) first
      simpa only [if_true,Nat.add_assoc,Nat.add_comm 1 n] using last

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 1600
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run group ten measurementCount packet surface ArchiveStockRows.Chronology
  Rolling1588.CutFrame StairArchiveNativeCut.canonical WindowFieldCosts.opk

theorem osee (j c x row : Nat) (hj : j∈bankIds) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (r : State) (state : OCut c origin r) : frame j row (boundaryCols j c) r := by
  obtain ⟨zero,X,Y,model,fr,view⟩ := state
  have list : j∈WindowBankCheck.banks := by simpa [WindowBankCheck.banks,bankIds] using hj
  apply oobserved (oddCutWord c) j c x row list rb origin ctx tr history X Y model r fr zero
  intro q inside_ off
  exact view q (by rw [surface];exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,inside_⟩)) off

/-- oddten: dadon's `pair_cuts` for the field group's own packets. -/
theorem opair_cuts (d : Bool) (j x row : Nat) (hj : j∈bankIds) (rb : row<63145) (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p row)
    (r : State) (m : List Bool) (state : OCut (if d then j else j+2) origin r) :
    (frame j row (StairArchiveNativeCut.canonical d d) r ∧ frame j row middle (orefMiddle j (!d) m r) ∧
      frame j row (StairArchiveNativeCut.canonical (!d) (!d)) (orefExit j (!d) m r)) ∧
    OCut (if d then j+2 else j) origin (orefExit j (!d) m r) := by
  have bounds : 1≤j ∧ j+1≤84 := by simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at hj; omega
  let observe := fun c t (h : OCut c origin t) => osee j c x row hj rb origin ctx tr history t h
  have lo : boundaryCols j j=StairArchiveNativeCut.canonical true true := by simp [boundaryCols]
  have mid : boundaryCols j (j+1)=middle := by simp [boundaryCols,middle]
  have hi : boundaryCols j (j+2)=StairArchiveNativeCut.canonical false false := by simp [boundaryCols]
  cases d
  · have one : OCut (j+1) origin (orefMiddle j true m r) :=
      ostep false (j+1) (by omega) (by omega) origin ctx en r _ state
    have two : OCut j origin (orefExit j true m r) :=
      ostep false j (by omega) (by omega) origin ctx en _ _ one
    exact ⟨⟨hi ▸ observe _ _ state,mid ▸ observe _ _ one,lo ▸ observe _ _ two⟩,two⟩
  · have one : OCut (j+1) origin (orefMiddle j false m r) :=
      ostep true j (by omega) (by omega) origin ctx en r _ state
    have two : OCut (j+2) origin (orefExit j false m r) :=
      ostep true (j+1) (by omega) (by omega) origin ctx en _ _ one
    exact ⟨⟨lo ▸ observe _ _ state,mid ▸ observe _ _ one,hi ▸ observe _ _ two⟩,two⟩

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open CodecBitSliceVerify WindowFieldMask WindowFieldCosts ArchiveFieldScratch
attribute [local irreducible] run measurementCount WindowFieldCosts.ogroup WindowFieldCosts.oten orefExit
  inputCols outputCols StairArchiveNativeCut.canonical enter leave WindowFieldCosts.opk
set_option linter.constructorNameAsVariable false

def oemitted (d : Bool) : Leg → Program
  | .native j n => ogroup d j n
  | .paired j => oten j (!d)
def ostock (d : Bool) (m : List Bool) (r : State) : Leg → State
  | .native j n => run (ogroup d j n) m r
  | .paired j => orefExit j (!d) m r
def onextTape (d : Bool) (l : Leg) (m : List Bool) := m.drop (measurementCount (oemitted d l))
def oconcatenate (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => oemitted d l ++ oconcatenate d ls
def odestination (d : Bool) : List Leg → List Bool → State → State
  | [],_,r => r
  | l::ls,m,r => odestination d ls (onextTape d l m) (ostock d m r l)
def OCuts (d : Bool) (row : Nat→Nat) (m : List Bool) (r : State) : Leg → Prop
  | .native _ _ => True
  | .paired j => frame j (row j) (StairArchiveNativeCut.canonical d d) r ∧
      frame j (row j) middle (orefMiddle j (!d) m r) ∧ frame j (row j) (StairArchiveNativeCut.canonical (!d) (!d)) (orefExit j (!d) m r)
def ONativeTrail (d : Bool) (row : Nat→Nat) : List Leg → List Bool → State → Prop
  | [],_,_ => True
  | l::ls,m,r => OCuts d row m r l ∧ ONativeTrail d row ls (onextTape d l m) (ostock d m r l)

theorem otravel (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (ls : List Leg) (m : List Bool) (a r : State) (c : Nat→Cols)
    (shape : valid d ls c) (cuts : ONativeTrail d row ls m r) (initial : Fits row c a r) :
    Fits row (finalCode d ls c) (run (oconcatenate d ls) m a) (odestination d ls m r) := by
  induction ls generalizing c m a r with
  | nil =>
    simpa only [oconcatenate,run,finalCode,odestination] using initial
  | cons l ls ih =>
    obtain ⟨loc,tail⟩ := shape
    obtain ⟨here,rest⟩ := cuts
    have one : Fits row (codes d c l) (run (oemitted d l) m a) (ostock d m r l) := by
      cases l with
      | native j n => exact plain _ _ _ _ _ _ initial (ot_groupSafe d j n loc)
      | paired j =>
        exact ot_stepTen j loc.1 row c (!d) (bounded j loc.1) m a r initial loc.2
          (by simpa only [Bool.not_not] using here.1) here.2.1 here.2.2
    rw [oconcatenate,run_append,run_take]
    exact ih _ _ _ _ tail rest one

theorem oemits (d : Bool) : group84 d=oconcatenate d (plan d) := by
  cases d <;> simp only [group84,ordered,oconcatenate,oemitted,plan,if_true,if_false,Bool.false_eq_true,
    List.append_assoc,List.append_nil]

theorem ogroup_run (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (m : List Bool) (a r : State) (initial : Fits row (initialCode d) a r)
    (native : ONativeTrail d row (plan d) m r) :
    Fits row (finalCode d (plan d) (initialCode d)) (run (group84 d) m a) (odestination d (plan d) m r) := by
  rw [oemits]
  exact otravel d row bounded _ m a r _ (valid_plan d) native initial

end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveTen
open WindowFieldMask WindowFieldCosts ArchiveFieldScratch StairArchiveInactive
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run measurementCount StairArchiveInactive.packet fieldHook WindowFieldCosts.opk
set_option maxRecDepth 8000
set_option maxHeartbeats 900000

def oreferenceLeg (d : Bool) : Leg → Program
  | .native j n => ogroup d j n
  | .paired j => ofirst j (!d) ++ osecond j (!d)
def olegTape (d : Bool) (m : List Bool) : Leg → List Bool
  | .native _ _ => m
  | .paired j => joinTapes (ofirst j (!d)) (tapeA j (!d) m) (otapeB j (!d) m)
theorem olocalTape (d : Bool) (m : List Bool) (s : State) (l : Leg) :
    ostock d m s l = run (oreferenceLeg d l) (olegTape d m l) s := by
  cases l with
  | native j n => rfl
  | paired j => exact (joined _ _ _ _ _).symm
def oreferenceProgram (d : Bool) : List Leg → Program
  | [] => []
  | l::ls => oreferenceLeg d l ++ oreferenceProgram d ls
def oreferenceTape (d : Bool) : List Leg → List Bool → List Bool
  | [],_ => []
  | l::ls,m => joinTapes (oreferenceLeg d l) (olegTape d m l) (oreferenceTape d ls (onextTape d l m))
theorem oref_run (d : Bool) (ls : List Leg) (m : List Bool) (r : State) :
    odestination d ls m r = run (oreferenceProgram d ls) (oreferenceTape d ls m) r := by
  induction ls generalizing m r with
  | nil => simp only [odestination,oreferenceProgram,oreferenceTape,run]
  | cons l ls ih => rw [odestination,oreferenceProgram,oreferenceTape,joined,←olocalTape,←ih]

theorem oreference_eq (d : Bool) : oreferenceProgram d (plan d)=PacketSequence.program d (opk d) 1 84 := by
  rw [shape' d (opk d)]
  cases d <;> simp only [oreferenceProgram,plan,oreferenceLeg,ofirst,osecond,ogroup,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false]

end ECDSAAdd.Entrant.StairPacket.WindowFieldJourney
end

section
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField CompressedFieldSupport StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 1600
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] run group ten measurementCount packet surface ArchiveStockRows.Chronology
  Rolling1588.CutFrame StairArchiveNativeCut.canonical WindowFieldCosts.opk

/-- oddten: dadon's `trail` for the field group's own packets. -/
theorem otrail (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (c : Nat) (ls : List Leg) (m : List Bool) (r : State) (route : path d c ls) (start : OCut c origin r) :
    ONativeTrail d rows ls m r := by
  induction ls generalizing c m r with
  | nil => trivial
  | cons l ls ih =>
    obtain ⟨rfl,good,more⟩ := route
    cases l with
    | native j n =>
      have post := oselected d j n good.1 good.2 origin ctx en r m start
      exact ⟨trivial,ih _ _ _ more post⟩
    | paired j =>
      have event := opair_cuts d j x (rows j) good (rb _ good) origin ctx en tr (history _ good) r m start
      exact ⟨event.1,ih _ _ _ more event.2⟩

/-- two runs that agree from `b` agree from any `a` that matches `b` on the larger footprint. -/
theorem ot_lift (P Q : Program) (sub : wires P⊆wires Q) (m n : List Bool) (a b : State)
    (agree : ∀ q∈wires Q, a.basis q=b.basis q) (same : run P m b=run Q n b) :
    run P m a=run Q n a := by
  have hp := Arithmetic.run_local_increment P a b m (fun q hq => agree q (sub hq))
  have hq := Arithmetic.run_local_increment Q a b n agree
  apply State.extensionality
  · have e1 := hp.1
    rw [same] at e1
    have e := e1.trans hq.1.symm
    revert e
    generalize (run P m a).phase = x
    generalize (run Q n a).phase = y
    generalize a.phase = z
    cases x <;> cases y <;> cases z <;> decide
  · funext q
    by_cases inQ : q∈wires Q
    · rw [hq.2 q inQ]
      by_cases inP : q∈wires P
      · rw [hp.2 q inP,same]
      · rw [run_preserves_outside P m a q inP,agree q inQ,←run_preserves_outside P m b q inP,same]
    · have inP : q∉wires P := fun h => inQ (sub h)
      rw [run_preserves_outside P m a q inP,run_preserves_outside Q n a q inQ]

set_option linter.unusedSimpArgs false in
theorem ot_seqWires (d : Bool) (p : Nat→Program) (j n : Nat) {q : Wire}
    (h : q∈wires (PacketSequence.program d p j n)) : ∃ k, j≤k ∧ k<j+n ∧ q∈wires (p k) := by
  induction n generalizing j with
  | zero => simp [PacketSequence.program,wires] at h
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true,
      wires_append,Finset.mem_union] at h
    · rcases h with h|h
      · obtain ⟨k,l,u,hk⟩ := ih (j+1) h
        exact ⟨k,by omega,by omega,hk⟩
      · exact ⟨j,Nat.le_refl j,by omega,h⟩
    · rcases h with h|h
      · exact ⟨j,Nat.le_refl j,by omega,h⟩
      · obtain ⟨k,l,u,hk⟩ := ih (j+1) h
        exact ⟨k,by omega,by omega,hk⟩

theorem ot_groupUses (d : Bool) {q : Wire} (h : q∈wires (group d 1 84)) : q∈surface ∧ q≠base 720 := by
  rw [WindowFieldCosts.group,WindowFieldCosts.distribute,WindowFieldCosts.distributed] at h
  obtain ⟨k,l,u,hk⟩ := ot_seqWires d _ 1 84 h
  exact packetUses d k (by omega) (by omega) hk

theorem ot_group_map (d : Bool) (j n : Nat) : group d j n=renameProgram wire (Rolling1588.groups d j n) := by
  rw [WindowFieldCosts.ot_group_eq,StairArchiveInactive.hosts_eq,renameProgram_comp]
  have g := StairGroups.groups_zero d j n
  unfold StairGroups.groups at g
  rw [g]
  unfold wire
  rfl

theorem ot_ogroup_map (d : Bool) (j n : Nat) :
    PacketSequence.program d (opk d) j n=renameProgram wire (PacketSequence.program d (oddPk d) j n) := by
  have ren (f : Wire → Wire) (a b : Program) : renameProgram f (a++b)=renameProgram f a++renameProgram f b :=
    List.map_append
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    cases d <;> simp only [PacketSequence.program,if_true,if_false,Bool.false_eq_true,ren,ih,ot_opk_map]

theorem ofield_sub (d : Bool) :
    wires (PacketSequence.program d (oddPk d) 1 84) ⊆ wires (Rolling1588.groups d 1 84) :=
  StairLoanGroupSupport.sequence_sub d _ _ (fun k => oddPk_sub d k) 1 84

-- `ofinal` retired: `othree_run` directly relates `group84 d` to `PacketSequence.program d (opk d) 1 84` on `OCut`.

end ECDSAAdd.Entrant.StairPacket.WindowFieldView
end
-- oddten:end SEM

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldView
open Arithmetic Secp256k1 MappedCompressed BalancedField StairArchiveTen StairArchiveInactive
open StairArchiveNativeCut ArchiveFieldScratch WindowFieldMask WindowFieldCosts StairField2V3Seg WindowFieldJourney
set_option maxRecDepth 1600
set_option maxHeartbeats 400000

/-- Archive-coupled field-group runner directly between odd-word `OCut` endpoints (cuts 1 and 85). -/
theorem othree_run (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (start : OCut (if d then 1 else 85) origin r) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84 d) m a)
      (run (PacketSequence.program d (opk d) 1 84) (oreferenceTape d (plan d) m) r) := by
  have route : path d (if d then 1 else 85) (plan d) := by cases d <;> simp [path,plan,prev,next,span,feasible,bankIds]
  have all := ogroup_run d rows rb m a r initial (otrail d x rows rb origin ctx en tr history _ _ m r route start)
  rwa [oref_run,oreference_eq] at all
end ECDSAAdd.Entrant.StairPacket.WindowFieldView

end

end
