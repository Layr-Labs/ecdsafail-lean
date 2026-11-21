import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.WindowCell
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic
import ECDSAAdd.Framework.WireRenamePool


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

private theorem walk {P : Program} (ready : ∀ q ∈ wires P, rawReady q = true)
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
theorem hosts_clear (k : Fp) : ∀ t ∈ moves, t.2 ∉ wires (suffix k) := by
  intro t ht used
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  have hi' := List.mem_range.mp hi
  unfold suffix placed at used
  rw [renameProgram_support] at used
  obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp used
  have orig : y ∈ wires (E1Reflected.merged base (base 2400) k.val) := by
    rw [E1Reflected.Square31.split, wires_append]
    apply Finset.mem_union_right
    exact hy
  have hh : base (258+i) ∈ S := List.mem_toFinset.mpr
    (E1Merge.in_mSites base (base 2400) (258+i) (by omega))
  have same := pmap_inj Baselines.layout Baselines.layout_widths Baselines.layout_nodup
    y (mergedR_S k.val orig) _ hh eq
  have mem := List.mem_toFinset.mp (E1Reflected.Square31.afterCompare_support _ _ _ hy)
  rw [same] at mem
  simp only [E1Reflected.Square31.mS5,wireBlock,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_map,List.mem_range'_1] at mem
  rcases mem with (((h|h|h)|h)|h)|h|h|h
  all_goals first
    | obtain ⟨j,hj,ej⟩ := h; have := base_injective ej; omega
    | have := base_injective h; omega
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
theorem walkPortZeros (k : Fp) (s : State) (m : List Bool) (X : Nat) (hx : regValue Baselines.layout.point.x s.basis=X)
    (hX : X<p) (hc : regValue Baselines.layout.dialogPool s.basis=0) :
    ∀ q ∈ ([4835,4837,4615,4616] : List Wire), (run (entryR Baselines.layout k) m s).basis q = false := by
  have geo : [(1542,4835),(1541,4837),(500,4615),(501,4616)].all
      (fun (i,q) => pmapR Baselines.layout (base i) == q) = true := by decide +kernel
  intro q hq
  have e : ∃ i ∈ exitClean, (i,q) ∈ [(1542,4835),(1541,4837),(500,4615),(501,4616)] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact ⟨1542,by decide,by decide⟩
    · exact ⟨1541,by decide,by decide⟩
    · exact ⟨500,by decide,by decide⟩
    · exact ⟨501,by decide,by decide⟩
  obtain ⟨i,hi,hm⟩ := e
  have pm : pmapR Baselines.layout (base i)=q := eq_of_beq (List.all_eq_true.mp geo _ hm)
  rw [←pm]
  exact stockExit k s m X hx hX hc i hi
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

private theorem outputs : ∀q∈outList,fit (U (outer ((Equiv.swap layout.doubleSelect (layout.core.poolWire 511)) q)))=true := by
  intro q hq
  rw [U_fast]
  exact List.all_eq_true.mp (by decide +kernel :
    outList.all (fun r => fit (StairPlaceFast.uB (outer ((Equiv.swap layout.doubleSelect (layout.core.poolWire 511)) r))))=true) q hq

private theorem ys : ∀q∈yList,fit (UG (duringY q))=true := by
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
    (encodeY (ParityUniform.entryYAll layout c)) := by
  apply lifted
  exact fun q hq => ys q (yList_mem (EntryFuse.fusedY_support layout layout_widths c
    (ParityUniform.entryYAll_wires layout layout_widths c hq)))

theorem exitY (c : Fp) : PieceOK StairPhysicalInventory.physicalHoles UG
    (encodeY (ParityUniform.exitYAll layout c)) := by
  apply lifted
  exact fun q hq => ys q (yList_mem (ExitFusionResearch.exitY_support layout layout_widths c
    (ParityUniform.exitYAll_wires layout layout_widths c hq)))

private theorem xs : ∀q∈xList,fit (UG (duringX (E1QubitPlacement.pmapR layout q)))=true := by
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
    pullState outer (run (encodeY (entryYAll layout k)) m actual) =
      run (entryYAll layout k) m (put s (pkW layout) flag) := by
  apply y_round _ actual _ m input (entries s flag clean)
  rw [run_put _ _ _ _ _ (pk_not_Y layout layout_widths layout_nodup _ flag_away),
    entryYAll_eq layout layout_widths layout_nodup Y k s m hy clean]
  have fy := EntryFuse.fusedY_correct layout layout_widths layout_nodup Y k s m hy clean
  exact entries _ flag (realPool _ _ clean fy.2.2)

theorem exit (Y k : Fp) (s actual : State) (m : List Bool) (flag : Bool)
    (hy : regValue layout.point.y s.basis=centerWord Y) (clean : regValue layout.dialogPool s.basis=0)
    (input : pullState outer actual = put s (pkW layout) flag) :
    pullState outer (run (encodeY (exitYAll layout k)) m actual) =
      run (exitYAll layout k) m (put s (pkW layout) flag) := by
  apply y_round _ actual _ m input (entries s flag clean)
  rw [run_put _ _ _ _ _ (FlagExit.pk_not_exitY layout layout_widths layout_nodup _ flag_away),
    exitYAll_eq layout layout_widths layout_nodup Y k s m m hy clean]
  have fy := ExitFusionResearch.exitY_correct layout layout_widths layout_nodup Y k s m hy clean
  exact entries _ flag (realPool _ _ clean fy.2.2)

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
  let hs := StairSqLoopA.hostDomain
  placedN (StairSquareFinal.brC hs) (StairSquareFinal.brB hs) (StairSquareFinal.brA hs) ++
    StairEntryRehost.routed (k - (C163Low4Offsets.delta : Fp))

abbrev hs := StairSqLoopA.hostDomain
theorem coreOK : CoreOK L0 (coreN (StairSquareFinal.brC hs) (StairSquareFinal.brB hs) (StairSquareFinal.brA hs)) := by
  let sub : hs.Sublist StairSqLoopA.hostDomain := List.Sublist.refl _
  have a := StairSquareBodyOK.bodyA_ok44 hs sub
  have b := StairSqBodyB.bodyB_ok44 hs sub
  have c := StairSquareBodyOK.bodyC_ok44 hs sub
  exact coreN_coreOK _ _ _ _ _ _ a b c
    (StairSquareKernel26C.kC_run_eq44 hs _ c (StairSquareBodyC.bodyC_avoids44 hs sub))
    (StairSquareKernel26C.kB_run_eq44 hs _ b (StairSqBodyB.bodyB_avoids44 hs sub))
    (StairSquareKernel26C.kA_run_eq44 hs _ a (StairSquareBodyA.bodyA_avoids44 hs sub))

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
    toffoliCount (program k) = toffoliCount (A161Generic.squareEntry L0 k) + 151 ∧
    measurementCount (program k) = measurementCount (A161Generic.squareEntry L0 k) ∧
    Challenge.gateSlots (program k) ≤ Challenge.gateSlots (A161Generic.squareEntry L0 k) + 3 := by
  have h : toffoliCount (program k) = toffoliCount (StairSquareFinal.square hs k) ∧
      measurementCount (program k) = measurementCount (StairSquareFinal.square hs k) ∧
      Challenge.gateSlots (program k) = Challenge.gateSlots (StairSquareFinal.square hs k) + 3 :=
    changingTail _ _
  have c := StairSquareFinal.square_counts hs k
  exact ⟨h.1.trans c.1,h.2.1.trans c.2,h.2.2.le.trans (Nat.add_le_add_right (StairSquareFinal.square_slots_le hs k) 3)⟩

theorem physical (k : Fp) : GatePhysical (program k) := by
  have p := StairSquareFinal.square_physical hs k
  rw [StairSquareFinal.square,squareN,gatePhysical_append] at p
  exact (gatePhysical_append _ _).mpr ⟨p.1,routedPhysical _⟩
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
  let sub : hs.Sublist StairSqLoopA.hostDomain := List.Sublist.refl _
  have member : ∀q∈hs, q∈StairSqLoopA.hostDomain := fun _ h => h
  have avC := StairSquareKernel26C.kC_avoids44 hs member _ (StairSquareBodyOK.bodyC_ok44 hs sub)
    (StairSquareBodyC.bodyC_avoids44 hs sub)
  have avB := StairSquareKernel26C.kB_avoids44 hs member _ (StairSqBodyB.bodyB_ok44 hs sub)
    (StairSqBodyB.bodyB_avoids44 hs sub)
  have avA := StairSquareKernel26C.kA_avoids44 hs member _ (StairSquareBodyOK.bodyA_ok44 hs sub)
    (StairSquareBodyA.bodyA_avoids44 hs sub)
  have hostsGood : ∀ h ∈ StairSquareKernel26C.hostsK,
      StairSiteAvoidance.UG (placeFn h) ∈ StairHoleSupport.recordArena ∧
        StairSiteAvoidance.UG (placeFn h) ∉ StairHoleSupport.oldHoles := by
    intro h hh
    obtain ⟨n, h1, h2, rfl⟩ := StairSquareKernel26C.hostsK_pool h hh
    exact host_good n h1 h2
  have arena := placedN_arenaB (StairSquareBodyA.bodyA hs) (StairSqBodyB.bodyB hs)
    (StairSquareBodyC.bodyC hs) (StairSquareFinal.brC hs) (StairSquareFinal.brB hs) (StairSquareFinal.brA hs) StairSquareKernel26C.hostsK
    (StairSquareBodyA.bodyA_coarse44 hs sub) (StairSquareBodyA.bodyA_fine44 hs sub)
    (StairSquareBodyC.bodyC_fine44 hs sub) (StairSqBodyB.bodyB_support44 hs sub)
    (StairSqBodyB.bodyB_normFlag44 hs sub (StairSquareBChecks.touchedAny_spec _ _ StairSqBodyB.middle_norm _ (List.mem_singleton_self _)))
    (StairSquareKernel26C.kC_support hs _) (StairSquareKernel26C.kB_support hs _)
    (StairSquareKernel26C.kA_support hs _) hostsGood
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

private theorem parts {P Q : Program} (h : Sound (P ++ Q)) : Sound P ∧ Sound Q :=
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

private theorem fw (d : Bool) (n : Nat) (h : Sound (Rolling1588TickGap.forward d 1 (15+n))) :
    Sound (Stair44WalkRun.forward d n) := by
  rw [forward_append] at h
  obtain ⟨a,b⟩ := parts h
  exact sound_append (sound_rename _ first.injective firstDom a)
    (sound_rename _ rest.injective restDom b)

private theorem bw (d : Bool) (n : Nat) (h : Sound (Rolling1588.reverse d 1 (15+n))) :
    Sound (Stair44WalkRun.backward d n) := by
  rw [reverse_append] at h
  obtain ⟨a,b⟩ := parts h
  exact sound_append (sound_rename _ rest.injective restDom a)
    (sound_rename _ first.injective firstDom b)

private theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

theorem dividePhysical : GatePhysical divide := by
  have eq : InverseFive23.lastPhase15 false = reverseEnd ++
      Rolling1588.reverse false 1 505 ++ FrontierEntry1591NativeH.inverse base := by
    simp only [InverseFive23.lastPhase15,InverseFive23.stackReverse15,InverseFive23.reverseTail15,
      reverseEnd,List.append_assoc]
  have h := sound_lastPhase15
  rw [eq] at h
  have ⟨a,native⟩ := parts h
  have ⟨tail,walk⟩ := parts a
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_entryFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [divide,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw true 409 sound_forward424),phase P.firstPack⟩,rest_physical _ field⟩,
    phase tail⟩,phase (bw false 490 walk)⟩,phase (sound_rename _ first.injective firstDom native)⟩

theorem multiplyPhysical (k : Nat) : GatePhysical (multiply k) := by
  have eq : Rolling1588TickGap.tailPhase false = Rolling1588TickGap.forward false 1 504 ++ forwardEnd := by
    simp only [Rolling1588TickGap.tailPhase,Rolling1588TickGap.stackForward,Six505.stackForward6,
      forwardEnd,List.append_assoc]
  have h := sound_tailPhase
  rw [eq] at h
  have ⟨walk,tail⟩ := parts h
  let P := primitiveSlots_v3 primitiveChecks
  have field := sound_exitFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [multiply,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw false 489 walk),phase tail⟩,rest_physical _ field⟩,phase P.firstUnpack⟩,
    phase (bw true 409 sound_reverse424)⟩,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ (phase (sound_x1N k))⟩

theorem genericPhysical (cx cy : Fp) : GatePhysical (generic cx cy) := by
  have g := FlagTop2.genericN_physical cx cy
  simp only [FlagExit.genericN,FlagExit.secondStageN,gatePhysical_append] at g
  simp only [generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.1.1.1,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ g.1.1.2⟩,dividePhysical⟩,
    Stair44Square.physical _⟩,multiplyPhysical _⟩,
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

theorem totals (C : Point) : toffoliCount (program C) ≤ 2169106 ∧ measurementCount (program C) ≤ 1520242 := by
  have h := StairCountsHosted.count_totals C
  change toffoliCount (concreteProgram C) ≤ 2169106 ∧ measurementCount (concreteProgram C) ≤ 1520242 at h
  cases C with
  | zero => exact h
  | @some cx cy hc =>
    let k := ReflectionE1.correction cx
    have old := StairSquareFinal.square_counts StairSqLoopA.holes k
    have new := Stair44Square.metrics k
    have ft := finite_eq tc (.some hc) cx cy (by
      change toffoliCount (Stair44Square.program k) = toffoliCount (StairSquareFinal.squareEntryHL _ layout k)
      rw [StairSquareFinal.squareEntryHL_layout]; exact new.1.trans old.1.symm)
    have fm := finite_eq mc (.some hc) cx cy (by
      change measurementCount (Stair44Square.program k) = measurementCount (StairSquareFinal.squareEntryHL _ layout k)
      rw [StairSquareFinal.squareEntryHL_layout]; exact new.2.1.trans old.2.symm)
    change toffoliCount _ = toffoliCount _ at ft
    change measurementCount _ = measurementCount _ at fm
    simp only [program,concreteProgram,hostedWrapper,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2] at h ⊢
    exact ⟨ft.le.trans h.1,fm.le.trans h.2⟩
open StairSlotsPlan

theorem slotBound (C : Point) : gateSlots (program C) ≤ 50860482 := by
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
        gateSlots (A161Generic.squareEntry layout (ReflectionE1.correction cx)) + 3 :=
      (Stair44Square.metrics (ReflectionE1.correction cx)).2.2
    have gen : gateSlots (generic cx cy) ≤ gateSlots (FlagExit.genericN layout cx cy) + (dE + dX) + 3 := by
      simp only [generic,FlagExit.genericN,FlagExit.secondStageN,Stair44PointMap.encodeY,
        Stair44PointMap.switchX,gateSlots_append,rename_gateSlots]
      omega
    have whole : gateSlots (program C) ≤ gateSlots (AboveFieldPointDevelop.programQ C) + (dE + dX) + 3 := by
      simp only [C,program,finite,borrowGeneric,Stair44PointMap.encode,AboveFieldPointDevelop.programQ,
        AboveFieldPointDevelop.wrapperBorrow,AboveFieldPointDevelop.finiteBorrow,AboveFieldPointDevelop.middle,
        ControlPointEncodingDevelop.borrowGeneric,ControlPointEncodingDevelop.genericBlock,
        gateSlots_append,rename_gateSlots] at ⊢
      omega
    have sum : dE + dX = 335196 := v3_slotDelta_1806
    have old := AboveFieldPointDevelop.program_slots_Q C
    change gateSlots (program C) ≤ 50860482
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

private theorem exitHead : PieceOK holes TP (StairHostsSchedule.exitHeadSuffix pr hp) := by
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
def domain (q : Nat) := (101 ≤ q && q ≤ 529) || (786 ≤ q && q ≤ 1045) || (1049 ≤ q && q ≤ 1300) || (1556 ≤ q && q ≤ 1812)

theorem domain_eq (q : Nat) : domain q = WindowCovered.domainW q := rfl

def Covered (P : Program) : Prop := ∀ q ∈ wires P, domain q = true

theorem covered_append {P Q : Program} (a : Covered P) (b : Covered Q) : Covered (P ++ Q) := by
  intro q h
  rw [wires_append,Finset.mem_union] at h
  exact h.elim (a q) (b q)

theorem from_check {P : Program} (h : allSites domain P = true) : Covered P := allSites_sound h

private theorem interval0 : (List.range' 101 429).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval1 : (List.range' 786 260).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval2 : (List.range' 1049 252).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval3 : (List.range' 1556 257).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel

theorem valid {q : Wire} (h : domain q = true) : Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true := by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩
  · exact List.all_eq_true.mp interval0 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval1 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval2 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval3 q (by simp only [List.mem_range'_1]; omega)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.RouteA.Rolling1588
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport Rolling1588Lifetime
open ECDSAAdd.Entrant.Rolling1588
attribute [local irreducible] run wires

/-- the `mstart` packet at any position (`mstartPacket_counts` is the case 84). -/
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

/-- gate slots of the `mstart` packet at any position (`mstartPacket_slots` is the case 84). -/
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

private theorem split (c : Cost) (d : Bool) (j n k : Nat) :
    c.measure (distributed d j (n+k)) =
    c.measure (distributed d j n) + c.measure (distributed d (j+n) k) := by
  unfold distributed
  induction n generalizing j with
  | zero =>
    simp only [Nat.zero_add,Nat.add_zero,PacketSequence.program]
    have z := c.append [] []
    simp only [List.nil_append] at z
    omega
  | succ n ih =>
    have rest := ih (j+1)
    have align : j+1+n=j+(n+1) := by omega
    rw [align] at rest
    cases d <;> simp only [Nat.succ_add,PacketSequence.program,Bool.false_eq_true,if_false,
      if_true,c.append] <;> omega

def group (d : Bool) (j n : Nat) := StairHostsSchedule.hostedGroup hostPlan d 0 j n

def ordered (d : Bool) (a b : Program) := if d then a++b else b++a


/-- The field group of the window ship: one archive ten-block per window block 120..255 (banks 25, 28, ..., 52;
bank `b` belongs to the block starting at tick `5b-5`). The odd cells of packets 1..45 are gone. -/
def group84rec (d : Bool) : Program :=
  ordered d (group d 1 18) (ordered d (ten 19 (!d)) (ordered d (group d 21 1) (ordered d (ten 22 (!d)) (ordered d (group d 24 1) (ordered d (ten 25 (!d)) (ordered d (group d 27 1) (ordered d (ten 28 (!d)) (ordered d (group d 30 1) (ordered d (ten 31 (!d)) (ordered d (group d 33 1) (ordered d (ten 34 (!d)) (ordered d (group d 36 1) (ordered d (ten 37 (!d)) (ordered d (group d 39 1) (ordered d (ten 40 (!d)) (ordered d (group d 42 1) (ordered d (ten 43 (!d)) (ordered d (group d 45 1) (ordered d (ten 46 (!d)) (ordered d (group d 48 1) (ordered d (ten 49 (!d)) (ordered d (group d 51 1) (ordered d (ten 52 (!d)) (ordered d (group d 54 1) (ordered d (ten 55 (!d)) (ordered d (group d 57 1) (ordered d (ten 58 (!d)) (ordered d (group d 60 1) (ordered d (ten 61 (!d)) (ordered d (group d 63 1) (ordered d (ten 64 (!d)) (ordered d (group d 66 1) (ordered d (ten 67 (!d)) (ordered d (group d 69 1) (ordered d (ten 70 (!d)) (ordered d (group d 72 1) (ordered d (ten 73 (!d)) (group d 75 10))))))))))))))))))))))))))))))))))))))

/-- packets `1..84` of both kernels run the odd-word cell (`dstart` / `dend` on the division kernel,
`mend` / `mstart` on the multiplication kernel), inside the archive ten-blocks too; packets `85..84` run the
record packets. -/
def oddPk (d : Bool) (k : Nat) : Program :=
  if k=1 then (if d then RouteA.Rolling1588.dstartPacket 1 else RouteA.Rolling1588.mendPacket 1)
  else if k<84 then RouteA.Rolling1588.packet d k
  else if k=84 then (if d then RouteA.Rolling1588.dendPacket 84 else RouteA.Rolling1588.mstartPacket 84)
  else ECDSAAdd.Entrant.Rolling1588.packet d k

/-- packet `k` of the field group, hosted like the record packets. -/
def opk (d : Bool) (k : Nat) : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (oddPk d k))

def ogroup (d : Bool) (j n : Nat) : Program := PacketSequence.program d (opk d) j n
def ofirst (j : Nat) (rev : Bool) := opk (!rev) (if rev then j+1 else j)
def osecond (j : Nat) (rev : Bool) := opk (!rev) (if rev then j else j+1)
/-- archive ten-block around the field group's own packets `j`, `j+1`. -/
def oten (j : Nat) (rev : Bool) :=
  fieldHook j (enter rev) ++ (ofirst j rev ++ (fieldHook j (shift rev) ++
    (osecond j rev ++ fieldHook j (leave rev))))

/-- the field group: the odd-word cell on packets 1..84 with the archive ten-blocks of the window banks
19, 22, 25, 28, 31, 34, 37, 40, 43, 46, 49, 52, 55, 58, 61, 64, 67, 70, 73 (bank `b` belongs to the block starting at tick `5b-5`) around the cell's own packets. -/
def group84 (d : Bool) : Program :=
  ordered d (ogroup d 1 18) (ordered d (oten 19 (!d)) (ordered d (ogroup d 21 1) (ordered d (oten 22 (!d)) (ordered d (ogroup d 24 1) (ordered d (oten 25 (!d)) (ordered d (ogroup d 27 1) (ordered d (oten 28 (!d)) (ordered d (ogroup d 30 1) (ordered d (oten 31 (!d)) (ordered d (ogroup d 33 1) (ordered d (oten 34 (!d)) (ordered d (ogroup d 36 1) (ordered d (oten 37 (!d)) (ordered d (ogroup d 39 1) (ordered d (oten 40 (!d)) (ordered d (ogroup d 42 1) (ordered d (oten 43 (!d)) (ordered d (ogroup d 45 1) (ordered d (oten 46 (!d)) (ordered d (ogroup d 48 1) (ordered d (oten 49 (!d)) (ordered d (ogroup d 51 1) (ordered d (oten 52 (!d)) (ordered d (ogroup d 54 1) (ordered d (oten 55 (!d)) (ordered d (ogroup d 57 1) (ordered d (oten 58 (!d)) (ordered d (ogroup d 60 1) (ordered d (oten 61 (!d)) (ordered d (ogroup d 63 1) (ordered d (oten 64 (!d)) (ordered d (ogroup d 66 1) (ordered d (oten 67 (!d)) (ordered d (ogroup d 69 1) (ordered d (oten 70 (!d)) (ordered d (ogroup d 72 1) (ordered d (oten 73 (!d)) (ogroup d 75 10))))))))))))))))))))))))))))))))))))))

theorem oddPk_one (d : Bool) :
    oddPk d 1=(if d then RouteA.Rolling1588.dstartPacket 1 else RouteA.Rolling1588.mendPacket 1) := by
  unfold oddPk; rw [if_pos rfl]
theorem oddPk_mid (d : Bool) (k : Nat) (h1 : 2≤k) (h2 : k<84) : oddPk d k=RouteA.Rolling1588.packet d k := by
  unfold oddPk; rw [if_neg (by omega),if_pos h2]
theorem oddPk_end (d : Bool) :
    oddPk d 84=(if d then RouteA.Rolling1588.dendPacket 84 else RouteA.Rolling1588.mstartPacket 84) := by
  unfold oddPk; rw [if_neg (by decide),if_neg (by decide),if_pos rfl]
theorem oddPk_std (d : Bool) (k : Nat) (h : 84<k) : oddPk d k=ECDSAAdd.Entrant.Rolling1588.packet d k := by
  unfold oddPk; rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]

/-- every packet of the family uses only wires of the record packet at its place (no new wire). -/
theorem oddPk_sub (d : Bool) (k : Nat) : wires (oddPk d k) ⊆ wires (ECDSAAdd.Entrant.Rolling1588.packet d k) := by
  by_cases h1 : k=1
  · subst h1
    rw [oddPk_one]
    cases d
    · simp only [Bool.false_eq_true,if_false]
      unfold RouteA.Rolling1588.mendPacket ECDSAAdd.Entrant.Rolling1588.packet
      exact StairLoanGroupSupport.rename_sub _ _ _ (StairLoanGroupSupport.c45_mendBasePacket_sub 1)
    · simp only [if_true]
      unfold RouteA.Rolling1588.dstartPacket ECDSAAdd.Entrant.Rolling1588.packet
      exact StairLoanGroupSupport.rename_sub _ _ _ (StairLoanGroupSupport.c45_dstartBasePacket_sub 1)
  by_cases h2 : k<84
  · rw [show oddPk d k=RouteA.Rolling1588.packet d k by unfold oddPk; rw [if_neg h1,if_pos h2]]
    cases d
    · exact StairLoanGroupSupport.c45_oddPacket_sub_false k
    · exact StairLoanGroupSupport.c45_oddPacket_sub k
  by_cases h3 : k=84
  · subst h3
    rw [oddPk_end]
    cases d
    · simp only [Bool.false_eq_true,if_false]
      unfold RouteA.Rolling1588.mstartPacket ECDSAAdd.Entrant.Rolling1588.packet
      exact StairLoanGroupSupport.rename_sub _ _ _ (StairLoanGroupSupport.c45_mstartBasePacket_sub 84)
    · simp only [if_true]
      unfold RouteA.Rolling1588.dendPacket ECDSAAdd.Entrant.Rolling1588.packet
      exact StairLoanGroupSupport.rename_sub _ _ _ (StairLoanGroupSupport.c45_dendBasePacket_sub 84)
  · intro q hq
    rwa [oddPk_std d k (by omega)] at hq

/-- the odd packets are physical. -/
theorem oddPk_physical (d : Bool) (k : Nat) (hk : k≤84) : GatePhysical (oddPk d k) := by
  by_cases h1 : k=1
  · subst h1
    rw [oddPk_one]
    cases d
    · exact RouteA.Rolling1588.ot_mendPacket_physical 1 (by decide)
    · exact RouteA.Rolling1588.ot_dstartPacket_physical
  by_cases h2 : k<84
  · rw [show oddPk d k=RouteA.Rolling1588.packet d k by unfold oddPk; rw [if_neg h1,if_pos h2]]
    exact RouteA.Rolling1588.packet_physical d k (by omega)
  · have h3 : k=84 := by omega
    subst h3
    rw [oddPk_end]
    cases d
    · exact RouteA.Rolling1588.ot_mstartPacket_physical 84 (by decide)
    · exact RouteA.Rolling1588.ot_dendPacket_physical 84 (by decide)

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

/-- the tape of the reference run is the actual tape (no cell any more). -/
def cellTape (_d : Bool) (m : List Bool) : List Bool := m




private theorem ord (c : Cost) (d : Bool) (a b : Program) :
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

theorem overhead (j : Nat) (d : Bool) :
    toffoliCount (ten j (!d)) = toffoliCount (group d j 2)+(if d then 195 else 192) ∧
    measurementCount (ten j (!d)) = measurementCount (group d j 2)+277 := by
  rw [group,distribute]
  cases d <;>
    simp only [distributed,PacketSequence.program,Bool.not_true,Bool.not_false,ten,first,second,
      enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
      List.append_nil,toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,enter0_toffoliCount,switch0_toffoliCount,leave0_toffoliCount,
      enter1_toffoliCount,switch1_toffoliCount,leave1_toffoliCount,enter0_measurementCount,
      switch0_measurementCount,leave0_measurementCount,enter1_measurementCount,
      switch1_measurementCount,leave1_measurementCount] <;> constructor <;> omega

private theorem partition (c : Cost) (d : Bool) :
    c.measure (group d 1 84) = c.measure (group d 1 18)+c.measure (group d 19 2)+c.measure (group d 21 1)+c.measure (group d 22 2)+c.measure (group d 24 1)+c.measure (group d 25 2)+c.measure (group d 27 1)+c.measure (group d 28 2)+c.measure (group d 30 1)+c.measure (group d 31 2)+c.measure (group d 33 1)+c.measure (group d 34 2)+c.measure (group d 36 1)+c.measure (group d 37 2)+c.measure (group d 39 1)+c.measure (group d 40 2)+c.measure (group d 42 1)+c.measure (group d 43 2)+c.measure (group d 45 1)+c.measure (group d 46 2)+c.measure (group d 48 1)+c.measure (group d 49 2)+c.measure (group d 51 1)+c.measure (group d 52 2)+c.measure (group d 54 1)+c.measure (group d 55 2)+c.measure (group d 57 1)+c.measure (group d 58 2)+c.measure (group d 60 1)+c.measure (group d 61 2)+c.measure (group d 63 1)+c.measure (group d 64 2)+c.measure (group d 66 1)+c.measure (group d 67 2)+c.measure (group d 69 1)+c.measure (group d 70 2)+c.measure (group d 72 1)+c.measure (group d 73 2)+c.measure (group d 75 10) := by
  simp only [group,distribute]
  have p0 := split c d 1 18 66
  have p1 := split c d 19 2 64
  have p2 := split c d 21 1 63
  have p3 := split c d 22 2 61
  have p4 := split c d 24 1 60
  have p5 := split c d 25 2 58
  have p6 := split c d 27 1 57
  have p7 := split c d 28 2 55
  have p8 := split c d 30 1 54
  have p9 := split c d 31 2 52
  have p10 := split c d 33 1 51
  have p11 := split c d 34 2 49
  have p12 := split c d 36 1 48
  have p13 := split c d 37 2 46
  have p14 := split c d 39 1 45
  have p15 := split c d 40 2 43
  have p16 := split c d 42 1 42
  have p17 := split c d 43 2 40
  have p18 := split c d 45 1 39
  have p19 := split c d 46 2 37
  have p20 := split c d 48 1 36
  have p21 := split c d 49 2 34
  have p22 := split c d 51 1 33
  have p23 := split c d 52 2 31
  have p24 := split c d 54 1 30
  have p25 := split c d 55 2 28
  have p26 := split c d 57 1 27
  have p27 := split c d 58 2 25
  have p28 := split c d 60 1 24
  have p29 := split c d 61 2 22
  have p30 := split c d 63 1 21
  have p31 := split c d 64 2 19
  have p32 := split c d 66 1 18
  have p33 := split c d 67 2 16
  have p34 := split c d 69 1 15
  have p35 := split c d 70 2 13
  have p36 := split c d 72 1 12
  have p37 := split c d 73 2 10
  norm_num only [] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37
  omega




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
    c.measure (ogroup d 1 84)=c.measure (ogroup d 1 18)+c.measure (ogroup d 19 2)+c.measure (ogroup d 21 1)+
      c.measure (ogroup d 22 2)+c.measure (ogroup d 24 1)+c.measure (ogroup d 25 2)+
      c.measure (ogroup d 27 1)+c.measure (ogroup d 28 2)+c.measure (ogroup d 30 1)+
      c.measure (ogroup d 31 2)+c.measure (ogroup d 33 1)+c.measure (ogroup d 34 2)+
      c.measure (ogroup d 36 1)+c.measure (ogroup d 37 2)+c.measure (ogroup d 39 1)+
      c.measure (ogroup d 40 2)+c.measure (ogroup d 42 1)+c.measure (ogroup d 43 2)+
      c.measure (ogroup d 45 1)+c.measure (ogroup d 46 2)+c.measure (ogroup d 48 1)+
      c.measure (ogroup d 49 2)+c.measure (ogroup d 51 1)+c.measure (ogroup d 52 2)+
      c.measure (ogroup d 54 1)+c.measure (ogroup d 55 2)+c.measure (ogroup d 57 1)+
      c.measure (ogroup d 58 2)+c.measure (ogroup d 60 1)+c.measure (ogroup d 61 2)+
      c.measure (ogroup d 63 1)+c.measure (ogroup d 64 2)+c.measure (ogroup d 66 1)+
      c.measure (ogroup d 67 2)+c.measure (ogroup d 69 1)+c.measure (ogroup d 70 2)+
      c.measure (ogroup d 72 1)+c.measure (ogroup d 73 2)+c.measure (ogroup d 75 10) := by
  have p0 := gsplit c d (opk d) 1 18 66
  have p1 := gsplit c d (opk d) 19 2 64
  have p2 := gsplit c d (opk d) 21 1 63
  have p3 := gsplit c d (opk d) 22 2 61
  have p4 := gsplit c d (opk d) 24 1 60
  have p5 := gsplit c d (opk d) 25 2 58
  have p6 := gsplit c d (opk d) 27 1 57
  have p7 := gsplit c d (opk d) 28 2 55
  have p8 := gsplit c d (opk d) 30 1 54
  have p9 := gsplit c d (opk d) 31 2 52
  have p10 := gsplit c d (opk d) 33 1 51
  have p11 := gsplit c d (opk d) 34 2 49
  have p12 := gsplit c d (opk d) 36 1 48
  have p13 := gsplit c d (opk d) 37 2 46
  have p14 := gsplit c d (opk d) 39 1 45
  have p15 := gsplit c d (opk d) 40 2 43
  have p16 := gsplit c d (opk d) 42 1 42
  have p17 := gsplit c d (opk d) 43 2 40
  have p18 := gsplit c d (opk d) 45 1 39
  have p19 := gsplit c d (opk d) 46 2 37
  have p20 := gsplit c d (opk d) 48 1 36
  have p21 := gsplit c d (opk d) 49 2 34
  have p22 := gsplit c d (opk d) 51 1 33
  have p23 := gsplit c d (opk d) 52 2 31
  have p24 := gsplit c d (opk d) 54 1 30
  have p25 := gsplit c d (opk d) 55 2 28
  have p26 := gsplit c d (opk d) 57 1 27
  have p27 := gsplit c d (opk d) 58 2 25
  have p28 := gsplit c d (opk d) 60 1 24
  have p29 := gsplit c d (opk d) 61 2 22
  have p30 := gsplit c d (opk d) 63 1 21
  have p31 := gsplit c d (opk d) 64 2 19
  have p32 := gsplit c d (opk d) 66 1 18
  have p33 := gsplit c d (opk d) 67 2 16
  have p34 := gsplit c d (opk d) 69 1 15
  have p35 := gsplit c d (opk d) 70 2 13
  have p36 := gsplit c d (opk d) 72 1 12
  have p37 := gsplit c d (opk d) 73 2 10
  simp only [ogroup]
  norm_num only [] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37
  omega


theorem ooverhead (j : Nat) (d : Bool) :
    toffoliCount (oten j (!d)) = toffoliCount (ogroup d j 2)+(if d then 195 else 192) ∧
    measurementCount (oten j (!d)) = measurementCount (ogroup d j 2)+277 := by
  cases d <;>
    simp only [ogroup,PacketSequence.program,Bool.not_true,Bool.not_false,oten,ofirst,osecond,
      enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
      List.append_nil,toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2,enter0_toffoliCount,switch0_toffoliCount,leave0_toffoliCount,
      enter1_toffoliCount,switch1_toffoliCount,leave1_toffoliCount,enter0_measurementCount,
      switch0_measurementCount,leave0_measurementCount,enter1_measurementCount,
      switch1_measurementCount,leave1_measurementCount] <;> constructor <;> omega

private theorem ofield_pieces (c : Cost) (d : Bool) :
    c.measure (ogroup d 1 84)=c.measure (oddPk d 1)+c.measure (RouteA.Rolling1588.groups d 2 82)+
      c.measure (oddPk d 84)+c.measure (ECDSAAdd.Entrant.Rolling1588.groups d 85 0) := by
  rw [ogroup_measure]
  have a := gsplit c d (oddPk d) 1 1 83
  have b := gsplit c d (oddPk d) 2 82 1
  have e := gsplit c d (oddPk d) 84 1 0
  have p1 := oneP c d (oddPk d) 1
  have p3 := oneP c d (oddPk d) 84
  have p2 := congrArg c.measure (oseq_congr d (oddPk d) (RouteA.Rolling1588.packet d) 82 2
    (fun k l u => oddPk_mid d k l (by omega)))
  have p4 := congrArg c.measure (oseq_congr d (oddPk d) (ECDSAAdd.Entrant.Rolling1588.packet d) 0 85
    (fun k l u => oddPk_std d k (by omega)))
  norm_num only [] at a b e
  unfold RouteA.Rolling1588.groups ECDSAAdd.Entrant.Rolling1588.groups
  omega

private theorem rfield_pieces (c : Cost) (d : Bool) :
    c.measure (group d 1 84)=c.measure (ECDSAAdd.Entrant.Rolling1588.packet d 1)+
      c.measure (ECDSAAdd.Entrant.Rolling1588.groups d 2 82)+
      c.measure (ECDSAAdd.Entrant.Rolling1588.packet d 84)+
      c.measure (ECDSAAdd.Entrant.Rolling1588.groups d 85 0) := by
  rw [group_measure]
  unfold ECDSAAdd.Entrant.Rolling1588.groups
  have a := gsplit c d (ECDSAAdd.Entrant.Rolling1588.packet d) 1 1 83
  have b := gsplit c d (ECDSAAdd.Entrant.Rolling1588.packet d) 2 82 1
  have e := gsplit c d (ECDSAAdd.Entrant.Rolling1588.packet d) 84 1 0
  have p1 := oneP c d (ECDSAAdd.Entrant.Rolling1588.packet d) 1
  have p3 := oneP c d (ECDSAAdd.Entrant.Rolling1588.packet d) 84
  norm_num only [] at a b e
  omega

/-- the hosted odd field packets save 749 T / 1169 M against the record packets 1..84 on either kernel. -/
theorem ofield_counts (d : Bool) :
    toffoliCount (ogroup d 1 84)+749=toffoliCount (group d 1 84) ∧
    measurementCount (ogroup d 1 84)+1169=measurementCount (group d 1 84) := by
  have o1 := ofield_pieces tc d
  have o2 := ofield_pieces mc d
  have r1 := rfield_pieces tc d
  have r2 := rfield_pieces mc d
  rw [show tc.measure=toffoliCount from rfl] at o1 r1
  rw [show mc.measure=measurementCount from rfl] at o2 r2
  have g := RouteA.Rolling1588.groups_count_delta d 2 82 (by decide)
  rw [if_neg (by cases d <;> decide)] at g
  cases d
  · have s := RouteA.Rolling1588.ot_mstartPacket_counts 84
    have e := RouteA.Rolling1588.mendPacket_counts
    rw [oddPk_one,oddPk_end] at o1 o2
    simp only [Bool.false_eq_true,if_false] at o1 o2
    exact ⟨by omega,by omega⟩
  · have s := RouteA.Rolling1588.dstartPacket_counts
    have e := RouteA.Rolling1588.dendPacket_counts 84
    rw [oddPk_one,oddPk_end] at o1 o2
    simp only [if_true] at o1 o2
    exact ⟨by omega,by omega⟩

/-- gate slots of the hosted odd field packets against the record packets 1..84. -/
theorem ofield_slots (d : Bool) :
    slots.measure (ogroup d 1 84)+(if d then 7065 else 3340)=
      slots.measure (group d 1 84)+(if d then 0 else 0) := by
  have o := ofield_pieces slots d
  have r := rfield_pieces slots d
  rw [show slots.measure=Challenge.gateSlots from rfl] at o r ⊢
  have g := RouteA.Rolling1588.groups_slot_delta d 2 82 (by decide)
  rw [if_neg (by cases d <;> decide)] at g
  cases d
  · have s := RouteA.Rolling1588.ot_mstartPacket_slots 84
    have e := RouteA.Rolling1588.mendPacket_slots
    simp only [RouteA.Rolling1588.halfSlotSaving,Bool.false_eq_true,if_false] at g ⊢
    rw [oddPk_one,oddPk_end] at o
    simp only [Bool.false_eq_true,if_false] at o
    omega
  · have s := RouteA.Rolling1588.dstartPacket_slots
    have e := RouteA.Rolling1588.dendPacket_slots 84
    simp only [RouteA.Rolling1588.halfSlotSaving,if_true] at g ⊢
    rw [oddPk_one,oddPk_end] at o
    simp only [if_true] at o
    omega

private theorem osolve (c : Cost) (d : Bool) (delta : Nat)
    (h : ∀j,c.measure (oten j (!d))=c.measure (ogroup d j 2)+delta) :
    c.measure (group84 d)=c.measure (ogroup d 1 84)+19*delta := by
  simp only [group84,ord,h,opartition]
  omega

/-- the field group (odd cell on packets 1..84, ten-blocks included) against the record packets 1..84. -/
theorem group_cost (d : Bool) :
    toffoliCount (group84 d)+0=toffoliCount (group d 1 84)+(if d then 2956 else 2899) ∧
    measurementCount (group84 d)+0=measurementCount (group d 1 84)+4094 := by
  have t := osolve tc d (if d then 195 else 192) (fun j => (ooverhead j d).1)
  have m := osolve mc d 277 (fun j => (ooverhead j d).2)
  have f := ofield_counts d
  rw [show tc.measure = toffoliCount from rfl] at t
  rw [show mc.measure = measurementCount from rfl] at m
  cases d <;> simp only [if_true,if_false,Bool.false_eq_true] at t ⊢ <;> exact ⟨by omega, by omega⟩

/-- Static syntax counts include both correction lists of every measurement. -/
theorem group_slots (d : Bool) :
    slots.measure (group84 d)+(if d then 7065 else 3340)=
      slots.measure (group d 1 84)+19*(if d then 5141 else 5535)+(if d then 0 else 0) := by
  have hc := ofield_slots d
  have h (j : Nat) : slots.measure (oten j (!d)) =
      slots.measure (ogroup d j 2)+(if d then 5141 else 5535) := by
    rw [show slots.measure=Challenge.gateSlots from rfl]
    cases d <;>
      simp only [ogroup,PacketSequence.program,Bool.not_true,Bool.not_false,oten,ofirst,osecond,
        enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
        List.append_nil,Challenge.gateSlots_append,Baselines.rename_gateSlots,enter0_gateSlots,
        switch0_gateSlots,leave0_gateSlots,enter1_gateSlots,switch1_gateSlots,leave1_gateSlots] <;> omega
  have w := osolve slots d (if d then 5141 else 5535) h
  cases d <;> simp only [if_true,if_false,Bool.false_eq_true] at hc w ⊢ <;> omega

theorem group_cost_div :
    toffoliCount (group84 true) = toffoliCount (group true 1 84)+2956 ∧
    measurementCount (group84 true) = measurementCount (group true 1 84)+4094 := by
  have t := (group_cost true).1
  have m := (group_cost true).2
  simp only [if_true] at t
  exact ⟨by omega,by omega⟩

theorem group_cost_mul :
    toffoliCount (group84 false) = toffoliCount (group false 1 84)+2899 ∧
    measurementCount (group84 false) = measurementCount (group false 1 84)+4094 := by
  have t := (group_cost false).1
  have m := (group_cost false).2
  simp only [Bool.false_eq_true,if_false] at t
  exact ⟨by omega,by omega⟩


end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [90,376); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 74 ++
    forward45plus1 d ++ Rolling1588TickGap.forward d 376 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 376 tail ++
    reverse45plus1 d ++ Rolling1588.reverse d 16 74) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

private theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (forward45plus1 d)+f=c.measure (Rolling1588TickGap.forward d 90 286))
    (hr : c.measure (reverse45plus1 d)+r=c.measure (Rolling1588.reverse d 90 286)) :
    c.measure (forward d tail)+f=c.measure (Stair44WalkRun.forward d (360+tail)) ∧
    c.measure (backward d tail)+r=c.measure (Stair44WalkRun.backward d (360+tail)) := by
  have a := StairRestSupport.forward_append d 74 16 (286+tail)
  have b := StairRestSupport.forward_append d 286 90 tail
  have x := StairRestSupport.reverse_append d 74 16 (286+tail)
  have y := StairRestSupport.reverse_append d 286 90 tail
  change Rolling1588TickGap.forward d 16 (74+(286+tail)) =
    Rolling1588TickGap.forward d 16 74 ++ Rolling1588TickGap.forward d 90 (286+tail) at a
  change Rolling1588.reverse d 16 (74+(286+tail)) =
    Rolling1588.reverse d 90 (286+tail) ++ Rolling1588.reverse d 16 74 at x
  rw [b] at a
  rw [y] at x
  have num : 360+tail=74+(286+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,forward,backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

attribute [local irreducible] Partial.forward45plus1 Partial.reverse45plus1 Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 24791 else 24810)=
      toffoliCount (Stair44WalkRun.forward d (360+tail)) ∧
    toffoliCount (backward d tail)+(if d then 24581 else 24581)=
      toffoliCount (Stair44WalkRun.backward d (360+tail)) ∧
    measurementCount (forward d tail)+12337=measurementCount (Stair44WalkRun.forward d (360+tail)) ∧
    measurementCount (backward d tail)+12349=measurementCount (Stair44WalkRun.backward d (360+tail)) := by
  cases d
  · have sf := StockWindowCosts.stock375 false
    have a : toffoliCount (forward45plus1 false) = 107828 := by rw [Partial.assembly]; exact WindowParams.ship_toffoliF_false
    have b : toffoliCount (reverse45plus1 false) = 108039 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_toffoliR_false
    have c : measurementCount (forward45plus1 false) = 54107 := by rw [Partial.assembly]; exact WindowParams.ship_measureF.2
    have e : measurementCount (reverse45plus1 false) = 53857 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_measureR.2
    have t := walk tc false tail 24810 24581
      (subEq 24810 a sf.1 (by omega)) (subEq 24581 b sf.2.2.1 (by omega))
    have m := walk mc false tail 12337 12349
      (subEq 12337 c sf.2.1 (by omega)) (subEq 12349 e sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,m⟩
  · have sf := StockWindowCosts.stock375 true
    have a : toffoliCount (forward45plus1 true) = 107847 := by rw [Partial.assembly]; exact WindowParams.ship_toffoliF_true
    have b : toffoliCount (reverse45plus1 true) = 108039 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_toffoliR_true
    have c : measurementCount (forward45plus1 true) = 54107 := by rw [Partial.assembly]; exact WindowParams.ship_measureF.1
    have e : measurementCount (reverse45plus1 true) = 53857 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_measureR.1
    have t := walk tc true tail 24791 24581
      (subEq 24791 a sf.1 (by omega)) (subEq 24581 b sf.2.2.1 (by omega))
    have m := walk mc true tail 12337 12349
      (subEq 12337 c sf.2.1 (by omega)) (subEq 12349 e sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,m⟩


/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 360+tail=n)
    (hf : (if d then 24791 else 24810)=f) (hr : (if d then 24581 else 24581)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+12337=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+12349=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact exactWalks d tail
end ECDSAAdd.Entrant.StairPacket.WindowWalkCosts

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
    hostedGroup hostPlan true 13 85 5 ++
    StairSchedule.forwardSegment p 62 47 450 465 ++
    hostedGroup hostPlan true 22 90 3 ++
    StairSchedule.forwardSegment p 47 32 465 480 ++
    hostedGroup hostPlan true 30 93 3 ++
    StairSchedule.forwardSegment p 32 22 480 490 ++
    hostedGroup hostPlan true 36 96 2 ++
    StairSchedule.forwardSegment p 22 12 490 500 ++
    hostedGroup hostPlan true 41 98 2 ++ StairSchedule.forwardLast p

def exitHeadSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.reverseLast p ++
    hostedGroup hostPlan false 41 98 2 ++
    StairSchedule.reverseSegment p 22 12 490 500 ++
    hostedGroup hostPlan false 36 96 2 ++
    StairSchedule.reverseSegment p 32 22 480 490 ++
    hostedGroup hostPlan false 30 93 3 ++
    StairSchedule.reverseSegment p 47 32 465 480 ++
    hostedGroup hostPlan false 22 90 3 ++
    StairSchedule.reverseSegment p 62 47 450 465 ++
    hostedGroup hostPlan false 13 85 5 ++
    StairSchedule.reverseSegment p 87 62 425 450 ++
    WindowFieldCosts.group84 false

def entryLowPrefix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
      (Rolling1588.placedFirstPacket true) ++
    FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (entryTailPrefix p) ++
    FourScratchWindow.unprefix

def exitLowSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (exitHeadSuffix p) ++
    FourScratchWindow.unprefix ++
    StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
      (Rolling1588.placedFirstPacket false)

def entryFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.fieldRename (entryLowPrefix p) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (entryLowSuffix hostPlan) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowPrefix hostPlan) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowSuffix p)

theorem field_delta (c : Cost) (d : Bool) (n : Nat)
    (h : c.measure (WindowFieldCosts.group84 d)=c.measure (WindowFieldCosts.group d 1 84)+n) :
    (if d then c.measure (entryFieldHosted checkpointPrimitives)
     else c.measure (exitFieldHosted checkpointPrimitives)) =
    (if d then c.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
     else c.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan))+n := by
  cases d <;> simp only [Bool.false_eq_true,if_true,if_false,WindowFieldCosts.group] at h ⊢
  all_goals simp only [entryFieldHosted,exitFieldHosted,entryLowPrefix,exitLowSuffix,
    entryTailPrefix,exitHeadSuffix,StairHostsSchedule.entryFieldHosted,
    StairHostsSchedule.exitFieldHosted,StairHostsSchedule.entryLowPrefix,
    StairHostsSchedule.exitLowSuffix,StairHostsSchedule.entryTailPrefix,
    StairHostsSchedule.exitHeadSuffix,StairSchedule.fieldRename,StairSchedule.parityRename,
    c.rename,c.append,h]
  all_goals omega

open Stair44Outer

def divide : Program :=
  phasePlace (WindowWalkCosts.forward true 49) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace (entryFieldHosted checkpointPrimitives) ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 130) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 129) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 49) ++
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

theorem kernels (c : Cost) (gainF gainR fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 49)+gainF=c.measure (Stair44WalkRun.forward true 409))
    (dR : c.measure (WindowWalkCosts.backward false 130)+gainR=c.measure (Stair44WalkRun.backward false 490))
    (g : c.measure (WindowFieldCosts.group84 true)=c.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    c.measure divide+gainF+gainR=c.measure Stair44Outer.divide+fieldExtra := by
  have h := field_delta c true _ g
  simp only [if_true] at h
  simp only [divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

theorem kernelsM (c : Cost) (k gainF gainR fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 129)+gainF=c.measure (Stair44WalkRun.forward false 489))
    (mR : c.measure (WindowWalkCosts.backward true 49)+gainR=c.measure (Stair44WalkRun.backward true 409))
    (g : c.measure (WindowFieldCosts.group84 false)=c.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
    c.measure (multiply k)+gainF+gainR=c.measure (Stair44Outer.multiply k)+fieldExtra := by
  have h := field_delta c false _ g
  simp only [Bool.false_eq_true,if_false] at h
  simp only [multiply,Stair44Outer.multiply,phasePlace,kernelPlace,c.append,c.rename,Stair44PointMap.switchX]
  omega

theorem finite_delta (c : Cost) (C : Point) (cx cy : Fp) (gain : Nat)
    (h : c.measure divide+c.measure (multiply cx.val)+gain =
      c.measure Stair44Outer.divide+c.measure (Stair44Outer.multiply cx.val)) :
    c.measure (finite C cx cy)+gain=c.measure (Stair44Outer.finite C cx cy) := by
  simp only [finite,Stair44Outer.finite,borrowGeneric,Stair44Outer.borrowGeneric,
    generic,Stair44Outer.generic,c.append,c.rename]
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

theorem forward45plus1_domain (d : Bool) : Covered (forward45plus1 d) := by
  intro q h
  rw [Partial.assembly] at h
  rw [domain_eq]
  exact (WindowCovered.window_covered d).1 q h
theorem reverse45plus1_domain (d : Bool) : Covered (reverse45plus1 d) := by
  intro q h
  rw [Partial.unwind_assembly] at h
  rw [domain_eq]
  exact (WindowCovered.window_covered d).2 q h

theorem forward45plus1_fits (d : Bool) : ∀ q ∈ wires (forward45plus1 d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (forward45plus1_domain d q h)

theorem reverse45plus1_fits (d : Bool) : ∀ q ∈ wires (reverse45plus1 d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
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
    tc.measure (WindowFieldCosts.group84 true)=tc.measure (WindowFieldCosts.group true 1 84)+2956 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_div.1
private theorem fieldMcDiv :
    mc.measure (WindowFieldCosts.group84 true)=mc.measure (WindowFieldCosts.group true 1 84)+4094 := by
  rw [show mc.measure=measurementCount from rfl]
  exact WindowFieldCosts.group_cost_div.2
private theorem fieldTcMul :
    tc.measure (WindowFieldCosts.group84 false)=tc.measure (WindowFieldCosts.group false 1 84)+2899 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_mul.1
private theorem fieldMcMul :
    mc.measure (WindowFieldCosts.group84 false)=mc.measure (WindowFieldCosts.group false 1 84)+4094 := by
  rw [show mc.measure=measurementCount from rfl]
  exact WindowFieldCosts.group_cost_mul.2
/-- the two kernels' field extras differ (460 vs 624 T, 442 vs 831 M). -/
private theorem pair_delta2 {a b x y g h i j f1 f2 r : Nat}
    (l : a+g+h=x+f1) (rr : b+i+j=y+f2) (v : g+h+i+j=r+f1+f2) : a+b+r=x+y := by omega
private theorem sum_delta2 {a b x y g h f1 f2 r : Nat}
    (l : a+g+h=x+f1) (rr : b+g+h=y+f2) (v : 2*(g+h)=r+f1+f2) : a+b+r=x+y := by omega
private theorem sum_delta {a b x y g h f r : Nat}
    (l : a+g+h=x+f) (rr : b+g+h=y+f) (v : 2*(g+h)=r+2*f) : a+b+r=x+y := by omega
private theorem pair_delta {a b x y g h i j f r : Nat}
    (l : a+g+h=x+f) (rr : b+i+j=y+f) (v : g+h+i+j=r+2*f) : a+b+r=x+y := by omega

attribute [local irreducible] Stair44Outer.divide Stair44Outer.multiply divide multiply
  finite Stair44Outer.finite WindowWalkCosts.forward WindowWalkCosts.backward
  WindowFieldCosts.group84 WindowFieldCosts.group Stair44WalkRun.forward Stair44WalkRun.backward
  toffoliCount measurementCount

theorem tc_div : tc.measure divide+24791+24581=tc.measure Stair44Outer.divide+2956 :=
  kernels tc 24791 24581 2956 (WindowWalkCosts.inst true 49 409 24791 24581 rfl rfl rfl).1
    (WindowWalkCosts.inst false 130 490 24810 24581 rfl rfl rfl).2.1 fieldTcDiv

theorem tc_mul (k : Nat) : tc.measure (multiply k)+24810+24581=tc.measure (Stair44Outer.multiply k)+2899 :=
  kernelsM tc k 24810 24581 2899 (WindowWalkCosts.inst false 129 489 24810 24581 rfl rfl rfl).1
    (WindowWalkCosts.inst true 49 409 24791 24581 rfl rfl rfl).2.1 fieldTcMul

theorem mc_div : mc.measure divide+12337+12349=mc.measure Stair44Outer.divide+4094 :=
  kernels mc 12337 12349 4094 (WindowWalkCosts.inst true 49 409 24791 24581 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst false 130 490 24810 24581 rfl rfl rfl).2.2.2 fieldMcDiv

theorem mc_mul (k : Nat) : mc.measure (multiply k)+12337+12349=mc.measure (Stair44Outer.multiply k)+4094 :=
  kernelsM mc k 12337 12349 4094 (WindowWalkCosts.inst false 129 489 24810 24581 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst true 49 409 24791 24581 rfl rfl rfl).2.2.2 fieldMcMul

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+92908=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+41184=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 92908 (pair_delta2 tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 41184 (sum_delta2 mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2076198 ∧
    measurementCount (program C) ≤ 1479740 := by
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
  Rolling1588TickGap.forward Rolling1588.reverse Partial.forward45plus1 Partial.reverse45plus1

private theorem walk (c : Cost) (d : Bool) (tail f r n : Nat) (hn : 360+tail=n)
    (hf : c.measure (Partial.forward45plus1 d) ≤ f) (hr : c.measure (Partial.reverse45plus1 d) ≤ r) :
    c.measure (WindowWalkCosts.forward d tail) ≤ c.measure (Stair44WalkRun.forward d n)+f ∧
    c.measure (WindowWalkCosts.backward d tail) ≤ c.measure (Stair44WalkRun.backward d n)+r := by
  subst n
  have a := StairRestSupport.forward_append d 74 16 (286+tail)
  have b := StairRestSupport.forward_append d 286 90 tail
  have x := StairRestSupport.reverse_append d 74 16 (286+tail)
  have y := StairRestSupport.reverse_append d 286 90 tail
  change Rolling1588TickGap.forward d 16 (74+(286+tail)) =
    Rolling1588TickGap.forward d 16 74 ++ Rolling1588TickGap.forward d 90 (286+tail) at a
  change Rolling1588.reverse d 16 (74+(286+tail)) =
    Rolling1588.reverse d 90 (286+tail) ++ Rolling1588.reverse d 16 74 at x
  rw [b] at a
  rw [y] at x
  have num : 360+tail=74+(286+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,WindowWalkCosts.forward,WindowWalkCosts.backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

private theorem kernels (c : Cost) (gainF gainR fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 49) ≤ c.measure (Stair44WalkRun.forward true 409)+gainF)
    (dR : c.measure (WindowWalkCosts.backward false 130) ≤ c.measure (Stair44WalkRun.backward false 490)+gainR)
    (g : c.measure (WindowFieldCosts.group84 true)=c.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    c.measure WindowCallerCosts.divide ≤ c.measure Stair44Outer.divide+gainF+gainR+fieldExtra := by
  have h  := WindowCallerCosts.field_delta c true _ g
  simp only [if_true] at h
  simp only [WindowCallerCosts.divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

private theorem kernelsM (c : Cost) (k gainF gainR fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 129) ≤ c.measure (Stair44WalkRun.forward false 489)+gainF)
    (mR : c.measure (WindowWalkCosts.backward true 49) ≤ c.measure (Stair44WalkRun.backward true 409)+gainR)
    (g : c.measure (WindowFieldCosts.group84 false)=c.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
    c.measure (WindowCallerCosts.multiply k) ≤ c.measure (Stair44Outer.multiply k)+gainF+gainR+fieldExtra := by
  have h  := WindowCallerCosts.field_delta c false _ g
  simp only [Bool.false_eq_true,if_false] at h
  simp only [WindowCallerCosts.multiply,Stair44Outer.multiply,phasePlace,kernelPlace,c.append,c.rename,Stair44PointMap.switchX]
  omega

private theorem finite_upper (c : Cost) (C : Point) (cx cy : Fp) (gain : Nat)
    (h : c.measure WindowCallerCosts.divide+c.measure (WindowCallerCosts.multiply cx.val) ≤
      c.measure Stair44Outer.divide+c.measure (Stair44Outer.multiply cx.val)+gain) :
    c.measure (WindowCallerCosts.finite C cx cy) ≤ c.measure (Stair44Outer.finite C cx cy)+gain := by
  simp only [WindowCallerCosts.finite,Stair44Outer.finite,WindowCallerCosts.borrowGeneric,Stair44Outer.borrowGeneric,
    WindowCallerCosts.generic,Stair44Outer.generic,c.append,c.rename]
  omega


private theorem casts {P : Program} {n : Nat} (h : gateSlots P ≤ n) : slots.measure P ≤ n := h
private theorem groupCap (d : Bool) (n : Nat)
    (hn : 19*(if d then 5141 else 5535)+(if d then 0 else 0)=n+(if d then 7065 else 3340)) :
    slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  have h := WindowFieldCosts.group_slots d
  omega
private theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+1552415+1557813+90614 :=
  kernels slots 1552415 1557813 90614
    (walk slots true 49 1552415 1557673 409 rfl (casts WindowParams.ship_slotsF.1) (casts WindowParams.ship_slotsR.1)).1
    (walk slots false 130 1552415 1557813 490 rfl (casts WindowParams.ship_slotsF.2) (casts WindowParams.ship_slotsR.2)).2
    (groupCap true 90614 rfl)

private theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+1552415+1557673+101825 :=
  kernelsM slots k 1552415 1557673 101825
    (walk slots false 129 1552415 1557813 489 rfl (casts WindowParams.ship_slotsF.2) (casts WindowParams.ship_slotsR.2)).1
    (walk slots true 49 1552415 1557673 409 rfl (casts WindowParams.ship_slotsF.1) (casts WindowParams.ship_slotsR.1)).2
    (groupCap false 101825 rfl)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+1552415+1557813+90614)
    (hm : b ≤ y+1552415+1557673+101825) : a+b ≤ x+y+6412755 := by omega

private theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+6412755 :=
  finite_upper slots C cx cy 6412755 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 57273237 := by
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


private theorem app {p q : Program} : Sound (p++q) ↔ Sound p ∧ Sound q :=
  ⟨fun h => ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩,
    fun h => sound_append h.1 h.2⟩

private theorem emitted (op : Stage) : GatePhysical (StairArchiveRelease.program op) := by
  cases op
  exacts [enter0_GatePhysical,switch0_GatePhysical,leave0_GatePhysical,
    enter1_GatePhysical,switch1_GatePhysical,leave1_GatePhysical]

private theorem hook (j : Nat) (hj : j∈[19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]) (op : Stage) :
    Sound (fieldHook j op) := by
  have span : j∈List.range' 1 83 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; apply List.mem_range'_1.mpr; omega
  have chk : (fieldSites j).all (fun q => decide (InDom q))=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
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

private theorem ordinary (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    Sound (group d j n) := by
  rw [group,distribute,distributed_ok]
  exact fun i l u => whole d i (by omega) (by omega)

private theorem pair (d : Bool) (j : Nat) (pick : j∈[19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]) (lo : 1≤j) (hi : j≤83) :
    Sound (ten j (!d)) := by
  have here := whole d j lo (by omega)
  have next := whole d (j+1) (by omega) (by omega)
  have firstOK : Sound (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (second j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))



/-- the field group's own packets are sound (record footprint, odd packets physical). -/
private theorem ot_opk_sound (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) : Sound (opk d k) := by
  by_cases big : 84<k
  · rw [WindowFieldCosts.ot_opk_std d k big]; exact whole d k lo (by omega)
  · refine ⟨?_,good_of_subset (WindowFieldCosts.ot_opk_sub d k) (whole d k lo (by omega)).good⟩
    simp only [opk,StairArchiveInactive.hosts_eq]
    exact gatePhysical_rename _ (Equiv.injective _) _
      (gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _ (WindowFieldCosts.oddPk_physical d k (by omega)))

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

private theorem ot_pair (d : Bool) (j : Nat) (pick : j∈[19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]) (lo : 1≤j) (hi : j≤83) :
    Sound (oten j (!d)) := by
  have here := ot_opk_sound d j lo (by omega)
  have next := ot_opk_sound d (j+1) (by omega) (by omega)
  have firstOK : Sound (ofirst j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (osecond j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))

theorem group84_ok (d : Bool) : Sound (group84 d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  have c38 := ord (ot_pair d 73 (by decide) (by decide) (by decide)) (ot_ogroup_sound d 75 10 (by decide) (by decide))
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
  exact ord (ot_ogroup_sound d 1 18 (by decide) (by decide)) c2

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

private theorem ordinary (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK reserved TP (group d j n) := by
  rw [group,distribute,distributed_ok]
  exact fun i l u => whole d i (by omega) (by omega)

private theorem pair (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) :
    PieceOK reserved TP (ten j (!d)) := by
  have jmem : j∈List.range' 1 83 := List.mem_range'_1.mpr ⟨lo,by omega⟩
  have here := whole d j lo (by omega)
  have next := whole d (j+1) (by omega) (by omega)
  have firstOK : PieceOK reserved TP (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : PieceOK reserved TP (second j (!d)) := by cases d <;> first | exact here | exact next
  exact (hook j jmem _).append (firstOK.append ((hook j jmem _).append (lastOK.append (hook j jmem _))))


/-- the field group's own packets avoid the reserved holes (their wires are record wires). -/
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
  have c38 := ord (ot_oten_piece d 73 (by decide) (by decide)) (ot_ogroup_piece d 75 10 (by decide) (by decide))
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
  exact ord (ot_ogroup_piece d 1 18 (by decide) (by decide)) c2

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
  have g14 := sound_hostedGroup H hs true 13 85 5 (by decide) (by omega) (by omega) (by omega)
  have g23 := sound_hostedGroup H hs true 22 90 3 (by decide) (by omega) (by omega) (by omega)
  have g31 := sound_hostedGroup H hs true 30 93 3 (by decide) (by omega) (by omega) (by omega)
  have g37 := sound_hostedGroup H hs true 36 96 2 (by decide) (by omega) (by omega) (by omega)
  have g42 := sound_hostedGroup H hs true 41 98 2 (by decide) (by omega) (by omega) (by omega)
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
  have g14 := sound_hostedGroup H hs false 13 85 5 (by decide) (by omega) (by omega) (by omega)
  have g23 := sound_hostedGroup H hs false 22 90 3 (by decide) (by omega) (by omega) (by omega)
  have g31 := sound_hostedGroup H hs false 30 93 3 (by decide) (by omega) (by omega) (by omega)
  have g37 := sound_hostedGroup H hs false 36 96 2 (by decide) (by omega) (by omega) (by omega)
  have g42 := sound_hostedGroup H hs false 41 98 2 (by decide) (by omega) (by omega) (by omega)
  have s5 := sound_reverseSegment P 22 12 490 500 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s4 := sound_reverseSegment P 32 22 480 490 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s3 := sound_reverseSegment P 47 32 465 480 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s2 := sound_reverseSegment P 62 47 450 465 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have s1 := sound_reverseSegment P 87 62 425 450 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have rl := sound_reverseLast P
  unfold WindowCallerCosts.exitHeadSuffix
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_append rl g42) s5) g37) s4) g31) s3) g23) s2) g14) s1) g0

theorem sound_entryFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryFieldHosted p) := by
  have first := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket true)
    (sound_firstPacket true)
  have pre : Sound (WindowCallerCosts.entryLowPrefix p) := by
    unfold WindowCallerCosts.entryLowPrefix
    exact sound_append (sound_append (sound_append first sound_clearProgram)
      (sound_borrow (sound_entryTailPrefix H P hs))) sound_unprefix
  have tail : Sound (StairHostsSchedule.entryTailSuffix hostPlan) := by
    have g := sound_hostedGroup H hs true 43 100 2 (by decide) (by omega) (by omega)
      (by omega)
    unfold StairHostsSchedule.entryTailSuffix
    exact sound_append (sound_append (sound_append g
      (sound_sig 511 (by omega) B.divEndpoint)) sound_copyN) B.canon
  have suf : Sound (StairHostsSchedule.entryLowSuffix hostPlan) := by
    unfold StairHostsSchedule.entryLowSuffix
    exact sound_append (sound_append sound_clearProgram (sound_borrow tail)) sound_unprefix
  unfold WindowCallerCosts.entryFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_fieldRename pre) sound_paritySetup) sound_hostedX)
    (sound_fieldRename suf)) sound_hostedX) sound_paritySetup

theorem sound_exitFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitFieldHosted p) := by
  have head : Sound (StairHostsSchedule.exitHeadPrefix hostPlan) := by
    have g := sound_hostedGroup H hs false 43 100 2 (by decide) (by omega) (by omega)
      (by omega)
    unfold StairHostsSchedule.exitHeadPrefix StairHostsSchedule.hostedEndpoint
      StairSchedule.placedEndPacket
    exact sound_append (sound_append (sound_append B.center sound_copyN)
      (sound_sig 511 (by omega) B.multEndpoint)) g
  have pre : Sound (StairHostsSchedule.exitLowPrefix hostPlan) := by
    unfold StairHostsSchedule.exitLowPrefix
    exact sound_append (sound_append sound_clearProgram (sound_borrow head)) sound_unprefix
  have last := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket false)
    (sound_firstPacket false)
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
attribute [local irreducible] wires renameProgram Partial.forward45plus1 Partial.reverse45plus1
  Rolling1588TickGap.forward Rolling1588.reverse Stair44WalkMap.rest Stair44WalkMap.first

abbrev GoodWindow (p : Program) :=
  ∀ q∈wires p, Stair44PhaseSites.valid (Stair44WalkMap.rest q)=true

private theorem native {p : Program} (h : GoodWindow p) :
    PieceOK reserved (fun x => PP (Stair44WalkMap.rest x)) p := by
  apply weaken
  apply Stair44OuterSites.fits
  intro x hx
  change Stair44OuterSites.fit (StairOuterPlacement.phasePlace (Stair44WalkMap.rest x))=true
  rw [StairPlaceFast.phasePlace_eqB]
  exact h x hx

theorem walkF (d : Bool) (tail : Nat) (bound : 16+(360+tail)≤506)
    (new : GoodWindow (Partial.forward45plus1 d)) :
    PieceOK reserved PP (WindowWalkCosts.forward d tail) := by
  have old := weaken (Stair44PhaseSites.forward d (360+tail) bound)
  have a := StairRestSupport.forward_append d 74 16 (286+tail)
  have b := StairRestSupport.forward_append d 286 90 tail
  change Rolling1588TickGap.forward d 16 (74+(286+tail)) =
    Rolling1588TickGap.forward d 16 74 ++ Rolling1588TickGap.forward d 90 (286+tail) at a
  rw [b] at a
  have num : 360+tail=74+(286+tail) := by omega
  simp only [Stair44WalkRun.forward,num,a,app,ren] at old
  simp only [WindowWalkCosts.forward,app,ren]
  exact ⟨old.1,⟨old.2.1,native new⟩,old.2.2.2⟩

theorem walkR (d : Bool) (tail : Nat) (bound : 16+(360+tail)≤506)
    (new : GoodWindow (Partial.reverse45plus1 d)) :
    PieceOK reserved PP (WindowWalkCosts.backward d tail) := by
  have old := weaken (Stair44PhaseSites.backward d (360+tail) bound)
  have a := StairRestSupport.reverse_append d 74 16 (286+tail)
  have b := StairRestSupport.reverse_append d 286 90 tail
  change Rolling1588.reverse d 16 (74+(286+tail)) =
    Rolling1588.reverse d 90 (286+tail) ++ Rolling1588.reverse d 16 74 at a
  rw [b] at a
  have num : 360+tail=74+(286+tail) := by omega
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
private theorem parts {P Q : Program} (h : Sound (P ++ Q)) : Sound P ∧ Sound Q :=
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


private theorem dom {p : Program} (cover : PartialSites.Covered p) : Good p := by
  intro q hq
  have h := cover q hq
  simp only [PartialSites.domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  unfold InDom InDomN
  left
  constructor
  all_goals omega

private theorem fw (d : Bool) (tail n : Nat) (hn : 15+(360+tail)=n)
    (ref_ : Sound (Rolling1588TickGap.forward d 1 n))
    (p : GatePhysical (Partial.forward45plus1 d)) : Sound (WindowWalkCosts.forward d tail) := by
  subst n
  rw [forward_append d 15 1 (360+tail)] at ref_
  obtain ⟨early,late⟩ := parts ref_
  change Sound (Rolling1588TickGap.forward d 16 (360+tail)) at late
  rw [show 360+tail=74+(286+tail) by omega,forward_append d 74 16 (286+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 90 (286+tail)) at ms
  rw [forward_append d 286 90 tail] at ms
  have patch : Sound (Partial.forward45plus1 d) := ⟨p,dom (PartialSites.forward45plus1_domain d)⟩
  have last : Sound (Rolling1588TickGap.forward d 376 tail) := (parts ms).2
  exact sound_append (sound_rename _ first.injective firstDom early)
    (sound_rename _ rest.injective restDom (sound_append (sound_append pre patch) last))

private theorem bw (d : Bool) (tail n : Nat) (hn : 15+(360+tail)=n)
    (ref_ : Sound (Rolling1588.reverse d 1 n))
    (p : GatePhysical (Partial.reverse45plus1 d)) : Sound (WindowWalkCosts.backward d tail) := by
  subst n
  rw [reverse_append d 15 1 (360+tail)] at ref_
  obtain ⟨late,early⟩ := parts ref_
  change Sound (Rolling1588.reverse d 16 (360+tail)) at late
  rw [show 360+tail=74+(286+tail) by omega,reverse_append d 74 16 (286+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 90 (286+tail)) at ms
  rw [reverse_append d 286 90 tail] at ms
  have patch : Sound (Partial.reverse45plus1 d) := ⟨p,dom (PartialSites.reverse45plus1_domain d)⟩
  have last : Sound (Rolling1588.reverse d 376 tail) := (parts ms).1
  exact sound_append (sound_rename _ rest.injective restDom (sound_append (sound_append last patch) pre))
    (sound_rename _ first.injective firstDom early)
private theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

variable (ff : ∀d,GatePhysical (Partial.forward45plus1 d)) (rr : ∀d,GatePhysical (Partial.reverse45plus1 d))

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
  have field := sound_entryFieldHosted StairOpenWiring.half760 P boundarySlots_current hostSlots_v3
  simp only [WindowCallerCosts.divide,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨phase (fw true 49 424 rfl sound_forward424 (ff _)),phase P.firstPack⟩,rest_physical _ field⟩,
    phase tail⟩,phase (bw false 130 505 rfl walk (rr _))⟩,phase (sound_rename _ first.injective firstDom native)⟩

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
  exact ⟨⟨⟨⟨⟨phase (fw false 129 504 rfl walk (ff _)),phase tail⟩,rest_physical _ field⟩,phase P.firstUnpack⟩,
    phase (bw true 49 424 rfl sound_reverse424 (rr _))⟩,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ (phase (sound_x1N k))⟩

include ff rr in
theorem genericPhysical (cx cy : Fp) : GatePhysical (WindowCallerCosts.generic cx cy) := by
  have g := FlagTop2.genericN_physical cx cy
  simp only [FlagExit.genericN,FlagExit.secondStageN,gatePhysical_append] at g
  simp only [WindowCallerCosts.generic,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.1.1.1,
    gatePhysical_rename _ Stair44PointMap.duringX.injective _ g.1.1.2⟩,dividePhysical ff rr⟩,
    Stair44Square.physical _⟩,multiplyPhysical ff rr _⟩,
    gatePhysical_rename _ Stair44PointMap.duringY.injective _ g.2.2⟩

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

/-- Replacing a child leaves the safety contract on the other children intact. -/
private def SafeChange (f : Wire → Wire) (old new : Program) :=
  PieceOK reserved f old → PieceOK reserved f new
private theorem same (f : Wire → Wire) (p : Program) : SafeChange f p p := id
private theorem fresh {f : Wire → Wire} {p q : Program} (h : PieceOK reserved f q) :
    SafeChange f p q := fun _ => h
private theorem appendChange {f : Wire → Wire} {a b x y : Program}
    (l : SafeChange f a x) (r : SafeChange f b y) : SafeChange f (a++b) (x++y) :=
  fun old => (l (app.mp old).1).append (r (app.mp old).2)
private theorem renameChange {f g : Wire → Wire} {a b : Program}
    (h : SafeChange (fun x => f (g x)) a b) : SafeChange f (renameProgram g a) (renameProgram g b) :=
  fun old => ren.mpr (h (ren.mp old))

private theorem tail (p : StairSchedule.StairPrimitives) :
    SafeChange TP (StairHostsSchedule.entryTailPrefix p hostPlan)
      (WindowCallerCosts.entryTailPrefix p) := by
  unfold StairHostsSchedule.entryTailPrefix WindowCallerCosts.entryTailPrefix
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  refine appendChange ?_ (same _ _)
  exact fresh (group84_ok true)

private theorem head (p : StairSchedule.StairPrimitives) :
    SafeChange TP (StairHostsSchedule.exitHeadSuffix p hostPlan)
      (WindowCallerCosts.exitHeadSuffix p) := by
  unfold StairHostsSchedule.exitHeadSuffix WindowCallerCosts.exitHeadSuffix
  exact appendChange (same _ _) (fresh (group84_ok false))

private theorem entryField : PieceOK reserved KP
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) := by
  have h : PieceOK reserved KP (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan) :=
    Stair44FieldSites.entry
  apply (show SafeChange KP (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) from ?_) h
  have low : SafeChange lowPlace (StairHostsSchedule.entryLowPrefix checkpointPrimitives hostPlan)
      (WindowCallerCosts.entryLowPrefix checkpointPrimitives) :=
    appendChange (appendChange (same _ _) (renameChange (tail _))) (same _ _)
  have field : SafeChange KP (StairSchedule.fieldRename (StairHostsSchedule.entryLowPrefix checkpointPrimitives hostPlan))
      (StairSchedule.fieldRename (WindowCallerCosts.entryLowPrefix checkpointPrimitives)) :=
    renameChange (renameChange low)
  exact appendChange (appendChange (appendChange (appendChange (appendChange field
    (same _ _)) (same _ _)) (same _ _)) (same _ _)) (same _ _)

private theorem exitField : PieceOK reserved KP
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) := by
  have h : PieceOK reserved KP (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) :=
    Stair44FieldSites.exit
  apply (show SafeChange KP (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) from ?_) h
  have low : SafeChange lowPlace (StairHostsSchedule.exitLowSuffix checkpointPrimitives hostPlan)
      (WindowCallerCosts.exitLowSuffix checkpointPrimitives) :=
    appendChange (appendChange (appendChange (same _ _) (renameChange (head _))) (same _ _)) (same _ _)
  exact appendChange (same _ _) (renameChange (renameChange low))

private theorem phase {P : Program} (v : PieceOK reserved PP P) :
    PieceOK reserved UG (Stair44Outer.phasePlace P) := ok_kernel (ok_phase v)

theorem division (f : GoodWindow (Partial.forward45plus1 true))
    (r : GoodWindow (Partial.reverse45plus1 false)) :
    PieceOK reserved UG WindowCallerCosts.divide :=
  (((((phase (walkF true 49 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.pack)))).append
    (ok_kernel entryField)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.reverseTail)))).append
    (phase (walkR false 130 (by decide) r))).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.native)))

theorem multiplication (k : Nat) (f : GoodWindow (Partial.forward45plus1 false))
    (r : GoodWindow (Partial.reverse45plus1 true)) :
    PieceOK reserved UG (WindowCallerCosts.multiply k) :=
  (((((phase (walkF false 129 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.forwardTail)))).append
    (ok_kernel exitField)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.unpack)))).append
    (phase (walkR true 49 (by decide) r))).append (weaken (Stair44PhaseSites.exitX k))

theorem program_width (C : Point) (f : ∀d, GoodWindow (Partial.forward45plus1 d))
    (r : ∀d,GoodWindow (Partial.reverse45plus1 d)) :
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
  WindowPhysical.physical (fun d => (Partial.assembly d).symm ▸ (WindowPhysicalW.window_physical d).1) (fun d => (Partial.unwind_assembly d).symm ▸ (WindowPhysicalW.window_physical d).2) C

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

def entry : Challenge.Entry := fun C => normalizeProgram (WindowCallerCosts.program C)
def bounds : Challenge.Bounds := ⟨2076198,1479740,1543,57273237⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowCallerCosts.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowCallerCosts.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowCallerCosts.totals C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1479740
    rw [normalize_measurements]
    exact (WindowCallerCosts.totals C).2
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1543
    rw [normalize_qubits]
    exact WindowCallerCosts.qubitBound C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 57273237
    rw [normalize_slots]
    exact WindowSlots.slotBound C

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

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
open Arithmetic MappedCompressed ArchiveFieldScratch StairArchiveInactive StairArchiveNativeCut StairArchiveRelease
def slots (j : Nat) := (List.range 16).map (fieldPort j)
def banks := [19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]
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
def apart (j h : Nat) := j=h || (slots h).all (fun q => !(StairArchiveRelease.fieldSites j).contains q)
def part (h offset count : Nat) := (List.range' offset count).all (allowed h)
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
theorem h25_1 : part 25 1 7 = true := by decide +kernel
theorem h25_8 : part 25 8 7 = true := by decide +kernel
theorem h25_15 : part 25 15 7 = true := by decide +kernel
theorem h25_22 : part 25 22 7 = true := by decide +kernel
theorem h25_29 : part 25 29 7 = true := by decide +kernel
theorem h25_36 : part 25 36 7 = true := by decide +kernel
theorem h25_43 : part 25 43 7 = true := by decide +kernel
theorem h25_50 : part 25 50 7 = true := by decide +kernel
theorem h25_57 : part 25 57 7 = true := by decide +kernel
theorem h25_64 : part 25 64 7 = true := by decide +kernel
theorem h25_71 : part 25 71 7 = true := by decide +kernel
theorem h25_78 : part 25 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h28_1 : part 28 1 7 = true := by decide +kernel
theorem h28_8 : part 28 8 7 = true := by decide +kernel
theorem h28_15 : part 28 15 7 = true := by decide +kernel
theorem h28_22 : part 28 22 7 = true := by decide +kernel
theorem h28_29 : part 28 29 7 = true := by decide +kernel
theorem h28_36 : part 28 36 7 = true := by decide +kernel
theorem h28_43 : part 28 43 7 = true := by decide +kernel
theorem h28_50 : part 28 50 7 = true := by decide +kernel
theorem h28_57 : part 28 57 7 = true := by decide +kernel
theorem h28_64 : part 28 64 7 = true := by decide +kernel
theorem h28_71 : part 28 71 7 = true := by decide +kernel
theorem h28_78 : part 28 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h31_1 : part 31 1 7 = true := by decide +kernel
theorem h31_8 : part 31 8 7 = true := by decide +kernel
theorem h31_15 : part 31 15 7 = true := by decide +kernel
theorem h31_22 : part 31 22 7 = true := by decide +kernel
theorem h31_29 : part 31 29 7 = true := by decide +kernel
theorem h31_36 : part 31 36 7 = true := by decide +kernel
theorem h31_43 : part 31 43 7 = true := by decide +kernel
theorem h31_50 : part 31 50 7 = true := by decide +kernel
theorem h31_57 : part 31 57 7 = true := by decide +kernel
theorem h31_64 : part 31 64 7 = true := by decide +kernel
theorem h31_71 : part 31 71 7 = true := by decide +kernel
theorem h31_78 : part 31 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h34_1 : part 34 1 7 = true := by decide +kernel
theorem h34_8 : part 34 8 7 = true := by decide +kernel
theorem h34_15 : part 34 15 7 = true := by decide +kernel
theorem h34_22 : part 34 22 7 = true := by decide +kernel
theorem h34_29 : part 34 29 7 = true := by decide +kernel
theorem h34_36 : part 34 36 7 = true := by decide +kernel
theorem h34_43 : part 34 43 7 = true := by decide +kernel
theorem h34_50 : part 34 50 7 = true := by decide +kernel
theorem h34_57 : part 34 57 7 = true := by decide +kernel
theorem h34_64 : part 34 64 7 = true := by decide +kernel
theorem h34_71 : part 34 71 7 = true := by decide +kernel
theorem h34_78 : part 34 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h37_1 : part 37 1 7 = true := by decide +kernel
theorem h37_8 : part 37 8 7 = true := by decide +kernel
theorem h37_15 : part 37 15 7 = true := by decide +kernel
theorem h37_22 : part 37 22 7 = true := by decide +kernel
theorem h37_29 : part 37 29 7 = true := by decide +kernel
theorem h37_36 : part 37 36 7 = true := by decide +kernel
theorem h37_43 : part 37 43 7 = true := by decide +kernel
theorem h37_50 : part 37 50 7 = true := by decide +kernel
theorem h37_57 : part 37 57 7 = true := by decide +kernel
theorem h37_64 : part 37 64 7 = true := by decide +kernel
theorem h37_71 : part 37 71 7 = true := by decide +kernel
theorem h37_78 : part 37 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h40_1 : part 40 1 7 = true := by decide +kernel
theorem h40_8 : part 40 8 7 = true := by decide +kernel
theorem h40_15 : part 40 15 7 = true := by decide +kernel
theorem h40_22 : part 40 22 7 = true := by decide +kernel
theorem h40_29 : part 40 29 7 = true := by decide +kernel
theorem h40_36 : part 40 36 7 = true := by decide +kernel
theorem h40_43 : part 40 43 7 = true := by decide +kernel
theorem h40_50 : part 40 50 7 = true := by decide +kernel
theorem h40_57 : part 40 57 7 = true := by decide +kernel
theorem h40_64 : part 40 64 7 = true := by decide +kernel
theorem h40_71 : part 40 71 7 = true := by decide +kernel
theorem h40_78 : part 40 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h43_1 : part 43 1 7 = true := by decide +kernel
theorem h43_8 : part 43 8 7 = true := by decide +kernel
theorem h43_15 : part 43 15 7 = true := by decide +kernel
theorem h43_22 : part 43 22 7 = true := by decide +kernel
theorem h43_29 : part 43 29 7 = true := by decide +kernel
theorem h43_36 : part 43 36 7 = true := by decide +kernel
theorem h43_43 : part 43 43 7 = true := by decide +kernel
theorem h43_50 : part 43 50 7 = true := by decide +kernel
theorem h43_57 : part 43 57 7 = true := by decide +kernel
theorem h43_64 : part 43 64 7 = true := by decide +kernel
theorem h43_71 : part 43 71 7 = true := by decide +kernel
theorem h43_78 : part 43 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h46_1 : part 46 1 7 = true := by decide +kernel
theorem h46_8 : part 46 8 7 = true := by decide +kernel
theorem h46_15 : part 46 15 7 = true := by decide +kernel
theorem h46_22 : part 46 22 7 = true := by decide +kernel
theorem h46_29 : part 46 29 7 = true := by decide +kernel
theorem h46_36 : part 46 36 7 = true := by decide +kernel
theorem h46_43 : part 46 43 7 = true := by decide +kernel
theorem h46_50 : part 46 50 7 = true := by decide +kernel
theorem h46_57 : part 46 57 7 = true := by decide +kernel
theorem h46_64 : part 46 64 7 = true := by decide +kernel
theorem h46_71 : part 46 71 7 = true := by decide +kernel
theorem h46_78 : part 46 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h49_1 : part 49 1 7 = true := by decide +kernel
theorem h49_8 : part 49 8 7 = true := by decide +kernel
theorem h49_15 : part 49 15 7 = true := by decide +kernel
theorem h49_22 : part 49 22 7 = true := by decide +kernel
theorem h49_29 : part 49 29 7 = true := by decide +kernel
theorem h49_36 : part 49 36 7 = true := by decide +kernel
theorem h49_43 : part 49 43 7 = true := by decide +kernel
theorem h49_50 : part 49 50 7 = true := by decide +kernel
theorem h49_57 : part 49 57 7 = true := by decide +kernel
theorem h49_64 : part 49 64 7 = true := by decide +kernel
theorem h49_71 : part 49 71 7 = true := by decide +kernel
theorem h49_78 : part 49 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
set_option maxRecDepth 36000
set_option maxHeartbeats 3500000
theorem h52_1 : part 52 1 7 = true := by decide +kernel
theorem h52_8 : part 52 8 7 = true := by decide +kernel
theorem h52_15 : part 52 15 7 = true := by decide +kernel
theorem h52_22 : part 52 22 7 = true := by decide +kernel
theorem h52_29 : part 52 29 7 = true := by decide +kernel
theorem h52_36 : part 52 36 7 = true := by decide +kernel
theorem h52_43 : part 52 43 7 = true := by decide +kernel
theorem h52_50 : part 52 50 7 = true := by decide +kernel
theorem h52_57 : part 52 57 7 = true := by decide +kernel
theorem h52_64 : part 52 64 7 = true := by decide +kernel
theorem h52_71 : part 52 71 7 = true := by decide +kernel
theorem h52_78 : part 52 78 7 = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

end
