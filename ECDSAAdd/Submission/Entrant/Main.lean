import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.Window
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

-- The generic window's domain (K2's `WindowCovered.domainW`): `[131,529] [786,1045] [1049,1300] [1556,1812]`.
def domain (q : Nat) := (131 ≤ q && q ≤ 529) || (786 ≤ q && q ≤ 1045) || (1049 ≤ q && q ≤ 1300) || (1556 ≤ q && q ≤ 1812)

theorem domain_eq (q : Nat) : domain q = WindowCovered.domainW q := rfl

def Covered (P : Program) : Prop := ∀ q ∈ wires P, domain q = true

theorem covered_append {P Q : Program} (a : Covered P) (b : Covered Q) : Covered (P ++ Q) := by
  intro q h
  rw [wires_append,Finset.mem_union] at h
  exact h.elim (a q) (b q)

theorem from_check {P : Program} (h : allSites domain P = true) : Covered P := allSites_sound h

private theorem interval0 : (List.range' 131 399).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
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
  ordered d (group d 1 24) (ordered d (ten 25 (!d)) (ordered d (group d 27 1) (ordered d (ten 28 (!d)) (ordered d (group d 30 1) (ordered d (ten 31 (!d)) (ordered d (group d 33 1) (ordered d (ten 34 (!d)) (ordered d (group d 36 1) (ordered d (ten 37 (!d)) (ordered d (group d 39 1) (ordered d (ten 40 (!d)) (ordered d (group d 42 1) (ordered d (ten 43 (!d)) (ordered d (group d 45 1) (ordered d (ten 46 (!d)) (ordered d (group d 48 1) (ordered d (ten 49 (!d)) (ordered d (group d 51 1) (ordered d (ten 52 (!d)) (group d 54 31))))))))))))))))))))

/-- the actual field group is the reference group (no cell any more). -/
def group84 (d : Bool) : Program := group84rec d

/-- the tape of the reference run is the actual tape (no cell any more). -/
def cellTape (_d : Bool) (m : List Bool) : List Bool := m




private theorem ord (c : Cost) (d : Bool) (a b : Program) :
    c.measure (ordered d a b)=c.measure a+c.measure b := by
  cases d <;> simp [ordered,c.append,Nat.add_comm]

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
    c.measure (group d 1 84) = c.measure (group d 1 24)+c.measure (group d 25 2)+c.measure (group d 27 1)+c.measure (group d 28 2)+c.measure (group d 30 1)+c.measure (group d 31 2)+c.measure (group d 33 1)+c.measure (group d 34 2)+c.measure (group d 36 1)+c.measure (group d 37 2)+c.measure (group d 39 1)+c.measure (group d 40 2)+c.measure (group d 42 1)+c.measure (group d 43 2)+c.measure (group d 45 1)+c.measure (group d 46 2)+c.measure (group d 48 1)+c.measure (group d 49 2)+c.measure (group d 51 1)+c.measure (group d 52 2)+c.measure (group d 54 31) := by
  simp only [group,distribute]
  have p0 := split c d 1 24 60
  have p1 := split c d 25 2 58
  have p2 := split c d 27 1 57
  have p3 := split c d 28 2 55
  have p4 := split c d 30 1 54
  have p5 := split c d 31 2 52
  have p6 := split c d 33 1 51
  have p7 := split c d 34 2 49
  have p8 := split c d 36 1 48
  have p9 := split c d 37 2 46
  have p10 := split c d 39 1 45
  have p11 := split c d 40 2 43
  have p12 := split c d 42 1 42
  have p13 := split c d 43 2 40
  have p14 := split c d 45 1 39
  have p15 := split c d 46 2 37
  have p16 := split c d 48 1 36
  have p17 := split c d 49 2 34
  have p18 := split c d 51 1 33
  have p19 := split c d 52 2 31
  norm_num only [] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19
  omega




/-- the field group with its ten archive ten-blocks. -/
private theorem solve (c : Cost) (d : Bool) (delta : Nat)
    (h : ∀j,c.measure (ten j (!d))=c.measure (group d j 2)+delta) :
    c.measure (group84 d) = c.measure (group d 1 84)+10*delta := by
  simp only [group84,group84rec,ord,h,partition]
  omega

theorem group_cost_div :
    toffoliCount (group84 true) = toffoliCount (group true 1 84)+1950 ∧
    measurementCount (group84 true) = measurementCount (group true 1 84)+2770 := by
  have t := solve tc true (if true then 195 else 192) (fun j => (overhead j true).1)
  have m := solve mc true 277 (fun j => (overhead j true).2)
  rw [show tc.measure = toffoliCount from rfl] at t
  rw [show mc.measure = measurementCount from rfl] at m
  exact ⟨t.trans (by norm_num), m.trans (by norm_num)⟩

theorem group_cost_mul :
    toffoliCount (group84 false) = toffoliCount (group false 1 84)+1920 ∧
    measurementCount (group84 false) = measurementCount (group false 1 84)+2770 := by
  have t := solve tc false (if false then 195 else 192) (fun j => (overhead j false).1)
  have m := solve mc false 277 (fun j => (overhead j false).2)
  rw [show tc.measure = toffoliCount from rfl] at t
  rw [show mc.measure = measurementCount from rfl] at m
  exact ⟨t.trans (by norm_num), m.trans (by norm_num)⟩
/-- Static syntax counts include both correction lists of every measurement. -/
theorem group_slots (d : Bool) :
    slots.measure (group84 d) = slots.measure (group d 1 84)+10*(if d then 5141 else 5535) := by
  have h (j : Nat) : slots.measure (ten j (!d)) =
      slots.measure (group d j 2)+(if d then 5141 else 5535) := by
    rw [show slots.measure=Challenge.gateSlots from rfl,group,distribute]
    cases d <;>
      simp only [distributed,PacketSequence.program,Bool.not_true,Bool.not_false,ten,first,second,
        enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
        List.append_nil,Challenge.gateSlots_append,Baselines.rename_gateSlots,enter0_gateSlots,
        switch0_gateSlots,leave0_gateSlots,enter1_gateSlots,switch1_gateSlots,leave1_gateSlots] <;> omega
  simp only [group84,group84rec,ord,h,partition]
  omega
end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [120,271); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 104 ++
    forward45plus1 d ++ Rolling1588TickGap.forward d 271 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 271 tail ++
    reverse45plus1 d ++ Rolling1588.reverse d 16 104) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

private theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (forward45plus1 d)+f=c.measure (Rolling1588TickGap.forward d 120 151))
    (hr : c.measure (reverse45plus1 d)+r=c.measure (Rolling1588.reverse d 120 151)) :
    c.measure (forward d tail)+f=c.measure (Stair44WalkRun.forward d (255+tail)) ∧
    c.measure (backward d tail)+r=c.measure (Stair44WalkRun.backward d (255+tail)) := by
  have a := StairRestSupport.forward_append d 104 16 (151+tail)
  have b := StairRestSupport.forward_append d 151 120 tail
  have x := StairRestSupport.reverse_append d 104 16 (151+tail)
  have y := StairRestSupport.reverse_append d 151 120 tail
  change Rolling1588TickGap.forward d 16 (104+(151+tail)) =
    Rolling1588TickGap.forward d 16 104 ++ Rolling1588TickGap.forward d 120 (151+tail) at a
  change Rolling1588.reverse d 16 (104+(151+tail)) =
    Rolling1588.reverse d 120 (151+tail) ++ Rolling1588.reverse d 16 104 at x
  rw [b] at a
  rw [y] at x
  have num : 255+tail=104+(151+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,forward,backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

attribute [local irreducible] Partial.forward45plus1 Partial.reverse45plus1 Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 13892 else 13902)=
      toffoliCount (Stair44WalkRun.forward d (255+tail)) ∧
    toffoliCount (backward d tail)+(if d then 13749 else 13749)=
      toffoliCount (Stair44WalkRun.backward d (255+tail)) ∧
    measurementCount (forward d tail)+6935=measurementCount (Stair44WalkRun.forward d (255+tail)) ∧
    measurementCount (backward d tail)+6989=measurementCount (Stair44WalkRun.backward d (255+tail)) := by
  cases d
  · have sf := StockWindowCosts.stock120 false
    have a : toffoliCount (forward45plus1 false) = 63609 := by rw [Partial.assembly]; exact WindowParams.ship_toffoliF_false
    have b : toffoliCount (reverse45plus1 false) = 63721 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_toffoliR_false
    have c : measurementCount (forward45plus1 false) = 31846 := by rw [Partial.assembly]; exact WindowParams.ship_measureF.2
    have e : measurementCount (reverse45plus1 false) = 31713 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_measureR.2
    have t := walk tc false tail 13902 13749
      (subEq 13902 a sf.1 (by omega)) (subEq 13749 b sf.2.2.1 (by omega))
    have m := walk mc false tail 6935 6989
      (subEq 6935 c sf.2.1 (by omega)) (subEq 6989 e sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,m⟩
  · have sf := StockWindowCosts.stock120 true
    have a : toffoliCount (forward45plus1 true) = 63619 := by rw [Partial.assembly]; exact WindowParams.ship_toffoliF_true
    have b : toffoliCount (reverse45plus1 true) = 63721 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_toffoliR_true
    have c : measurementCount (forward45plus1 true) = 31846 := by rw [Partial.assembly]; exact WindowParams.ship_measureF.1
    have e : measurementCount (reverse45plus1 true) = 31713 := by rw [Partial.unwind_assembly]; exact WindowParams.ship_measureR.1
    have t := walk tc true tail 13892 13749
      (subEq 13892 a sf.1 (by omega)) (subEq 13749 b sf.2.2.1 (by omega))
    have m := walk mc true tail 6935 6989
      (subEq 6935 c sf.2.1 (by omega)) (subEq 6989 e sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,m⟩


/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 255+tail=n)
    (hf : (if d then 13892 else 13902)=f) (hr : (if d then 13749 else 13749)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+6935=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+6989=mc.measure (Stair44WalkRun.backward d n) := by
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

theorem kernels (c : Cost) (gainF gainR fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 154)+gainF=c.measure (Stair44WalkRun.forward true 409))
    (dR : c.measure (WindowWalkCosts.backward false 235)+gainR=c.measure (Stair44WalkRun.backward false 490))
    (g : c.measure (WindowFieldCosts.group84 true)=c.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    c.measure divide+gainF+gainR=c.measure Stair44Outer.divide+fieldExtra := by
  have h := field_delta c true _ g
  simp only [if_true] at h
  simp only [divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

theorem kernelsM (c : Cost) (k gainF gainR fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 234)+gainF=c.measure (Stair44WalkRun.forward false 489))
    (mR : c.measure (WindowWalkCosts.backward true 154)+gainR=c.measure (Stair44WalkRun.backward true 409))
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
    tc.measure (WindowFieldCosts.group84 true)=tc.measure (WindowFieldCosts.group true 1 84)+1950 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_div.1
private theorem fieldMcDiv :
    mc.measure (WindowFieldCosts.group84 true)=mc.measure (WindowFieldCosts.group true 1 84)+2770 := by
  rw [show mc.measure=measurementCount from rfl]
  exact WindowFieldCosts.group_cost_div.2
private theorem fieldTcMul :
    tc.measure (WindowFieldCosts.group84 false)=tc.measure (WindowFieldCosts.group false 1 84)+1920 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact WindowFieldCosts.group_cost_mul.1
private theorem fieldMcMul :
    mc.measure (WindowFieldCosts.group84 false)=mc.measure (WindowFieldCosts.group false 1 84)+2770 := by
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

theorem tc_div : tc.measure divide+13892+13749=tc.measure Stair44Outer.divide+1950 :=
  kernels tc 13892 13749 1950 (WindowWalkCosts.inst true 154 409 13892 13749 rfl rfl rfl).1
    (WindowWalkCosts.inst false 235 490 13902 13749 rfl rfl rfl).2.1 fieldTcDiv

theorem tc_mul (k : Nat) : tc.measure (multiply k)+13902+13749=tc.measure (Stair44Outer.multiply k)+1920 :=
  kernelsM tc k 13902 13749 1920 (WindowWalkCosts.inst false 234 489 13902 13749 rfl rfl rfl).1
    (WindowWalkCosts.inst true 154 409 13892 13749 rfl rfl rfl).2.1 fieldTcMul

theorem mc_div : mc.measure divide+6935+6989=mc.measure Stair44Outer.divide+2770 :=
  kernels mc 6935 6989 2770 (WindowWalkCosts.inst true 154 409 13892 13749 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst false 235 490 13902 13749 rfl rfl rfl).2.2.2 fieldMcDiv

theorem mc_mul (k : Nat) : mc.measure (multiply k)+6935+6989=mc.measure (Stair44Outer.multiply k)+2770 :=
  kernelsM mc k 6935 6989 2770 (WindowWalkCosts.inst false 234 489 13902 13749 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst true 154 409 13892 13749 rfl rfl rfl).2.2.2 fieldMcMul

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+51422=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+22308=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 51422 (pair_delta2 tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 22308 (sum_delta2 mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2117684 ∧
    measurementCount (program C) ≤ 1498616 := by
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

private theorem walk (c : Cost) (d : Bool) (tail f r n : Nat) (hn : 255+tail=n)
    (hf : c.measure (Partial.forward45plus1 d) ≤ f) (hr : c.measure (Partial.reverse45plus1 d) ≤ r) :
    c.measure (WindowWalkCosts.forward d tail) ≤ c.measure (Stair44WalkRun.forward d n)+f ∧
    c.measure (WindowWalkCosts.backward d tail) ≤ c.measure (Stair44WalkRun.backward d n)+r := by
  subst n
  have a := StairRestSupport.forward_append d 104 16 (151+tail)
  have b := StairRestSupport.forward_append d 151 120 tail
  have x := StairRestSupport.reverse_append d 104 16 (151+tail)
  have y := StairRestSupport.reverse_append d 151 120 tail
  change Rolling1588TickGap.forward d 16 (104+(151+tail)) =
    Rolling1588TickGap.forward d 16 104 ++ Rolling1588TickGap.forward d 120 (151+tail) at a
  change Rolling1588.reverse d 16 (104+(151+tail)) =
    Rolling1588.reverse d 120 (151+tail) ++ Rolling1588.reverse d 16 104 at x
  rw [b] at a
  rw [y] at x
  have num : 255+tail=104+(151+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,WindowWalkCosts.forward,WindowWalkCosts.backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

private theorem kernels (c : Cost) (gainF gainR fieldExtra : Nat)
    (dF : c.measure (WindowWalkCosts.forward true 154) ≤ c.measure (Stair44WalkRun.forward true 409)+gainF)
    (dR : c.measure (WindowWalkCosts.backward false 235) ≤ c.measure (Stair44WalkRun.backward false 490)+gainR)
    (g : c.measure (WindowFieldCosts.group84 true)=c.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    c.measure WindowCallerCosts.divide ≤ c.measure Stair44Outer.divide+gainF+gainR+fieldExtra := by
  have h  := WindowCallerCosts.field_delta c true _ g
  simp only [if_true] at h
  simp only [WindowCallerCosts.divide,Stair44Outer.divide,phasePlace,kernelPlace,c.append,c.rename]
  omega

private theorem kernelsM (c : Cost) (k gainF gainR fieldExtra : Nat)
    (mF : c.measure (WindowWalkCosts.forward false 234) ≤ c.measure (Stair44WalkRun.forward false 489)+gainF)
    (mR : c.measure (WindowWalkCosts.backward true 154) ≤ c.measure (Stair44WalkRun.backward true 409)+gainR)
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
private theorem groupCap (d : Bool) (n : Nat) (hn : 10*(if d then 5141 else 5535)=n) :
    slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  rw [WindowFieldCosts.group_slots d, hn]
private theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+825001+827694+51410 :=
  kernels slots 825001 827694 51410
    (walk slots true 154 825001 827626 409 rfl (casts WindowParams.ship_slotsF.1) (casts WindowParams.ship_slotsR.1)).1
    (walk slots false 235 825001 827694 490 rfl (casts WindowParams.ship_slotsF.2) (casts WindowParams.ship_slotsR.2)).2
    (groupCap true 51410 rfl)

private theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+825001+827626+55350 :=
  kernelsM slots k 825001 827626 55350
    (walk slots false 234 825001 827694 489 rfl (casts WindowParams.ship_slotsF.2) (casts WindowParams.ship_slotsR.2)).1
    (walk slots true 154 825001 827626 409 rfl (casts WindowParams.ship_slotsF.1) (casts WindowParams.ship_slotsR.1)).2
    (groupCap false 55350 rfl)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+825001+827694+51410)
    (hm : b ≤ y+825001+827626+55350) : a+b ≤ x+y+3412082 := by omega

private theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+3412082 :=
  finite_upper slots C cx cy 3412082 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 54272564 := by
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

private theorem hook (j : Nat) (hj : j∈[25,28,31,34,37,40,43,46,49,52]) (op : Stage) :
    Sound (fieldHook j op) := by
  have span : j∈List.range' 1 83 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; apply List.mem_range'_1.mpr; omega
  have chk : (fieldSites j).all (fun q => decide (InDom q))=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
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

private theorem pair (d : Bool) (j : Nat) (pick : j∈[25,28,31,34,37,40,43,46,49,52]) (lo : 1≤j) (hi : j≤83) :
    Sound (ten j (!d)) := by
  have here := whole d j lo (by omega)
  have next := whole d (j+1) (by omega) (by omega)
  have firstOK : Sound (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (second j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))



theorem group84_ok (d : Bool) : Sound (group84 d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  exact ord (ordinary d 1 24 (by decide) (by decide))
    (ord (pair d 25 (by decide) (by decide) (by decide))
    (ord (ordinary d 27 1 (by decide) (by decide))
    (ord (pair d 28 (by decide) (by decide) (by decide))
    (ord (ordinary d 30 1 (by decide) (by decide))
    (ord (pair d 31 (by decide) (by decide) (by decide))
    (ord (ordinary d 33 1 (by decide) (by decide))
    (ord (pair d 34 (by decide) (by decide) (by decide))
    (ord (ordinary d 36 1 (by decide) (by decide))
    (ord (pair d 37 (by decide) (by decide) (by decide))
    (ord (ordinary d 39 1 (by decide) (by decide))
    (ord (pair d 40 (by decide) (by decide) (by decide))
    (ord (ordinary d 42 1 (by decide) (by decide))
    (ord (pair d 43 (by decide) (by decide) (by decide))
    (ord (ordinary d 45 1 (by decide) (by decide))
    (ord (pair d 46 (by decide) (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide) (by decide))
    (ord (pair d 49 (by decide) (by decide) (by decide))
    (ord (ordinary d 51 1 (by decide) (by decide))
    (ord (pair d 52 (by decide) (by decide) (by decide))
    (ordinary d 54 31 (by decide) (by decide)))))))))))))))))))))

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


theorem group84_ok (d : Bool) : PieceOK reserved TP (group84 d) := by
  have ord {a b : Program} (ha : PieceOK reserved TP a) (hb : PieceOK reserved TP b) :
      PieceOK reserved TP (ordered d a b) := by cases d <;> first | exact ha.append hb | exact hb.append ha
  exact ord (ordinary d 1 24 (by decide) (by decide))
    (ord (pair d 25 (by decide) (by decide))
    (ord (ordinary d 27 1 (by decide) (by decide))
    (ord (pair d 28 (by decide) (by decide))
    (ord (ordinary d 30 1 (by decide) (by decide))
    (ord (pair d 31 (by decide) (by decide))
    (ord (ordinary d 33 1 (by decide) (by decide))
    (ord (pair d 34 (by decide) (by decide))
    (ord (ordinary d 36 1 (by decide) (by decide))
    (ord (pair d 37 (by decide) (by decide))
    (ord (ordinary d 39 1 (by decide) (by decide))
    (ord (pair d 40 (by decide) (by decide))
    (ord (ordinary d 42 1 (by decide) (by decide))
    (ord (pair d 43 (by decide) (by decide))
    (ord (ordinary d 45 1 (by decide) (by decide))
    (ord (pair d 46 (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide) (by decide))
    (ord (pair d 49 (by decide) (by decide))
    (ord (ordinary d 51 1 (by decide) (by decide))
    (ord (pair d 52 (by decide) (by decide))
    (ordinary d 54 31 (by decide) (by decide)))))))))))))))))))))

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

theorem walkF (d : Bool) (tail : Nat) (bound : 16+(255+tail)≤506)
    (new : GoodWindow (Partial.forward45plus1 d)) :
    PieceOK reserved PP (WindowWalkCosts.forward d tail) := by
  have old := weaken (Stair44PhaseSites.forward d (255+tail) bound)
  have a := StairRestSupport.forward_append d 104 16 (151+tail)
  have b := StairRestSupport.forward_append d 151 120 tail
  change Rolling1588TickGap.forward d 16 (104+(151+tail)) =
    Rolling1588TickGap.forward d 16 104 ++ Rolling1588TickGap.forward d 120 (151+tail) at a
  rw [b] at a
  have num : 255+tail=104+(151+tail) := by omega
  simp only [Stair44WalkRun.forward,num,a,app,ren] at old
  simp only [WindowWalkCosts.forward,app,ren]
  exact ⟨old.1,⟨old.2.1,native new⟩,old.2.2.2⟩

theorem walkR (d : Bool) (tail : Nat) (bound : 16+(255+tail)≤506)
    (new : GoodWindow (Partial.reverse45plus1 d)) :
    PieceOK reserved PP (WindowWalkCosts.backward d tail) := by
  have old := weaken (Stair44PhaseSites.backward d (255+tail) bound)
  have a := StairRestSupport.reverse_append d 104 16 (151+tail)
  have b := StairRestSupport.reverse_append d 151 120 tail
  change Rolling1588.reverse d 16 (104+(151+tail)) =
    Rolling1588.reverse d 120 (151+tail) ++ Rolling1588.reverse d 16 104 at a
  rw [b] at a
  have num : 255+tail=104+(151+tail) := by omega
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

private theorem fw (d : Bool) (tail n : Nat) (hn : 15+(255+tail)=n)
    (ref_ : Sound (Rolling1588TickGap.forward d 1 n))
    (p : GatePhysical (Partial.forward45plus1 d)) : Sound (WindowWalkCosts.forward d tail) := by
  subst n
  rw [forward_append d 15 1 (255+tail)] at ref_
  obtain ⟨early,late⟩ := parts ref_
  change Sound (Rolling1588TickGap.forward d 16 (255+tail)) at late
  rw [show 255+tail=104+(151+tail) by omega,forward_append d 104 16 (151+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 120 (151+tail)) at ms
  rw [forward_append d 151 120 tail] at ms
  have patch : Sound (Partial.forward45plus1 d) := ⟨p,dom (PartialSites.forward45plus1_domain d)⟩
  have last : Sound (Rolling1588TickGap.forward d 271 tail) := (parts ms).2
  exact sound_append (sound_rename _ first.injective firstDom early)
    (sound_rename _ rest.injective restDom (sound_append (sound_append pre patch) last))

private theorem bw (d : Bool) (tail n : Nat) (hn : 15+(255+tail)=n)
    (ref_ : Sound (Rolling1588.reverse d 1 n))
    (p : GatePhysical (Partial.reverse45plus1 d)) : Sound (WindowWalkCosts.backward d tail) := by
  subst n
  rw [reverse_append d 15 1 (255+tail)] at ref_
  obtain ⟨late,early⟩ := parts ref_
  change Sound (Rolling1588.reverse d 16 (255+tail)) at late
  rw [show 255+tail=104+(151+tail) by omega,reverse_append d 104 16 (151+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 120 (151+tail)) at ms
  rw [reverse_append d 151 120 tail] at ms
  have patch : Sound (Partial.reverse45plus1 d) := ⟨p,dom (PartialSites.reverse45plus1_domain d)⟩
  have last : Sound (Rolling1588.reverse d 271 tail) := (parts ms).1
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
  exact ⟨⟨⟨⟨⟨phase (fw true 154 424 rfl sound_forward424 (ff _)),phase P.firstPack⟩,rest_physical _ field⟩,
    phase tail⟩,phase (bw false 235 505 rfl walk (rr _))⟩,phase (sound_rename _ first.injective firstDom native)⟩

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
  exact ⟨⟨⟨⟨⟨phase (fw false 234 504 rfl walk (ff _)),phase tail⟩,rest_physical _ field⟩,phase P.firstUnpack⟩,
    phase (bw true 154 424 rfl sound_reverse424 (rr _))⟩,
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
  (((((phase (walkF true 154 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.pack)))).append
    (ok_kernel entryField)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.reverseTail)))).append
    (phase (walkR false 235 (by decide) r))).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.native)))

theorem multiplication (k : Nat) (f : GoodWindow (Partial.forward45plus1 false))
    (r : GoodWindow (Partial.reverse45plus1 true)) :
    PieceOK reserved UG (WindowCallerCosts.multiply k) :=
  (((((phase (walkF false 234 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.forwardTail)))).append
    (ok_kernel exitField)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.unpack)))).append
    (phase (walkR true 154 (by decide) r))).append (weaken (Stair44PhaseSites.exitX k))

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
def bounds : Challenge.Bounds := ⟨2117684,1498616,1543,54272564⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowCallerCosts.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowCallerCosts.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowCallerCosts.totals C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1498616
    rw [normalize_measurements]
    exact (WindowCallerCosts.totals C).2
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1543
    rw [normalize_qubits]
    exact WindowCallerCosts.qubitBound C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 54272564
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
def banks := [25,28,31,34,37,40,43,46,49,52]
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
theorem ten_masked (j : Nat) (hs : j ∈ starts) (hj : j ∈ List.range' 1 83)
    (rev : Bool) (row : Nat) (hr : row < 63145) (m : List Bool) (a r : State)
    (other : Finset Wire) (apart : ∀ q ∈ inside j, q ∉ other)
    (ha : avoids (first j rev) other) (hb : avoids (second j rev) other)
    (arch : frame j row (inputCols (enter rev)) a) (same : offBanks (bank j) other a r)
    (ph : a.phase = r.phase)
    (before_ : frame j row (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j row middle (refMiddle j rev m r))
    (after_ : frame j row (StairArchiveNativeCut.canonical rev rev) (refExit j rev m r)) :
    let next := run (ten j rev) m a
    let final := refExit j rev m r
    next.phase = final.phase ∧ offBanks (bank j) other next final ∧
      frame j row (outputCols (leave rev)) next := by
  let shadow := mask other a r
  have mid : refMiddle j rev m shadow = mask other a (refMiddle j rev m r) := by
    exact mask_run (first j rev) other _ a r ha
  have fin : refExit j rev m shadow = mask other a (refExit j rev m r) := by
    unfold refExit
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
  have mm : frame j row middle (refMiddle j rev m shadow) := mid ▸ mask_frame _ _ _ _ _ _ apart middle_
  have ff : frame j row (StairArchiveNativeCut.canonical rev rev) (refExit j rev m shadow) := fin ▸ mask_frame _ _ _ _ _ _ apart after_
  have result := ten_run j hs hj rev row hr m a shadow arch outer ph
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

namespace ECDSAAdd.Entrant.StairPacket.WindowBankCheck
open Arithmetic MappedCompressed ArchiveFieldScratch StairArchiveInactive StairArchiveNativeCut StairArchiveRelease WindowFieldMask
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 100000
private theorem splitRange : List.range' 1 84 = List.range' 1 7 ++ List.range' 8 7 ++ List.range' 15 7 ++ List.range' 22 7 ++ List.range' 29 7 ++ List.range' 36 7 ++ List.range' 43 7 ++ List.range' 50 7 ++ List.range' 57 7 ++ List.range' 64 7 ++ List.range' 71 7 ++ List.range' 78 7 := by decide +kernel
attribute [local irreducible] allowed fieldPort packet cover preimage
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
private theorem pass (h : Nat) (hm : h ∈ banks) : (List.range' 1 84).all (allowed h) = true := by
  simp only [banks,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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

private def distinct (j h : Nat) := j=h || (slots h).all (fun q =>
  !((List.range 121).map (fieldPort j)).contains q)
private theorem distinct_ok : banks.all (fun j=>banks.all (distinct j))=true := by decide +kernel

theorem separate (j h : Nat) (jm : j∈banks) (hm : h∈banks) (ne : j≠h) :
    ∀ q∈inside j, q∉bank h := by
  have ok := List.all_eq_true.mp (List.all_eq_true.mp distinct_ok j jm) h hm
  simp only [distinct, decide_eq_false ne, Bool.false_or] at ok
  intro q own other
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp other
  have qmem : fieldPort h i ∈ slots h := List.mem_map.mpr ⟨i,List.mem_range.mpr (Finset.mem_range.mp hi),rfl⟩
  have outside := List.all_eq_true.mp ok _ qmem
  have inside' : fieldPort h i ∈ (List.range 121).map (fieldPort j) := by
    obtain ⟨t,ht,eq⟩ := Finset.mem_image.mp own
    exact List.mem_map.mpr ⟨t,List.mem_range.mpr (Finset.mem_range.mp ht),eq⟩
  simp [inside'] at outside
end ECDSAAdd.Entrant.StairPacket.WindowBankCheck

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldMask
open Arithmetic MappedCompressed StairArchiveRelease StairArchiveNativeCut StairArchiveInactive
open ArchiveFieldScratch StairArchiveTen CodecBitSliceVerify
def bankIds : Finset Nat := {25,28,31,34,37,40,43,46,49,52}
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
def nativeRanges (j n : Nat) := (j=1 ∧ n=24) ∨ (j=27 ∧ n=1) ∨ (j=30 ∧ n=1) ∨ (j=33 ∧ n=1) ∨ (j=36 ∧ n=1) ∨ (j=39 ∧ n=1) ∨ (j=42 ∧ n=1) ∨ (j=45 ∧ n=1) ∨ (j=48 ∧ n=1) ∨ (j=51 ∧ n=1) ∨ (j=54 ∧ n=31)
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
private theorem geometry {j : Nat} (h : j∈bankIds) : j∈starts ∧ j∈List.range' 1 83 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
private theorem apart {j : Nat} (hj : j∈bankIds) : ∀ q∈inside j, q∉others j := by
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

theorem stepTen (j : Nat) (hj : j∈bankIds) (rows : Nat→Nat) (code : Nat→Cols) (rev : Bool)
    (bound : rows j < 63145) (m : List Bool) (a r : State) (h : Fits rows code a r)
    (active : code j=inputCols (enter rev))
    (before_ : frame j (rows j) (StairArchiveNativeCut.canonical (!rev) (!rev)) r)
    (middle_ : frame j (rows j) middle (refMiddle j rev m r))
    (after_ : frame j (rows j) (StairArchiveNativeCut.canonical rev rev) (refExit j rev m r)) :
    Fits rows (update code j (outputCols (leave rev))) (run (ten j rev) m a) (refExit j rev m r) := by
  have ⟨hs,hr⟩ := geometry hj
  have fa : avoids (first j rev) (others j) := by
    rw [first]; apply native_safe _ _ hj; cases rev <;> simp
  have sa : avoids (second j rev) (others j) := by
    rw [second]; apply native_safe _ _ hj; cases rev <;> simp
  have ea : avoids (ten j rev) (others j) := by
    rw [ten]; exact append_safe (hook_safe j hj _)
      (append_safe fa (append_safe (hook_safe j hj _) (append_safe sa (hook_safe j hj _))))
  have same : offBanks (bank j) (others j) a r := by
    intro q a0 a1; apply h.outside; rw [decompose j hj,Finset.mem_union]; exact fun hit => hit.elim a0 a1
  have result := ten_masked j hs hr rev (rows j) bound m a r (others j) (apart hj) fa sa
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
def Cuts (d : Bool) (row : Nat→Nat) (m : List Bool) (r : State) : Leg → Prop
  | .native _ _ => True
  | .paired j => frame j (row j) (StairArchiveNativeCut.canonical d d) r ∧
      frame j (row j) middle (refMiddle j (!d) m r) ∧ frame j (row j) (StairArchiveNativeCut.canonical (!d) (!d)) (refExit j (!d) m r)
def NativeTrail (d : Bool) (row : Nat→Nat) : List Leg → List Bool → State → Prop
  | [],_,_ => True
  | l::ls,m,r => Cuts d row m r l ∧ NativeTrail d row ls (nextTape d l m) (stock d m r l)

theorem travel (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (ls : List Leg) (m : List Bool) (a r : State) (c : Nat→Cols)
    (shape : valid d ls c) (cuts : NativeTrail d row ls m r) (initial : Fits row c a r) :
    Fits row (finalCode d ls c) (run (concatenate d ls) m a) (destination d ls m r) := by
  induction ls generalizing c m a r with
  | nil =>
    simpa only [concatenate,run,finalCode,destination] using initial
  | cons l ls ih =>
    obtain ⟨loc,tail⟩ := shape
    obtain ⟨here,rest⟩ := cuts
    have one : Fits row (codes d c l) (run (emitted d l) m a) (stock d m r l) := by
      cases l with
      | native j n => exact plain _ _ _ _ _ _ initial (groupSafe d j n loc)
      | paired j =>
        exact stepTen j loc.1 row c (!d) (bounded j loc.1) m a r initial loc.2
          (by simpa only [Bool.not_not] using here.1) here.2.1 here.2.2
    rw [concatenate,run_append,run_take]
    exact ih _ _ _ _ tail rest one

def plan : Bool→List Leg
  | true => [.native 1 24,.paired 25,.native 27 1,.paired 28,.native 30 1,.paired 31,.native 33 1,.paired 34,.native 36 1,.paired 37,.native 39 1,.paired 40,.native 42 1,.paired 43,.native 45 1,.paired 46,.native 48 1,.paired 49,.native 51 1,.paired 52,.native 54 31]
  | false => [.native 54 31,.paired 52,.native 51 1,.paired 49,.native 48 1,.paired 46,.native 45 1,.paired 43,.native 42 1,.paired 40,.native 39 1,.paired 37,.native 36 1,.paired 34,.native 33 1,.paired 31,.native 30 1,.paired 28,.native 27 1,.paired 25,.native 1 24]
def initialCode (d : Bool) : Nat→Cols := fun _=>inputCols (enter (!d))
private theorem emits (d : Bool) : group84rec d=concatenate d (plan d) := by
  cases d <;> simp only [group84rec,ordered,concatenate,emitted,plan,if_true,if_false,Bool.false_eq_true,
    List.append_assoc,List.append_nil]
private theorem valid_plan (d : Bool) : valid d (plan d) (initialCode d) := by
  cases d <;> simp [valid,plan,validLeg,nativeRanges,bankIds,codes,update,initialCode]
theorem group_run (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (m : List Bool) (a r : State) (initial : Fits row (initialCode d) a r)
    (native : NativeTrail d row (plan d) m r) :
    Fits row (finalCode d (plan d) (initialCode d)) (run (group84rec d) m a) (destination d (plan d) m r) := by
  rw [emits]
  exact travel d row bounded _ m a r _ (valid_plan d) native initial
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
def referenceTape0 (d : Bool) : List Leg → List Bool → List Bool
  | [],_ => []
  | l::ls,m => joinTapes (referenceLeg d l) (legTape d m l) (referenceTape0 d ls (nextTape d l m))
theorem ref_run (d : Bool) (ls : List Leg) (m : List Bool) (r : State) :
    destination d ls m r = run (referenceProgram d ls) (referenceTape0 d ls m) r := by
  induction ls generalizing m r with
  | nil => simp only [destination,referenceProgram,referenceTape0,run]
  | cons l ls ih => rw [destination,referenceProgram,referenceTape0,joined,←localTape,←ih]
/-- the reference tape of the record run, seen from the actual tape `m` of the field group. -/
def referenceTape (d : Bool) (ls : List Leg) (m : List Bool) : List Bool :=
  referenceTape0 d ls (WindowFieldCosts.cellTape d m)

set_option maxRecDepth 8000
set_option maxHeartbeats 900000
private theorem shape' (d : Bool) (p : Nat→Program) : PacketSequence.program d p 1 84 =
  let seq := PacketSequence.program d p
  if d then seq 1 24 ++ ((p 25 ++ p 26) ++ (seq 27 1 ++ ((p 28 ++ p 29) ++ (seq 30 1 ++ ((p 31 ++ p 32) ++ (seq 33 1 ++ ((p 34 ++ p 35) ++ (seq 36 1 ++ ((p 37 ++ p 38) ++ (seq 39 1 ++ ((p 40 ++ p 41) ++ (seq 42 1 ++ ((p 43 ++ p 44) ++ (seq 45 1 ++ ((p 46 ++ p 47) ++ (seq 48 1 ++ ((p 49 ++ p 50) ++ (seq 51 1 ++ ((p 52 ++ p 53) ++ (seq 54 31 ++ []))))))))))))))))))))
  else seq 54 31 ++ ((p 53 ++ p 52) ++ (seq 51 1 ++ ((p 50 ++ p 49) ++ (seq 48 1 ++ ((p 47 ++ p 46) ++ (seq 45 1 ++ ((p 44 ++ p 43) ++ (seq 42 1 ++ ((p 41 ++ p 40) ++ (seq 39 1 ++ ((p 38 ++ p 37) ++ (seq 36 1 ++ ((p 35 ++ p 34) ++ (seq 33 1 ++ ((p 32 ++ p 31) ++ (seq 30 1 ++ ((p 29 ++ p 28) ++ (seq 27 1 ++ ((p 26 ++ p 25) ++ (seq 1 24 ++ [])))))))))))))))))))) := by
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
  backwards : Bool

def guarded (labels neg : List Wire) (pivot : Option Wire) : Clause :=
  let ph := match pivot with
    | none => []
    | some z => ((List.range 16).erase z).map (fun i=>Aff.cx i z)
  let mid := (labels.drop 2).dropLast
  ⟨ph++neg.map Aff.x,labels[0]!,labels[1]!,labels.getLast!, mid.zipIdx.map (fun ⟨c,i⟩=>(c,18+i)),false⟩

def firstPair : Clause :=
  let c := guarded [1,2,0,3,4,5] [4,5] none
  { c with prep := (((List.range 16).erase 5).erase 12).map (fun i=>Aff.cx i 5) ++ c.prep, backwards := true }

def commonPrep : List Aff :=
  [8,9,10,11].map (Aff.cx 0) ++ ((List.range 16).erase 1).map (fun i=>Aff.cx i 1) ++ [Aff.x 1]

def tailLeft : Clause := guarded [8,9,10,11,1,0,12] [0,12] none

def tailRight : Clause :=
  let c := guarded [8,9,10,11,1,2,3,5,6,7,12,13,14,15] [2,3,5,6,7,12,13,14,15] none
  { c with prep := [2,3].map (Aff.cx 0) ++ [6,7,12,14,15].map (Aff.cx 4) ++ c.prep }

def positivePair : Clause := guarded [4,5,0,3,6,7,1] [] (some 1)

def negativePair : Clause := { tailLeft with prep := commonPrep ++ tailLeft.prep }

def literalPair : Clause :=
  { tailRight with prep := commonPrep ++ tailRight.prep, backwards := true }

def clauses : List Clause := [firstPair,positivePair,negativePair,literalPair]

def body (c : Clause) := affine c.prep ++
  ((if c.backwards then [Instr.CCX c.a c.b 17] ++ (chain 17 c.last 16 c.xs ++
    ([Instr.CCX c.a c.b 17] ++ chain 17 c.last 16 c.xs)) else mcx c.a c.b 17 c.last 16 c.xs) ++
    affine c.prep.reverse)

def arm (c : Clause) : Program :=
  affine c.prep ++ (chain 17 c.last 16 c.xs ++ affine c.prep.reverse)
def pairWord : Program :=
  let f := arm tailLeft ++ arm tailRight
  f ++ ([Instr.CCX 8 9 17] ++ (f ++ [Instr.CCX 8 9 17]))
def jointTail : Program := affine commonPrep ++ (pairWord ++ affine commonPrep.reverse)
def groupedRegion : Program := (body firstPair ++ body positivePair) ++ jointTail

-- Remove equal gates when each intervening gate can commute with them.
def gateDst : Instr → Wire
  | .X t | .CX _ t | .CCX _ _ t | .measureX t _ _ => t
def gateFree (q : Wire) : Instr → Bool
  | .X _ => true
  | .CX c _ => decide (c≠q)
  | .CCX a b _ => decide (a≠q ∧ b≠q)
  | .measureX _ _ _ => false
def swappable (g h : Instr) : Bool :=
  gateFree (gateDst g) g && gateFree (gateDst h) h &&
    gateFree (gateDst g) h && gateFree (gateDst h) g
def eraseMate (g : Instr) : Program → Option Program
  | [] => none
  | h::p => if g=h ∧ gateFree (gateDst g) g=true then some p
      else if swappable g h then (eraseMate g p).map (h::·) else none
def cancelPairs : Program → Program
  | [] => []
  | g::p => let q := cancelPairs p
      match eraseMate g q with
      | none => g::q
      | some r => r

end ECDSAAdd.Entrant.StairPacket.WindowParityDirty
namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed WindowParityDirty
def region : Program := cancelPairs groupedRegion
def site (j i : Nat) := OB5.sig 511 (NewHistory5.payloadWire base (8*j+i))
def other (j : Nat) := if j=46 then 49 else 46
def port (j q : Nat) : Wire :=
  if q<16 then site j q else if q=16 then FrontierEntry1591Field.host else site (other j) (q-17)
def bankCorrection (j : Nat) := renameProgram (port j) region
def correction := bankCorrection 25 ++ (bankCorrection 28 ++ (bankCorrection 31 ++ (bankCorrection 34 ++ (bankCorrection 37 ++ (bankCorrection 40 ++ (bankCorrection 43 ++ (bankCorrection 46 ++ (bankCorrection 49 ++ bankCorrection 52))))))))
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



-- ==== w4: build-w4b B2-b selected_receipt (b2b/Main_SelectedReceipt.lean) ====
-- BEGIN build-w4b NativeJ.selected_receipt (B2-b part 4)
-- Main (w4r): next to dadon's `NativePack{240,255}.selected_receipt` (after `StockCanonicalRow`, Main ~5436).
section

namespace ECDSAAdd.Entrant.StairPacket.NativeJ
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction StairArchiveTrace StockCanonicalRow Partial
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run onRails routed measurementCount body

/-- dadon's `NativePack{s}.selected_receipt`, generic: block `j` keeps the previous block's archive at the row
`select` picks from the recorded key. -/
theorem selected_receipt (j : Fin 23) (h2 : 1≤j.val) (h19 : j.val≤19) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:min z.u z.v<2^(sbP (start j)))
    (cut:PackedCut (EnterJ.lowerPairs j) (EnterJ.upperPairs j) (EnterJ.gate j) (EnterJ.flagN j) (EnterJ.flagF j)
      (EnterJ.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (sbP (start j)) 15 z)) (decide (Shadow.far (sbP (start j)) 15 z ∧ 2^(sbP (start j))≤z.u))
      (pullState (EnterJ.pull j) raw) (eraseSites (EnterJ.pending j) s))
    (input:SkywalkIntegerInput (EnterJ.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ.pull j (windowNet j (IntegerPacket.ports (shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Partial.enterP j) m s
      let tape:=m.drop (measurementCount (Partial.enterP j))
      (run (program j d) (tape.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) tape pre)).basis
        (ArchiveJ.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:min past.u past.v<2^(sbP (start (prev j))))
    (prior:PastFacts (prev j) (ArchiveJ.rawPorts (prev j)) (sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    let v:=key (sbP (start (prev j))) past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    select v<63145 ∧ Encodes v (select v) ∧ Kept (ArchiveJ.codePorts (prev j)) d (select v) out:=by
  let pre:=run (Partial.enterP j) m s
  let tape:=m.drop (measurementCount (Partial.enterP j))
  let T:=Shadow.reduced (sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd (sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨_,row,limit,frame⟩:=admits j h2 (by omega) d s m tape (tape.drop (measurementCount (routed j 0 1))) Z parity
    ready.2.1 scratch past pg ps cross po pm prior
  have held:=bank_kept j h2 (by omega) d s m tape (tape.drop (measurementCount (routed j 0 1))) Z parity ready.2.1
  have all:=frame_key (prev j) (ArchiveJ.rawPorts (prev j))
    (ArchiveJ.chronological_all (prev j) (by simp only [prev]; omega)) row (sbP (start (prev j))) past pg ps cross s _
    prior held frame
  have spec:=select_spec ⟨row,limit,all⟩
  have final:=receipt j h2 (by omega) d pre tape _ spec.1 (reframe limit all (ArchiveJ.rawPorts (prev j)) _ frame)
  dsimp only [nextWindow,window]
  simp only [run_append,run_take]
  exact ⟨spec.1,spec.2,final.1⟩

end ECDSAAdd.Entrant.StairPacket.NativeJ

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
attribute [local irreducible] run body routed measurementCount

/-! Generic history hand-off of an interior window block `j` (par-c2; dadon's `Ordinary{s}Exit`, `Ordinary{s}Native`,
`Logical{s}Exit`). The block's pack re-encodes the cells of ticks `s-15..s-11` exactly as the stock encoder of
group `s-15` does, and the logical end state differs from the stock run only on the archived cells of ticks
`s-10..s-1` (`newBank`). Interior: `oldStart s = s-15` (par-a's `oldStart_interior`). Blocks `1 ≤ j ≤ 21`. -/

def plain (j : Fin 23) : Fin 10 → Wire := History5.historyMap base (start j-15)
def newBank (j : Fin 23) : List Wire := (List.range' (start j-10) 10).flatMap (fun r=>[base r,base (1028+r)])

theorem plain_cell (j : Fin 23) (i : Fin 10) :
    (i.val%2=0 ∧ (plain j i:Nat)=start j-15+i.val/2+16) ∨ (i.val%2≠0 ∧ (plain j i:Nat)=start j-15+i.val/2+1044) := by
  simp only [plain,History5.historyMap,History5.historyId,base,Wire]
  split
  · left; constructor; assumption; omega
  · right; constructor; assumption; omega
theorem plain_inj (j : Fin 23) : Function.Injective (plain j) := by
  intro a b e
  have ha:=a.isLt; have hb:=b.isLt
  have ca:=plain_cell j a; have cb:=plain_cell j b
  have e':(plain j a:Nat)=plain j b:=e
  apply Fin.ext
  simp only [Wire] at ca cb e'
  omega
/-- `OB5.sig s` and `OB5.sig (s+14)` agree on these cells (both swap the moved history cells). -/
theorem sig_same (j : Fin 23) (i : Fin 10) :
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

theorem heads_all : ∀ j : Fin 23, 1≤j.val → j.val≤21 → ∀i:Fin 10,
    oldRange (start j+1) (windowNet j (NativeJ.history j i)) ∧
    NativeJ.history j i∉ArchiveJ.rawHead (NativeJ.prev j) ∧ ArchiveJ.Band (start (NativeJ.prev j)+15) (NativeJ.history j i) ∧
    NativeJ.history j i∉EnterJ.pending j ∧ NativeJ.history j i≠EnterJ.flagN j ∧ NativeJ.history j i≠EnterJ.flagF j ∧
    NativeJ.history j i≠EnterJ.flagU j ∧ NativeJ.history j i∉RailPair.sites (EnterJ.upperPairs j) ∧
    EnterJ.pull j (NativeJ.history j i)=plain j i := by
  decide +kernel

theorem kept (j:Fin 23) (admin:Program) (m:List Bool) (s:State) (q:Wire) (early:oldRange (start j+1) (windowNet j q)) :
    (run (body j admin) m s).basis q=
      (run admin (m.drop (measurementCount (routed j 0 1))) (run (routed j 0 1) m s)).basis q := by
  simp only [body,run_append,run_take]
  exact route_outside j 1 14 (by decide) q (old_clear (by decide) early) _ _

theorem pastInput (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (x p:Nat) (good:Bounds x p) (raw:State)
    (dom:Domain (start j) x p raw) (i:Fin 10) :
    raw.basis (plain j i)=(run (span (start j) 15) [] raw).basis (plain j i) := by
  have pp:=preservePast (start j) 15 x p (start j-15+i.val/2) (by simp only [start]; omega) good raw dom
    (by simp only [start]; omega) []
  rcases plain_cell j i with ⟨-,e⟩|⟨-,e⟩
  · rw [e]; exact pp.1.symm
  · rw [e,show start j-15+i.val/2+1044=base (1028+(start j-15+i.val/2)) by simp only [base]; omega]; exact pp.2.symm

theorem encode (j : Fin 23) (h1 : 1≤j.val) (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (NativeJ.history j i)=b.basis (plain j i)) (i:Fin 10) :
    (run (NativeJ.program j d) tape a).basis (NativeJ.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] b).basis (plain j i) := by
  rw [(NativeJ.equals j h1 d).1]
  exact ArchiveOrdinaryFive.stock_relocated d (NativeJ.history j) (plain j) (NativeJ.histInj j) (plain_inj j) a b tape [] agree i

theorem readback (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (d:Bool) (raw pre wide out:State) (tape:List Bool)
    (input:∀i,pre.basis (NativeJ.history j i)=raw.basis (plain j i))
    (stable:∀i,raw.basis (plain j i)=wide.basis (plain j i))
    (last:∀i,out.basis (NativeJ.history j i)=(run (NativeJ.withArchive j d) tape pre).basis (NativeJ.history j i)) (i:Fin 10) :
    out.basis (NativeJ.history j i)=(run (Rolling1588.encodeAt base d (start j-15)) [] wide).basis (plain j i) := by
  apply (last i).trans
  rw [NativeJ.withArchive,run_append,run_take]
  have hp:(NativeJ.prev j).val≤20:=by simp only [NativeJ.prev]; omega
  obtain ⟨-,offHead,band,-⟩:=heads_all j h1 h21 i
  have off:NativeJ.history j i∉ArchiveJ.rawPortsList (NativeJ.prev j):=by
    rw [ArchiveJ.raw_split,List.mem_append]
    rintro (h|h)
    · exact offHead h
    · obtain ⟨k,hk,eq⟩:=List.mem_map.mp h
      exact ArchiveJ.band_off _ (ArchiveJ.tick_lt _) (List.mem_range.mp hk) band eq
  rw [run_preserves_outside (archiveLoadP (NativeJ.prev j) d) _ _ _
    (fun h=>off (List.mem_toFinset.mp (ArchiveJ.load_cover (NativeJ.prev j) hp d h)))]
  exact encode j h1 d pre wide tape (fun k=>(input k).trans (stable k)) i

/-- `Ordinary{s}Exit.result` for every interior block. -/
theorem result (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (d:Bool) (raw s:State) (m:List Bool) (x p:Nat)
    (good:Bounds x p) (dom:Domain (start j) x p raw)
    (input:∀i,(run (routed j 0 1) m s).basis (NativeJ.history j i)=raw.basis (plain j i)) :
    ∀i,(run (body j (NativeJ.withArchive j d)) m s).basis (NativeJ.history j i)=
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)).basis (plain j i) :=
  readback j h1 h21 d raw (run (routed j 0 1) m s) (run (span (start j) 15) [] raw) _ _ input
    (pastInput j h1 h21 x p good raw dom) (fun i=>kept j _ m s _ (heads_all j h1 h21 i).1)

/-- `Logical{s}Exit.window` for every interior block (par-a's `Fixed`-free `endRaw_*_gen`). -/
theorem window (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21)
    (interior:oldStart (start j)=start j-15 ∧ oldCount (start j)=15) (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,historyState.basis (NativeJ.history j i)=
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
theorem native (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21)
    (interior:oldStart (start j)=start j-15 ∧ oldCount (start j)=15) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (domain:Domain (start j) x p raw) (a b:List Bool) (neg far long:Bool)
    (cut:PackedCut (EnterJ.lowerPairs j) (EnterJ.upperPairs j) (EnterJ.gate j) (EnterJ.flagN j) (EnterJ.flagF j)
      (EnterJ.flagU j) neg far long (pullState (EnterJ.pull j) raw) (eraseSites (EnterJ.pending j) s))
    (z:SkywalkRails.State) (odd:(z.a+z.b)%2=1) (active:onRails j 0 z (run (enterP j) a s).basis) :
    let historyState:=run (body j (NativeJ.withArchive j d)) b (run (enterP j) a s)
    ArchiveHistoryCompare.Except (newBank j) (endRaw (start j) raw historyState)
      (run (Rolling1588.encodeAt base d (start j-15)) [] (run (span (start j) 15) [] raw)) := by
  let e:=run (enterP j) a s
  have input:∀i,(run (routed j 0 1) b e).basis (NativeJ.history j i)=raw.basis (plain j i) := by
    intro i
    have kept0:=NativeJ.prefix_kept j h1 h21 s a b z odd active i
    obtain ⟨-,-,-,notTag,hn,hf,hu,hi,same⟩:=heads_all j h1 h21 i
    exact kept0.trans (by simpa only [eraseSites,if_neg notTag,pullState,same] using cut.unchanged _ hn hf hu hi)
  exact fun q hq=>window j h1 h21 interior d raw _ (result j h1 h21 d raw e b x p good domain input) q hq

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
private theorem leaf : toffoliCount region=86 ∧ measurementCount region=0 ∧ gateSlots region=208 := by
  decide +kernel
private theorem correction_eq (c : Cost) : c.measure correction=10*c.measure region := by
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
    c.measure (finite C cx cy)=c.measure (WindowCallerCosts.finite C cx cy)+40*c.measure region := by
  simp only [finite,WindowCallerCosts.finite,borrowGeneric,WindowCallerCosts.borrowGeneric,generic,
    WindowCallerCosts.generic,c.append,c.rename,div,mul,correction_eq]; omega
theorem metrics (C : Point) : toffoliCount (program C) ≤ 2121124 ∧
    measurementCount (program C) ≤ 1498616 ∧ gateSlots (program C) ≤ 54280884 := by
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
  have h := WindowPhysical.dividePhysical (fun d => (Partial.assembly d).symm ▸ (WindowPhysicalW.window_physical d).1) (fun d => (Partial.unwind_assembly d).symm ▸ (WindowPhysicalW.window_physical d).2)
  simp only [WindowCallerCosts.divide,gatePhysical_append] at h
  simp only [divide,gatePhysical_append]
  exact ⟨⟨⟨⟨h.1.1.1.1,ef _ h.1.1.1.2⟩,h.1.1.2⟩,h.1.2⟩,h.2⟩
private theorem mp (k : Nat) : GatePhysical (multiply k) := by
  have h := WindowPhysical.multiplyPhysical (fun d => (Partial.assembly d).symm ▸ (WindowPhysicalW.window_physical d).1) (fun d => (Partial.unwind_assembly d).symm ▸ (WindowPhysicalW.window_physical d).2) k
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
private theorem regionSites : wires region⊆Finset.range 31 :=
  ECDSAAdd.Entrant.WSlimMain.wires_subset_range_of_all (by decide +kernel)
private theorem subpart {j : Nat} (hj : j=25 ∨ j=28 ∨ j=31 ∨ j=34 ∨ j=37 ∨ j=40 ∨ j=43 ∨ j=46 ∨ j=49 ∨ j=52) : Sub (bankCorrection j) StairSchedule.paritySetup := by
  intro q h
  rw [bankCorrection,renameProgram_support] at h
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
  have ii := Finset.mem_range.mp (regionSites hi)
  unfold port
  split_ifs with low host
  · apply controlsG
    exact List.mem_map.mpr ⟨8*j+i,List.mem_range.mpr (by rcases hj with h|h|h|h|h|h|h|h|h|h <;> omega),rfl⟩
  · exact hostused
  · apply controlsG
    exact List.mem_map.mpr ⟨8*(other j)+(i-17),List.mem_range.mpr (by
      rcases hj with h|h|h|h|h|h|h|h|h|h <;> subst j <;> simp [other] <;> omega),rfl⟩
set_option linter.constructorNameAsVariable false in
private theorem repair : Sub setup StairSchedule.paritySetup := by
  intro q h; simp only [setup,correction,wires_append,Finset.mem_union] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h
  · exact h
  · exact subpart (Or.inl rfl) h
  · exact subpart (Or.inr (Or.inl rfl)) h
  · exact subpart (Or.inr (Or.inr (Or.inl rfl))) h
  · exact subpart (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
  · exact subpart (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h
  · exact subpart (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) h
  · exact subpart (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) h
  · exact subpart (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))) h
  · exact subpart (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))) h
  · exact subpart (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))) h

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
def bounds : Challenge.Bounds := ⟨2121124,1498616,1543,54280884⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowParityCaller.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowParityCaller.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowParityCaller.metrics C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1498616
    rw [normalize_measurements]
    exact (WindowParityCaller.metrics C).2.1
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1543
    rw [normalize_qubits]
    exact WindowParityCaller.width C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 54280884
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
  rcases hc with rfl|rfl|rfl|rfl
  all_goals constructor
  all_goals first | (constructor <;> decide +kernel) | decide +kernel

def trigger : Instr → BasisState → Bool
  | .X _,_ => true
  | .CX c _,s => s c
  | .CCX a b _,s => s a && s b
  | .measureX _ _ _,_ => false
private theorem stepGate (g : Instr) (hg : gateFree (gateDst g) g=true)
    (p : Program) (m : List Bool) (s : State) :
    run (g::p) m s=run p m (flip (gateDst g) (trigger g s.basis) s) := by
  cases g with
  | X t =>
    simp only [run,gateDst,trigger,flip]
    congr 2; funext q
    by_cases e : q=t <;> simp [writeBit,e]
  | CX c t => simp only [run,gateDst,trigger,flip]
  | CCX a b t => simp only [run,gateDst,trigger,flip]
  | measureX t a b => contradiction
private theorem freeRead (g : Instr) (q : Wire) (hg : gateFree q g=true)
    (s : State) (v : Bool) : trigger g (flip q v s).basis=trigger g s.basis := by
  cases g with
  | X _ => rfl
  | CX c _ => exact at_other s c q v (of_decide_eq_true hg)
  | CCX a b _ =>
    obtain ⟨ha,hb⟩ := of_decide_eq_true hg
    simp only [trigger,at_other s a q v ha,at_other s b q v hb]
  | measureX _ _ _ => contradiction
private theorem equalGate (g : Instr) (hg : gateFree (gateDst g) g=true)
    (p : Program) (m : List Bool) (s : State) : run (g::g::p) m s=run p m s := by
  rw [stepGate g hg,stepGate g hg,freeRead g _ hg,flip_twice,Bool.xor_self,flip_zero]
private theorem swapGate (g h : Instr) (ok : swappable g h=true)
    (p : Program) (m : List Bool) (s : State) : run (g::h::p) m s=run (h::g::p) m s := by
  simp only [swappable,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨gg,hh⟩,gh⟩,hg⟩ := ok
  rw [stepGate g gg,stepGate h hh,freeRead h _ gh,stepGate h hh,stepGate g gg,freeRead g _ hg]
  by_cases ne : gateDst h≠gateDst g
  · rw [flip_comm _ _ _ _ _ ne]
  · have eq : gateDst h=gateDst g := Decidable.byContradiction ne
    rw [eq,flip_twice,flip_twice,Bool.xor_comm]
private theorem eraseMate_run (g : Instr) (p r : Program) (eq : eraseMate g p=some r)
    (m : List Bool) (s : State) : run (g::p) m s=run r m s := by
  induction p generalizing r m s with
  | nil => simp [eraseMate] at eq
  | cons h p ih =>
    simp only [eraseMate] at eq
    split at eq
    · next same =>
        obtain ⟨same,hg⟩ := same
        subst h
        cases eq
        exact equalGate g hg p m s
    · next different =>
        split at eq
        · next commute =>
            cases e : eraseMate g p with
            | none => simp [e] at eq
            | some q =>
                simp only [e,Option.map_some,Option.some.injEq] at eq
                subst r
                have hh : gateFree (gateDst h) h=true := by
                  simp only [swappable,Bool.and_eq_true] at commute
                  exact commute.1.1.2
                rw [swapGate g h commute,stepGate h hh,stepGate h hh]
                exact ih q e m _
        · simp at eq
theorem cancelPairs_run (p : Program) (m : List Bool) (s : State) :
    run (cancelPairs p) m s=run p m s := by
  induction p generalizing m s with
  | nil => rfl
  | cons g p ih =>
    simp only [cancelPairs]
    split
    · next e =>
        cases g <;> simp only [run] <;> rw [ih]
    · next r e =>
        rw [←eraseMate_run g (cancelPairs p) r e]
        cases g <;> simp only [run] <;> rw [ih]

theorem mcx_back_run (a b src last t : Wire) (xs : Hops) (m : List Bool) (s : State)
    (h : Good a b src last t xs) :
    run ([Instr.CCX a b src] ++ (chain src last t xs ++
      ([Instr.CCX a b src] ++ chain src last t xs))) m s =
      flip t ((s.basis a && s.basis b) && product last s.basis xs) s := by
  let d := s.basis a && s.basis b
  let u := flip src d s
  let first := value last s.basis xs (s.basis src)
  let second := first ^^ (d && product last s.basis xs)
  have readSrc : u.basis src=(s.basis src^^d) := at_flip _ _ _
  have readValue : value last u.basis xs (u.basis src)=second := by
    rw [readSrc]
    unfold u second first
    rw [value_away _ _ _ _ _ _ h.source,value_xor]
  simp only [run_append,run_take,single,chain_run _ _ _ _ _ _ h.chained]
  change flip t (value last (flip src _ (flip t _ u)).basis xs
    ((flip src _ (flip t _ u)).basis src)) (flip src _ (flip t _ u))=_
  simp only [at_other _ _ _ _ h.at_,at_other _ _ _ _ h.bt,
    at_other _ _ _ _ h.as_,at_other _ _ _ _ h.bs]
  rw [readValue]
  change flip t (value last (flip src d (flip t second u)).basis xs
    ((flip src d (flip t second u)).basis src)) (flip src d (flip t second u))=_
  rw [flip_comm _ src t _ _ h.st]
  change flip t (value last (flip t second (flip src d (flip src d s))).basis xs
    ((flip t second (flip src d (flip src d s))).basis src))
    (flip t second (flip src d (flip src d s)))=_
  rw [flip_twice s src d d,Bool.xor_self,flip_zero,value_away _ _ _ _ _ _ h.target,
    at_other _ _ _ _ h.st,flip_twice]
  have finish : (second^^first)=(d && product last s.basis xs) := by
    unfold second; cases first <;> cases (d && product last s.basis xs) <;> rfl
  rw [finish]

theorem body_run (c : Clause) (hc : c∈clauses) (m : List Bool) (s : State) :
    run (body c) m s=flip 16 ((predicate c).eval s.basis) s := by
  obtain ⟨bounded,valid⟩ := valid_clause c hc
  cases back : c.backwards <;>
    simp only [body,back,Bool.false_eq_true,if_false,if_true,run_append,run_take,aff_run,
      mcx_run _ _ _ _ _ _ _ _ bounded,mcx_back_run _ _ _ _ _ _ _ _ bounded,undo _ _ valid] <;>
    rw [product_eval,symbol_eval,symbol_eval] <;> rfl
private theorem effect_flip (p : List Aff) (q : Wire) (hp : ∀g∈p,lawful q g)
    (s : State) (v : Bool) : effect p (flip q v s)=flip q v (effect p s) := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    have hg := hp g (by simp)
    have ht := fun k (hk : k∈p)=>hp k (List.mem_cons_of_mem _ hk)
    change effect p (applyAff (flip q v s) g)=flip q v (effect p (applyAff s g))
    rw [commute g q hg,ih ht]
private theorem effect_same (p : List Aff) (q : Wire) (hp : ∀g∈p,lawful q g)
    (s : State) : (effect p s).basis q=s.basis q := by
  induction p generalizing s with
  | nil => rfl
  | cons g p ih =>
    have hg := hp g (by simp)
    have ht := fun k (hk : k∈p)=>hp k (List.mem_cons_of_mem _ hk)
    change (effect p (applyAff s g)).basis q=s.basis q
    rw [ih ht]
    cases g with
    | x t => exact at_other s q t _ hg.symm
    | cx c t => exact at_other s q t _ hg.2.2.symm

def armValue (c : Clause) (s : State) :=
  value c.last (effect c.prep s).basis c.xs ((effect c.prep s).basis 17)
def armProduct (c : Clause) (s : State) := product c.last (effect c.prep s).basis c.xs
private theorem arm_run (c : Clause) (h : Good c.a c.b 17 c.last 16 c.xs)
    (hp : ∀g∈c.prep,lawful 16 g) (m : List Bool) (s : State) :
    run (arm c) m s=flip 16 (armValue c s) s := by
  simp only [arm,run_append,run_take,aff_run,chain_run _ _ _ _ _ _ h.chained,undo _ _ hp]
  rfl
private theorem arm_value_flip (c : Clause) (q : Wire) (hp : ∀g∈c.prep,lawful q g)
    (away : outside q c.last c.xs) (ne : 17≠q) (s : State) (v : Bool) :
    armValue c (flip q v s)=armValue c s := by
  unfold armValue
  rw [effect_flip c.prep q hp,value_away _ _ _ _ _ _ away,at_other _ _ _ _ ne]
private theorem arm_value_source (c : Clause) (hp : ∀g∈c.prep,lawful 17 g)
    (away : outside 17 c.last c.xs) (s : State) (v : Bool) :
    armValue c (flip 17 v s)=(armValue c s ^^ (v && armProduct c s)) := by
  unfold armValue armProduct
  rw [effect_flip c.prep 17 hp,at_flip,value_away _ _ _ _ _ _ away,value_xor]

private theorem borrowed_pair_run (F : Program) (f g : State→Bool)
    (hf : ∀m s,run F m s=flip 16 (f s) s)
    (h16 : ∀s v,f (flip 16 v s)=f s)
    (h17 : ∀s v,f (flip 17 v s)=(f s ^^ (v && g s)))
    (m : List Bool) (s : State) :
    run (F ++ ([Instr.CCX 8 9 17] ++ (F ++ [Instr.CCX 8 9 17]))) m s =
      flip 16 ((s.basis 8 && s.basis 9) && g s) s := by
  let d := s.basis 8 && s.basis 9
  let first := f s
  let u := flip 17 d (flip 16 first s)
  let second := first ^^ (d && g s)
  have next : f u=second := by
    unfold u second first
    rw [flip_comm _ 17 16 _ _ (by decide),h16,h17]
  simp only [run_append,run_take,hf,single,
    at_other _ 8 16 _ (by decide),at_other _ 9 16 _ (by decide),
    at_other _ 8 17 _ (by decide),at_other _ 9 17 _ (by decide)]
  change flip 17 ((flip 16 (f u) u).basis 8 && (flip 16 (f u) u).basis 9)
    (flip 16 (f u) u)=_
  rw [next]
  simp only [at_other _ 8 16 _ (by decide),at_other _ 9 16 _ (by decide)]
  change flip 17 d (flip 16 second u)=_
  rw [flip_comm _ 17 16 _ _ (by decide)]
  change flip 16 second (flip 17 d (flip 17 d (flip 16 first s)))=_
  rw [flip_twice,Bool.xor_self,flip_zero,flip_twice]
  have finish : (first^^second)=(d && g s) := by
    unfold second; cases first <;> cases (d && g s) <;> rfl
  rw [finish]

private theorem leftOK : Good tailLeft.a tailLeft.b 17 tailLeft.last 16 tailLeft.xs := by
  constructor <;> decide +kernel
private theorem rightOK : Good tailRight.a tailRight.b 17 tailRight.last 16 tailRight.xs := by
  constructor <;> decide +kernel
private theorem prepOK (c : Clause) (hc : c=tailLeft ∨ c=tailRight) (q : Wire)
    (hq : q=8 ∨ q=9 ∨ q=16 ∨ q=17) : ∀g∈c.prep,lawful q g := by
  rcases hc with rfl|rfl <;> rcases hq with rfl|rfl|rfl|rfl <;> decide +kernel
private theorem pair_run (m : List Bool) (s : State) :
    run pairWord m s=flip 16 ((s.basis 8 && s.basis 9) &&
      (armProduct tailLeft s ^^ armProduct tailRight s)) s := by
  let f := fun s=>armValue tailLeft s ^^ armValue tailRight s
  let g := fun s=>armProduct tailLeft s ^^ armProduct tailRight s
  have l16 := prepOK tailLeft (Or.inl rfl) 16 (Or.inr (Or.inr (Or.inl rfl)))
  have r16 := prepOK tailRight (Or.inr rfl) 16 (Or.inr (Or.inr (Or.inl rfl)))
  have l17 := prepOK tailLeft (Or.inl rfl) 17 (Or.inr (Or.inr (Or.inr rfl)))
  have r17 := prepOK tailRight (Or.inr rfl) 17 (Or.inr (Or.inr (Or.inr rfl)))
  have lf := arm_value_flip tailLeft 16 l16 leftOK.target (by decide)
  have rf := arm_value_flip tailRight 16 r16 rightOK.target (by decide)
  have hs (m : List Bool) (s : State) : run (arm tailLeft++arm tailRight) m s=flip 16 (f s) s := by
    rw [run_append,run_take,arm_run _ leftOK l16,arm_run _ rightOK r16,rf,flip_twice]
  have h16 (s : State) (v : Bool) : f (flip 16 v s)=f s := by
    unfold f; rw [lf,rf]
  have h17 (s : State) (v : Bool) : f (flip 17 v s)=(f s ^^ (v && g s)) := by
    unfold f g
    rw [arm_value_source _ l17 leftOK.source,arm_value_source _ r17 rightOK.source]
    cases armValue tailLeft s <;> cases armValue tailRight s <;>
      cases armProduct tailLeft s <;> cases armProduct tailRight s <;> cases v <;> rfl
  exact borrowed_pair_run _ f g hs h16 h17 m s

private theorem predicate_value (c : Clause) (s : State) :
    (predicate c).eval s.basis=
      (((effect c.prep s).basis c.a && (effect c.prep s).basis c.b) &&
        product c.last (effect c.prep s).basis c.xs) := by
  rw [product_eval,symbol_eval,symbol_eval]
  rfl
private theorem commonEffect (p q : List Aff) (s : State) : effect (p++q) s=effect q (effect p s) := by
  simp only [effect,List.foldl_append]
private theorem tail_values (s : State) :
    ((predicate negativePair).eval s.basis ^^ (predicate literalPair).eval s.basis)=
      (((effect commonPrep s).basis 8 && (effect commonPrep s).basis 9) &&
        (armProduct tailLeft (effect commonPrep s) ^^ armProduct tailRight (effect commonPrep s))) := by
  rw [predicate_value,predicate_value]
  change ((((effect (commonPrep++tailLeft.prep) s).basis 8 && (effect (commonPrep++tailLeft.prep) s).basis 9) &&
    product tailLeft.last (effect (commonPrep++tailLeft.prep) s).basis tailLeft.xs) ^^
    (((effect (commonPrep++tailRight.prep) s).basis 8 && (effect (commonPrep++tailRight.prep) s).basis 9) &&
    product tailRight.last (effect (commonPrep++tailRight.prep) s).basis tailRight.xs))=_
  rw [commonEffect,commonEffect,
    effect_same _ 8 (prepOK tailLeft (Or.inl rfl) 8 (Or.inl rfl)),
    effect_same _ 9 (prepOK tailLeft (Or.inl rfl) 9 (Or.inr (Or.inl rfl))),
    effect_same _ 8 (prepOK tailRight (Or.inr rfl) 8 (Or.inl rfl)),
    effect_same _ 9 (prepOK tailRight (Or.inr rfl) 9 (Or.inr (Or.inl rfl)))]
  have distrib (a b c : Bool) : ((a && b) ^^ (a && c))=(a && (b^^c)) := by
    cases a <;> cases b <;> cases c <;> rfl
  exact distrib _ _ _

private theorem product_away (xs : Hops) (last q : Wire) (s : State) (v : Bool)
    (h : outside q last xs) : product last (flip q v s).basis xs=product last s.basis xs := by
  induction xs with
  | nil => exact at_other s last q v h.1.symm
  | cons x xs ih =>
    have ht : outside q last xs := ⟨h.1,fun e he=>h.2 e (List.mem_cons_of_mem _ he)⟩
    simp only [product,at_other s x.1 q v (h.2 x (by simp)).1.symm,ih ht]

private theorem jointTail_run (m : List Bool) (s : State) :
    run jointTail m s=run (body negativePair++body literalPair) m s := by
  have valid : ∀g∈commonPrep,lawful 16 g := by decide +kernel
  have nl : negativePair∈clauses := by simp [clauses]
  have nr : literalPair∈clauses := by simp [clauses]
  simp only [jointTail,run_append,run_take,aff_run,pair_run,undo _ _ valid]
  rw [body_run _ nl,body_run _ nr]
  have unchanged : (predicate literalPair).eval (flip 16 ((predicate negativePair).eval s.basis) s).basis=
      (predicate literalPair).eval s.basis := by
    rw [predicate_value literalPair _,predicate_value literalPair s]
    have h := (valid_clause literalPair nr).2
    rw [effect_flip _ 16 h]
    rw [at_other _ _ 16 _ (by decide),at_other _ _ 16 _ (by decide)]
    rw [product_away _ _ 16 _ _ (valid_clause literalPair nr).1.target]
  rw [unchanged,flip_twice,tail_values]

theorem groupedRegion_run (m : List Bool) (s : State) :
    run groupedRegion m s=run (clauses.flatMap body) m s := by
  have eq : run ((body firstPair++body positivePair)++jointTail) m s=
      run ((body firstPair++body positivePair)++(body negativePair++body literalPair)) m s := by
    simp only [run_append,run_take,jointTail_run]
  simpa only [groupedRegion,clauses,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using eq

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

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 20000
attribute [local irreducible] wires domain
theorem reverse_domain (d : Bool) : ∀ q ∈ wires (reverse45plus1 d), domain q = true := by
  intro q h
  rw [Partial.unwind_assembly] at h
  rw [domain_eq]
  exact (WindowCovered.window_covered d).2 q h

theorem inside (n:Nat) (use:domain n=true):(16:Nat)≤n ∧ n≤1812:=by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at use
  rcases use with ⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩|⟨lo,hi⟩
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
def first (d:Bool):Program:=Stair44WalkRun.forward d 104
def regular (d:Bool) (s:State) (m:List Bool):State:=run (Rolling1588.Integer.regularForward base d 1 119) m s
theorem cut120 (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Rolling1588.Integer.Stage base d x p 120 (regular d s m).basis ∧
    pullState Stair44WalkMap.rest (run (first d) m a)=pullState (OB5.sig 119) (regular d s m):=by
  obtain ⟨hp0,odd,cap,cop⟩:=StackOB5.prime_facts x good.nonzero good.small
  have spec:=Rolling1588.Integer.regularForward_spec base d base_pool_nodup StackOB5.historyAbove x p 1 119 hp0 good.nonzero odd cap (by norm_num [p]) good.small cop (by decide) s m stage
  refine ⟨spec.2,?_⟩
  have entry:=Stair44WalkRun.forward_run d 104 x good.nonzero good.small s a m stage input
  have logical:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 119 1 (by decide) (by decide) s m stage
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
      run (forwardEnd d n) (m.drop (measurementCount (first d))) (pullState (OB5.sig 119) (regular d s m)):=by
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
  rw [region,cancelPairs_run,groupedRegion_run,runList _ _ (fun _ h=>h) _ rb m s data,columnMatch d,Nat.testBit_xor]
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

private def regular (z : Wire) := !(EP.contains z) && !((futurePayload 87).contains z)
private def archiveGood (j : Nat) := (List.range 121).all (fun q => q==16 || regular (host.symm (fieldPort j q)))
private theorem portsCheck : WindowBankCheck.banks.all archiveGood=true := by decide +kernel
private theorem cleanPort (j q : Nat) (jb : j∈bankIds) (qb : q<121) (ne : fieldPort j q≠base 720) :
    Off (host.symm (fieldPort j q)) ∧ host.symm (fieldPort j q)∉futurePayload 87 := by
  have jm : j∈WindowBankCheck.banks := by simpa [bankIds,WindowBankCheck.banks] using jb
  have ok := List.all_eq_true.mp (List.all_eq_true.mp portsCheck _ jm) q (List.mem_range.mpr qb)
  have eq16 : fieldPort j 16=base 720 := by
    simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at jb
    rcases jb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
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

/-- dadon's three windows on the record first group `group84rec` (dadon's proof). -/
theorem three_run_rec (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (ref : StockCut (if d then 1 else 85) origin r) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84rec d) m a)
      (run (group d 1 84) (referenceTape0 d (plan d) m) r) := by
  have route : path d (if d then 1 else 85) (plan d) := by cases d <;> simp [path,plan,prev,next,span,feasible,bankIds]
  have all := group_run d rows rb m a r initial (trail d x rows rb origin ctx en tr history _ _ m r route ref)
  rwa [ref_run,reference_eq] at all

set_option linter.unusedSimpArgs false in
/-- the actual field group is the reference group (no cell any more). -/
theorem c45_actual (d : Bool) (m : List Bool) (a : State) :
    run (group84 d) m a=run (group84rec d) (cellTape d m) a := rfl

/-- the three windows with the odd cell on packets 1..45 of the division kernel; the reference
side is still the record run of `group d 1 84`. -/
theorem three_run (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin) (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (m : List Bool) (a r : State) (initial : Fits rows (initialCode d) a r)
    (ref : StockCut (if d then 1 else 85) origin r) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84 d) m a)
      (run (group d 1 84) (referenceTape d (plan d) m) r) := by
  rw [c45_actual d m a]
  exact three_run_rec d x rows rb origin ctx en tr history (cellTape d m) a r initial ref
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
private def stable0 := List.range 200
private def stable1 := List.range' 216 8
private def stable2 := List.range' 240 8
private def stable3 := List.range' 264 8
private def stable4 := List.range' 288 8
private def stable5 := List.range' 312 8
private def stable6 := List.range' 336 8
private def stable7 := List.range' 360 8
private def stable8 := List.range' 384 8
private def stable9 := List.range' 408 8
private def stable10 := List.range' 432 384
private theorem split : List.range 816 = stable0 ++ block 25 ++ stable1 ++ block 28 ++ stable2 ++ block 31 ++ stable3 ++ block 34 ++ stable4 ++ block 37 ++ stable5 ++ block 40 ++ stable6 ++ block 43 ++ stable7 ++ block 46 ++ stable8 ++ block 49 ++ stable9 ++ block 52 ++ stable10 := by decide +kernel
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
def Elsewhere (i : Nat) := i<200 ∨ (216 ≤ i ∧ i<224) ∨ (240 ≤ i ∧ i<248) ∨ (264 ≤ i ∧ i<272) ∨ (288 ≤ i ∧ i<296) ∨ (312 ≤ i ∧ i<320) ∨ (336 ≤ i ∧ i<344) ∨ (360 ≤ i ∧ i<368) ∨ (384 ≤ i ∧ i<392) ∨ (408 ≤ i ∧ i<416) ∨ (432 ≤ i ∧ i<816)
def stockParity (s : State) := TraceParity5.parity (FrontierEntry1591Field.controls.map s.basis)
private theorem allSum (s : State) : stockParity s=
    ((((((((((((((((((((sum stable0 s ^^ sum (block 25) s) ^^ sum stable1 s) ^^ sum (block 28) s) ^^ sum stable2 s) ^^ sum (block 31) s) ^^ sum stable3 s) ^^ sum (block 34) s) ^^ sum stable4 s) ^^ sum (block 37) s) ^^ sum stable5 s) ^^ sum (block 40) s) ^^ sum stable6 s) ^^ sum (block 43) s) ^^ sum stable7 s) ^^ sum (block 46) s) ^^ sum stable8 s) ^^ sum (block 49) s) ^^ sum stable9 s) ^^ sum (block 52) s) ^^ sum stable10 s) := by
  unfold stockParity FrontierEntry1591Field.controls ParityHost5.payloadControls
  rw [split]
  simp only [List.map_append,List.map_map,join,sum,Function.comp_def,addr]
private theorem pair_step (p q s x y : Bool) : (((p ^^ x) ^^ s) ^^ ((q ^^ y) ^^ s)) = ((p ^^ q) ^^ (x ^^ y)) := by
  cases p <;> cases q <;> cases s <;> cases x <;> cases y <;> rfl
theorem fold_pair (rows : Nat→Nat) (dirs : Nat→Bool) (a b : State)
    (rest : ∀i,Elsewhere i→a.basis (addr i)=b.basis (addr i))
    (custom : ∀j,j=25 ∨ j=28 ∨ j=31 ∨ j=34 ∨ j=37 ∨ j=40 ∨ j=43 ∨ j=46 ∨ j=49 ∨ j=52 → ∀i<16,a.basis (site j i)=(get (ArchivePortAction.code (dirs j)) i).testBit (rows j))
    (stock : ∀j,j=25 ∨ j=28 ∨ j=31 ∨ j=34 ∨ j=37 ∨ j=40 ∨ j=43 ∨ j=46 ∨ j=49 ∨ j=52 → ∀i<16,b.basis (site j i)=(get (StairArchiveNativeCut.canonical (dirs j) (dirs j)) i).testBit (rows j)) :
    (stockParity a ^^ stockParity b) =
    (((((((((((parity (ArchivePortAction.code (dirs 25))).testBit (rows 25) ^^ (parity (StairArchiveNativeCut.canonical (dirs 25) (dirs 25))).testBit (rows 25)) ^^ ((parity (ArchivePortAction.code (dirs 28))).testBit (rows 28) ^^ (parity (StairArchiveNativeCut.canonical (dirs 28) (dirs 28))).testBit (rows 28))) ^^ ((parity (ArchivePortAction.code (dirs 31))).testBit (rows 31) ^^ (parity (StairArchiveNativeCut.canonical (dirs 31) (dirs 31))).testBit (rows 31))) ^^ ((parity (ArchivePortAction.code (dirs 34))).testBit (rows 34) ^^ (parity (StairArchiveNativeCut.canonical (dirs 34) (dirs 34))).testBit (rows 34))) ^^ ((parity (ArchivePortAction.code (dirs 37))).testBit (rows 37) ^^ (parity (StairArchiveNativeCut.canonical (dirs 37) (dirs 37))).testBit (rows 37))) ^^ ((parity (ArchivePortAction.code (dirs 40))).testBit (rows 40) ^^ (parity (StairArchiveNativeCut.canonical (dirs 40) (dirs 40))).testBit (rows 40))) ^^ ((parity (ArchivePortAction.code (dirs 43))).testBit (rows 43) ^^ (parity (StairArchiveNativeCut.canonical (dirs 43) (dirs 43))).testBit (rows 43))) ^^ ((parity (ArchivePortAction.code (dirs 46))).testBit (rows 46) ^^ (parity (StairArchiveNativeCut.canonical (dirs 46) (dirs 46))).testBit (rows 46))) ^^ ((parity (ArchivePortAction.code (dirs 49))).testBit (rows 49) ^^ (parity (StairArchiveNativeCut.canonical (dirs 49) (dirs 49))).testBit (rows 49))) ^^ ((parity (ArchivePortAction.code (dirs 52))).testBit (rows 52) ^^ (parity (StairArchiveNativeCut.canonical (dirs 52) (dirs 52))).testBit (rows 52))) := by
  have h0 := stable_sum stable0 a b (fun i hi=>rest i (Or.inl (List.mem_range.mp hi)))
  have h1 := stable_sum stable1 a b (fun i hi=>rest i (Or.inr (Or.inl (by
    simpa only [stable1,List.mem_range'_1] using hi))))
  have h2 := stable_sum stable2 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inl (by
    simpa only [stable2,List.mem_range'_1] using hi)))))
  have h3 := stable_sum stable3 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable3,List.mem_range'_1] using hi))))))
  have h4 := stable_sum stable4 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable4,List.mem_range'_1] using hi)))))))
  have h5 := stable_sum stable5 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable5,List.mem_range'_1] using hi))))))))
  have h6 := stable_sum stable6 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable6,List.mem_range'_1] using hi)))))))))
  have h7 := stable_sum stable7 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable7,List.mem_range'_1] using hi))))))))))
  have h8 := stable_sum stable8 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable8,List.mem_range'_1] using hi)))))))))))
  have h9 := stable_sum stable9 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable9,List.mem_range'_1] using hi))))))))))))
  have h10 := stable_sum stable10 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by
    simpa only [stable10,List.mem_range'_1] using hi)))))))))))))
  rw [allSum a,allSum b,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,fromData _ _ _ _ (custom 25 (Or.inl rfl)),fromData _ _ _ _ (custom 28 (Or.inr (Or.inl rfl))),fromData _ _ _ _ (custom 31 (Or.inr (Or.inr (Or.inl rfl)))),fromData _ _ _ _ (custom 34 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),fromData _ _ _ _ (custom 37 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),fromData _ _ _ _ (custom 40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),fromData _ _ _ _ (custom 43 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))),fromData _ _ _ _ (custom 46 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))),fromData _ _ _ _ (custom 49 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))),fromData _ _ _ _ (custom 52 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))),fromData _ _ _ _ (stock 25 (Or.inl rfl)),fromData _ _ _ _ (stock 28 (Or.inr (Or.inl rfl))),fromData _ _ _ _ (stock 31 (Or.inr (Or.inr (Or.inl rfl)))),fromData _ _ _ _ (stock 34 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),fromData _ _ _ _ (stock 37 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),fromData _ _ _ _ (stock 40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),fromData _ _ _ _ (stock 43 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))),fromData _ _ _ _ (stock 46 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))),fromData _ _ _ _ (stock 49 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))),fromData _ _ _ _ (stock 52 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))]
  rw [pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,Bool.xor_self,Bool.false_xor]
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
end ECDSAAdd.Entrant.StairPacket.OrdinaryChain

end

-- ==== w4: step 9: build-w4b drop-ins StockWindowW, FinalW_inst, OrdinaryChainW (+ holes) ====
-- BEGIN par-d2 StockWindowW (parallel chain: Tail752; needs Tail10d9 (WideReference, ArchiveStockRows), HBJ/FirstHit, PointMap/QTop; no Stair44Stock/BO)
section

namespace ECDSAAdd.Entrant.StairPacket.StockWindowGeo
open Arithmetic MappedCompressed
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2 (job D2): geometry of the stock comparison over an `n`-block window, generic in the first block
start `s1` and `n`. The blocks start at `s1, s1+15, ..., s1+15(n-1)` and the exit is at `e = s1+15n`.
- The stock walk over the window packs `3n+1` groups at ticks `s1-5, s1, ..., e-5` (`gstart`).
- The window packs the `plain` groups itself: the pre-window letters, then each block's own pack.
- Bank `b`'s archive holds the two `packed` groups `2+3b` and `3+3b`. Their letters 5 and 9 are the `holes`; the
  other 16 letters are the bank's 16 code cells.
This replaces dadon's `decide +kernel` checks over `Fin 13` and `Fin 4 × Fin 16` (`StockGroups.sparse/distinct/
holeSlot`, `StockArchiveBanks.chart`, `ArchiveStockSuffix.sites*`). Every lemma is a 16-way or 10-way case split
plus `omega`, so the cost is O(1) in `n`. -/

/-- Start tick of pack group `i` of the window. -/
def gstart (s1 i : Nat) : Nat := s1-5+5*i
def slot (s1 i : Nat) : Fin 10 → Wire := History5.historyMap base (gstart s1 i)
/-- Groups the window packs itself: the five pre-window letters, then the pack of each block. -/
def plain (n : Nat) : List Nat := 0 :: (List.range n).map (fun b => 1+3*b)
/-- Groups the archives hold: two per bank. -/
def packed (n : Nat) : List Nat := (List.range n).flatMap (fun b => [2+3*b, 3+3*b])
/-- The two letters of each archived group that no code cell keeps (letters 5 and 9). -/
def holes (s1 n : Nat) : List Wire :=
  (packed n).flatMap (fun i => [base (1028+gstart s1 i+2), base (1028+gstart s1 i+4)])

def logical (sw : Bool) (r : Nat) : Wire := if sw then base (1028+r) else base r
/-- A history cell of tick `r < e` in the exit-tick frame. -/
def site (e : Nat) (sw : Bool) (r : Nat) : Wire := OB5.sig e (logical sw r)
def offset (j : Fin 16) : Nat := 5*(j.val/8)+[0,0,1,1,2,3,3,4].getD (j.val%8) 0
def swap (j : Fin 16) : Bool := j.val%8∈[1,3,6]
def index (j : Fin 16) : Fin 10 := ⟨if j.val%8<5 then j.val%8 else j.val%8+1,by split <;> omega⟩
def group (b : Nat) (j : Fin 16) : Nat := 2+3*b+j.val/8
/-- Block start of bank `b` (the archive of block `j1+b`, or the exit archive for `b = n-1`). -/
def tick (s1 b : Nat) : Nat := s1+15*b
/-- Code cell `j` of bank `b`: the first 16 code ports of the archive at tick `tick s1 b+15`. -/
def bankSite (s1 b : Nat) (j : Fin 16) : Wire := (Partial.cellsRestoreP (tick s1 b+15)).getD j 0
def packet (s1 i : Nat) : Nat := s1+15*((i-2)/3)
def high (i : Nat) : Bool := decide ((i-2)%3=1)
/-- `StockArchiveTruth.tile` (same body, so the two agree by `rfl`). -/
def tile (k : Nat) (hi : Bool) : Nat := k+5+(if hi then 5 else 0)
/-- All archive cells of the window. -/
def archives (s1 n : Nat) : List Wire := (List.range n).flatMap (fun b => (List.finRange 16).map (bankSite s1 b))

/-- `OB5.sig` keeps the history cell of tick `r` fixed in every frame later than `r`. -/
theorem stable (i e r : Nat) (hi : i ≤ 511) (he : e ≤ 511) (ri : r < i) (re : r < e) (sw : Bool) :
    OB5.sig i (logical sw r)=site e sw r := by
  show OB5.sigNat i (logical sw r)=OB5.sigNat e (logical sw r)
  cases sw <;> simp only [logical,base,Bool.false_eq_true,if_false,if_true,OB5.sigNat] <;>
    split_ifs with h1 h2 h2 <;> (try rcases h1 with h1|h1) <;> (try rcases h2 with h2|h2) <;> omega

/-- The 16 code cells of the archive at tick `t` are the history cells of ticks `t-10..t-1`. -/
theorem cells (t : Nat) (lo : 10≤t) (hi : t≤511) (j : Fin 16) :
    (Partial.cellsRestoreP t).getD j 0=OB5.sig t (logical (swap j) (t-10+offset j)) := by
  show _=OB5.sigNat t (logical (swap j) (t-10+offset j))
  rcases j with ⟨j,hj⟩
  interval_cases j <;>
    simp only [Partial.cellsRestoreP,List.getD_cons_zero,List.getD_cons_succ,logical,swap,offset,base,
      OB5.sig_nat,List.mem_cons,List.not_mem_nil,or_false,List.getD,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] <;>
    first | rfl | (simp only [OB5.sigNat]; split_ifs with h1 h2 <;> (try rcases h1 with h1|h1) <;>
      (try rcases h2 with h2|h2) <;> omega) | (norm_num [OB5.sigNat]; split_ifs <;> omega)

/-- Bank cells in the exit frame: tick `tick s1 b+5+offset j`, older than the exit. -/
theorem bank_site (s1 b e : Nat) (lo : 5≤s1) (hb : tick s1 b+15≤e) (he : e≤511) (j : Fin 16) :
    bankSite s1 b j=site e (swap j) (tick s1 b+5+offset j) ∧ tick s1 b+5+offset j<e := by
  have ho:offset j≤9:=by
    rcases j with ⟨j,hj⟩; interval_cases j <;> simp [offset]
  refine ⟨?_,by omega⟩
  rw [bankSite,cells _ (by simp only [tick]; omega) (by omega)]
  rw [show tick s1 b+15-10+offset j=tick s1 b+5+offset j by omega]
  exact stable _ e _ (by omega) he (by omega) (by omega) _

/-- `StockArchiveBanks.chart`, generic: bank cell `j` of bank `b` is letter `index j` of group `group b j`, a
packed group whose packet tick is the bank's block start. -/
theorem chart (s1 n b e : Nat) (lo : 5≤s1) (hb : b<n) (he : e=s1+15*n) (le : e≤511) (j : Fin 16) :
    bankSite s1 b j=OB5.sig e (slot s1 (group b j) (index j)) ∧ packet s1 (group b j)=tick s1 b ∧
      group b j∈packed n ∧ high (group b j)=decide (8≤j.val) := by
  have bs:=(bank_site s1 b e lo (by simp only [tick]; omega) le j).1
  refine ⟨?_,?_,?_,?_⟩
  · rw [bs,site]
    congr 1
    rcases j with ⟨j,hj⟩
    interval_cases j <;> simp [logical,swap,offset,slot,History5.historyMap,History5.historyId,index,group,
      gstart,tick,base] <;> omega
  · simp only [packet,group]; rw [show (2+3*b+j.val/8-2)/3=b by have:=j.isLt; omega]; rfl
  · simp only [packed,group,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨b,hb,by have:=j.isLt; omega⟩
  · simp only [high,group]; have:=j.isLt; congr 1; apply propext; omega

theorem bank_mem (s1 n b : Nat) (hb : b<n) (j : Fin 16) : bankSite s1 b j∈archives s1 n := by
  simp only [archives,List.mem_flatMap,List.mem_range,List.mem_map,List.mem_finRange,true_and]
  exact ⟨b,hb,j,rfl⟩

/-- Every archive cell is a history cell of a tick older than the exit (the stock suffix never touches it). -/
theorem archive_old (s1 n e : Nat) (lo : 5≤s1) (he : e=s1+15*n) (le : e≤511) :
    ∀q∈archives s1 n,∃sw r,r<e ∧ q=site e sw r := by
  intro q hq
  simp only [archives,List.mem_flatMap,List.mem_range,List.mem_map,List.mem_finRange,true_and] at hq
  obtain ⟨b,hb,j,rfl⟩:=hq
  obtain ⟨eq,lt⟩:=bank_site s1 b e lo (by simp only [tick]; omega) le j
  exact ⟨_,_,lt,eq⟩

/-- `StockGroups.sparse`, generic: each letter of an archived group is a hole (letters 5, 9) or, in the exit
frame, an archive cell. -/
theorem sparse (s1 n e : Nat) (lo : 5≤s1) (he : e=s1+15*n) (le : e≤511) :
    ∀i∈packed n,∀j:Fin 10,(j=5 ∨ j=9) ∧ slot s1 i j∈holes s1 n ∨ OB5.sig e (slot s1 i j)∈archives s1 n := by
  intro i hi j
  have hi':=hi
  simp only [packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hi'
  obtain ⟨b,hb,hib⟩:=hi'
  by_cases hole:j=5 ∨ j=9
  · left
    refine ⟨hole,?_⟩
    simp only [holes,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
    refine ⟨i,hi,?_⟩
    rcases hole with rfl|rfl
    · left; simp [slot,History5.historyMap,History5.historyId,base] <;> omega
    · right; simp [slot,History5.historyMap,History5.historyId,base] <;> omega
  · right
    -- the bank cell holding letter `j` of group `i`
    let k:Nat:=8*(i-2-3*b)+(if j.val<5 then j.val else j.val-1)
    have hk:k<16:=by have:=j.isLt; simp only [k]; split <;> omega
    have gi:group b ⟨k,hk⟩=i:=by simp only [group,k]; split <;> omega
    have ij:index ⟨k,hk⟩=j:=by
      apply Fin.ext; simp only [index,k]
      have:=j.isLt
      have h5:j.val≠5:=fun h=>hole (Or.inl (Fin.ext h))
      have h9:j.val≠9:=fun h=>hole (Or.inr (Fin.ext h))
      split <;> split <;> omega
    have c:=(chart s1 n b e lo hb he le ⟨k,hk⟩).1
    rw [gi,ij] at c
    rw [←c]
    exact bank_mem s1 n b hb _

theorem hole_slot (s1 n : Nat) : ∀q∈holes s1 n,∃i∈packed n,∃j:Fin 10,q=slot s1 i j := by
  intro q hq
  simp only [holes,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at hq
  obtain ⟨i,hi,e|e⟩:=hq
  · exact ⟨i,hi,5,by simp [e,slot,History5.historyMap,History5.historyId,base] <;> omega⟩
  · exact ⟨i,hi,9,by simp [e,slot,History5.historyMap,History5.historyId,base] <;> omega⟩

/-- `StockGroups.distinct`, generic: different groups use different history cells. -/
theorem distinct (s1 : Nat) (lo : 5≤s1) (i h : Nat) (hi : gstart s1 i+5≤1028) (hh : gstart s1 h+5≤1028)
    (ne : i≠h) (a b : Fin 10) : slot s1 i a≠slot s1 h b := by
  have:=a.isLt; have:=b.isLt
  intro eq
  have e2:History5.historyId (gstart s1 i) a+16=History5.historyId (gstart s1 h) b+16:=eq
  simp only [History5.historyId,gstart] at e2 hi hh
  split_ifs at e2 <;> omega

theorem split (n i : Nat) (hi : i<3*n+1) : i∈plain n ∨ i∈packed n := by
  simp only [plain,packed,List.mem_cons,List.mem_map,List.mem_range,List.mem_flatMap,List.not_mem_nil,or_false]
  rcases Nat.lt_or_ge i 1 with h|h
  · left; left; omega
  · have:=Nat.mod_lt (i-1) (show 0<3 by decide)
    rcases (show (i-1)%3=0 ∨ (i-1)%3=1 ∨ (i-1)%3=2 by omega) with r|r|r
    · left; right; exact ⟨(i-1)/3,by omega,by omega⟩
    · right; exact ⟨(i-1)/3,by omega,by omega⟩
    · right; exact ⟨(i-1)/3,by omega,by omega⟩

theorem plain_packed (n i : Nat) (a : i∈plain n) : i∉packed n := by
  simp only [plain,packed,List.mem_cons,List.mem_map,List.mem_range,List.mem_flatMap,List.not_mem_nil,
    or_false] at a ⊢
  rintro ⟨b,_,h|h⟩ <;> rcases a with a|⟨c,_,a⟩ <;> omega

/-! Instances at dadon's +210 window (`s1 = 210`, `n = 4`, `e = 270`): the generic data are dadon's lists. -/
example : plain 4=[0,1,4,7,10] := rfl
example : packed 4=[2,3,5,6,8,9,11,12] := rfl
example : holes 210 4=[215,220,230,235,245,250,260,265].flatMap (fun t=>[base (1028+t+2),base (1028+t+4)]) := rfl

end ECDSAAdd.Entrant.StairPacket.StockWindowGeo

end

-- ArchiveStockRows.FinalW / bankPorts / FinalW.bank: in Window (build-chain switch)

section

namespace ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffixW
open Arithmetic MappedCompressed StockWindowGeo
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2: `ArchiveStockSuffix`, generic in the exit tick `e` (dadon: 270, a multiple of 5) and over the
window's archive cells `StockWindowGeo.archives s1 n` (dadon: four banks). The stock suffix ticks after `e`
never touch an archive cell. The proofs are dadon's with 270/271 replaced by `e`/`e+1`. Ticks `e+1..e+4` are not
due, which dadon special-cased as `i < 275`; here the `packDue` split alone handles them. -/

private theorem no_pack (e i:Nat) (e5:e%5=0) (lo:e+1 ≤ i) (hi:i < 512) (r:Nat) (old:r < e) (d sw:Bool):
    logical sw r∉wires (Rolling1588.Integer.packFirst base d i) ∧
    logical sw r∉wires (Rolling1588.unpackAtTick d i):=by
  have disjoint (due:History5.packDue i=true) (j:Fin 10):logical sw r≠History5.historyMap base (i-5) j:=by
    simp only [History5.packDue,decide_eq_true_eq] at due
    have lim:=j.isLt
    cases sw <;> simp only [logical,Bool.false_eq_true,if_false,if_true,History5.historyMap,History5.historyId,base,Wire]
    all_goals split_ifs <;> omega
  constructor
  · intro h
    rw [Rolling1588.Integer.packFirst,if_neg (show i≠5 by omega),Rolling1588.Integer.pack_support_eq] at h
    unfold History5.packAfter at h
    split at h
    · rename_i due
      obtain ⟨j,eq⟩:=History5.history_gate_mem base (i-5) _ (Or.inl rfl) _ h
      exact disjoint due j eq
    · simp [wires] at h
  · intro h
    rw [←Rolling1588.Integer.unpackFirst_base,Rolling1588.Integer.unpackFirst,if_neg (show i≠5 by omega),
      Rolling1588.Integer.decodeBefore_support_eq] at h
    unfold History5.decodeBefore at h
    split at h
    · rename_i due
      obtain ⟨j,eq⟩:=History5.history_gate_mem base (i-5) _ (Or.inr rfl) _ h
      exact disjoint due j eq
    · simp [wires] at h

private theorem one (e:Nat) (e5:e%5=0) (he:e≤511) (d sw:Bool) (r i:Nat) (old:r < e) (lo:e+1 ≤ i) (hi:i < 512):
    site e sw r∉wires (renameProgram (OB5.sig i) (TickRanges.tick base i ++ Rolling1588.Integer.packFirst base d i)) ∧
    site e sw r∉wires (renameProgram (OB5.sig i) (Rolling1588.unpackAtTick d i ++ W.ReverseCarry.compactReceiverTick base i)):=by
  have past:WideReference.Earlier i (logical sw r):=⟨r,by omega,by cases sw <;> simp [logical]⟩
  have off:=WideReference.away hi past
  have pack:=no_pack e i e5 lo hi r old d sw
  have pre (q:Wire) (eq:OB5.sig i q=site e sw r):q=logical sw r:=by
    -- `StairPacket.stable` (parent) hides the opened name
    rw [←StockWindowGeo.stable i e r (by omega) he (by omega) old sw] at eq
    have inj:Function.Injective (OB5.sig i):=(OB5.sig_injective i (by omega))
    exact inj eq
  constructor <;> intro h <;> rw [renameProgram_support] at h <;>
    obtain ⟨q,mem,eq⟩:=Finset.mem_image.mp h <;> rw [pre q eq,wires_append,Finset.mem_union] at mem
  · rcases mem with tick|packet
    · exact off (List.mem_toFinset.mp (W.repairedTick_support base i hi base_pool_nodup (TickRanges.tick_support base i hi base_pool_nodup tick)))
    · exact pack.1 packet
  · rcases mem with packet|tick
    · exact pack.2 packet
    · exact off (List.mem_toFinset.mp (W.ReverseCarry.compactReceiverTick_support base i hi base_pool_nodup tick))

theorem suffix (e:Nat) (e5:e%5=0) (he:e≤511) (d sw:Bool) (r i n:Nat) (old:r < e) (lo:e+1 ≤ i) (hi:i+n≤512):
    site e sw r∉wires (Rolling1588TickGap.forward d i n) ∧ site e sw r∉wires (Rolling1588.reverse d i n):=by
  induction n generalizing i with
  | zero=>simp [Rolling1588TickGap.forward,Rolling1588.reverse,wires]
  | succ n ih=>
    have a:=one e e5 he d sw r i old lo (by omega)
    have b:=ih (i+1) (by omega) (by omega)
    simp only [Rolling1588TickGap.forward,Rolling1588.reverse,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨a.1,b.1⟩,⟨b.2,a.2⟩⟩

/-- `ArchiveStockSuffix.safe`, generic over the window's archive cells. -/
theorem safe (s1 n e:Nat) (lo5:5≤s1) (he:e=s1+15*n) (le:e≤511) (e5:e%5=0) (d:Bool) (i m:Nat) (lo:e+1 ≤ i)
    (hi:i+m≤512) (q:Wire) (mem:q∈archives s1 n):
    q∉wires (Rolling1588TickGap.forward d i m) ∧ q∉wires (Rolling1588.reverse d i m):=by
  obtain ⟨sw,r,old,rfl⟩:=archive_old s1 n e lo5 he le q mem
  exact suffix e e5 le d sw r i m old lo hi

def Same (s1 n:Nat) (a b:State):Prop:=a.phase=b.phase ∧ ∀q,q∉archives s1 n → a.basis q=b.basis q
theorem independent (s1 n:Nat) (P:Program) (off:∀q∈archives s1 n,q∉wires P)
    (m:List Bool) (s t:State) (same:Same s1 n s t):
    Same s1 n (run P m s) (run P m t) ∧ ∀q∈archives s1 n,(run P m s).basis q=s.basis q:=by
  have eqs:=pool_run_agrees P (wires P) (Finset.Subset.refl _) m s t same.1
    (fun q h=>same.2 q (fun mem=>off q mem h))
  refine ⟨⟨eqs.1,?_⟩,fun q mem=>run_preserves_outside _ m s _ (off q mem)⟩
  intro q ext
  by_cases use:q∈wires P
  · exact eqs.2 q use
  · rw [run_preserves_outside _ m s _ use,run_preserves_outside _ m t _ use]
    exact same.2 q ext
end ECDSAAdd.Entrant.StairPacket.ArchiveStockSuffixW

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockGroupsW
open Arithmetic MappedCompressed StockWindowGeo
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

/-! par-d2: `StockGroups` for the `n`-block window from `s1`. Group `i < 3n+1` packs ticks `gstart s1 i .. +4`.
Groups are `Nat` indices; dadon used `Fin 13`. dadon's `stockEq` was `rfl` at 210/61; here it is an induction
over the window's due ticks. -/

def ports (s1 i:Nat):Finset Wire:=Finset.univ.image (slot s1 i)
def one (s1:Nat) (d:Bool) (i:Nat):Program:=Rolling1588.encodeAt base d (gstart s1 i)
def batch (s1:Nat) (d:Bool) (seq:List Nat):Program:=seq.flatMap (one s1 d)
def all (n:Nat):List Nat:=List.range (3*n+1)
/-- `packs`, restated here (parallel chain); `StockTailW.packs_bridge` equates the two. -/
def packs (d:Bool) (i:Nat):Nat→Program
  | 0=>[]
  | n+1=>Rolling1588.Integer.packAfter base d i ++ packs d (i+1) n

theorem packs_add (d:Bool) (i a b:Nat):
    packs d i (a+b)=packs d i a++packs d (i+a) b:=by
  induction a generalizing i with
  | zero=>simp [packs]
  | succ a ih=>
    rw [show a+1+b=(a+b)+1 by omega,packs,packs,ih (i+1),List.append_assoc,
      show i+1+a=i+(a+1) by omega]

theorem pack_idle (d:Bool) (k:Nat) (hk:k%5≠0):Rolling1588.Integer.packAfter base d k=[]:=by
  unfold Rolling1588.Integer.packAfter
  rw [if_neg (by simp only [History5.packDue,decide_eq_true_eq]; omega)]

theorem packs_idle (d:Bool) (i:Nat) (h:i%5=1):packs d i 4=[]:=by
  simp only [packs,List.append_nil]
  rw [pack_idle d i (by omega),pack_idle d (i+1) (by omega),pack_idle d (i+1+1) (by omega),
    pack_idle d (i+1+1+1) (by omega)]
  rfl

theorem packs_due (d:Bool) (i:Nat) (h5:10≤ i) (h:i%5=0):
    packs d i 1=Rolling1588.encodeAt base d (i-5):=by
  simp only [packs,List.append_nil]
  unfold Rolling1588.Integer.packAfter Rolling1588.Integer.encode
  rw [if_pos (by simp only [History5.packDue,decide_eq_true_eq]; omega),if_neg (by omega)]

/-- `StockGroups.stockEq`, generic: the stock walk's packs over the window are the batch of its `3n+1` groups. -/
theorem stockEq (d:Bool) (s1 n:Nat) (lo:10≤s1) (h5:s1%5=0):
    packs d s1 (15*n+1)=batch s1 d (all n):=by
  have g:∀ m k,packs d (s1+5*k) (5*m+1)=(List.range' k (m+1)).flatMap (one s1 d):=by
    intro m
    induction m with
    | zero=>
      intro k
      rw [show 5*0+1=1 by rfl,packs_due d _ (by omega) (by omega)]
      simp only [List.range'_succ,List.range'_zero,List.flatMap_cons,List.flatMap_nil,List.append_nil,one,gstart]
      congr 1; omega
    | succ m ih=>
      intro k
      rw [show 5*(m+1)+1=1+(4+(5*m+1)) by omega,packs_add,packs_add,packs_due d _ (by omega) (by omega),
        packs_idle d _ (by omega),show s1+5*k+1+4=s1+5*(k+1) by omega,ih (k+1)]
      -- unfold both sides together; a `rw` of `range'_succ` hits only the left copy
      simp only [List.append_nil,List.range'_succ,List.flatMap_cons,List.nil_append,one,gstart]
      rw [show s1 - 5 + 5 * k = s1 + 5 * k - 5 by omega]
  have e:=g (3*n) 0
  rw [show 5*(3*n)+1=15*n+1 by omega,show s1+5*0=s1 by omega] at e
  rw [e,batch,all,List.range_eq_range']

theorem allNodup (n:Nat):(all n).Nodup:=List.nodup_range
theorem inAll {n i:Nat} (h:i<3*n+1):i∈all n:=List.mem_range.mpr h
theorem plainNodup (n:Nat):(plain n).Nodup:=by
  simp only [plain,List.nodup_cons,List.mem_map,List.mem_range,not_exists,not_and]
  refine ⟨fun b _ e=>by omega,?_⟩
  exact (List.nodup_range).map (fun a b e=>by omega)

theorem cover (s1:Nat) (d:Bool) (i:Nat):wires (one s1 d i)⊆ports s1 i:=by
  intro q h
  change q∈wires (renameProgram (MeasuredCodec5.label (slot s1 i)) (Rolling1588.codeEncode d)) at h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
  rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
  exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,by simp [MeasuredCodec5.label,ha]⟩

private theorem distant (s1:Nat) (lo:5≤s1) {i h:Nat} (hi:gstart s1 i+5≤1028) (hh:gstart s1 h+5≤1028) (ne:i≠h)
    {q:Wire} (mem:q∈ports s1 i):q∉ports s1 h:=by
  intro hit
  obtain ⟨a,_,ea⟩:=Finset.mem_image.mp mem
  obtain ⟨b,_,eb⟩:=Finset.mem_image.mp hit
  exact distinct s1 lo i h hi hh ne a b (ea.trans eb.symm)

theorem batch_cover (s1:Nat) (d:Bool) (seq:List Nat) (q:Wire) (hit:q∈wires (batch s1 d seq)):
    ∃i∈seq,q∈ports s1 i:=by
  induction seq with
  | nil=>simp [batch,wires] at hit
  | cons h t ih=>
    change q∈wires (one s1 d h++batch s1 d t) at hit
    rw [wires_append,Finset.mem_union] at hit
    rcases hit with a|b
    · exact ⟨h,by simp,cover _ _ _ a⟩
    · obtain ⟨i,ii,v⟩:=ih b
      exact ⟨i,by simp [ii],v⟩
theorem outside (s1:Nat) (d:Bool) (seq:List Nat) (s:State) (q:Wire) (off:∀i∈seq,q∉ports s1 i):
    (run (batch s1 d seq) [] s).basis q=s.basis q:=by
  apply run_preserves_outside
  intro hit;obtain ⟨i,mem,h⟩:=batch_cover s1 d seq q hit;exact off i mem h
theorem isolated (s1:Nat) (lo:5≤s1) (d:Bool) (seq:List Nat) (nd:seq.Nodup) (small:∀i∈seq,gstart s1 i+5≤1028)
    (s:State) (i:Nat) (mem:i∈seq) (q:Wire) (hq:q∈ports s1 i):
    (run (batch s1 d seq) [] s).basis q=(run (one s1 d i) [] s).basis q:=by
  induction seq generalizing s with
  | nil=>simp at mem
  | cons h t ih=>
    change (run (one s1 d h++batch s1 d t) [] s).basis q=_
    rw [run_append,run_take,List.drop_nil]
    obtain ⟨not,unique⟩:=List.nodup_cons.mp nd
    have sh:gstart s1 h+5≤1028:=small h (by simp)
    have st:∀k∈t,gstart s1 k+5≤1028:=fun k hk=>small k (by simp [hk])
    rcases List.mem_cons.mp mem with rfl|im
    · exact outside s1 d t _ q (fun j jj=>distant s1 lo sh (st j jj) (fun eq=>not (eq.symm ▸ jj)) hq)
    · have ne:i≠h:=fun eq=>not (eq ▸ im)
      have si:=st i im
      have hd:Disjoint (wires (one s1 d i)) (wires (one s1 d h)):=by
        rw [Finset.disjoint_left]
        intro q' a b
        exact distant s1 lo si sh ne (cover _ _ _ a) (cover _ _ _ b)
      rw [ih unique st (run (one s1 d h) [] s) im,run_disjoint_commute _ _ hd]
      exact run_preserves_outside _ _ _ _ (fun bad=>distant s1 lo si sh ne hq (cover _ _ _ bad))

/-- Window groups stay inside the history pool. -/
theorem small_all (s1 n:Nat) (ge:5≤s1) (le:s1+15*n≤511) :∀i∈all n,gstart s1 i+5≤1028:=by
  intro i hi; have:=List.mem_range.mp hi; simp only [gstart]; omega
theorem small_plain (s1 n:Nat) (ge:5≤s1) (le:s1+15*n≤511) :∀i∈plain n,gstart s1 i+5≤1028:=by
  intro i hi
  simp only [plain,List.mem_cons,List.mem_map,List.mem_range] at hi
  rcases hi with rfl|⟨b,hb,rfl⟩ <;> simp only [gstart] <;> omega

/-- dadon's instance: the 13 groups of 210..270. -/
example (d:Bool) : packs d 210 61=batch 210 d (all 4) := stockEq d 210 4 (by decide) (by decide)
end ECDSAAdd.Entrant.StairPacket.StockGroupsW

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveReferenceW
open Arithmetic MappedCompressed WideReference StockWindowGeo
set_option linter.unusedVariables false
/-- par-d2: `StockArchiveReference.common` for the `n`-block window from `s1` (exit `s1+15n`). The native packs
of the window are the batch of its `plain` groups. -/
def ordinary (s1 n:Nat) (d:Bool):Program:=StockGroupsW.batch s1 d (plain n)
def common (s1 n:Nat) (d:Bool) (raw:State):State:=
  pullState (OB5.sig (s1+15*n)) (eraseSites (holes s1 n) (run (ordinary s1 n d) [] (run (span s1 (15*n+1)) [] raw)))
end ECDSAAdd.Entrant.StairPacket.StockArchiveReferenceW


namespace ECDSAAdd.Entrant.StairPacket.StockBaselineW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span WideReference.canonical

theorem high_lo (b:Nat):high (2+3*b)=false:=by simp only [high]; rw [decide_eq_false_iff_not]; omega
theorem high_hi (b:Nat):high (3+3*b)=true:=by simp only [high]; rw [decide_eq_true_eq]; omega
theorem packed_lt {n i:Nat} (h:i∈StockWindowGeo.packed n):i<3*n+1:=by
  -- `StairPacket.packed` (parent) hides `StockWindowGeo.packed`
  simp only [StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at h
  obtain ⟨b,hb,h|h⟩:=h <;> omega
theorem plain_lt {n i:Nat} (h:i∈plain n):i<3*n+1:=by
  simp only [plain,List.mem_cons,List.mem_map,List.mem_range] at h
  rcases h with rfl|⟨b,hb,rfl⟩ <;> omega

/-- `StockBaseline.chart`, generic: an archived group is the young/old half of its bank's tile. -/
theorem chart (s1 n i:Nat) (lo:5≤s1) (hi:i∈StockWindowGeo.packed n):gstart s1 i=tile (packet s1 i) (high i) ∧
    s1≤packet s1 i ∧ packet s1 i+15≤s1+15*n ∧ ∃b<n,packet s1 i=s1+15*b:=by
  simp only [StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at hi
  obtain ⟨b,hb,h|h⟩:=hi <;> subst h
  · rw [high_lo]
    simp only [gstart,tile,packet,Bool.false_eq_true,if_false]
    exact ⟨by omega,by omega,by omega,b,hb,by omega⟩
  · rw [high_hi]
    simp only [gstart,tile,packet,if_true]
    exact ⟨by omega,by omega,by omega,b,hb,by omega⟩

theorem small512 (s1 n:Nat) (ge:5≤s1) (le:s1+15*n≤511) (seq:List Nat) (bound:∀i∈seq,i<3*n+1):∀i∈seq,gstart s1 i+5≤512:=by
  intro i hi; have:=bound i hi; simp only [gstart]; omega

theorem phase_batch (s1:Nat) (d:Bool) (seq:List Nat) (small:∀i∈seq,gstart s1 i+5≤512) (s:State):
    (run (batch s1 d seq) [] s).phase=s.phase:=by
  induction seq generalizing s with
  | nil=>simp only [batch,List.flatMap_nil,run]
  | cons h t ih=>
    change (run (one s1 d h++batch s1 d t) [] s).phase=_
    rw [run_append,run_take,List.drop_nil,ih (fun k hk=>small k (by simp [hk]))]
    exact Rolling1588.codeEncodeAt_zero_phase d (slot s1 h)
      (History5.historyMap_injective base base_pool_nodup (gstart s1 h) (small h (by simp))) s

end ECDSAAdd.Entrant.StairPacket.StockBaselineW

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span

/-! par-d2: `StockArchiveBanks` for the window of blocks `j1 .. jn` (`n = jn-j1+1` banks, exit at
`start j1+15n`). Bank `b < n` is the archive of block `j1+b`, or the exit archive for the last bank.
`exitCells` is the one fact needed from par-c2's exit form: its first 16 code ports are the cells of the exit
tick. `ArchiveBoundary270.codePortsList` starts with `cellsRestoreP 270`, as the generic exit form will. -/

theorem window_cells (k:Fin 23) (j:Fin 16):
    ArchiveJ.codePorts k ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start k+15)).getD j 0:=by
  rw [ArchiveJ.codePorts,ArchiveJ.code_split,List.append_assoc,
    List.getD_append _ _ _ _ (by simp [Partial.cellsRestoreP])]

def siteAt (j1 jn:Fin 23) (exitPorts:Ports) (b:Nat) (j:Fin 16):Wire:=
  ArchiveStockRows.bankPorts j1 jn exitPorts b ⟨j.val,by omega⟩

theorem site_eq (j1 jn:Fin 23) (exitPorts:Ports)
    (exitCells:∀j:Fin 16,exitPorts ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start jn+15)).getD j 0)
    (b:Nat) (hb:j1.val+b≤jn.val) (j:Fin 16):siteAt j1 jn exitPorts b j=bankSite (start j1) b j:=by
  simp only [siteAt,ArchiveStockRows.bankPorts,bankSite,tick]
  split
  · rw [window_cells]; congr 2; simp only [start]; omega
  · rw [exitCells]; congr 2; simp only [start]; omega

/-- dadon's `byte`, now independent of the bank: one small decide over `Bool × Fin 16`. -/
theorem byte:∀(d:Bool)(j:Fin 16),
    get (storage (native d (decide (8≤j.val)))) (index j)=get (StairArchiveNativeCut.canonical d d) j:=by decide +kernel

def nativeAt (ps:Fin 16→Wire) (d:Bool) (r:Nat) (s:State):Prop:=
  ∀j:Fin 16,s.basis (ps j)=(get (StairArchiveNativeCut.canonical d d) j).testBit r

theorem readback (e:Nat) (he:e≤511) (z:State) (q w:Wire) (eq:q=OB5.sig e w):
    (pullState (OB5.sig e) z).basis q=z.basis w:=by
  change z.basis (OB5.sig e q)=z.basis w
  rw [eq,OB5.sig_invol e he]

end ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW

end
-- END par-d2 StockWindowW

-- BEGIN par-d2 OrdinaryChainW (Tail8dd, serial tail; after ArchiveHistoryCompare)
section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainW
open Arithmetic MappedCompressed WideReference ArchiveHistoryCompare
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run

/-! par-d2: the mask/program half of dadon's `OrdinaryChain` (`mask{s}`, `progW{s}`, `add{s}`), as a fold over the
window's blocks from `s1`. Block `k` (start `s1+15k`) has two parts:
- its exit hands the previous block's archive cells (ticks `s-10..s-1`) to the stock frame (`newBank`, empty for
  the first block; dadon's `Logical{s}Exit.newBank`);
- its ordinary program is the stock encoder of its plain group (`s1-5` for the first block, `s-15` after).
dadon's three per-step decides over the growing masks (`maskEarly`, `progEarly`, `apart`) become `omega` bounds:
mask cells are older than `s-15`, and program cells are older than `s-10`. -/

/-- History cells of ticks `t .. t+9`. -/
def cells10 (t:Nat):List Wire:=(List.range' t 10).flatMap (fun r=>[base r,base (1028+r)])
def newBank (s1 s:Nat):List Wire:=if s=s1 then [] else cells10 (s-10)
/-- Plain group of block `k`. -/
def group (s1 k:Nat):Nat:=if k=0 then s1-5 else s1+15*k-15
def mask (s1:Nat):Nat→List Wire
  | 0=>[]
  | k+1=>mask s1 k++newBank s1 (s1+15*k)
def progW (s1:Nat) (d:Bool):Nat→Program
  | 0=>[]
  | k+1=>progW s1 d k++Rolling1588.encodeAt base d (group s1 k)

theorem mask_cells (s1:Nat) (lo:10≤s1) : ∀k,∀q∈mask s1 k,∃r,r+16≤s1+15*k ∧ (q=base r ∨ q=base (1028+r))
  | 0,q,h=>by simp [mask] at h
  | k+1,q,h=>by
    simp only [mask,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨r,hr,e⟩:=mask_cells s1 lo k q h
      exact ⟨r,by omega,e⟩
    · unfold newBank at h
      split at h
      · simp at h
      · simp only [cells10,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,or_false] at h
        obtain ⟨r,⟨r1,r2⟩,e⟩:=h
        exact ⟨r,by omega,e⟩

theorem encode_cells (d:Bool) (t:Nat) : ∀q∈wires (Rolling1588.encodeAt base d t),
    ∃r,t≤r ∧ r≤t+4 ∧ (q=base r ∨ q=base (1028+r)) := by
  intro q h
  change q∈wires (renameProgram (MeasuredCodec5.label (History5.historyMap base t)) (Rolling1588.codeEncode d)) at h
  rw [renameProgram_support] at h
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
  rw [(Rolling1588.code_support d).1,Finset.mem_range] at ha
  refine ⟨t+a/2,by omega,by omega,?_⟩
  simp only [MeasuredCodec5.label,ha,dif_pos,History5.historyMap,History5.historyId]
  split
  · left; rfl
  · right; congr 1; omega

theorem prog_cells (s1:Nat) (lo:10≤s1) (d:Bool) : ∀k,∀q∈wires (progW s1 d k),∃r,r+11≤s1+15*k ∧ (q=base r ∨ q=base (1028+r))
  | 0,q,h=>by simp [progW,wires] at h
  | k+1,q,h=>by
    simp only [progW,wires_append,Finset.mem_union] at h
    rcases h with h|h
    · obtain ⟨r,hr,e⟩:=prog_cells s1 lo d k q h
      exact ⟨r,by omega,e⟩
    · obtain ⟨r,r1,r2,e⟩:=encode_cells d _ q h
      refine ⟨r,?_,e⟩
      simp only [group] at r1 r2
      split at r1 <;> split at r2 <;> omega

/-- `OrdinaryChain.add{s}`, generic: block `k ≥ 1` extends the mask and the ordinary program by one block. -/
theorem add (s1:Nat) (lo:10≤s1) (k:Nat) (hk:1≤k) (lim:s1+15*k+15≤512) (d:Bool) (raw baseRaw out:State)
    (old:Except (mask s1 k) raw (run (progW s1 d k) [] (run (span s1 (15*k)) [] baseRaw)))
    (step:Except (newBank s1 (s1+15*k)) out
      (run (Rolling1588.encodeAt base d (group s1 k)) [] (run (span (s1+15*k) 15) [] raw))) :
    Except (mask s1 (k+1)) out (run (progW s1 d (k+1)) [] (run (span s1 (15*(k+1))) [] baseRaw)) := by
  have h:=extend (s1+15*k) 15 lim _ _ _ _ raw (run (span s1 (15*k)) [] baseRaw) out old step
    (fun q hit=>by obtain ⟨r,hr,e⟩:=mask_cells s1 lo k q hit; exact ⟨r,by omega,e⟩)
    (fun q hit=>by obtain ⟨r,hr,e⟩:=prog_cells s1 lo d k q hit; exact ⟨r,by omega,e⟩)
    (fun q hit used=>by
      obtain ⟨r,hr,e⟩:=mask_cells s1 lo k q hit
      obtain ⟨r',r1,r2,e'⟩:=encode_cells d _ q used
      simp only [group,if_neg (show k≠0 by omega)] at r1 r2
      rcases e with rfl|rfl <;> rcases e' with e'|e' <;> simp only [base,Wire] at e' <;> omega)
  have chronology:run (span s1 (15*(k+1))) [] baseRaw=run (span (s1+15*k) 15) [] (run (span s1 (15*k)) [] baseRaw):=by
    rw [show 15*(k+1)=15*k+15 by omega,spanAppend s1 (15*k) 15,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h

/-- The window's ordinary chain over its `n` blocks, from per-block exits (par-c2's `Logical#Exit` / `Ordinary#Exit`
for block `k`, on the block's stock input `st k`). -/
theorem chain (s1:Nat) (lo:10≤s1) (d:Bool) (st:Nat→State) (n:Nat) (lim:s1+15*n≤512)
    (step:∀k<n,Except (newBank s1 (s1+15*k)) (st (k+1))
      (run (Rolling1588.encodeAt base d (group s1 k)) [] (run (span (s1+15*k) 15) [] (st k)))) :
    ∀k,1≤k → k≤n → Except (mask s1 k) (st k) (run (progW s1 d k) [] (run (span s1 (15*k)) [] (st 0)))
  | 0,h,_=>by omega
  | 1,_,hn=>by
    have s0:=step 0 (by omega)
    simp only [mask,progW,newBank,if_pos (show s1+15*0=s1 by omega),List.nil_append,
      show s1+15*0=s1 by omega] at s0 ⊢
    exact s0
  | k+2,_,hn=>by
    have ih:=chain s1 lo d st n lim step (k+1) (by omega) (by omega)
    exact add s1 lo (k+1) (by omega) (by omega) d (st (k+1)) (st 0) (st (k+2)) ih (step (k+1) (by omega))

/-- The exit tick (`OrdinaryChain.add270`, generic): the stock tick `e` itself and the last archive's cells. -/
theorem add_last (s1:Nat) (lo:10≤s1) (n:Nat) (hn:1≤n) (lim:s1+15*n+1≤512) (d:Bool) (raw baseRaw out:State)
    (old:Except (mask s1 n) raw (run (progW s1 d n) [] (run (span s1 (15*n)) [] baseRaw)))
    (step:Except (cells10 (s1+15*n-10)) out
      (run (Rolling1588.encodeAt base d (s1+15*n-15)) [] (run (span (s1+15*n) 1) [] raw))) :
    Except (mask s1 n++cells10 (s1+15*n-10)) out
      (run (progW s1 d n++Rolling1588.encodeAt base d (s1+15*n-15)) [] (run (span s1 (15*n+1)) [] baseRaw)) := by
  have h:=extend (s1+15*n) 1 lim _ _ _ _ raw (run (span s1 (15*n)) [] baseRaw) out old step
    (fun q hit=>by obtain ⟨r,hr,e⟩:=mask_cells s1 lo n q hit; exact ⟨r,by omega,e⟩)
    (fun q hit=>by obtain ⟨r,hr,e⟩:=prog_cells s1 lo d n q hit; exact ⟨r,by omega,e⟩)
    (fun q hit used=>by
      obtain ⟨r,hr,e⟩:=mask_cells s1 lo n q hit
      obtain ⟨r',r1,r2,e'⟩:=encode_cells d _ q used
      rcases e with rfl|rfl <;> rcases e' with e'|e' <;> simp only [base,Wire] at e' <;> omega)
  have chronology:run (span s1 (15*n+1)) [] baseRaw=run (span (s1+15*n) 1) [] (run (span s1 (15*n)) [] baseRaw):=by
    rw [spanAppend s1 (15*n) 1,run_append,run_take,List.drop_nil]
  rw [chronology]
  exact h

/-! First ship 120..255 (s1 = 120, n = 10 blocks, exit 270). -/
example : group 120 0=115 ∧ group 120 9=240 ∧ newBank 120 120=[] ∧ newBank 120 135=cells10 125 := ⟨rfl,rfl,rfl,rfl⟩

-- needs par-a WideReference patch (oldSites, endRaw_inside_gen/outside_gen); goes inside OrdinaryChainW after `add_last`
/-! Hole carry, generic (`OrdinaryChain.carry240/255` and `holes225/240/255`).
dadon decided `q∉sites` and `oldRange` per block. Here both are hypotheses, so the proof
does not grow with the window. `clear` is par-c2's `cleared_holes` (still per block).
`endRaw_inside_gen` reads the snapshot through `OB5.sig (s+14)`, which is the identity
on these wires only while `Fixed s` holds; the statement does not assume that. -/

theorem holes_inside (s:Nat) (hs:s+14≤511) (holes:List Wire)
    (mem:∀q∈holes,q∈oldSites s) (raw history:State)
    (clear:∀q∈holes,history.basis (OB5.sig (s+14) q)=false) :
    ∀q∈holes,(endRaw s raw history).basis q=false := by
  intro q hq
  rw [endRaw_inside_gen s hs raw history q (mem q hq)]
  exact clear q hq

theorem carry (s:Nat) (hs:s+14≤511) (holes:List Wire)
    (off:∀q∈holes,q∉oldSites s) (aged:∀q∈holes,oldRange s q)
    (raw history:State) (clear:∀q∈holes,raw.basis q=false) :
    ∀q∈holes,(endRaw s raw history).basis q=false := by
  intro q hq
  rw [endRaw_outside_gen s hs raw history q (off q hq)]
  rw [run_preserves_outside (span s 15) [] raw q
    (pastOffSpan s 15 q (by omega) (OrdinaryChain.early s q (aged q hq)))]
  exact clear q hq

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainW

end
-- END par-d2 OrdinaryChainW

-- ==== w4: build-w4b StockTailW + StockRowVectorW ====
-- BEGIN par-d2 StockTailW (serial tail: Tail8dd; only what needs StockDelayed.window / StockArchiveByte)
section

namespace ECDSAAdd.Entrant.StairPacket.StockGroupsW
set_option linter.unusedVariables false
/-- The parallel chain's `packs` is dadon's `StockDelayed.packs`. -/
theorem packs_bridge (d:Bool) (i n:Nat):StockDelayed.packs d i n=packs d i n:=by
  induction n generalizing i with
  | zero=>rfl
  | succ n ih=>rw [StockDelayed.packs,packs,ih]
end ECDSAAdd.Entrant.StairPacket.StockGroupsW

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveTruthW
open Arithmetic MappedCompressed WideReference SkywalkRails StairArchiveTrace StairArchiveRaw StairArchiveNativeRows CodecBitSliceVerify
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run SkywalkNat.step span WideReference.canonical StairArchiveRaw.rawCol SkywalkTrace.trace

private theorem observeSite (b:BasisState) (t:Nat) (q:Fin 10) (v:Bool×Bool)
    (a:b (base (t+q.val/2))=v.1) (c:b (base (1028+(t+q.val/2)))=v.2):
    b (History5.historyMap base t q)=letterBit v q:=by
  unfold History5.historyMap History5.historyId letterBit
  by_cases h:q.val%2=0
  · simpa only [if_pos h] using a
  · simpa only [if_neg h,Nat.add_assoc] using c

/-- `StockArchiveTruth.raw_for`, generic in the window start `s1` and length `len` (dadon: 210, 61). -/
theorem raw_for (s1 len x p:Nat) (lim:s1+len≤512) (good:Bounds x p) (s:State) (dom:Domain s1 x p s)
    (k:Nat) (start:s1≤k) (stop:k+15≤s1+len)
    (row:Nat) (truth:ArchiveStockRows.Chronology k x p row) (hi:Bool) (q:Fin 10):
    (run (span s1 len) [] s).basis (History5.historyMap base (StockWindowGeo.tile k hi) q)=
      (rawCol ((if hi then 10 else 0)+q.val)).testBit row:=by
  let e:Nat:=(if hi then 10 else 0)+q.val
  have bound:e<20:=by cases hi <;> simp [e] <;> omega
  have lo:s1≤StockWindowGeo.tile k hi+q.val/2:=by unfold StockWindowGeo.tile;omega
  have lim':StockWindowGeo.tile k hi+q.val/2<s1+len:=by cases hi <;> simp [StockWindowGeo.tile] <;> omega
  have obs:=trace_sites s1 len x p lim good s [] dom (StockWindowGeo.tile k hi+q.val/2) lo lim'
  have exactBit:=observeSite (run (span s1 len) [] s).basis (StockWindowGeo.tile k hi) q _ obs.1 obs.2
  have label:=StockArchiveTruth.observedLabel k x p row truth ⟨e,bound⟩
  change (rawCol e).testBit row=letterBit (SkywalkTrace.code (WideReference.canonical (k+(5+e/2)) x p)) e at label
  have shift : k+(5+e/2)=StockWindowGeo.tile k hi+q.val/2:=by cases hi <;> simp [StockWindowGeo.tile,e] <;> omega
  have parity:e%2=q.val%2:=by
    cases hi <;> simp [e]
    omega
  rw [shift] at label
  have bit (v:Bool×Bool):letterBit v e=letterBit v q:=by simp only [letterBit,parity]
  exact exactBit.trans ((bit _).symm.trans label.symm)

theorem native_byte (s1 len x p:Nat) (lim:s1+len≤512) (good:Bounds x p) (s:State) (dom:Domain s1 x p s)
    (k:Nat) (start:s1≤k) (stop:k+15≤s1+len)
    (row:Nat) (lm:row<63145) (truth:ArchiveStockRows.Chronology k x p row) (d hi:Bool) (m:List Bool):
    let raw:=run (span s1 len) [] s
    let f:=History5.historyMap base (StockWindowGeo.tile k hi)
    let out:=run (Rolling1588.codeEncodeAt d f) m raw
    out.phase=raw.phase ∧ ∀q:Fin 10,out.basis (f q)=(get (storage (native d hi)) q).testBit row:=by
  exact StockArchiveByte.run_byte d hi row lm _ (History5.historyMap_injective base base_pool_nodup _
    (by cases hi <;> simp [StockWindowGeo.tile] <;> omega)) _ m
    (raw_for s1 len x p lim good s dom k start stop row truth hi)
end ECDSAAdd.Entrant.StairPacket.StockArchiveTruthW


namespace ECDSAAdd.Entrant.StairPacket.StockBaselineW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 14000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span WideReference.canonical

theorem receipt (s1 n:Nat) (lo:10≤s1) (le:s1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p) (s:State)
    (dom:Domain s1 x p s) (i:Nat) (active:i∈StockWindowGeo.packed n) (row:Nat) (lim:row<63145)
    (truth:ArchiveStockRows.Chronology (packet s1 i) x p row) (j:Fin 10):
    let raw:=run (span s1 (15*n+1)) [] s
    (run (batch s1 d (all n)) [] raw).basis (slot s1 i j)=(get (storage (native d (high i))) j).testBit row:=by
  have ⟨shape,lo',hi',_⟩:=chart s1 n i (by omega) active
  let raw:=run (span s1 (15*n+1)) [] s
  have obs:=StockArchiveTruthW.native_byte s1 (15*n+1) x p (by omega) good s dom (packet s1 i) lo' (by omega)
    row lim truth d (high i) []
  have bit:=obs.2 j
  change (run (batch s1 d (all n)) [] raw).basis (slot s1 i j)=_
  rw [isolated s1 (by omega) d (all n) (allNodup n) (small_all s1 n (by omega) le) raw i (inAll (packed_lt active)) (slot s1 i j)
    (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)]
  change (run (Rolling1588.codeEncodeAt d (History5.historyMap base (gstart s1 i))) [] raw).basis
    (History5.historyMap base (gstart s1 i) j)=_
  rwa [shape]

/-- `StockBaseline.from_final`, generic over the window's banks. -/
theorem from_final {j1 jn:Fin 23} {exitPorts:ArchivePortAction.Ports} (n:Nat) (hn:jn.val+1=j1.val+n) (d:Bool)
    (x:Nat) (a:State) (results:ArchiveStockRows.FinalW j1 jn exitPorts d x p a) (i:Nat) (active:i∈StockWindowGeo.packed n) :
    ∃row<63145,ArchiveStockRows.Chronology (packet (start j1) i) x p row:=by
  obtain ⟨-,-,-,b,hb,eq⟩:=chart (start j1) n i (by simp only [start]; omega) active
  obtain ⟨r,l,t,_⟩:=results.bank b (by omega)
  exact ⟨r,l,by rw [eq]; exact t⟩

/-- `StockBaseline.comparison`, generic: after the window, the stock walk and the window's reference state agree
off the archive cells. -/
theorem comparison {j1 jn:Fin 23} {exitPorts:ArchivePortAction.Ports} (n:Nat) (hn:jn.val+1=j1.val+n)
    (le:start j1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start j1) s.basis)
    (results:ArchiveStockRows.FinalW j1 jn exitPorts d x p a):
    ArchiveStockSuffixW.Same (start j1) n
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) s))
      (StockArchiveReferenceW.common (start j1) n d s):=by
  have lo:10≤start j1:=by simp only [start]; omega
  have h5:start j1%5=0:=by simp only [start]; omega
  let s1:=start j1
  let raw:=run (span s1 (15*n+1)) [] s
  have stock:=StockDelayed.window d x good.nonzero good.small s1 (15*n+1) (by omega) (by omega) s m stage
  rw [show s1+(15*n+1)-1=s1+15*n by omega] at stock
  change run (Rolling1588TickGap.forward d s1 (15*n+1)) m (pullState (OB5.sig (s1-1)) s)=
    pullState (OB5.sig (s1+15*n)) (run (StockDelayed.packs d s1 (15*n+1)) [] raw) at stock
  rw [stock,packs_bridge,stockEq d s1 n lo h5,StockArchiveReferenceW.common,StockArchiveReferenceW.ordinary]
  refine ⟨(phase_batch s1 d (all n) (small512 s1 n (by omega) le _ (fun i hi=>List.mem_range.mp hi)) raw).trans
    (phase_batch s1 d (plain n) (small512 s1 n (by omega) le _ (fun i hi=>plain_lt hi)) raw).symm,?_⟩
  intro q safe
  let y:=OB5.sig (s1+15*n) q
  change (run (batch s1 d (all n)) [] raw).basis y=
    (if y∈holes s1 n then false else (run (batch s1 d (plain n)) [] raw).basis y)
  have away:OB5.sig (s1+15*n) y∉archives s1 n:=by simpa only [y,OB5.sig_invol (s1+15*n) (by omega)] using safe
  by_cases old:∃i∈StockWindowGeo.packed n,y∈ports s1 i
  · obtain ⟨i,used,inside⟩:=old
    obtain ⟨j,_,atSite⟩:=Finset.mem_image.mp inside
    have hs:=sparse s1 n (s1+15*n) (by omega) rfl le i used j
    rcases hs with ⟨blank,hit⟩|covered
    · rw [←atSite,if_pos hit]
      obtain ⟨row,lim,history⟩:=from_final n hn d x a results i used
      have dom:=WideReference.initial s1 x p (by omega) d s stage
      have bit:=receipt s1 n lo le d x good s dom i used row lim history j
      have cleared (k:Nat) (ok:k=5 ∨ k=9):CodecBitSliceVerify.get (storage (native d (high i))) k=0:=by
        rcases ok with rfl|rfl <;> rfl
      exact bit.trans ((congrArg (fun a:Nat=>a.testBit row) (cleared j (by rcases blank with rfl|rfl <;> decide))).trans
        (Nat.zero_testBit row))
    · exact (away (atSite ▸ covered)).elim
  · have nh:y∉holes s1 n:=by
      intro h;obtain ⟨i,used,j,e⟩:=hole_slot s1 n y h
      exact old ⟨i,used,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.symm⟩⟩
    rw [if_neg nh]
    by_cases saved:∃i∈plain n,y∈ports s1 i
    · obtain ⟨i,mem,h⟩:=saved
      exact (isolated s1 (by omega) d (all n) (allNodup n) (small_all s1 n (by omega) le) raw i (inAll (plain_lt mem)) y h).trans
        (isolated s1 (by omega) d (plain n) (plainNodup n) (small_plain s1 n (by omega) le) raw i mem y h).symm
    · have off (i:Nat) (hi:i<3*n+1):y∉ports s1 i:=by
        intro h;rcases StockWindowGeo.split n i hi with m|m
        · exact saved ⟨i,m,h⟩
        · exact old ⟨i,m,h⟩
      exact (outside s1 d (all n) raw y (fun i hi=>off i (List.mem_range.mp hi))).trans
        (outside s1 d (plain n) raw y (fun i hi=>off i (plain_lt hi))).symm

end ECDSAAdd.Entrant.StairPacket.StockBaselineW

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW
open Arithmetic MappedCompressed Secp256k1 WideReference StockWindowGeo StockGroupsW
open ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run span

/-! par-d2: `StockArchiveBanks` for the window of blocks `j1 .. jn` (`n = jn-j1+1` banks, exit at
`start j1+15n`). Bank `b < n` is the archive of block `j1+b`, or the exit archive for the last bank.
`exitCells` is the one fact needed from par-c2's exit form: its first 16 code ports are the cells of the exit
tick. `ArchiveBoundary270.codePortsList` starts with `cellsRestoreP 270`, as the generic exit form will. -/

theorem stock_state (s1 n:Nat) (lo:10≤s1) (h5:s1%5=0) (le:s1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p)
    (s:State) (m:List Bool) (stage:Rolling1588.Integer.Stage base d x p s1 s.basis):
    run (Rolling1588TickGap.forward d s1 (15*n+1)) m (pullState (OB5.sig (s1-1)) s)=
    pullState (OB5.sig (s1+15*n)) (run (batch s1 d (all n)) [] (run (span s1 (15*n+1)) [] s)):=by
  rw [←stockEq d s1 n lo h5,←packs_bridge]
  have w:=StockDelayed.window d x good.nonzero good.small s1 (15*n+1) (by omega) (by omega) s m stage
  rwa [show s1+(15*n+1)-1=s1+15*n by omega] at w

theorem stored (j1 jn:Fin 23) (exitPorts:Ports)
    (exitCells:∀j:Fin 16,exitPorts ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start jn+15)).getD j 0)
    (n:Nat) (hn:jn.val+1=j1.val+n) (le:start j1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p) (s:State)
    (m:List Bool) (stage:Rolling1588.Integer.Stage base d x p (start j1) s.basis) (b:Nat) (hb:b<n) (row:Nat)
    (lim:row<63145) (truth:ArchiveStockRows.Chronology (start j1+15*b) x p row):
    nativeAt (siteAt j1 jn exitPorts b) d row
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) s)):=by
  have lo:10≤start j1:=by simp only [start]; omega
  have h5:start j1%5=0:=by simp only [start]; omega
  intro j
  obtain ⟨addr,clock,used,hj⟩:=chart (start j1) n b (start j1+15*n) (by omega) hb rfl le j
  have dom:=WideReference.initial (start j1) x p (by omega) d s stage
  have bit:=StockBaselineW.receipt (start j1) n lo le d x good s dom (group b j) used row lim
    (by rw [clock]; exact truth) (index j)
  rw [stock_state (start j1) n lo h5 le d x good s m stage,
    readback _ (by omega) _ _ _ ((site_eq j1 jn exitPorts exitCells b (by omega) j).trans addr)]
  exact bit.trans (congrArg (fun a:Nat=>a.testBit row) (by rw [hj]; exact byte d j))

structure Paired (j1 jn:Fin 23) (exitPorts:Ports) (n:Nat) (d:Bool) (x:Nat) (a s:State) (rows:Nat→Nat):Prop where
  equality:ArchiveStockSuffixW.Same (start j1) n a s
  labels:∀b<n,rows b<63145 ∧ ArchiveStockRows.Chronology (start j1+15*b) x p (rows b)
  custom:∀b<n,Kept (ArchiveStockRows.bankPorts j1 jn exitPorts b) d (rows b) a
  stock:∀b<n,nativeAt (siteAt j1 jn exitPorts b) d (rows b) s

theorem paired (j1 jn:Fin 23) (exitPorts:Ports)
    (exitCells:∀j:Fin 16,exitPorts ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start jn+15)).getD j 0)
    (n:Nat) (hn:jn.val+1=j1.val+n) (le:start j1+15*n≤511) (d:Bool) (x:Nat) (good:Bounds x p) (s a:State)
    (m:List Bool) (stage:Rolling1588.Integer.Stage base d x p (start j1) s.basis)
    (res:ArchiveStockRows.FinalW j1 jn exitPorts d x p a)
    (normalized:ArchiveStockSuffixW.Same (start j1) n a (StockArchiveReferenceW.common (start j1) n d s)):
    ∃rows,Paired j1 jn exitPorts n d x a
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) s)) rows:=by
  classical
  let rows (b:Nat):Nat:=if hb:j1.val+b≤jn.val then (res.bank b hb).choose else 0
  have facts (b:Nat) (hb:b<n):rows b<63145 ∧ ArchiveStockRows.Chronology (start j1+15*b) x p (rows b) ∧
      Kept (ArchiveStockRows.bankPorts j1 jn exitPorts b) d (rows b) a:=by
    have h:j1.val+b≤jn.val:=by omega
    simp only [rows,dif_pos h]
    exact (res.bank b h).choose_spec
  have cmp:=StockBaselineW.comparison n hn le d x good s a m stage res
  exact ⟨rows,⟨⟨normalized.1.trans cmp.1.symm,fun q off=>(normalized.2 q off).trans (cmp.2 q off).symm⟩,
    fun b hb=>⟨(facts b hb).1,(facts b hb).2.1⟩,fun b hb=>(facts b hb).2.2,
    fun b hb=>stored j1 jn exitPorts exitCells n hn le d x good s m stage b hb (rows b) (facts b hb).1 (facts b hb).2.1⟩⟩

theorem Paired.through {j1 jn exitPorts n d x a s rows}
    (exitCells:∀j:Fin 16,exitPorts ⟨j.val,by omega⟩=(Partial.cellsRestoreP (start jn+15)).getD j 0)
    (hn:jn.val+1=j1.val+n) (le:start j1+15*n≤511)
    (pair:Paired j1 jn exitPorts n d x a s rows) (P:Program)
    (off:∀q∈archives (start j1) n,q∉wires P) (m:List Bool):Paired j1 jn exitPorts n d x (run P m a) (run P m s) rows:=by
  have h:=ArchiveStockSuffixW.independent (start j1) n P off m a s pair.equality
  have mem (b:Nat) (hb:b<n) (j:Fin 16):siteAt j1 jn exitPorts b j∈archives (start j1) n:=by
    rw [site_eq j1 jn exitPorts exitCells b (by omega) j]; exact bank_mem _ n b hb j
  refine ⟨h.1,pair.labels,?_,?_⟩
  · intro b hb j
    exact (h.2 (siteAt j1 jn exitPorts b j) (mem b hb j)).trans (pair.custom b hb j)
  · intro b hb j
    exact (run_preserves_outside P m s (siteAt j1 jn exitPorts b j) (off _ (mem b hb j))).trans (pair.stock b hb j)
end ECDSAAdd.Entrant.StairPacket.StockArchiveBanksW

end
-- END par-d2 StockTailW

-- BEGIN build-w4b StockRowVectorW (B2-a)
-- Main (w4r): after par-d2's StockTailW section (StockArchiveBanksW) and after dadon's StockRowVector (uses its
-- `historical`, generic already).
section

namespace ECDSAAdd.Entrant.StairPacket.StockRowVectorW
open Arithmetic MappedCompressed Secp256k1 StockCanonicalRow StockStrongChain StockArchiveBanksW
open StairArchiveRaw WideReference ArchivePortAction Partial
set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-- dadon's `cross{s}`, for every block: the bank-high crossing bit of the leave's true middle. -/
def crossW (j : Fin 23) (z : SkywalkNat.State) : Bool := HighBankSum.cross (LeaveJ.TrueMiddle.d j z)
/-- dadon's `StockRowVector.keys`, for the window of blocks `j1, j1+1, …`: bank `b` is block `j1+b`'s archive key. -/
noncomputable def keys (j1 : Fin 23) (x p b : Nat) : Nat → Bool :=
  if h : j1.val + b < 23 then value x p (start j1 + 15*b) (sbP (start j1 + 15*b)) (crossW ⟨j1.val+b, h⟩)
  else fun _ => false
/-- dadon's `StockRowVector.rows`: a function of `(x, p)` only (the pairing across runs needs that). -/
noncomputable def rows (j1 : Fin 23) (x p : Nat) (b : Nat) : Nat := select (keys j1 x p b)

/-- dadon's `StockStrongChain.final`, generic: every bank holds its key-selected row. -/
def final (j1 jn : Fin 23) (exitPorts : Ports) (d : Bool) (x p : Nat) (s : State) : Prop :=
  ∀ b, j1.val + b ≤ jn.val → SavedKey (keys j1 x p b) (ArchiveStockRows.bankPorts j1 jn exitPorts b) d s

theorem trace {j1 jn exitPorts d x p s} (h : final j1 jn exitPorts d x p s) (b : Nat) (hb : j1.val + b ≤ jn.val) :
    ArchiveStockRows.Chronology (start j1 + 15*b) x p (rows j1 x p b) := by
  have k := (h b hb).2.1
  have lt : j1.val + b < 23 := by have := jn.isLt; omega
  simp only [rows, keys, dif_pos lt] at k ⊢
  exact StockRowVector.historical _ _ x p _ _ k

/-- dadon's `StockRowVector.binding`, generic over the window's banks. -/
theorem binding (j1 jn : Fin 23) (exitPorts : Ports)
    (exitCells : ∀ j : Fin 16, exitPorts ⟨j.val, by omega⟩ = (Partial.cellsRestoreP (start jn+15)).getD j 0)
    (n : Nat) (hn : jn.val+1 = j1.val+n) (le : start j1+15*n ≤ 511) (d : Bool) (x : Nat) (good : Bounds x p)
    (raw a : State) (m : List Bool) (stage : Rolling1588.Integer.Stage base d x p (start j1) raw.basis)
    (stored : final j1 jn exitPorts d x p a)
    (same : ArchiveStockSuffixW.Same (start j1) n a
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) raw))) :
    Paired j1 jn exitPorts n d x a
      (run (Rolling1588TickGap.forward d (start j1) (15*n+1)) m (pullState (OB5.sig (start j1-1)) raw)) (rows j1 x p) := by
  refine ⟨same, fun b hb => ⟨(stored b (by omega)).1, trace stored b (by omega)⟩, fun b hb => (stored b (by omega)).2.2,
    fun b hb => ?_⟩
  exact StockArchiveBanksW.stored j1 jn exitPorts exitCells n hn le d x good raw m stage b hb _ (stored b (by omega)).1
    (trace stored b (by omega))

end ECDSAAdd.Entrant.StairPacket.StockRowVectorW

end
-- END build-w4b StockRowVectorW
-- ==== w4: end stocktail ====

-- ==== build-main2: generic OrdinaryChain (build-leaves OrdW) ====
/-! build-ordinary (build-leaves): the generic `OrdinaryChain` Ref half for the window 120..255 (exit 270).
Replaces dadon's literal `OrdinaryChain` (`Ref240/255/270`, `begin225`, `next240/255`, `last270`, `terminal`, `finish`,
`project`, `readOld`, `keepTick`, `keepEncode`, `holes240/255`, `carry255`, `seven`, `wires`) by one induction over
the fold's blocks. Every proof here is O(1) in the number of blocks: no decide over the window's growing lists. -/

-- ===== Part 1: generic list facts and the finish (any window `s1`, `n` blocks, exit `s1+15n`) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed WideReference ArchiveHistoryCompare
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

theorem plain_succ (n : Nat) : StockWindowGeo.plain (n+1)=StockWindowGeo.plain n++[1+3*n] := by
  simp only [StockWindowGeo.plain,List.range_succ,List.map_append,List.map_cons,List.map_nil,List.cons_append]

theorem packed_succ (n : Nat) : StockWindowGeo.packed (n+1)=StockWindowGeo.packed n++[2+3*n,3+3*n] := by
  simp only [StockWindowGeo.packed,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil]

theorem holes_succ (s1 n : Nat) : StockWindowGeo.holes s1 (n+1)=StockWindowGeo.holes s1 n++
    [base (1028+StockWindowGeo.gstart s1 (2+3*n)+2),base (1028+StockWindowGeo.gstart s1 (2+3*n)+4),
     base (1028+StockWindowGeo.gstart s1 (3+3*n)+2),base (1028+StockWindowGeo.gstart s1 (3+3*n)+4)] := by
  simp only [StockWindowGeo.holes,packed_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.cons_append,List.nil_append]

theorem batch_append (s1 : Nat) (d : Bool) (a b : List Nat) :
    StockGroupsW.batch s1 d (a++b)=StockGroupsW.batch s1 d a++StockGroupsW.batch s1 d b := by
  simp only [StockGroupsW.batch,List.flatMap_append]

/-- The window's ordinary program after `n+1` blocks is the reference's batch of the `plain` groups. -/
theorem progW_plain (s1 : Nat) (lo : 5≤s1) (d : Bool) :
    ∀n,OrdinaryChainW.progW s1 d (n+1)=StockGroupsW.batch s1 d (StockWindowGeo.plain n)
  | 0=>by
    show []++Rolling1588.encodeAt base d (OrdinaryChainW.group s1 0)=_
    simp only [OrdinaryChainW.group,↓reduceIte,List.nil_append,StockWindowGeo.plain,List.range_zero,List.map_nil,
      StockGroupsW.batch,List.flatMap_cons,List.flatMap_nil,List.append_nil,StockGroupsW.one,StockWindowGeo.gstart,
      Nat.mul_zero,Nat.add_zero]
  | n+1=>by
    have e:OrdinaryChainW.progW s1 d (n+1+1)=OrdinaryChainW.progW s1 d (n+1)++
      Rolling1588.encodeAt base d (OrdinaryChainW.group s1 (n+1)):=rfl
    rw [e,progW_plain s1 lo d n,plain_succ,batch_append]
    congr 1
    simp only [StockGroupsW.batch,List.flatMap_cons,List.flatMap_nil,List.append_nil,StockGroupsW.one,
      OrdinaryChainW.group,if_neg (show n+1≠0 by omega),StockWindowGeo.gstart]
    congr 1; omega

theorem progW_last (s1 n : Nat) (lo : 5≤s1) (hn : 1≤n) (d : Bool) :
    OrdinaryChainW.progW s1 d n++Rolling1588.encodeAt base d (s1+15*n-15)=
      StockGroupsW.batch s1 d (StockWindowGeo.plain n) := by
  rw [←progW_plain s1 lo d n]
  show _=OrdinaryChainW.progW s1 d n++Rolling1588.encodeAt base d (OrdinaryChainW.group s1 n)
  rw [OrdinaryChainW.group,if_neg (by omega)]

/-- Every hole is a B-side history cell of a tick inside the window (after its first five ticks). -/
theorem hole_cell (s1 n : Nat) (lo : 5≤s1) :
    ∀w∈StockWindowGeo.holes s1 n,∃r:Nat,s1+7≤r ∧ r+1≤s1+15*n ∧ w=base (1028+r) := by
  intro w hw
  simp only [StockWindowGeo.holes,StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false] at hw
  obtain ⟨i,⟨b,hb,hi⟩,e⟩:=hw
  simp only [StockWindowGeo.gstart] at e
  rcases hi with rfl|rfl <;> rcases e with rfl|rfl
  · exact ⟨s1-5+5*(2+3*b)+2,by omega,by omega,by congr 1⟩
  · exact ⟨s1-5+5*(2+3*b)+4,by omega,by omega,by congr 1⟩
  · exact ⟨s1-5+5*(3+3*b)+2,by omega,by omega,by congr 1⟩
  · exact ⟨s1-5+5*(3+3*b)+4,by omega,by omega,by congr 1⟩

/-- Letter `a` of bank `b`'s ten ticks is a letter of one of its two archived groups. -/
theorem cell_letter (s1 b a : Nat) (lo : 5≤s1) (ha : a<10) :
    base (s1+15*b+5+a)=StockWindowGeo.slot s1 (2+3*b+a/5) ⟨2*(a%5),by omega⟩ ∧
    base (1028+(s1+15*b+5+a))=StockWindowGeo.slot s1 (2+3*b+a/5) ⟨2*(a%5)+1,by omega⟩ := by
  simp only [StockWindowGeo.slot,History5.historyMap,History5.historyId,StockWindowGeo.gstart,Fin.val_mk]
  constructor
  · rw [if_pos (by omega)]; congr 1; omega
  · rw [if_neg (by omega)]; congr 1; omega

/-- `StockGroups.sparse` read on bank `b`'s ten ticks: each cell is a hole or, in the exit frame, an archive cell. -/
theorem cells_census (s1 n b : Nat) (lo : 5≤s1) (hb : b<n) (le : s1+15*n≤511) :
    ∀w∈OrdinaryChainW.cells10 (s1+15*b+5),
      w∈StockWindowGeo.holes s1 n ∨ OB5.sig (s1+15*n) w∈StockWindowGeo.archives s1 n := by
  intro w hw
  simp only [OrdinaryChainW.cells10,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
    or_false] at hw
  obtain ⟨r,⟨r1,r2⟩,e⟩:=hw
  have hi:2+3*b+(r-(s1+15*b+5))/5∈StockWindowGeo.packed n:=by
    simp only [StockWindowGeo.packed,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨b,hb,by omega⟩
  have hr:s1+15*b+5+(r-(s1+15*b+5))=r:=by omega
  have cl:=cell_letter s1 b (r-(s1+15*b+5)) lo (by omega)
  rw [hr] at cl
  have sp:=StockWindowGeo.sparse s1 n (s1+15*n) lo rfl le _ hi
  rcases e with rfl|rfl
  · rw [cl.1]
    rcases sp ⟨2*((r-(s1+15*b+5))%5),by omega⟩ with ⟨_,h⟩|h
    · exact Or.inl h
    · exact Or.inr h
  · rw [cl.2]
    rcases sp ⟨2*((r-(s1+15*b+5))%5)+1,by omega⟩ with ⟨_,h⟩|h
    · exact Or.inl h
    · exact Or.inr h

theorem mask_mem (s1 : Nat) : ∀k,∀w∈OrdinaryChainW.mask s1 k,∃b,b+1<k ∧ w∈OrdinaryChainW.cells10 (s1+15*b+5)
  | 0,w,h=>by simp [OrdinaryChainW.mask] at h
  | k+1,w,h=>by
    have e:OrdinaryChainW.mask s1 (k+1)=OrdinaryChainW.mask s1 k++OrdinaryChainW.newBank s1 (s1+15*k):=rfl
    rw [e,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨b,hb,m⟩:=mask_mem s1 k w h
      exact ⟨b,by omega,m⟩
    · unfold OrdinaryChainW.newBank at h
      split at h
      · simp at h
      · rename_i hne
        refine ⟨k-1,by omega,?_⟩
        have e2:s1+15*k-10=s1+15*(k-1)+5:=by omega
        rw [←e2]; exact h

/-- dadon's `census` (`finish`), generic: the masked cells are holes or archive cells in the exit frame. -/
theorem census (s1 n : Nat) (lo : 5≤s1) (hn : 1≤n) (le : s1+15*n≤511) :
    ∀w∈OrdinaryChainW.mask s1 n++OrdinaryChainW.cells10 (s1+15*n-10),
      w∈StockWindowGeo.holes s1 n ∨ OB5.sig (s1+15*n) w∈StockWindowGeo.archives s1 n := by
  intro w hw
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨b,hb,m⟩:=mask_mem s1 n w h
    exact cells_census s1 n b lo (by omega) le w m
  · have e:s1+15*n-10=s1+15*(n-1)+5:=by omega
    rw [e] at h
    exact cells_census s1 n (n-1) lo (by omega) le w h

/-- dadon's `OrdinaryChain.finish`, generic: the stock-masked exit state plus clear holes is the reference off the
archive cells. -/
theorem finishW (s1 n : Nat) (lo : 5≤s1) (hn : 1≤n) (le : s1+15*n≤511) (d:Bool) (out initial:State)
    (all:Except (OrdinaryChainW.mask s1 n++OrdinaryChainW.cells10 (s1+15*n-10)) (pullState (OB5.sig (s1+15*n)) out)
      (run (OrdinaryChainW.progW s1 d n++Rolling1588.encodeAt base d (s1+15*n-15)) [] (run (span s1 (15*n+1)) [] initial)))
    (zero:∀w∈StockWindowGeo.holes s1 n,out.basis (OB5.sig (s1+15*n) w)=false) :
    ∀q∉StockWindowGeo.archives s1 n,out.basis q=(StockArchiveReferenceW.common s1 n d initial).basis q := by
  intro q away
  have inv:OB5.sig (s1+15*n) (OB5.sig (s1+15*n) q)=q:=OB5.sig_invol (s1+15*n) le q
  generalize ey:OB5.sig (s1+15*n) q=y at inv
  have goal:(StockArchiveReferenceW.common s1 n d initial).basis q=(eraseSites (StockWindowGeo.holes s1 n)
      (run (StockArchiveReferenceW.ordinary s1 n d) [] (run (span s1 (15*n+1)) [] initial))).basis y:=by
    rw [←ey]; rfl
  rw [goal]
  by_cases hole:y∈StockWindowGeo.holes s1 n
  · simp only [eraseSites,if_pos hole]
    have z:=zero y hole
    rw [inv] at z
    exact z
  · have free:y∉OrdinaryChainW.mask s1 n++OrdinaryChainW.cells10 (s1+15*n-10):=by
      intro hit
      rcases census s1 n lo hn le y hit with h|h
      · exact hole h
      · rw [inv] at h; exact away h
    have value:=all y free
    change out.basis (OB5.sig (s1+15*n) y)=_ at value
    rw [inv,progW_last s1 n lo hn d] at value
    simpa only [eraseSites,if_neg hole,StockArchiveReferenceW.ordinary] using value

/-- `OB5.sig i` fixes the B-side history cell of every tick `r ≤ 256`. -/
theorem sig_fixed (i r : Nat) (hi : i≤511) (hr : r≤256) : OB5.sig i (base (1028+r))=base (1028+r) := by
  rw [OB5.sig_nat]
  unfold OB5.sigNat
  simp only [base,Wire]
  split_ifs <;> omega

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 2: the exit at 270 (dadon's `terminal`, without `At270`'s saved keys) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic IntegerPacket MappedCompressed Secp256k1 WideReference SkywalkRails NativePack270 Partial ParkEndpoint StockWindowTicket
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

/-- `Ordinary270Native.result` with the exit frame as a hypothesis (dadon took it from `step270`, which needs
`At270.saved225/240`; the generic hand-off `AtJ 13` has no saved keys). Proof otherwise dadon's. -/
theorem resultW (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg:Bool) (m:List Bool)
    (domain:Domain 270 x p raw) (input:InputAt 270 (signedAt 270 x p g sg) raw)
    (cut:PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (flagNeg 270 x p sg)
      (decide (farAt 121 270 x p)) (decide (farAt 121 270 x p ∧ 2^121≤(unsigned 270 x p).u))
      (pullState (OB5.sig 269) raw) (eraseSites ParkEndpoint.src s))
    (last:StockWindowW.LastW d x p (run (lastWindow d) m s)) :
    ArchiveHistoryCompare.Except Ordinary270Terminal.newBank (run (lastWindow d) m s)
      (pullState (OB5.sig 270) (run (Rolling1588.encodeAt base d 255) [] (run EndTick.canonical [] raw))) := by
  obtain ⟨ref,stage,read,hist,spare,spaces⟩:=terminal d x raw domain
  let z:=unsigned 270 x p
  let v:=run EndTick.canonical [] raw
  let p1:=m.drop (measurementCount park270)
  let p2:=p1.drop (measurementCount portal270Inv)
  let p3:=p2.drop (measurementCount EndTick.physP)
  let p4:=p3.drop (measurementCount (program d))
  have lim:min z.u z.v<2^121:=true_small x p 270 (lt_trans good.small good.cap) good.cap (by decide)
  have mode:farAt 121 270 x p=(3*2^137≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have first:=parked_release z lim raw s m p1 g sg (readInput 270 x p raw g sg input)
    (by simpa only [mode] using cut) (empty_from_cut _ _ _ _ _ cut spaces)
  have tick:=EndTick.physical d x good.nonzero good.small raw ref s read stage hist spare p2
  let loaded:=run (archiveLoad270 d) p4 (run (program d) p3 (stash s (pullState (OB5.sig 270) v)))
  have actual:run (lastWindow d) m s=loaded := by
    simp only [lastWindow,endSlice,run_append,run_take]
    change run (archiveLoad270 d) p4 (run (program d) p3 (run EndTick.physP p2 (run portal270Inv p1 (run park270 m s))))=_
    rw [first.1,tick.1]
  obtain ⟨row,_,_,frame⟩:=last
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

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 3: the window's reference hand-off `RefW` and the exit block (dadon's `Ref270`, `last270`) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 ArchiveHistoryCompare StockWindowW
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount

/-- dadon's `Ref240/255/270` for any block `j` of the window from 120: the block's stock hand-off (build-chain's
`AtJ`), the logical state agrees with the stock run of `j-3` blocks off the archived cells (par-d2's `mask`/`progW`),
and the holes of the banks of blocks `3..j-2` (cleared by blocks `4..j-1`) are zero. -/
def RefW (j : Fin 23) (d:Bool) (x:Nat) (initial s:State) : Prop :=
  ∃raw g sg pg ps,AtJ j d x p raw s g sg pg ps ∧
    Except (OrdinaryChainW.mask 120 (j.val-3)) raw
      (run (OrdinaryChainW.progW 120 d (j.val-3)) [] (run (span 120 (15*(j.val-3))) [] initial)) ∧
    ∀q∈StockWindowGeo.holes 120 (j.val-4),raw.basis q=false

/-- The generic hand-off at block 13 is dadon's literal exit cut (`At270.cut`). -/
theorem exitCut (L8:ExitBridgeSpec) (d:Bool) (x:Nat) (raw s:State) (g sg pg ps:Bool)
    (pre:AtJ ⟨13,by decide⟩ d x p raw s g sg pg ps) :
    PackedCut Portal270Flag.loPairs Portal270Flag.hiPairs 285 1700 1698 1699 (flagNeg 270 x p sg)
      (decide (farAt 121 270 x p)) (decide (farAt 121 270 x p ∧ 2^121≤(unsigned 270 x p).u))
      (pullState (OB5.sig 269) raw) (eraseSites ParkEndpoint.src s) := by
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,-,-,-⟩:=L8
  have cut:=pre.cut
  rw [bl,bu,bg,bn,bf,bu',bp] at cut
  have e13:start (⟨13,by decide⟩:Fin 23)=270:=rfl
  have sb:sbP 270=121:=by decide
  have pl:EnterJ.pull ⟨13,by decide⟩=OB5.sig 269:=rfl
  simp only [e13,sb,pl] at cut
  exact cut

/-- The exit frame from the generic hand-off (build-chain's `exitStep`, its `LastW` part). -/
theorem exitLast (L8:ExitBridgeSpec) (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool)
    (pre:AtJ ⟨13,by decide⟩ d x p raw s g sg pg ps) (m:List Bool) :
    LastW d x p (run (NativePack270.lastWindow d) m s) := by
  have cut:=exitCut L8 d x raw s g sg pg ps pre
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,r20,r21,r22⟩:=L8
  let z:=unsigned 270 x p
  have short:min z.u z.v<2^121:=true_small x p 270 (lt_trans good.small good.cap) good.cap (by decide)
  have old:=LeaveJ.Admission.actualNumbers ⟨12,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 121 270 x p=(3*2^137≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have facts:=pre.facts
  have mode:s.basis 1701=decide (Shadow.far 129 15 (unsigned 255 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1702=(decide (Shadow.far 129 15 (unsigned 255 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 255 x p).v<(unsigned 255 x p).u))
        ((physicalCells ArchiveBoundary270.sourceIdx s).take 5)):=by rw [←r21]; exact facts.suffix
  have cross:s.basis 1703=(decide (Shadow.far 129 15 (unsigned 255 x p)) &&
      HighBankSum.cross (LeaveJ.TrueMiddle.d ⟨12,by decide⟩ (unsigned 255 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack270.matched_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 270 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 255 x p) pg ps _
    old.odd old.small facts.records mode side cross
  obtain ⟨r,lim,truth,frame⟩:=last.2.1
  have pc:signedAt 255 x p pg ps=WideReference.canonical 255 x p:=pre.pastCanonical
  have chr:Chronology 255 x p r:=by unfold Chronology;rw [←pc];exact truth
  exact ⟨r,lim,chr,frame⟩

/-- dadon's `OrdinaryChain.project` (exit unchanged at 270; `lastBank = cells10 260`). -/
theorem projectW (d:Bool) (raw out:State)
    (direct:Except Ordinary270Terminal.newBank out
      (pullState (OB5.sig 270) (run (Rolling1588.encodeAt base d 255) [] (run EndTick.canonical [] raw)))) :
    Except (OrdinaryChainW.cells10 260) (pullState (OB5.sig 270) out)
      (run (Rolling1588.encodeAt base d 255) [] (run (span 270 1) [] raw)) := by
  have one:span 270 1=EndTick.canonical:=by simp [span,EndTick.canonical]
  rw [one]
  intro q absent
  have map:∀w∈Ordinary270Terminal.newBank,OB5.sig 270 w∈OrdinaryChainW.cells10 260:=by decide +kernel
  have free:OB5.sig 270 q∉Ordinary270Terminal.newBank:=fun hit=>absent (by simpa only [OB5.sig_invol 270 (by decide)] using map _ hit)
  simpa only [pullState,OB5.sig_invol 270 (by decide)] using direct _ free

/-- dadon's `readOld`/`keepTick`/`keepEncode` for one older hole (a B-side cell of a tick `r ≤ 254`). -/
theorem old_hole_270 (d:Bool) (raw out:State) (r:Nat) (r1:120≤r) (r2:r≤254)
    (direct:Except Ordinary270Terminal.newBank out
      (pullState (OB5.sig 270) (run (Rolling1588.encodeAt base d 255) [] (run EndTick.canonical [] raw))))
    (clear:raw.basis (base (1028+r))=false) :
    out.basis (base (1028+r))=false := by
  have notNew:base (1028+r)∉Ordinary270Terminal.newBank:=by
    intro hit
    simp only [Ordinary270Terminal.newBank,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
      or_false] at hit
    obtain ⟨r',⟨a,b⟩,e|e⟩:=hit <;> simp only [OB5.sig,base,Wire] at e <;> split_ifs at e <;> omega
  have eq:=direct _ notNew
  change out.basis _=(run (Rolling1588.encodeAt base d 255) [] (run EndTick.canonical [] raw)).basis
    (OB5.sig 270 (base (1028+r))) at eq
  rw [sig_fixed 270 r (by decide) (by omega)] at eq
  have enc:base (1028+r)∉wires (Rolling1588.encodeAt base d 255):=by
    intro used
    obtain ⟨r',a,b,e|e⟩:=OrdinaryChainW.encode_cells d 255 _ used <;> simp only [base,Wire] at e <;> omega
  have one:span 270 1=EndTick.canonical:=by simp [span,EndTick.canonical]
  have tick:base (1028+r)∉wires EndTick.canonical:=by
    rw [←one]; exact pastOffSpan 270 1 _ (by decide) ⟨r,by omega,Or.inr rfl⟩
  rw [eq,run_preserves_outside _ _ _ _ enc,run_preserves_outside _ _ _ _ tick]
  exact clear

/-- dadon's `last270`/`terminal`, generic: from the hand-off at block 13 the exit pieces reach the reference. -/
theorem lastW (L7:ExitProgSpec) (L8:ExitBridgeSpec) (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State)
    (m:List Bool) (h:RefW ⟨13,by decide⟩ d x initial s) :
    ∀q∉StockWindowGeo.archives 120 10,(run (exitF WindowParams.params d 270).flatten m s).basis q=
      (StockArchiveReferenceW.common 120 10 d initial).basis q := by
  rw [(L7 d).1]
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  have lastF:=exitLast L8 d x good raw s g sg pg ps pre m
  have direct:=resultW d x good raw s g sg m pre.domain pre.input (exitCut L8 d x raw s g sg pg ps pre) lastF
  have all:=OrdinaryChainW.add_last 120 (by decide) 10 (by decide) (by decide) d raw initial _ old
    (projectW d raw _ direct)
  apply finishW 120 10 (by decide) (by decide) (by decide) d _ initial all
  obtain ⟨row,_,_,frame⟩:=lastF
  have cleared:=NativePack270.cleared_holes d row _ frame
  intro w hw
  have hs:StockWindowGeo.holes 120 10=_:=holes_succ 120 9
  rw [hs] at hw
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨r,r1,r2,rfl⟩:=hole_cell 120 9 (by decide) w h
    rw [sig_fixed (120+15*10) r (by decide) (by omega)]
    exact old_hole_270 d raw _ r (by omega) (by omega) direct (zeros _ h)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> exact cleared _ (by decide)

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 4: interior blocks 4..12 (dadon's `next240/255`), first block (`begin225`), the fold, `wiresW` =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 ArchiveHistoryCompare StockWindowW
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount body

/-- L11 (new, first form at 120; dadon's `StockWindowTicket.ordinary225`): the first block's logical end state is
the stock run of its 15 ticks with the five pre-window letters (group 115) encoded. -/
abbrev FirstOrdinarySpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis),
    Except [] (endRaw 120 raw (run (portalP 120 ++ NativeFirstJ.enteredWindow WindowParams.first d) m
        (pullState (OB5.sig 119) raw)))
      (run (Rolling1588.encodeAt base d 115) [] (run (span 120 15) [] raw))

/-- The open leaves `wiresW` uses: five of build-chain's (Skel.lean statements) and the first block's ordinary. -/
structure OrdLeaves : Prop where
  endpoint : EndpointSpec
  scratch : ScratchSpec
  first : FirstSpec
  exitProg : ExitProgSpec
  exitBridge : ExitBridgeSpec
  firstOrdinary : FirstOrdinarySpec

def OrdLeaves.of (L : Leaves) (F : FirstOrdinarySpec) : OrdLeaves :=
  ⟨L.endpoint,L.scratch,L.first,L.exitProg,L.exitBridge,F⟩

theorem not_first (k : Fin 23) (h4 : 4≤k.val) : start k≠firstBlock := by
  simp only [StairPacket.start,firstBlock]; omega

/-- `OB5.sig i` is the identity below the moved band. -/
theorem sig_id_low (i q : Nat) (hi : i≤511) (hq : q<1301) (hq2 : q+i<2069) : OB5.sig i q=q := by
  rw [OB5.sig_nat]; unfold OB5.sigNat
  split_ifs with h
  · rcases h with ⟨h1,h2⟩|⟨h1,h2⟩ <;> omega
  · rfl

/-- dadon's `pinned{s}` for block `k`: the next block's hand-off (build-chain's `interior`, its `AtJ` part). -/
theorem pinnedW (L1:EndpointSpec) (L2:ScratchSpec) (k k1:Fin 23) (hk:k1.val=k.val+1) (h4:4≤k.val) (h12:k.val≤12)
    (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool)
    (pre:AtJ k d x p raw s g sg pg ps) :
    ∃a b c e,AtJ k1 d x p (endRaw (start k) raw (run (NativeJ.nextWindow k d) m s))
      (run (leaveP k) (m.drop (measurementCount (NativeJ.nextWindow k d))) (run (NativeJ.nextWindow k d) m s)) a b c e := by
  let v:=run (NativeJ.nextWindow k d) m s
  let n:=m.drop (measurementCount (NativeJ.nextWindow k d))
  have p1:NativeJ.prev k1=k:=prev_of k k1 hk
  have s1:start k1=start k+15:=start_succ k k1 hk
  let flags:=LeaveJ.Admission.flags (unsigned (start k) x p) g sg
  have h2 : 2≤k.val := by omega
  have h19 : k.val≤19 := by omega
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k h2 h19 d x p good raw s g sg pg ps m pre
  have native:=NativeJ.from_domain_matched k h2 h19 d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨cut,facts⟩:=L1 k k1 hk h4 h12 d x p good raw s m n pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  have hin:=native.1
  have carried:=stepInput_gen (start k) (sbP (start k)) x p (by simp only [StairPacket.start]; omega)
    (by simp only [StairPacket.start]; omega) good raw v g sg pre.domain pre.input hin.small
  have canon:=unique_input pre.input (fixed_input _ _ _ (by simp only [StairPacket.start]; omega) good raw pre.domain)
  refine ⟨flags.1,flags.2,g,sg,⟨?_,?_,cut,?_,?_⟩⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [p1]; exact facts
  · rw [p1]; exact canon

/-- dadon's `ordinary{s}` for block `k` (par-c2's `OrdinaryJ.native` on the hand-off). -/
theorem ordinaryW (k:Fin 23) (h4:4≤k.val) (h12:k.val≤12) (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State)
    (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) :
    Except (OrdinaryJ.newBank k) (endRaw (start k) raw (run (NativeJ.nextWindow k d) m s))
      (run (Rolling1588.encodeAt base d (start k-15)) [] (run (span (start k) 15) [] raw)) := by
  let z:=unsigned (start k) x p
  let T:=Shadow.reduced (sbP (start k)) 15 z
  have nums:=LeaveJ.Admission.actualNumbers k (by omega) (by omega) x p good
  have hist:=pulled_history k rfl pre.domain
  have inp:=readInput (start k) x p raw g sg pre.input
  have ready:=EnterJ.ready_pending_at k raw s z g sg m nums.small pre.cut inp hist
  have odd:T.v%2=1:=shadow_odd (sbP (start k)) z nums.small nums.odd
  have parity:((encode g sg T.u T.v).a+(encode g sg T.u T.v).b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have hne:=not_first k h4
  have h:=OrdinaryJ.native k (by omega) (by omega) ⟨oldStart_interior hne,oldCount_interior hne⟩ d x p good raw s
    pre.domain m (m.drop (measurementCount (Partial.enterP k))) _ _ _ pre.cut _ parity ready.2.1
  simpa only [NativeJ.nextWindow,NativeJ.window,run_append,run_take] using h

theorem hole_in_four (k : Fin 23) (h1 : 1≤k.val) (h12 : k.val≤12) (r : Nat)
    (hr : r=start k-8 ∨ r=start k-6 ∨ r=start k-3 ∨ r=start k-1) :
    base (1028+r)∈NativeJ.fourHoles k := by
  rw [NativeJ.fourHoles_eq k h1]
  have s0 : 90≤start k ∧ start k≤255 := by simp only [StairPacket.start]; omega
  rw [sig_id_low (start k) (start k+1036) (by omega) (by omega) (by omega),
    sig_id_low (start k) (start k+1038) (by omega) (by omega) (by omega),
    sig_id_low (start k) (start k+1041) (by omega) (by omega) (by omega),
    sig_id_low (start k) (start k+1043) (by omega) (by omega) (by omega)]
  simp only [List.mem_cons,List.not_mem_nil,or_false,base,Wire]
  rcases hr with rfl|rfl|rfl|rfl <;> omega

/-- dadon's `holes{s}` for block `k`: the four holes of bank `k-4` (ticks `start k-10 .. start k-1`) are zero in the
next block's logical state (build-w4b's `NativeJ.cleared_holes`). -/
theorem holesW (L2:ScratchSpec) (k:Fin 23) (h4:4≤k.val) (h12:k.val≤12) (d:Bool) (x:Nat) (good:Bounds x p)
    (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) (r:Nat)
    (hr : r=start k-8 ∨ r=start k-6 ∨ r=start k-3 ∨ r=start k-1) :
    (endRaw (start k) raw (run (NativeJ.nextWindow k d) m s)).basis (base (1028+r))=false := by
  let z:=unsigned (start k) x p
  have nums:=LeaveJ.Admission.actualNumbers k (by omega) (by omega) x p good
  have old:=LeaveJ.Admission.actualNumbers (NativeJ.prev k) (by simp only [NativeJ.prev]; omega)
    (by simp only [NativeJ.prev]; omega) x p good
  have hist:=pulled_history k rfl pre.domain
  have inp:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k (by omega) (by omega) d x p good raw s g sg pg ps m pre
  have clear:=NativeJ.cleared_holes k (by omega) (by omega) d raw s m z g sg nums.odd nums.small pre.cut inp hist scr
    _ pg ps _ old.odd old.small pre.facts
  have hne:=not_first k h4
  have s0 : 135≤start k ∧ start k≤255 := by simp only [StairPacket.start]; omega
  have bound:start k+14≤511:=by omega
  have r0 : start k-8≤r ∧ r≤start k-1 := by rcases hr with rfl|rfl|rfl|rfl <;> omega
  have mem:base (1028+r)∈oldSites (start k):=by
    simp only [oldSites,oldStart_interior hne,oldCount_interior hne,List.mem_flatMap,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨r,⟨by omega,by omega⟩,Or.inr rfl⟩
  rw [endRaw_inside_gen _ bound _ _ _ mem,sig_fixed (start k+14) r (by omega) (by omega)]
  exact clear _ (hole_in_four k (by omega) h12 r hr)

/-- dadon's `next240/next255` for any interior block `k` (4..12). -/
theorem nextW (L1:EndpointSpec) (L2:ScratchSpec) (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State) (k k1:Fin 23)
    (hk:k1.val=k.val+1) (h4:4≤k.val) (h12:k.val≤12) (m:List Bool) (h:RefW k d x initial s) :
    RefW k1 d x initial (run (NativeJ.nextWindow k d++leaveP k) m s) := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  rw [run_append,run_take]
  obtain ⟨a,b,c,e,pre'⟩:=pinnedW L1 L2 k k1 hk h4 h12 d x good raw s g sg pg ps m pre
  have hne:=not_first k h4
  have s0 : 135≤start k ∧ start k≤255 := by simp only [StairPacket.start]; omega
  have sk:start k=120+15*(k.val-3):=by simp only [StairPacket.start]; omega
  refine ⟨_,a,b,c,e,pre',?_,?_⟩
  · have step:=ordinaryW k h4 h12 d x good raw s g sg pg ps m pre
    have step':Except (OrdinaryChainW.newBank 120 (120+15*(k.val-3))) (endRaw (start k) raw (run (NativeJ.nextWindow k d) m s))
        (run (Rolling1588.encodeAt base d (OrdinaryChainW.group 120 (k.val-3))) []
          (run (span (120+15*(k.val-3)) 15) [] raw)):=by
      rw [←sk,OrdinaryChainW.newBank,if_neg (by omega),OrdinaryChainW.group,if_neg (by omega),
        show 120+15*(k.val-3)-15=start k-15 by omega]
      exact step
    have e1:k1.val-3=(k.val-3)+1:=by omega
    rw [e1]
    exact OrdinaryChainW.add 120 (by decide) (k.val-3) (by omega) (by omega) d raw initial _ old step'
  · have e1:k1.val-4=(k.val-4)+1:=by omega
    rw [e1,holes_succ]
    intro q hq
    rcases List.mem_append.mp hq with h|h
    · apply OrdinaryChainW.carry (start k) (by omega) (StockWindowGeo.holes 120 (k.val-4)) ?_ ?_ raw _ zeros q h
      · intro w hw hit
        obtain ⟨r,r1,r2,rfl⟩:=hole_cell 120 (k.val-4) (by decide) w hw
        obtain ⟨r',a1,a2,e'⟩:=old_cell hit
        rw [oldStart_interior hne] at a1 a2
        rw [oldCount_interior hne] at a2
        rcases e' with e'|e' <;> simp only [base,Wire] at e' <;> omega
      · intro w hw
        obtain ⟨r,r1,r2,rfl⟩:=hole_cell 120 (k.val-4) (by decide) w hw
        right; simp only [base,Wire]; omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      have g0:∀i,StockWindowGeo.gstart 120 i=115+5*i:=fun i=>by simp only [StockWindowGeo.gstart]
      rcases h with rfl|rfl|rfl|rfl
      · have := holesW L2 k h4 h12 d x good raw s g sg pg ps m pre (start k-8) (Or.inl rfl)
        rw [show 1028+StockWindowGeo.gstart 120 (2+3*(k.val-4))+2=1028+(start k-8) by rw [g0]; omega]; exact this
      · have := holesW L2 k h4 h12 d x good raw s g sg pg ps m pre (start k-6) (Or.inr (Or.inl rfl))
        rw [show 1028+StockWindowGeo.gstart 120 (2+3*(k.val-4))+4=1028+(start k-6) by rw [g0]; omega]; exact this
      · have := holesW L2 k h4 h12 d x good raw s g sg pg ps m pre (start k-3) (Or.inr (Or.inr (Or.inl rfl)))
        rw [show 1028+StockWindowGeo.gstart 120 (3+3*(k.val-4))+2=1028+(start k-3) by rw [g0]; omega]; exact this
      · have := holesW L2 k h4 h12 d x good raw s g sg pg ps m pre (start k-1) (Or.inr (Or.inr (Or.inr rfl)))
        rw [show 1028+StockWindowGeo.gstart 120 (3+3*(k.val-4))+4=1028+(start k-1) by rw [g0]; omega]; exact this

/-- dadon's `begin225` at 120: the first block (portal, enter, pack, leave) reaches the hand-off of block 4. -/
theorem beginW (L:OrdLeaves) (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) :
    RefW ⟨4,by decide⟩ d x raw (run ((portalP 120++NativeFirstJ.enteredWindow WindowParams.first d)++
      leaveP WindowParams.first) m (pullState (OB5.sig 119) raw)) := by
  rw [run_append,run_take]
  let v:=run (portalP 120++NativeFirstJ.enteredWindow WindowParams.first d) m (pullState (OB5.sig 119) raw)
  let n:=m.drop (measurementCount (portalP 120++NativeFirstJ.enteredWindow WindowParams.first d))
  obtain ⟨g,sg,input,hin,cut,facts⟩:=L.first d x p good raw m n stage
  let flags:=LeaveJ.Admission.flags (unsigned 120 x p) g sg
  have dom:=initial 120 x p (by decide) d raw stage
  have carried:=stepInput_gen 120 (sbP 120) x p (by decide) (by decide) good raw v g sg dom input hin.small
  refine ⟨endRaw 120 raw v,flags.1,flags.2,g,sg,⟨carried.1,carried.2,cut,facts,
    unique_input input (fixed_input 120 x p (by decide) good raw dom)⟩,?_,?_⟩
  · exact L.firstOrdinary d x p good raw m stage
  · intro q hq
    simp [StockWindowGeo.holes,StockWindowGeo.packed] at hq

theorem run_nil_eq (m:List Bool) (s:State) : run [] m s=s := by
  with_unfolding_all rfl

/-- The interior fold (`chainF`), by induction on the block list (`WindowChain.window_strong`'s recursion). -/
theorem chainW (L1:EndpointSpec) (L2:ScratchSpec) (d:Bool) (x:Nat) (good:Bounds x p) (initial:State) :
    ∀(i:Fin 23) (js:List (Fin 23)),Consec i js → (∀k∈js,4≤k.val ∧ k.val≤12) →
    ∀(j j':Fin 23),j.val=i.val+1 → j'.val=(lastBlock i js).val+1 → ∀s m,RefW j d x initial s →
      RefW j' d x initial (run (chainF WindowParams.params d i js).flatten m s)
  | i,[],_,_,j,j',hj,hj',s,m,h=>by
    have e:j'=j:=Fin.ext (by simp only [lastBlock] at hj'; omega)
    subst e
    rw [chainF,List.flatten_nil,run_nil_eq]
    exact h
  | i,k::js,⟨hk,rest⟩,hb,j,j',hj,hj',s,m,h=>by
    have e:j=k:=Fin.ext (by omega)
    subst e
    have bk:=hb j List.mem_cons_self
    rw [chainF,List.flatten_append,run_append,next_eq d i j hk]
    exact chainW L1 L2 d x good initial j js rest (fun k hk=>hb k (List.mem_cons_of_mem _ hk))
      ⟨j.val+1,by omega⟩ j' rfl (by simpa only [lastBlock] using hj') _ _
      (nextW L1 L2 d x good initial s j ⟨j.val+1,by omega⟩ rfl bk.1 bk.2 _ h)

theorem lastBlock_ship : lastBlock WindowParams.first WindowParams.rest=⟨12,by decide⟩ := by
  rw [rest_eq]; rfl

/-- The window program split into its first block, interior fold and exit. -/
theorem split (d:Bool) : Partial.forward45plus1 d=
    (((WindowParams.params.portal (start WindowParams.first) :: firstF WindowParams.params d WindowParams.first).flatten++
      (chainF WindowParams.params d WindowParams.first WindowParams.rest).flatten)++
      (exitF WindowParams.params d 270).flatten) := by
  rw [Partial.assembly,forwardW,forwardL,exitTick_ship]
  simp only [List.flatten_cons,List.flatten_append,List.append_assoc]

/-- `OrdinaryChain.wires` for the window 120..255 (exit 270), generic over the fold. -/
theorem wiresW (L:OrdLeaves) (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) :
    ∀q∉StockWindowGeo.archives 120 10,(run (Partial.forward45plus1 d) m (pullState (OB5.sig 119) raw)).basis q=
      (StockArchiveReferenceW.common 120 10 d raw).basis q := by
  have beg:∀n,RefW ⟨4,by decide⟩ d x raw (run ((WindowParams.params.portal (start WindowParams.first) ::
      firstF WindowParams.params d WindowParams.first).flatten) n (pullState (OB5.sig 119) raw)):=by
    intro n
    rw [first_eq d]
    exact beginW L d x good raw n stage
  have mid:∀s n,RefW ⟨4,by decide⟩ d x raw s →
      RefW ⟨13,by decide⟩ d x raw (run (chainF WindowParams.params d WindowParams.first WindowParams.rest).flatten n s):=
    fun s n h=>chainW L.endpoint L.scratch d x good raw WindowParams.first WindowParams.rest consec_ship
      (fun k hk=>mem_rest hk) ⟨4,by decide⟩ ⟨13,by decide⟩ rfl (by rw [lastBlock_ship]) s n h
  rw [split d,run_append,run_append]
  exact lastW L.exitProg L.exitBridge d x good raw _ _ (mid _ _ (beg _))

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 5: the first block's ordinary (`FirstOrdinarySpec`) from the portal frame at 120 =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction
open StockWindowTicket Secp256k1 ArchiveHistoryCompare StockWindowW
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run body routed measurementCount

/-- The five pre-window letters of the first block `j` (group `start j-5`). -/
def plainF (j : Fin 23) : Fin 10 → Wire := History5.historyMap base (start j-5)

theorem plainF_cell (j : Fin 23) (i : Fin 10) :
    (i.val%2=0 ∧ (plainF j i:Nat)=start j-5+i.val/2+16) ∨ (i.val%2≠0 ∧ (plainF j i:Nat)=start j-5+i.val/2+1044) := by
  simp only [plainF,History5.historyMap,History5.historyId,base,Wire]
  split
  · left; constructor; assumption; omega
  · right; constructor; assumption; omega

theorem plainF_inj (j : Fin 23) : Function.Injective (plainF j) := by
  intro a b e
  have ha:=a.isLt; have hb:=b.isLt
  have ca:=plainF_cell j a; have cb:=plainF_cell j b
  have e':(plainF j a:Nat)=plainF j b:=e
  apply Fin.ext
  simp only [Wire] at ca cb e'
  omega

/-- `OB5.sig s` and `OB5.sig (s+14)` agree on the first block's letters. -/
theorem sigF_same (j : Fin 23) (i : Fin 10) :
    (OB5.sig (start j) (plainF j i):Nat)=OB5.sig (start j+14) (plainF j i) := by
  have c:=plainF_cell j i
  have hj:=j.isLt; have hi:=i.isLt
  simp only [OB5.sig,Wire]
  simp only [start,Wire] at *
  split <;> split <;> omega

theorem pastInputF (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21) (x p:Nat) (good:Bounds x p) (raw:State)
    (dom:Domain (start j) x p raw) (i:Fin 10) :
    raw.basis (plainF j i)=(run (span (start j) 15) [] raw).basis (plainF j i) := by
  have pp:=preservePast (start j) 15 x p (start j-5+i.val/2) (by simp only [start]; omega) good raw dom
    (by simp only [start]; omega) []
  rcases plainF_cell j i with ⟨-,e⟩|⟨-,e⟩
  · rw [e]; exact pp.1.symm
  · rw [e,show start j-5+i.val/2+1044=base (1028+(start j-5+i.val/2)) by simp only [base]; omega]; exact pp.2.symm

theorem encodeF (j : Fin 23) (h1 : 1≤j.val) (d:Bool) (a b:State) (tape:List Bool)
    (agree:∀i,a.basis (NativeFirstJ.history j i)=b.basis (plainF j i)) (i:Fin 10) :
    (run (NativeFirstJ.program j d) tape a).basis (NativeFirstJ.history j i)=
      (run (Rolling1588.encodeAt base d (start j-5)) [] b).basis (plainF j i) := by
  rw [(NativeFirstJ.equals j h1 d).1]
  exact ArchiveOrdinaryFive.stock_relocated d (NativeFirstJ.history j) (plainF j) (NativeFirstJ.histInj j)
    (plainF_inj j) a b tape [] agree i

/-- `Ordinary225Exit.result` for the first block `j`. -/
theorem resultF (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21)
    (old:∀i,oldRange (start j+1) (windowNet j (NativeFirstJ.history j i))) (d:Bool) (raw s:State) (m:List Bool)
    (x p:Nat) (good:Bounds x p) (dom:Domain (start j) x p raw)
    (input:∀i,(run (routed j 0 1) m s).basis (NativeFirstJ.history j i)=raw.basis (plainF j i)) :
    ∀i,(run (body j (NativeFirstJ.program j d)) m s).basis (NativeFirstJ.history j i)=
      (run (Rolling1588.encodeAt base d (start j-5)) [] (run (span (start j) 15) [] raw)).basis (plainF j i) := by
  intro i
  rw [OrdinaryJ.kept j _ m s _ (old i)]
  exact encodeF j h1 d _ _ _ (fun k=>(input k).trans (pastInputF j h1 h21 x p good raw dom k)) i

/-- `Logical225Exit.window` for the first block `j` (old cells = the five ticks before it). -/
theorem windowF (j : Fin 23) (h1 : 1≤j.val) (h21 : j.val≤21)
    (first:oldStart (start j)=start j-5 ∧ oldCount (start j)=5) (d:Bool) (raw historyState:State)
    (ordinaryBits:∀i,historyState.basis (NativeFirstJ.history j i)=
      (run (Rolling1588.encodeAt base d (start j-5)) [] (run (span (start j) 15) [] raw)).basis (plainF j i))
    (q:Wire) :
    (endRaw (start j) raw historyState).basis q=
      (run (Rolling1588.encodeAt base d (start j-5)) [] (run (span (start j) 15) [] raw)).basis q := by
  have bound:start j+14≤511:=by simp only [start]; omega
  have s5:5≤start j:=by simp only [start]; omega
  by_cases inside:q∈oldSites (start j)
  · obtain ⟨r,r1,r2,hq⟩:=old_cell inside
    rw [first.1] at r1 r2
    rw [first.2] at r2
    have ex:∃i:Fin 10,q=plainF j i:=by
      simp only [Wire] at *
      rcases hq with hq|hq
      · refine ⟨⟨2*(r-(start j-5)),by omega⟩,?_⟩
        rcases plainF_cell j ⟨2*(r-(start j-5)),by omega⟩ with ⟨-,e⟩|⟨od,-⟩
        · rw [e]; dsimp only; omega
        · exfalso; simp only at od; omega
      · refine ⟨⟨2*(r-(start j-5))+1,by omega⟩,?_⟩
        rcases plainF_cell j ⟨2*(r-(start j-5))+1,by omega⟩ with ⟨ev,-⟩|⟨-,e⟩
        · exfalso; simp only at ev; omega
        · rw [e]; dsimp only; omega
    obtain ⟨i,rfl⟩:=ex
    rw [endRaw_inside_gen _ bound _ _ _ inside,← sigF_same j i]
    exact ordinaryBits i
  · rw [endRaw_outside_gen _ bound _ _ _ inside]
    apply (run_preserves_outside _ _ _ q _).symm
    intro used
    obtain ⟨r,r1,r2,hq⟩:=OrdinaryJ.encode_cells d _ q used
    apply inside
    simp only [oldSites,first.1,first.2,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
      or_false,base]
    simp only [Wire] at *
    exact ⟨r,⟨by omega,by omega⟩,by omega⟩

theorem old_first : ∀i:Fin 10,oldRange (start WindowParams.first+1)
    (windowNet WindowParams.first (NativeFirstJ.history WindowParams.first i)) := by decide +kernel

/-- `FirstOrdinarySpec` (dadon's `ordinary225` at 120), from build-chain's `NativeFirstJ.first_core` (portal frame). -/
theorem firstOrdinary : FirstOrdinarySpec := by
  intro d x p good raw m stage
  let j:=WindowParams.first
  let z:=unsigned 120 x p
  let origin:=pullState (OB5.sig 119) raw
  let cut:=run (portalP 120) m origin
  let n:=m.drop (measurementCount (portalP 120))
  let pre:=run (Partial.enterP j) n cut
  let tape:=n.drop (measurementCount (Partial.enterP j))
  let T:=Shadow.reduced (sbP 120) 15 z
  obtain ⟨G,S,inputAt,frame,-⟩:=NativeFirstJ.first_core d x p good raw m stage
  have eqg:(SkywalkRails.encode G S (unsigned 120 x p).u (unsigned 120 x p).v).g=G:=by cases G <;> rfl
  have input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 120)
      (SkywalkRails.encode G S (unsigned 120 x p).u (unsigned 120 x p).v).a
      (SkywalkRails.encode G S (unsigned 120 x p).u (unsigned 120 x p).v).b G raw.basis:=by
    unfold InputAt at inputAt; rwa [eqg] at inputAt
  have nums:=LeaveJ.Admission.actualNumbers j (by decide) (by decide) x p good
  have dom:=initial 120 x p (by decide) d raw stage
  have hist:=pulled_history j rfl dom
  have ready:=EnterJ.ready_from_cut_at j raw cut z G S n nums.small frame input hist
  have to':T.v%2=1:=shadow_odd (sbP 120) z nums.small nums.odd
  have parity:((encode G S T.u T.v).a+(encode G S T.u T.v).b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have inp:=NativeFirstJ.history_from_stock j (by decide) (by decide) raw cut pre frame n tape rfl _ parity ready.2
  have res:=resultF j (by decide) (by decide) old_first d raw pre tape x p good dom inp
  have fb:start j=firstBlock:=rfl
  have firstB:oldStart (start j)=start j-5 ∧ oldCount (start j)=5:=by
    rw [fb]; exact ⟨oldStart_first,oldCount_first⟩
  intro q _
  have w:=windowF j (by decide) (by decide) firstB d raw _ res q
  have e:run (portalP 120++NativeFirstJ.enteredWindow WindowParams.first d) m origin=
      run (body j (NativeFirstJ.program j d)) tape pre:=by
    simp only [NativeFirstJ.enteredWindow,NativeFirstJ.window,run_append,run_take]; rfl
  rw [e]
  exact w

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowW

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowW

/-- `OrdinaryChain.wires` of the ship (window 120..255, exit 270). -/
theorem wiresShip (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) :
    ∀q∉StockWindowGeo.archives 120 10,(run (Partial.forward45plus1 d) m (pullState (OB5.sig 119) raw)).basis q=
      (StockArchiveReferenceW.common 120 10 d raw).basis q :=
  wiresW (OrdLeaves.of leaves firstOrdinary) d x good raw m stage

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ==== end build-main2 OrdW ====

-- ==== build-main2: the ship's stock comparison API (window 120..255, exit 270, 10 banks) ====
-- dadon's 3-bank names (StockArchiveReference.common, StockStrongChain.result, StockArchiveBanks.*,
-- StockRowVector.rows/binding, StockBaseline.comparison) re-opened as instances of the generic W sections.
section
namespace ECDSAAdd.Entrant.StairPacket.StockStrongChain
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 StockCanonicalRow StockWindowW
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount key select WideReference.canonical

/-- Block `i`'s saved key (dadon's `SavedKey (value x p s b cross{s}) codePorts{s+15}`), for every block. -/
def KeyS (d:Bool) (x p:Nat) (i:Fin 23) (s:State) : Prop :=
  SavedKey (value x p (start i) (sbP (start i)) (StockRowVectorW.crossW i)) (ArchiveJ.codePorts i) d s

/-- The last bank's key, in the exit archive (dadon's `finalBank`). -/
def KeyLast (d:Bool) (x p:Nat) (s:State) : Prop :=
  SavedKey (value x p 255 129 (StockRowVectorW.crossW ⟨12,by decide⟩)) ArchiveBoundary270.codePorts d s

/-- The exit: dadon's `Final.last` frame and the last bank's key. -/
def LastS (d:Bool) (x p:Nat) (s:State) : Prop := LastW d x p s ∧ KeyLast d x p s

/-- dadon's `selected{s}` receipt for any interior block `k` (saves block `i = k-1`'s key). -/
theorem receiptS (L:Leaves) (d:Bool) (x p:Nat) (good:Bounds x p) (i k:Fin 23) (hk:k.val=i.val+1)
    (h2:2≤k.val) (h12:k.val≤12) :
    ∀ s m, ReadyW d x p (start k) s → KeyS d x p i (run (nextF WindowParams.params d i k).flatten m s) := by
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  have pk:=prev_of i k hk
  rw [next_eq d i k hk,←pk]
  simp only [run_append,run_take]
  have nums:=LeaveJ.Admission.actualNumbers k (by omega) (by omega) x p good
  have old:=LeaveJ.Admission.actualNumbers (NativeJ.prev k) (by simp only [NativeJ.prev]; omega)
    (by simp only [NativeJ.prev]; omega) x p good
  have hist:=pulled_history k rfl pre.domain
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L.scratch k h2 (by omega) d x p good raw s g sg pg ps m pre
  have cert:=NativeJ.selected_receipt k (by omega) (by omega) d raw s m (unsigned (start k) x p) g sg nums.odd nums.small
    pre.cut curr hist scr (unsigned (start (NativeJ.prev k)) x p) pg ps _ old.odd old.small pre.facts
  have canon:=pre.pastCanonical
  unfold signedAt at canon
  dsimp only at cert
  rw [canon] at cert
  exact ⟨cert.1,cert.2.1,ArchiveWindowPreserve.keep cert.2.2 (fun q hq=>L.keepLeave k h2 h12 q hq _ _)⟩

theorem keepS (L:Leaves) (d:Bool) (x p:Nat) (i k:Fin 23) (hk:k.val=i.val+1) (h12:k.val≤12) :
    ∀ s m, ReadyW d x p (start k) s → ∀ i' : Fin 23, 3 ≤ i'.val → i'.val < i.val → KeyS d x p i' s →
      KeyS d x p i' (run (nextF WindowParams.params d i k).flatten m s) := by
  intro s m _ i' h1 h2 key
  obtain ⟨r,c,kept⟩:=key
  exact ⟨r,c,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepOlder i k i' hk (by omega) (by omega) h12 d q hq s m)⟩

/-- dadon's `finalBank` from the generic hand-off at block 13 (the exit archive keeps block 12's key). -/
theorem finalS (L:Leaves) (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (m:List Bool) (h:ReadyW d x p 270 s) :
    KeyLast d x p (run (NativePack270.lastWindow d) m s) := by
  obtain ⟨k,ek,raw,g,sg,pg,ps,pre⟩:=h
  have k13:k=⟨13,by decide⟩:=Fin.ext (by have := ek; simp only [StairPacket.start] at this; show k.val=13; omega)
  subst k13
  have cut:=OrdinaryChainG.exitCut L.exitBridge d x raw s g sg pg ps pre
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,r20,r21,r22⟩:=L.exitBridge
  let z:=unsigned 270 x p
  have short:min z.u z.v<2^121:=true_small x p 270 (lt_trans good.small good.cap) good.cap (by decide)
  have old:=LeaveJ.Admission.actualNumbers ⟨12,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 121 270 x p=(3*2^137≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have facts:=pre.facts
  have mode:s.basis 1701=decide (Shadow.far 129 15 (unsigned 255 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1702=(decide (Shadow.far 129 15 (unsigned 255 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 255 x p).v<(unsigned 255 x p).u))
        ((physicalCells ArchiveBoundary270.sourceIdx s).take 5)):=by rw [←r21]; exact facts.suffix
  have cross:s.basis 1703=(decide (Shadow.far 129 15 (unsigned 255 x p)) &&
      HighBankSum.cross (LeaveJ.TrueMiddle.d ⟨12,by decide⟩ (unsigned 255 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack270.selected_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 270 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 255 x p) pg ps _
    old.odd old.small facts.records mode side cross
  have canon:signedAt 255 x p pg ps=WideReference.canonical 255 x p:=pre.pastCanonical
  unfold signedAt at canon
  have cert:=last.2.1
  dsimp only at cert
  rw [canon] at cert
  exact ⟨cert.1,cert.2.1,kept_frame _ _ _ _ cert.2.2⟩

theorem keys_eq (x p b:Nat) (hb:3+b<23) :
    StockRowVectorW.keys ⟨3,by decide⟩ x p b=value x p (start ⟨3+b,hb⟩) (sbP (start ⟨3+b,hb⟩))
      (StockRowVectorW.crossW ⟨3+b,hb⟩) := by
  have e:start (⟨3,by decide⟩:Fin 23)+15*b=start ⟨3+b,hb⟩:=by simp only [StairPacket.start]; omega
  simp only [StockRowVectorW.keys,dif_pos hb]
  rw [e]

/-- The window's strong chain (dadon's `StockStrongChain.result` at 120, 10 keys). -/
theorem resultW (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) :
    let start0:=pullState (OB5.sig 119) raw
    let out:=run (forward45plus1 d) m start0
    out.phase=raw.phase ∧ StockRowVectorW.final ⟨3,by decide⟩ ⟨12,by decide⟩ ArchiveBoundary270.codePorts d x p out ∧
      ∀n,run (reverse45plus1 d) n out=start0 := by
  have L:=StockWindowW.leaves
  have bl:blockOf (exitTick WindowParams.first WindowParams.rest)=13:=by rw [exitTick_ship]; rfl
  have lastC:Checked (exitF WindowParams.params d (exitTick WindowParams.first WindowParams.rest)).flatten
      (exitR WindowParams.params d (exitTick WindowParams.first WindowParams.rest)).flatten
      (ReadyW d x p (exitTick WindowParams.first WindowParams.rest)) (LastS d x p):=by
    rw [exitTick_ship]
    intro s n h
    have e:=exitStep L d x good s n h
    refine ⟨e.1,⟨e.2.1,?_⟩,e.2.2⟩
    rw [(L.exitProg d).1]
    exact finalS L d x good s n h
  have strong:=window_strong WindowParams.params d (ReadyW d x p) (KeyS d x p) (BeforeW d x p) (LastS d x p)
    WindowParams.first WindowParams.rest consec_ship (firstStep L d x p good)
    (fun i k hm hk=>interior L d x p good i k hk (mem_rest hm).1 (mem_rest hm).2)
    (fun i k hm hk=>receiptS L d x p good i k hk (by have := mem_rest hm; omega) (by have := mem_rest hm; omega))
    (fun i k hm hk s n r i' h1 h2=>keepS L d x p i k hk (by have := mem_rest hm; omega) s n r i' h1 h2)
    lastC
    (by
      intro s n _ i h1 h2 key
      rw [bl] at h2
      revert key
      rw [exitTick_ship]
      intro key
      obtain ⟨r,c,kept⟩:=key
      exact ⟨r,c,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepExit i h1 (by omega) d q hq s n)⟩)
  rw [Partial.assembly,Partial.unwind_assembly]
  intro start0 out
  obtain ⟨ph,⟨⟨_,lastKey⟩,saved⟩,undo⟩:=strong start0 m ⟨raw,stage,rfl⟩
  refine ⟨ph,?_,undo⟩
  intro b hb
  change 3+b ≤ 12 at hb
  have lt:3+b<23:=by omega
  rw [keys_eq x p b lt]
  unfold ArchiveStockRows.bankPorts
  by_cases h:(⟨3,by decide⟩:Fin 23).val+b<(⟨12,by decide⟩:Fin 23).val
  · rw [dif_pos h]
    change 3+b < 12 at h
    exact saved ⟨3+b,lt⟩ (by show 3 ≤ 3+b; omega) (by rw [bl]; show 3+b+2 ≤ 13; omega)
  · rw [dif_neg h]
    change ¬(3+b < 12) at h
    have e:(⟨3+b,lt⟩:Fin 23)=⟨12,by decide⟩:=Fin.ext (by show 3+b=12; omega)
    rw [e]
    have s12:start (⟨12,by decide⟩:Fin 23)=255:=rfl
    have b12:sbP 255=129:=by decide
    rw [s12,b12]
    exact lastKey

/-- dadon's name: the ship's strong chain. -/
theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) :
    let start0:=pullState (OB5.sig 119) raw
    let out:=run (forward45plus1 d) m start0
    out.phase=raw.phase ∧ StockRowVectorW.final ⟨3,by decide⟩ ⟨12,by decide⟩ ArchiveBoundary270.codePorts d x p out ∧
      ∀n,run (reverse45plus1 d) n out=start0 :=
  resultW d x good raw m stage

end ECDSAAdd.Entrant.StairPacket.StockStrongChain
end

section
namespace ECDSAAdd.Entrant.StairPacket.StockArchiveReference
open Arithmetic MappedCompressed WideReference
/-- The ship's stock reference (dadon's `common` at 225..270, now 120..270). -/
def common (d:Bool) (raw:State):State:=StockArchiveReferenceW.common 120 10 d raw
end ECDSAAdd.Entrant.StairPacket.StockArchiveReference

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanks
open Arithmetic MappedCompressed Secp256k1 WideReference ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run span
/-- The ship's banks: bank `b` is block `3+b`'s archive, bank 9 the exit archive. -/
abbrev Bank := Fin 10
def j1 : Fin 23 := ⟨3,by decide⟩
def jn : Fin 23 := ⟨12,by decide⟩
def ports (b:Bank):Ports:=ArchiveStockRows.bankPorts j1 jn ArchiveBoundary270.codePorts b.val
def siteAt (b:Bank) (j:Fin 16):Wire:=ports b ⟨j.val,by omega⟩
def tick (b:Bank):Nat:=120+15*b.val
def archives:List Wire:=StockWindowGeo.archives 120 10
def Same (a b:State):Prop:=ArchiveStockSuffixW.Same 120 10 a b
def nativeAt (d:Bool) (b:Bank) (r:Nat) (s:State):Prop:=StockArchiveBanksW.nativeAt (siteAt b) d r s

theorem exitCells : ∀j:Fin 16,ArchiveBoundary270.codePorts ⟨j.val,by omega⟩=
    (Partial.cellsRestoreP (start jn+15)).getD j 0 := by decide +kernel
theorem site_eq (b:Bank) (j:Fin 16) : siteAt b j=StockWindowGeo.bankSite 120 b.val j :=
  StockArchiveBanksW.site_eq j1 jn ArchiveBoundary270.codePorts exitCells b.val (by simp only [j1,jn]; omega) j
theorem mem (b:Bank) (j:Fin 16) : siteAt b j∈archives := by
  rw [site_eq]; exact StockWindowGeo.bank_mem 120 10 b.val b.isLt j
theorem bank_rep (q:Wire) (h:q∈archives) : ∃(b:Bank)(j:Fin 16),siteAt b j=q := by
  simp only [archives,StockWindowGeo.archives,List.mem_flatMap,List.mem_range,List.mem_map,List.mem_finRange,
    true_and] at h
  obtain ⟨b,hb,j,rfl⟩:=h
  exact ⟨⟨b,hb⟩,j,site_eq ⟨b,hb⟩ j⟩

structure Paired (d:Bool) (x:Nat) (a s:State) (rows:Bank→Nat):Prop where
  equality:Same a s
  labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b)
  custom:∀b,Kept (ports b) d (rows b) a
  stock:∀b,nativeAt d b (rows b) s

theorem Paired.ofW {d x a s} {rows:Nat→Nat}
    (h:StockArchiveBanksW.Paired j1 jn ArchiveBoundary270.codePorts 10 d x a s rows) :
    Paired d x a s (fun b=>rows b.val) :=
  ⟨h.equality,fun b=>h.labels b.val b.isLt,fun b=>h.custom b.val b.isLt,fun b=>h.stock b.val b.isLt⟩

theorem Paired.through {d x a s rows} (pair:Paired d x a s rows) (P:Program)
    (off:∀q∈archives,q∉wires P) (m:List Bool):Paired d x (run P m a) (run P m s) rows:=by
  have h:=ArchiveStockSuffixW.independent 120 10 P off m a s pair.equality
  refine ⟨h.1,pair.labels,?_,?_⟩
  · intro b j
    exact (h.2 (siteAt b j) (mem b j)).trans (pair.custom b j)
  · intro b j
    exact (run_preserves_outside P m s (siteAt b j) (off _ (mem b j))).trans (pair.stock b j)

/-- `ArchiveStockSuffix.safe` for the ship's banks. -/
theorem safe (d:Bool) (i n:Nat) (lo:271 ≤ i) (hi:i+n ≤ 512) (q:Wire) (mem:q∈archives) :
    q∉wires (Rolling1588TickGap.forward d i n) ∧ q∉wires (Rolling1588.reverse d i n) :=
  ArchiveStockSuffixW.safe 120 10 270 (by decide) rfl (by decide) (by decide) d i n lo hi q mem
end ECDSAAdd.Entrant.StairPacket.StockArchiveBanks

namespace ECDSAAdd.Entrant.StairPacket.StockRowVector
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks
/-- The ship's key-selected rows (bank `b` = block `3+b`). -/
noncomputable def rows (x p:Nat) (b:Bank):Nat:=StockRowVectorW.rows j1 x p b.val
theorem binding (d:Bool) (x:Nat) (good:Bounds x p) (raw a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis)
    (stored:StockRowVectorW.final j1 jn ArchiveBoundary270.codePorts d x p a)
    (same:Same a (run (Rolling1588TickGap.forward d 120 151) m (pullState (OB5.sig 119) raw))) :
    Paired d x a (run (Rolling1588TickGap.forward d 120 151) m (pullState (OB5.sig 119) raw)) (rows x p) :=
  Paired.ofW (StockRowVectorW.binding j1 jn ArchiveBoundary270.codePorts exitCells 10 rfl (by decide) d x good raw a m
    stage stored same)
end ECDSAAdd.Entrant.StairPacket.StockRowVector

namespace ECDSAAdd.Entrant.StairPacket.StockBaseline
open Arithmetic MappedCompressed WideReference Secp256k1 StockArchiveBanks
/-- dadon's `comparison` for the ship. -/
theorem comparison (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 s.basis) (results:ArchiveStockRows.Final d x p a) :
    Same (run (Rolling1588TickGap.forward d 120 151) m (pullState (OB5.sig 119) s)) (StockArchiveReference.common d s) :=
  StockBaselineW.comparison (j1:=⟨3,by decide⟩) (jn:=⟨12,by decide⟩) 10 rfl (by decide) d x good s a m stage results
end ECDSAAdd.Entrant.StairPacket.StockBaseline
end
-- ==== end build-main2 ship API ====



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
private theorem hook (j:Nat) (hj:j∈[25,28,31,34,37,40,43,46,49,52]) (op:Stage):GoodP (fieldHook j op):=by
  have span:j∈List.range' 1 83:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;apply List.mem_range'_1.mpr;omega
  have table:∀(j:Nat),j∈[25,28,31,34,37,40,43,46,49,52]→∀q∈fieldSites j,16 ≤ q ∧ q < 2330:=by decide +kernel
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
private theorem pair (d:Bool) (j:Nat) (hj:j∈[25,28,31,34,37,40,43,46,49,52]) (hi:j≤83):GoodP (ten j (!d)):=by
  have here:=singleton d j (by omega)
  have next:=singleton d (j+1) (by omega)
  have a:GoodP (first j (!d)):=by cases d <;> first | exact here | exact next
  have b:GoodP (second j (!d)):=by cases d <;> first | exact here | exact next
  exact app (hook j hj _) (app a (app (hook j hj _) (app b (hook j hj _))))
theorem group84_good (d:Bool):GoodP (group84 d):=by
  have ord {a b:Program} (x:GoodP a) (y:GoodP b):GoodP (ordered d a b):=by cases d <;> first | exact app x y | exact app y x
  exact ord (ordinary d 1 24 (by decide))
    (ord (pair d 25 (by decide) (by decide))
    (ord (ordinary d 27 1 (by decide))
    (ord (pair d 28 (by decide) (by decide))
    (ord (ordinary d 30 1 (by decide))
    (ord (pair d 31 (by decide) (by decide))
    (ord (ordinary d 33 1 (by decide))
    (ord (pair d 34 (by decide) (by decide))
    (ord (ordinary d 36 1 (by decide))
    (ord (pair d 37 (by decide) (by decide))
    (ord (ordinary d 39 1 (by decide))
    (ord (pair d 40 (by decide) (by decide))
    (ord (ordinary d 42 1 (by decide))
    (ord (pair d 43 (by decide) (by decide))
    (ord (ordinary d 45 1 (by decide))
    (ord (pair d 46 (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide))
    (ord (pair d 49 (by decide) (by decide))
    (ord (ordinary d 51 1 (by decide))
    (ord (pair d 52 (by decide) (by decide))
    (ordinary d 54 31 (by decide)))))))))))))))))))))

theorem entryTailPrefix_ours :
    wires (WindowCallerCosts.entryTailPrefix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.entryTailPrefix
  simp only [wires_append, Finset.union_subset_iff, and_assoc]
  exact ⟨group84_good true,
    fseg_caller 87 62 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 13 85 5 (by omega) (by omega),
    fseg_caller 62 47 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 22 90 3 (by omega) (by omega),
    fseg_caller 47 32 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 30 93 3 (by omega) (by omega),
    fseg_caller 32 22 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 36 96 2 (by omega) (by omega),
    fseg_caller 22 12 (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller true 41 98 2 (by omega) (by omega),
    forwardLastV3_caller⟩

theorem exitHeadSuffix_ours :
    wires (WindowCallerCosts.exitHeadSuffix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.exitHeadSuffix
  simp only [wires_append, Finset.union_subset_iff, and_assoc]
  exact ⟨reverseLastV3_caller,
    hostedGroupV3_caller false 41 98 2 (by omega) (by omega),
    rseg_caller 22 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 36 96 2 (by omega) (by omega),
    rseg_caller 32 22 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 30 93 3 (by omega) (by omega),
    rseg_caller 47 32 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 22 90 3 (by omega) (by omega),
    rseg_caller 62 47 (by decide) (by decide) (by decide) (by decide) (by decide),
    hostedGroupV3_caller false 13 85 5 (by omega) (by omega),
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

namespace ECDSAAdd.Entrant.StairPacket.StockNativeCompare
open Arithmetic MappedCompressed WideReference Secp256k1
attribute [local irreducible] run
theorem common_phase (d:Bool) (x:Nat) (good:Bounds x p) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 120 s.basis) :
    (StockArchiveReferenceW.common 120 10 d s).phase=s.phase := by
  have final:=(StockWindowChain.result d x good s [] stage).2.1
  have same:=StockBaselineW.comparison (j1:=⟨3,by decide⟩) (jn:=⟨12,by decide⟩) 10 rfl (by decide) d x good s _ [] stage final
  exact same.1.symm.trans (StockBaseline.forward_phase d x good 120 151 (by decide) (by decide) s [] stage)

theorem normalized (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) :
    ArchiveStockSuffixW.Same 120 10 (run (Partial.forward45plus1 d) m (pullState (OB5.sig 119) raw))
      (StockArchiveReferenceW.common 120 10 d raw) :=
  ⟨(StockWindowChain.result d x good raw m stage).1.trans (common_phase d x good raw stage).symm,
    OrdinaryChainG.wiresShip d x good raw m stage⟩
end ECDSAAdd.Entrant.StairPacket.StockNativeCompare

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkPrefix
set_option maxRecDepth 9500
set_option maxHeartbeats 3000000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount Partial.forward45plus1
def NewNormalized (d:Bool) (x:Nat):Prop:=∀(raw:State)(m:List Bool),Rolling1588.Integer.Stage base d x p 120 raw.basis →
    Same (run (Partial.forward45plus1 d) m (pullState (OB5.sig 119) raw)) (StockArchiveReference.common d raw)

theorem steady (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:0 < i) (hi:i+n≤512) (s:State) (u v:List Bool) (stage:Rolling1588.Integer.Stage base d x p i s.basis):
    run (Rolling1588TickGap.forward d i n) u (pullState (OB5.sig (i-1)) s)=run (Rolling1588TickGap.forward d i n) v (pullState (OB5.sig (i-1)) s):=
  (StockDelayed.window d x good.nonzero good.small i n lo hi s u stage).trans
    (StockDelayed.window d x good.nonzero good.small i n lo hi s v stage).symm
theorem suffix_independent (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 120 s.basis) (u v y z:List Bool):
    let t:=pullState (OB5.sig 119) s
    let old:=Rolling1588TickGap.forward d 120 151
    let tail:=Rolling1588TickGap.forward d 271 n
    run tail u (run old v t)=run tail y (run old z t):=by
  let t:=pullState (OB5.sig 119) s
  let A:=Rolling1588TickGap.forward d 120 151
  let B:=Rolling1588TickGap.forward d 271 n
  let mix (v u:List Bool):=FlagEntry.pfx (measurementCount A) v++u
  have eq:=steady d x good 120 (151+n) (by decide) (by omega) s (mix v u) (mix z y) stage
  rw [StairRestSupport.forward_append d 151 120 n] at eq
  exact (Stair44PointSecond.joinRecords A B v u t).symm.trans (eq.trans (Stair44PointSecond.joinRecords A B z y t))

theorem window (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) (m stockTape:List Bool) (norm:NewNormalized d x):
    let s:=pullState (OB5.sig 119) raw
    Paired d x (run (forwardEnd d n) m s) (run (Rolling1588TickGap.forward d 120 (151+n)) stockTape s) (StockRowVector.rows x p):=by
  let s:=pullState (OB5.sig 119) raw
  have result:=StockWindowChain.result d x good raw m stage
  have old:=StockBaseline.comparison d x good raw _ m stage result.2.1
  have new:=norm raw m stage
  have eq:Same _ _:=⟨new.1.trans old.1.symm,fun q off=>(new.2 q off).trans (old.2 q off).symm⟩
  have h:=StockRowVector.binding d x good raw _ m stage (StockStrongChain.result d x good raw m stage).2.1 eq
  have onward:=h.through (Rolling1588TickGap.forward d 271 n) (fun q h=>(safe d 271 n (by decide) bound q h).1) (m.drop (measurementCount (Partial.forward45plus1 d)))
  simp only [forwardEnd,StairRestSupport.forward_append d 151 120 n,run_append,run_take]
  rw [←suffix_independent d n x good bound raw stage (m.drop (measurementCount (Partial.forward45plus1 d))) m (stockTape.drop (measurementCount (Rolling1588TickGap.forward d 120 151))) stockTape]
  exact onward
end ECDSAAdd.Entrant.StairPacket.StockWalkWindow

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockPlacedWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkPrefix StockWalkWindow
set_option maxRecDepth 12000
set_option maxHeartbeats 2500000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount Partial.forward45plus1
theorem fixed:∀(b:Bank)(j:Fin 16),Stair44WalkMap.rest (siteAt b j)=siteAt b j:=by decide +kernel
theorem unplace {d x a s rows} (pair:Paired d x (pullState Stair44WalkMap.rest a) (pullState Stair44WalkMap.rest s) rows):Paired d x a s rows:=by
  refine ⟨⟨pair.equality.1,?_⟩,pair.labels,?_,?_⟩
  · intro q off
    have safe:Stair44WalkMap.rest.symm q∉archives:=by
      intro hit
      obtain ⟨b,j,e⟩:=bank_rep _ hit
      apply off
      have same:=congrArg Stair44WalkMap.rest e
      rw [fixed,Equiv.apply_symm_apply] at same
      exact same ▸ (StockArchiveBanks.mem b j)
    simpa only [pullState,Equiv.apply_symm_apply] using pair.equality.2 _ safe
  · intro b j
    change a.basis (siteAt b j)=_
    rw [←fixed b j]
    exact pair.custom b j
  · intro b j
    rw [←fixed b j]
    exact pair.stock b j

theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.forward d (255+n)=
    first d++renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 120 (151+n)):=by
  have e:=StairRestSupport.forward_append d 104 16 (151+n)
  change Rolling1588TickGap.forward d 16 (104+(151+n))=Rolling1588TickGap.forward d 16 104++Rolling1588TickGap.forward d 120 (151+n) at e
  rw [show 255+n=104+(151+n) by omega]
  simp only [Stair44WalkRun.forward,first,e,renameProgram,List.map_append,List.append_assoc]

theorem forward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s) (norm:NewNormalized d x):
    Paired d x (run (WindowWalkCosts.forward d n) m a) (run (Stair44WalkRun.forward d (255+n)) m a) (StockRowVector.rows x p):=by
  let t:=m.drop (measurementCount (first d))
  have rel:=window d n x good bound (regular d s m) (cut120 d x good s a m stage input).1 t t norm
  apply unplace
  rw [placed d n x good s a m stage input,old_split,run_append,run_take,run_rename _ Stair44WalkMap.rest.injective,(cut120 d x good s a m stage input).2]
  exact rel
end ECDSAAdd.Entrant.StairPacket.StockPlacedWindow

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks StairArchiveRelease WindowFieldMask
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
/-- Field bank of the ship's bank `b` (block `3+b`, start `5*groupId-5`): banks 25, 28, …, 52. -/
def groupId (b:Bank):Nat:=25+3*b.val
def parityPort (b:Bank) (i:Fin 16):Wire:=OB5.sig 511 (NewHistory5.payloadWire base (8*groupId b+i.val))
theorem native_ports:∀(b:Bank)(i:Fin 16),parityPort b i=siteAt b i:=by decide +kernel
theorem host_ports:∀(b:Bank)(i:Fin 16),Rolling1588Lifetime.phaseHost (siteAt b i)=siteAt b i:=by decide +kernel
theorem field_ports:∀(b:Bank)(i:Fin 16),fieldPort (groupId b) i.val=siteAt b i:=by decide +kernel
theorem whole:allBanks=archives.toFinset:=by decide +kernel
theorem whole_iff (q:Wire):q∈allBanks ↔ q∈archives:=by rw [whole,List.mem_toFinset]
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockInverseReplay
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkWindow StockPlacedWindow
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
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks StairArchiveRelease WindowFieldMask CodecBitSliceVerify ArchivePortAction
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
def fieldRows (r:Bank→Nat) (j:Nat):Nat:=r ⟨((j-25)/3)%10,Nat.mod_lt _ (by decide)⟩
theorem rowsAt (r:Bank→Nat) (b:Bank):fieldRows r (groupId b)=r b:=by
  unfold fieldRows groupId
  congr 1
  apply Fin.ext
  have hb:=b.isLt
  show ((25+3*b.val-25)/3)%10=b.val
  omega
theorem idAt : ∀j∈bankIds,∃b:Bank,groupId b=j:=by decide +kernel
theorem enterCode (d:Bool) (j:Nat): (code d).take 16=(WindowFieldJourney.initialCode d j).take 16:=by
  cases d
  · simpa only [code,List.take_take,Nat.min_self] using StairArchiveHandoff.archive_edges.2.1
  · simpa only [code,List.take_take,Nat.min_self] using StairArchiveHandoff.archive_edges.1
theorem fits {d x a s rows} (pair:Paired d x a s rows):
    Fits (fieldRows rows) (WindowFieldJourney.initialCode d) a s := by
  refine ⟨pair.equality.1,fun q h=>pair.equality.2 q (fun hit=>h ((whole_iff q).mpr hit)),?_⟩
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
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkWindow StockInverseReplay
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse
  Rolling1588.Integer.regularForward Partial.forward45plus1 Partial.reverse45plus1

def real (d:Bool) (raw:State):State:=run (Partial.forward45plus1 d) [] (pullState (OB5.sig 119) raw)
def stock (d:Bool) (raw:State):State:=run (Rolling1588TickGap.forward d 120 151) [] (pullState (OB5.sig 119) raw)
theorem shadow (d:Bool) (x:Nat) (good:Bounds x p) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) (norm:NewNormalized d x):
    Paired d x (real d raw) (stock d raw) (StockRowVector.rows x p):=by
  have e:=norm raw [] stage
  have cmp:=StockBaseline.comparison d x good raw _ [] stage (StockWindowChain.result d x good raw [] stage).2.1
  exact StockRowVector.binding d x good raw _ [] stage (StockStrongChain.result d x good raw [] stage).2.1
    ⟨e.1.trans cmp.1.symm,fun q off=>(e.2 q off).trans (cmp.2 q off).symm⟩
theorem candidate_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis):
    run (Partial.reverse45plus1 d) m (real d raw)=pullState (OB5.sig 119) raw:=
  (StockWindowChain.result d x good raw [] stage).2.2 m
theorem stock_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis):
    run (Rolling1588.reverse d 120 151) m (stock d raw)=pullState (OB5.sig 119) raw:=
  reverse_forward d x good 120 151 (by decide) (by decide) raw [] m stage
attribute [local irreducible] real stock poolEq
theorem inner (d:Bool) (x:Nat) (good:Bounds x p) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (stock d raw)):
    run (Partial.reverse45plus1 d) m a=run (Rolling1588.reverse d 120 151) m ref:=by
  have ghost:=shadow d x good raw stage norm
  exact replay _ _ m a ref (real d raw) (stock d raw) _ (PartialSites.pool_partial d) (PartialSites.pool_old d 120 151 (by decide) (by decide))
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
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 120 (151+n)) [] (pullState (OB5.sig 119) raw))):
    run (backwards d n) m a=run (Rolling1588.reverse d 120 (151+n)) m ref:=by
  have h:=pair.through (Rolling1588.reverse d 271 n) (fun q hq=>(safe d 271 n (by decide) bound q hq).2) m
  have pools:=pool_run (PartialSites.pool_old d 271 n (by decide) bound) agree m
  simp only [StairRestSupport.forward_append d 151 120 n,run_append,run_take,List.drop_nil] at pools
  rw [tail_cancel d x 120 151 n good (by decide) bound raw stage m] at pools
  simp only [backwards,StairRestSupport.reverse_append d 151 120 n,run_append,run_take]
  apply inner d x good raw _ _ _ stage norm h
  unfold stock
  exact pools
end ECDSAAdd.Entrant.StairPacket.StockBackWindow

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks StairArchiveRelease WindowFieldMask CodecBitSliceVerify ArchivePortAction WindowFieldJourney
set_option maxRecDepth 25000
set_option maxHeartbeats 3200000
def Fixed (f:Wire→Wire):Prop:=∀b i,f (siteAt b i)=siteAt b i
theorem archive_pre {f:Wire→Wire} (inj:Function.Injective f) (fix:Fixed f) (q:Wire) (off:q∉archives):f q∉archives:=by
  intro hit
  obtain ⟨b,i,e⟩:=StockArchiveBanks.bank_rep _ hit
  have eq:=inj ((fix b i).trans e)
  exact off (eq ▸ (StockArchiveBanks.mem b i))
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
    exact ff.outside _ (fun hit=>archive_pre inj fix q (fun h=>off ((whole_iff q).mpr h)) ((whole_iff _).mp hit))
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
  refine ⟨⟨ff.phase,fun q h=>ff.outside q (fun hit=>h ((whole_iff q).mp hit))⟩,labels,?_,old⟩
  intro b i
  have pick:∀b:Bank,groupId b∈bankIds:=by decide +kernel
  have v:=ff.bytes _ (pick b) i.val (Finset.mem_range.mpr i.isLt)
  rw [field_ports b i,rowsAt] at v
  exact v.trans (StairArchiveHandoff.wires_eq _ _ 16 (completeCode d b) i.val _ i.isLt)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockPlacedBack
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkWindow StockInverseReplay FlagEntry
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse Partial.reverse45plus1
theorem pull {d x a s rows} (h:Paired d x a s rows):
    Paired d x (pullState Stair44WalkMap.rest a) (pullState Stair44WalkMap.rest s) rows:=by
  refine ⟨⟨h.equality.1,?_⟩,h.labels,?_,?_⟩
  · intro q off
    apply h.equality.2
    intro hit
    obtain ⟨b,j,atSite⟩:=StockArchiveBanks.bank_rep _ hit
    have eq:siteAt b j=q:=Stair44WalkMap.rest.injective ((StockPlacedWindow.fixed b j).trans atSite)
    exact off (eq ▸ (StockArchiveBanks.mem b j))
  · intro b j
    change a.basis (Stair44WalkMap.rest (siteAt b j))=_
    rw [StockPlacedWindow.fixed]
    exact h.custom b j
  · intro b j
    change s.basis (Stair44WalkMap.rest (siteAt b j))=_
    rw [StockPlacedWindow.fixed]
    exact h.stock b j
def R (P:Program):Program:=renameProgram Stair44WalkMap.rest P
def remaining (d:Bool):Program:=R (Rolling1588.reverse d 16 104)++renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)
theorem split (d:Bool) (n:Nat):WindowWalkCosts.backward d n=R (StockBackWindow.backwards d n)++remaining d:=by
  simp only [WindowWalkCosts.backward,StockBackWindow.backwards,R,remaining,renameProgram,List.map_append,List.append_assoc]
theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.backward d (255+n)=R (Rolling1588.reverse d 120 (151+n))++remaining d:=by
  have e:=StairRestSupport.reverse_append d 104 16 (151+n)
  change Rolling1588.reverse d 16 (104+(151+n))=Rolling1588.reverse d 120 (151+n)++Rolling1588.reverse d 16 104 at e
  rw [show 255+n=104+(151+n) by omega]
  simp only [remaining,Stair44WalkRun.backward,e,R,renameProgram,List.map_append,List.append_assoc]

theorem backward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:271+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 120 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 120 (151+n)) [] (pullState (OB5.sig 119) raw))):
    ∃old,run (WindowWalkCosts.backward d n) m a=run (Stair44WalkRun.backward d (255+n)) old ref:=by
  let A:=R (StockBackWindow.backwards d n)
  let B:=R (Rolling1588.reverse d 120 (151+n))
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
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks WindowFieldMask CodecBitSliceVerify
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
      run (Rolling1588TickGap.forward d 120 (151+n)) [] (pullState (OB5.sig 119) raw):=by
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  have same:=StockWalkWindow.steady d x good 1 (270+n) (by decide) (by omega) s m [] stage
  rw [show 1-1=0 from rfl,init] at same
  have cut:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 119 1 (by decide) (by decide) s [] stage
  rw [show 1-1=0 from rfl,init] at cut
  have shape:270+n=119+(151+n):=by omega
  rw [same,shape,StairRestSupport.forward_append d 119 1 (151+n),run_append,run_take,List.drop_nil,cut]
  rfl

theorem move {f:Wire→Wire} (a b c:State) (mem:∀q∈pool,f q∈pool) (eq:poolEq a b)
    (fixed:pullState f b=b) (next:b=c):poolEq (pullState f a) c:=by
  intro q hq
  exact (eq _ (mem q hq)).trans ((congrArg (fun s:State=>s.basis q) fixed).trans (congrArg (fun s:State=>s.basis q) next))
theorem endpoint_stage (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (stage:Rolling1588.Integer.Stage base d x p 1 s.basis):
    Rolling1588.Integer.Stage base d x p 120 (regular d s []).basis:=StockBackWindow.stageAt d x good 1 119 (by decide) s [] stage
theorem endpoint_pool (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:271+n∈[425,505,506]) (s ref:State) (enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:271+n≤512)
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (270+n)) enc s)):
    poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 120 (151+n)) [] (pullState (OB5.sig 119) (regular d s []))):=
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
  have loc:siteAt b j∈pool:=archives_pool _ (StockArchiveBanks.mem b j)
  exact (eq _ loc).trans ((congrArg (fun s:State=>s.basis (siteAt b j)) same.symm).trans (pair.stock b j))

theorem div_native {s:State} (F:StairConcreteAssembly.EntryFrame s) (m:List Bool):
    Native false F.x (pullState phaseHost (run oldDivHead m s)):=
  ofEndpoint false 235 F.x F.x_pos F.x_lt (by decide) _ (div_endpoint F m)
theorem mul_native (k:Nat) {s:State} (F:StairConcreteAssembly.ExitFrame k s) (m:List Bool):
    Native true F.x (pullState phaseHost (run oldMulHead m s)):=
  ofEndpoint true 154 F.x F.x_pos F.x_lt (by decide) _ (mul_endpoint k F m)

theorem Native.pair {d x a ref} (old:Native d x ref) (eq:StockArchiveBanks.Same a ref)
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
  rw [Partial.assembly] at h
  rw [domain_eq]
  exact (WindowCovered.window_covered d).1 q h
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
  have shape:270+n=15+(104+(151+n)):=by omega
  rw [shape,tickGap_forward_split d 15 1 (104+(151+n)),tickGap_forward_split d 104 16 (151+n),tickGap_forward_split d 151 120 n] at stock
  simp only [wires_append,Finset.union_subset_iff] at stock
  apply wires_sub_of_parts _ _
  · exact rename_caller _ firstOK _ stock.1
  · apply rename_caller _ restOK
    exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ stock.2.1 (part d).1) stock.2.2.2

theorem backward (d:Bool) (n:Nat) (bound:270+n≤505):wires (WindowWalkCosts.backward d n)⊆callerDomain:=by
  have stock:=reverse_own d (270+n) bound
  have shape:270+n=15+(104+(151+n)):=by omega
  rw [shape,reverse_split d 15 1 (104+(151+n)),reverse_split d 104 16 (151+n),reverse_split d 151 120 n] at stock
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
def Active (j : Nat) := j=25 ∨ j=28 ∨ j=31 ∨ j=34 ∨ j=37 ∨ j=40 ∨ j=43 ∨ j=46 ∨ j=49 ∨ j=52
private theorem mesh : wires region⊆Finset.range 31 :=
  ECDSAAdd.Entrant.WSlimMain.wires_subset_range_of_all (by decide +kernel)
private theorem portDistinct : ∀ j∈([25,28,31,34,37,40,43,46,49,52]:List Nat), ((List.range 31).map (port j)).Nodup := by decide +kernel
private theorem inj {j : Nat} (hj : Active j) :
    ∀a∈Finset.range 31,∀b∈Finset.range 31, port j a=port j b → a=b := by
  intro a ha b hb eq
  have mem : j∈([25,28,31,34,37,40,43,46,49,52]:List Nat) := by rcases hj with h|h|h|h|h|h|h|h|h|h <;> simp [h]
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
      (((((((((delta (dirs 25) (rows 25) ^^ delta (dirs 28) (rows 28)) ^^ delta (dirs 31) (rows 31)) ^^ delta (dirs 34) (rows 34)) ^^ delta (dirs 37) (rows 37)) ^^ delta (dirs 40) (rows 40)) ^^ delta (dirs 43) (rows 43)) ^^ delta (dirs 46) (rows 46)) ^^ delta (dirs 49) (rows 49)) ^^ delta (dirs 52) (rows 52)) s := by
  have a : Active 25 := Or.inl rfl
  have b : Active 28 := Or.inr (Or.inl rfl)
  have c : Active 31 := Or.inr (Or.inr (Or.inl rfl))
  have e : Active 34 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have f : Active 37 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have g : Active 40 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have i : Active 43 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have k : Active 46 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have l : Active 49 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have n : Active 52 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))
  simp only [correction,run_append,run_take]
  rw [bank_run 25 a _ _ (hr _ a) _ s (hd _ a),
    bank_run 28 b _ _ (hr _ b) _ _ (data_flip _ _ b (hd _ b)),
    bank_run 31 c _ _ (hr _ c) _ _ (data_flip _ _ c (data_flip _ _ c (hd _ c))),
    bank_run 34 e _ _ (hr _ e) _ _ (data_flip _ _ e (data_flip _ _ e (data_flip _ _ e (hd _ e)))),
    bank_run 37 f _ _ (hr _ f) _ _ (data_flip _ _ f (data_flip _ _ f (data_flip _ _ f (data_flip _ _ f (hd _ f))))),
    bank_run 40 g _ _ (hr _ g) _ _ (data_flip _ _ g (data_flip _ _ g (data_flip _ _ g (data_flip _ _ g (data_flip _ _ g (hd _ g)))))),
    bank_run 43 i _ _ (hr _ i) _ _ (data_flip _ _ i (data_flip _ _ i (data_flip _ _ i (data_flip _ _ i (data_flip _ _ i (data_flip _ _ i (hd _ i))))))),
    bank_run 46 k _ _ (hr _ k) _ _ (data_flip _ _ k (data_flip _ _ k (data_flip _ _ k (data_flip _ _ k (data_flip _ _ k (data_flip _ _ k (data_flip _ _ k (hd _ k)))))))),
    bank_run 49 l _ _ (hr _ l) _ _ (data_flip _ _ l (data_flip _ _ l (data_flip _ _ l (data_flip _ _ l (data_flip _ _ l (data_flip _ _ l (data_flip _ _ l (data_flip _ _ l (hd _ l))))))))),
    bank_run 52 n _ _ (hr _ n) _ _ (data_flip _ _ n (data_flip _ _ n (data_flip _ _ n (data_flip _ _ n (data_flip _ _ n (data_flip _ _ n (data_flip _ _ n (data_flip _ _ n (data_flip _ _ n (hd _ n))))))))))]
  simp only [flip_twice,Bool.xor_assoc]
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
open StockArchiveBanks ExteriorPorts WindowFieldMask
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
private theorem ids {j : Nat} (h : Active j) : j∈bankIds := by
  rcases h with h|h|h|h|h|h|h|h|h|h <;> simp [h,bankIds]
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
  obtain ⟨b,q,e⟩ := StockArchiveBanks.bank_rep _ h
  have eq : addr (8*groupId b+q.val)=addr i := (native_ports b q).trans e
  have bb := b.isLt
  have qq := q.isLt
  unfold Elsewhere at hi
  have k := addr_inj (a:=8*groupId b+q.val) (b:=i) (by unfold groupId;omega) (by omega) eq
  unfold groupId at k
  omega
private theorem host_outside : host∉archives := by
  intro h
  obtain ⟨b,i,e⟩ := StockArchiveBanks.bank_rep _ h
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
end

-- ==== end PrizeTail05e06b1e9 ====

-- ==== begin PrizeTaila22007f05 ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Stair44Outer StockArchiveBanks StairV3Primitives StairPhysicalPhase
def free (q:Wire):Bool:=!(61302683078834518773225434680755157133632473222803583166596865976506739040523029895568267513251196792255204421816894308665018709045412178787043866194374854402116607740113365899388834408881813264026296013592557237293723584032560848235751221052922696553280376677796803509878622975228445380832509722244681682341150631890215483646043686833883810907469310905075598233066735727182494357386884098959478235605293492742515720306851144110350050045724028693235668379661122040980092369643341723350745941868377230356896273059798211482881335257707688375615488:Nat).testBit q
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
theorem occupied:∀(b:Bank)(i:Fin 16),free (siteAt b i)=false:=by decide +kernel
def check (P:Program):Bool:=StairWireCheck.allSites free P
theorem checked {P:Program} (h:check P=true):∀q∈archives,q∉wires P:=by
  intro q hq used
  obtain ⟨b,j,rfl⟩:=StockArchiveBanks.bank_rep q hq
  have safe:=StairWireCheck.allSites_sound free P h _ used
  rw [occupied] at safe
  contradiction
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitFrame
open Arithmetic MappedCompressed Secp256k1 StairField13V3 StairField13V3Clean
open StairConcreteAssembly StairField2V3Replay StairField2V3Delta StairField2V3Couple
open StairField2V3ExitPlanR StairField2V3LastRecX StairPhysicalLayout StairOuterPlacement
open StairLoanExitReachX
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run wires renameProgram

def stockPrefix (k : Nat) : Program := (((exitPieces cp hostPlan k).take 21).map Piece.H).flatten

def Pinned (x : Nat) (ref : State) : Prop := ∃ record, FrameAt x 85 record ∧ AgreeOutside (Δv 87) ref record
def Loan (ref : State) : Prop := ∀q ∈ StairSchedule.exclusiveRoles ++ hosts 87, ref.basis (fieldPlace q) = false

private theorem ofMiddle (k x : Nat) (u : State) (hu : ExitMiddleX k x u) (m : List Bool) :
    Pinned x (run XS21 m u) := by
  obtain ⟨Q, link⟩ := rch21 k x (StairOpenWiring.exitPlans k x) StairOpenWiring.half760
  obtain ⟨old,rel,reachable⟩ := link u u ⟨hu,rfl⟩ m
  exact ⟨_,WindowFieldView.exitFrame 85 x _
    (StairField2V3ExitRec.reach_YE k x _ (reachX_E StairOpenWiring.half760 k x _ reachable)),rel.1⟩

private theorem logicalPinned (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Pinned F.x (run (cut (xps k) 21) m s) := by
  rw [xcut21,run_append]
  exact ofMiddle k F.x _ ⟨s,F,rfl,_,rfl⟩ _

private theorem loanSite (q : Wire) (hq : q∈StairSchedule.exclusiveRoles ++ hosts 87) :
    fieldPlace q ∈ ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap) := by
  rw [hp_group false 0 1 84 (by decide)]
  exact List.mem_map.mpr ⟨q,hq,rfl⟩

private theorem fullCutClean (k : Nat) (parts : StairField13V3Fresh.ExitClean k) :
    CutClean (ExitPre k) (cut (xps k) 21) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap) :=
  parts.groupsBefore (21,0,1,84) (by simp)

private theorem cutLoan {P : Program} {pre : State → Prop}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) : Loan (run P m s) := by
  intro q hq
  exact clean s h m _ (loanSite q hq)

private theorem logicalLoan (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Loan (run (cut (xps k) 21) m s) :=
  cutLoan (fullCutClean k (exitClean_of_planR StairOpenWiring.exitPlans StairOpenWiring.half760 k)) s ⟨F⟩ m

theorem at_cut (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    Pinned F.x (run (stockPrefix k) m s) ∧ Loan (run (stockPrefix k) m s) := by
  have eq := Stair44HostedCut.exit k 21 s ⟨F⟩ m
  change run (stockPrefix k) m s = run (cut (xps k) 21) m s at eq
  rw [eq]
  exact ⟨logicalPinned k F m,logicalLoan k F m⟩

theorem tag (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    (run (stockPrefix k) m s).basis (fieldPlace (base 720)) = false :=
  (at_cut k F m).2 _ (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.WindowExitFrame

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Stair44Outer StockArchiveBanks
open StairV3Primitives StairPhysicalPhase StairPhysicalLayout
set_option maxRecDepth 80000
set_option maxHeartbeats 6000000
attribute [local irreducible] wires
def Clear (P:Program):Prop:=∀q∈archives,q∉wires P
theorem both {A B:Program} (a:Clear A) (b:Clear B):Clear (A++B):=by
  intro q h
  rw [wires_append,Finset.mem_union]
  exact fun hit=>hit.elim (a q h) (b q h)
private theorem rows87 {P:Program} (sub:∀q∈wires P,q∈StairPhysicalPrimitives.rowSitesL 87):
    Clear (renameProgram phaseRelabel P):=by
  have rowFree:∀q∈StairPhysicalPrimitives.rowSitesL 87,free (phaseRelabel q)=true:=by decide +kernel
  intro q h used
  obtain ⟨b,i,rfl⟩:=StockArchiveBanks.bank_rep _ h
  rw [renameProgram_support] at used
  obtain ⟨w,hw,eq⟩:=Finset.mem_image.mp used
  have ok:=rowFree w (sub w hw)
  rw [eq,occupied] at ok
  contradiction
private theorem orientOK:Clear (renameProgram xRelabel (StairV3Primitives.orient 425)):=checked (by decide +kernel)
private theorem packetOK:Clear (renameProgram (OB5.sig 425) (Rolling1588.Integer.packFirst base true 425)):=checked (by decide +kernel)
private theorem unpacketOK:Clear (renameProgram (OB5.sig 425) (Rolling1588.unpackAtTick true 425)):=checked (by decide +kernel)
private theorem moveOK:Clear (phaseBMove):=checked (by decide +kernel)
private theorem restoreOK:Clear (phaseBReturn):=checked (by decide +kernel)
theorem firstPack_free:Clear checkpointPrimitives.firstPack:=by
  exact both (both (both orientOK packetOK) moveOK) (rows87 (StairPhysicalPrimitives.pack_rows 87 (by decide)))
theorem firstUnpack_free:Clear checkpointPrimitives.firstUnpack:=by
  exact both (both (both (rows87 (StairPhysicalPrimitives.unpack_rows 87 (by decide))) restoreOK) unpacketOK) orientOK
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires

def beforeParity := StairSchedule.hostedX ++ StairSchedule.fieldRename (exitLowPrefix hostPlan)
def beforeGroup := StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram ++
  StairSchedule.fieldRename (renameProgram Prefix1590.borrow
    (StairSchedule.reverseLast cp ++ hostedGroup hostPlan false 41 98 2 ++
    StairSchedule.reverseSegment cp 22 12 490 500 ++ hostedGroup hostPlan false 36 96 2 ++
    StairSchedule.reverseSegment cp 32 22 480 490 ++ hostedGroup hostPlan false 30 93 3 ++
    StairSchedule.reverseSegment cp 47 32 465 480 ++ hostedGroup hostPlan false 22 90 3 ++
    StairSchedule.reverseSegment cp 62 47 450 465 ++ hostedGroup hostPlan false 13 85 5 ++
    StairSchedule.reverseSegment cp 87 62 425 450))
def afterGroup := StairSchedule.fieldRename (FourScratchWindow.unprefix ++
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false) (Rolling1588.placedFirstPacket false))
def leading (setup : Program) := setup ++ beforeParity ++ setup ++ beforeGroup
def field (setup group : Program) := leading setup ++ renameProgram fieldEquiv group ++ afterGroup

theorem ordinary : StairHostsSchedule.exitFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (WindowFieldCosts.group false 1 84) := by
  simp only [field,leading,beforeParity,beforeGroup,afterGroup,StairHostsSchedule.exitFieldHosted,
    exitLowSuffix,exitHeadSuffix,WindowFieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : WindowParityCaller.exitFieldHosted cp =
    field WindowFieldParity.setup (WindowFieldCosts.group84 false) := by
  simp only [field,leading,beforeParity,beforeGroup,afterGroup,WindowParityCaller.exitFieldHosted,
    WindowCallerCosts.exitLowSuffix,WindowCallerCosts.exitHeadSuffix,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem prefix_shape (k : Nat) : WindowExitFrame.stockPrefix k =
    exitReferenceOpening ++ leading StairSchedule.paritySetup := by
  simp only [WindowExitFrame.stockPrefix,leading,beforeParity,beforeGroup,exitPieces,List.take_succ_cons,
    List.take_zero,groupSlot,lowCommon,common,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,exitReferenceOpening,exitLowPrefix,exitHeadPrefix,
    hostedEndpoint,fieldRename_append,rename_append,List.append_assoc]

theorem cutAfter (k : Nat) {s : State} (F : ExitFrame k s) (m n : List Bool) :
    let ref := run (leading StairSchedule.paritySetup) n (run exitReferenceOpening m s)
    WindowExitFrame.Pinned F.x ref ∧ WindowExitFrame.Loan ref := by
  have h := WindowExitFrame.at_cut k F (WindowFieldJourney.joinTapes exitReferenceOpening m n)
  rwa [prefix_shape,WindowFieldJourney.joined] at h

theorem hostedGroup (x : Nat) (a r : State) (m : List Bool)
    (rows : StockArchiveBanks.Bank → Nat)
    (labels : ∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (StockArchiveBanks.tick b) x p (rows b))
    (initial : WindowFieldMask.Fits (fieldRows rows) (WindowFieldJourney.initialCode false) a r)
    (pinned : WindowExitFrame.Pinned x r) (loan : WindowExitFrame.Loan r) :
    WindowFieldMask.Fits (fieldRows rows)
      (WindowFieldJourney.finalCode false (WindowFieldJourney.plan false) (WindowFieldJourney.initialCode false))
      (run (renameProgram fieldEquiv (WindowFieldCosts.group84 false)) m a)
      (run (renameProgram fieldEquiv (WindowFieldCosts.group false 1 84))
        (WindowFieldJourney.referenceTape false (WindowFieldJourney.plan false) m) r) := by
  obtain ⟨record,pin,agreement⟩ := pinned
  have ids : ∀j∈WindowFieldMask.bankIds,fieldRows rows j<63145 := by
    intro j hj
    obtain ⟨b,rfl⟩ := idAt j hj
    rw [rowsAt]
    exact (labels b).1
  have chronological : ∀j∈WindowFieldMask.bankIds, ArchiveStockRows.Chronology (5*j-5) x p (fieldRows rows j) := by
    intro j hj
    obtain ⟨b,rfl⟩ := idAt j hj
    rw [rowsAt]
    have times : ∀k : StockArchiveBanks.Bank, 5*groupId k-5=StockArchiveBanks.tick k := by decide +kernel
    rw [times]
    exact (labels b).2
  apply hosted
  exact WindowFieldView.caller false x (fieldRows rows) ids chronological (pullState fieldEquiv a) r record m
    (fitsPull fieldEquiv fieldEquiv.injective fieldFix initial) pin agreement
    (loan _ (by decide +kernel)) loan
end ECDSAAdd.Entrant.StairPacket.WindowExitPieces

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 35000
theorem clearSafe:Clear (FourScratchWindow.clearProgram):=checked (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 35000
theorem unprefixSafe:Clear (FourScratchWindow.unprefix):=checked (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5 StairConcreteAssembly Stair44Outer
set_option maxRecDepth 80000
set_option maxHeartbeats 6000000
private theorem wipeOK:Clear (skywalkArithmeticClear base):=checked (by decide +kernel)
private theorem tickOK:Clear (renameProgram (sig 511) tickR):=checked (by decide +kernel)
private theorem lastBackOK:Clear (renameProgram (sig 510) (Rolling1588.unpackAtTick false 510 ++ InverseFive23.candidate15)):=checked (by decide +kernel)
private theorem mergedOK:Clear (Six505.merged6):=checked (by decide +kernel)
private theorem packedOK:Clear (Six505.packP false):=checked (by decide +kernel)
private theorem afterOK:Clear (ForwardSixPlacement.after false):=checked (by decide +kernel)
theorem reverseEnd_free:Clear reverseEnd:=both (both wipeOK tickOK) lastBackOK
theorem forwardEnd_free:Clear forwardEnd:=both (both (both mergedOK packedOK) afterOK) wipeOK
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks StairOuterPlacement
theorem mapped {P:Program} (f:Wire→Wire) (inj:Function.Injective f) (fix:Fixed f) (clear:Clear P):Clear (renameProgram f P):=by
  intro q hit used
  rw [renameProgram_support] at used
  obtain ⟨v,use,eq⟩:=Finset.mem_image.mp used
  obtain ⟨b,i,rfl⟩:=StockArchiveBanks.bank_rep q hit
  have same:=inj (eq.trans (fix b i).symm)
  exact clear _ ((StockArchiveBanks.mem b i)) (same ▸ use)
theorem fieldMapped {P:Program} (c:Clear P):Clear (renameProgram fieldEquiv P):=mapped _ fieldEquiv.injective fieldFix c
def noBorrow:Equiv.Perm Wire:=⟨fun q=>Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host (HostOB5.hostSwap q),
  fun q=>HostOB5.hostSwap (Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host q),
  fun q=>by simp only [Equiv.swap_apply_self,HostOB5.hostSwap_invol],fun q=>by simp only [HostOB5.hostSwap_invol,Equiv.swap_apply_self]⟩
theorem noBorrowFixed:Fixed noBorrow:=by unfold Fixed;decide +kernel
theorem fieldRename_free {P:Program} (c:Clear P):Clear (StairSchedule.fieldRename P):=by
  unfold StairSchedule.fieldRename StairSchedule.parityRename
  rw [renameProgram_comp]
  exact mapped _ noBorrow.injective noBorrowFixed c
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StockArchiveBanks StairPhysicalLayout StairPhysicalPrimitives
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
theorem live_rows (B:Nat) (h:B∈budgets):∀q∈rowSitesL B,free q=true:=by
  have ok:budgets.all (fun b=>(rowSitesL b).all free)=true:=by decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp ok B h)
theorem of_rows {B:Nat} (h:B∈budgets) {P:Program} (sub:∀q∈wires P,q∈rowSitesL B):Clear P:=by
  intro q hit used
  obtain ⟨b,i,rfl⟩:=StockArchiveBanks.bank_rep q hit
  have pass:=live_rows B h _ (sub _ used)
  rw [occupied] at pass
  contradiction
theorem packFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.pack B):=of_rows h (pack_rows B h)
theorem unpackFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.unpack B):=of_rows h (unpack_rows B h)
theorem tfFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.tickForward (startFor B)):=of_rows h (tickForward_rows B h)
theorem trFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.tickReverse (startFor B)):=of_rows h (tickReverse_rows B h)
theorem mfFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.middleForward (startFor B+1) (endFor B-startFor B-1)):=of_rows h (middleForward_rows B h)
theorem mrFree (B:Nat) (h:B∈budgets):Clear (checkpointPrimitives.middleReverse (startFor B+1) (StairPhysicalPrimitivesFix505.reverseEnd B-startFor B-1)):=
  of_rows h (StairPhysicalPrimitivesFix505.middleReverseFix_rows B h)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StockArchiveBanks StairArchiveInactive
open StairConcreteAssembly StairHostsSchedule StairPhysicalLayout StairLoanGroupSupport
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] wires renameProgram
def src (j:Nat) (b:Bank) (i:Fin 16):Wire:=(shifted (Placement5.pi j)).symm (OB5.sig 511 (siteAt b i))
private def past (q:Wire):Bool:=(126775176741751802172534374612801623113655154107519818739362101347847539651850299900170773321862711354777495908003543032104099924651718855905263309643262332217634660183554185202144971264893654204745026496662452708307024209700285685290779590922023760297029502421797612905695170713802829736761900279759222157698263652867535809274357967389401062846791346776399219215885054332714801480100203292786688:Nat).testBit q
private theorem fixedSources:∀j∈List.range' 85 17,∀(b:Bank)(i:Fin 16),src j b i=src 85 b i:=by decide +kernel
private theorem tagged:∀(b:Bank)(i:Fin 16),past (src 85 b i)=true:=by decide +kernel
private theorem globals:∀q∈[base 2400,base 2409,base 2410]++Q6EndpointCell.ids.map base,past q=false:=by decide +kernel
private theorem recent:∀j∈List.range' 85 17,∀i:Fin 10,past (History5.historyMap base (5*j) i)=false:=by decide +kernel
private theorem miss (j:Nat) (hj:j∈List.range' 85 17) (b:Bank) (i:Fin 16):src j b i∉cover j:=by
  intro hit
  have yes:=tagged b i
  rw [←fixedSources j hj b i] at yes
  rcases List.mem_append.mp hit with g|hist
  · rw [globals _ g] at yes;contradiction
  · obtain ⟨k,_,eq⟩:=List.mem_map.mp hist
    rw [←eq,recent j hj k] at yes;contradiction

private theorem packetFree (d:Bool) (j:Nat) (lo:85≤j) (hi:j<102):Clear (renameProgram (OB5.sig 511) (Rolling1588.packet d j)):=by
  intro q hit use
  obtain ⟨b,i,rfl⟩:=StockArchiveBanks.bank_rep q hit
  rw [renameProgram_support] at use
  obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp use
  rw [Rolling1588.packet,renameProgram_support] at hv
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hv
  have geom:src j b i=w:=by simp only [src,←eq,OB5.sig_invol 511 (by decide),Equiv.symm_apply_apply]
  apply miss j (List.mem_range'_1.mpr (by omega)) b i
  rw [geom]
  exact cover_read j (Rolling1588.basePacket_readSites_support d j hi hw)

private theorem regular (d:Bool) (j n:Nat) (lo:85≤j) (hi:j+n≤102):Clear (renameProgram (OB5.sig 511) (Rolling1588.groups d j n)):=by
  induction n generalizing j with
  | zero=>intro q _;simp [Rolling1588.groups,PacketSequence.program,renameProgram,wires]
  | succ n ih=>
    have a:=packetFree d j lo (by omega)
    have b:=ih (j+1) (by omega) (by omega)
    cases d <;> simp only [Rolling1588.groups,PacketSequence.program,if_true,if_false,Bool.false_eq_true,Six505.rename_append]
    · exact both b a
    · exact both a b

theorem groups (d:Bool) (k j n:Nat) (lo:85≤j) (hi:j+n≤102) (dk:k≤68)
    (safe:∀q∈hostPlan.group d k j n,free q=true):Clear (hostedGroup hostPlan d k j n):=by
  have roles:∀q∈StairSchedule.exclusiveRoles,free q=true:=by decide +kernel
  intro q hit used
  obtain ⟨b,i,rfl⟩:=StockArchiveBanks.bank_rep q hit
  obtain host|role|inner:=StairWireCheck.rebindMany_support _ _ _ _ used
  · have ok:=safe _ host;rw [occupied] at ok;contradiction
  · have ok:=roles _ (List.mem_of_mem_drop role);rw [occupied] at ok;contradiction
  · exact regular d j n lo hi _ ((StockArchiveBanks.mem b i)) (placedGroups_sub d k dk j n inner)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment425Ori:Clear (checkpointPrimitives.orient 450):=checked (by decide +kernel)
private theorem segment425P:Clear (renameProgram (OB5.sig 450) (Rolling1588.Integer.packFirst base true 450)):=checked (by decide +kernel)
private theorem segment425U:Clear (renameProgram (OB5.sig 450) (Rolling1588.unpackAtTick true 450)):=checked (by decide +kernel)
theorem forward425:Clear (StairSchedule.forwardSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 87 (by decide)) (tfFree 87 (by decide))) (mfFree 87 (by decide))) segment425Ori) segment425P) (packFree 62 (by decide))
theorem reverse425:Clear (StairSchedule.reverseSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 62 (by decide)) segment425U) segment425Ori) (mrFree 87 (by decide))) (trFree 87 (by decide))) (packFree 87 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment450Ori:Clear (checkpointPrimitives.orient 465):=checked (by decide +kernel)
private theorem segment450P:Clear (renameProgram (OB5.sig 465) (Rolling1588.Integer.packFirst base true 465)):=checked (by decide +kernel)
private theorem segment450U:Clear (renameProgram (OB5.sig 465) (Rolling1588.unpackAtTick true 465)):=checked (by decide +kernel)
theorem forward450:Clear (StairSchedule.forwardSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 62 (by decide)) (tfFree 62 (by decide))) (mfFree 62 (by decide))) segment450Ori) segment450P) (packFree 47 (by decide))
theorem reverse450:Clear (StairSchedule.reverseSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 47 (by decide)) segment450U) segment450Ori) (mrFree 62 (by decide))) (trFree 62 (by decide))) (packFree 62 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment465Ori:Clear (checkpointPrimitives.orient 480):=checked (by decide +kernel)
private theorem segment465P:Clear (renameProgram (OB5.sig 480) (Rolling1588.Integer.packFirst base true 480)):=checked (by decide +kernel)
private theorem segment465U:Clear (renameProgram (OB5.sig 480) (Rolling1588.unpackAtTick true 480)):=checked (by decide +kernel)
theorem forward465:Clear (StairSchedule.forwardSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 47 (by decide)) (tfFree 47 (by decide))) (mfFree 47 (by decide))) segment465Ori) segment465P) (packFree 32 (by decide))
theorem reverse465:Clear (StairSchedule.reverseSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 32 (by decide)) segment465U) segment465Ori) (mrFree 47 (by decide))) (trFree 47 (by decide))) (packFree 47 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment480Ori:Clear (checkpointPrimitives.orient 490):=checked (by decide +kernel)
private theorem segment480P:Clear (renameProgram (OB5.sig 490) (Rolling1588.Integer.packFirst base true 490)):=checked (by decide +kernel)
private theorem segment480U:Clear (renameProgram (OB5.sig 490) (Rolling1588.unpackAtTick true 490)):=checked (by decide +kernel)
theorem forward480:Clear (StairSchedule.forwardSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 32 (by decide)) (tfFree 32 (by decide))) (mfFree 32 (by decide))) segment480Ori) segment480P) (packFree 22 (by decide))
theorem reverse480:Clear (StairSchedule.reverseSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 22 (by decide)) segment480U) segment480Ori) (mrFree 32 (by decide))) (trFree 32 (by decide))) (packFree 32 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment490Ori:Clear (checkpointPrimitives.orient 500):=checked (by decide +kernel)
private theorem segment490P:Clear (renameProgram (OB5.sig 500) (Rolling1588.Integer.packFirst base true 500)):=checked (by decide +kernel)
private theorem segment490U:Clear (renameProgram (OB5.sig 500) (Rolling1588.unpackAtTick true 500)):=checked (by decide +kernel)
theorem forward490:Clear (StairSchedule.forwardSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 22 (by decide)) (tfFree 22 (by decide))) (mfFree 22 (by decide))) segment490Ori) segment490P) (packFree 12 (by decide))
theorem reverse490:Clear (StairSchedule.reverseSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 12 (by decide)) segment490U) segment490Ori) (mrFree 22 (by decide))) (trFree 22 (by decide))) (packFree 22 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5 StairConcreteAssembly Stair44Outer
open StairPhysicalLayout StairTerminalV3
set_option maxRecDepth 80000
set_option maxHeartbeats 4800000
attribute [local irreducible] wires renameProgram
theorem terminalFixed:Fixed terminalPerm:=by unfold Fixed;decide +kernel
private theorem w:Clear (skywalkArithmeticClear base):=checked (by decide +kernel)
private theorem f:Clear Six505.merged6:=checked (by decide +kernel)
private theorem pk:Clear (Six505.packP true):=checked (by decide +kernel)
private theorem a:Clear (ForwardSixPlacement.after true):=checked (by decide +kernel)
private theorem t:Clear (renameProgram (sig 511) tickR):=checked (by decide +kernel)
private theorem k:Clear (renameProgram (sig 510) (Rolling1588.unpackAtTick true 510 ++ InverseFive23.candidate15)):=checked (by decide +kernel)
theorem forwardTerm:Clear checkpointPrimitives.forwardTerminal:=
  mapped _ terminalPerm.injective terminalFixed (both (both (both f pk) a) w)
theorem reverseTerm:Clear checkpointPrimitives.reverseTerminal:=
  mapped _ terminalPerm.injective terminalFixed (both w (both t k))
theorem forwardLast:Clear (StairSchedule.forwardLast checkpointPrimitives):=
  both (both (both (unpackFree 12 (by decide)) (tfFree 12 (by decide))) (mfFree 12 (by decide))) forwardTerm
theorem reverseLast:Clear (StairSchedule.reverseLast checkpointPrimitives):=
  both (both (both reverseTerm (mrFree 12 (by decide))) (trFree 12 (by decide))) (packFree 12 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitStages
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates WindowMiddlePieces ExteriorPorts WindowExitPieces
open WindowFieldMask WindowFieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount

def endF := renameProgram phaseHost Stair44Outer.forwardEnd
def unpack := renameProgram phaseHost checkpointPrimitives.firstUnpack
def beginW := opening false 234 ++ endF
def beginR := original false 234 ++ endF

theorem refBegin : beginR = Stair44Kernel.mulLead := by
  simp only [beginR,original,endF,Stair44Kernel.mulLead,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]

theorem begin_pair (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    ∃n, Paired false F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening false 234
  let B := original false 234
  let t := m.drop (measurementCount A)
  refine ⟨joinTapes B m t,?_⟩
  rw [beginW,beginR,joined,run_append,run_take]
  apply pairUnpull phaseHost phaseFix
  rw [endF,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  exact (WindowStartStates.multiplication k F m).through _ forwardEnd_free _

theorem begin_record (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    run beginR m s = run StairField2V3Replay.exitReferenceOpening m s := by
  rw [refBegin]
  exact WindowStockHead.leadM k F m

def newP := (beginW ++ WindowParityCaller.exitFieldHosted checkpointPrimitives) ++ unpack
def oldP := (beginR ++ StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan) ++ unpack

theorem newShape : WindowMiddleContract.mulHead = newP := by
  simp only [WindowMiddleContract.mulHead,WindowKernelPrograms.mulBefore,newP,beginW,opening,endF,unpack,
    Six505.rename_append,List.append_assoc]
theorem oldShape : WindowMiddleContract.oldMulHead = oldP := by
  rw [oldP,refBegin]
  rfl

end ECDSAAdd.Entrant.StairPacket.WindowExitStages

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem viaFree {P : Program} (touch : ∀q∈wires P,free q=true) : Clear P := by
  intro q h used
  obtain ⟨b,i,rfl⟩ := StockArchiveBanks.bank_rep q h
  exact Bool.noConfusion ((occupied b i).symm.trans (touch _ used))

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitReplay
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates WindowMiddlePieces ExteriorPorts WindowExitPieces
open WindowFieldMask WindowFieldJourney WindowExitStages
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] run measurementCount wires

def leadingOK : Prop := ∀ (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (a r : State) (m : List Bool),
  Paired false x a r rows → ∃n, Paired false x (run (leading WindowFieldParity.setup) m a)
    (run (leading StairSchedule.paritySetup) n r) rows

abbrev C0 := initialCode false
abbrev C1 := finalCode false (plan false) C0
def gW := renameProgram fieldEquiv (WindowFieldCosts.group84 false)
def gR := renameProgram fieldEquiv (WindowFieldCosts.group false 1 84)

def RStart (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (s : State) (a r : State) : Prop :=
  Paired false x a r rows ∧ ∃m, r = run StairField2V3Replay.exitReferenceOpening m s
def RCut (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (a r : State) : Prop :=
  Paired false x a r rows ∧ WindowExitFrame.Pinned x r ∧ WindowExitFrame.Loan r

private theorem beginRel (k : Nat) {s : State} (F : ExitFrame k s) :
    Relates beginW beginR (fun a r=>a=s ∧ r=s) (RStart F.x (StockRowVector.rows F.x p) s) := by
  rintro a r ⟨rfl,eq⟩ m
  subst r
  obtain ⟨n,rel⟩ := begin_pair k F m
  exact ⟨n,rel,n,begin_record k F n⟩

private theorem leadingRel (ok : leadingOK) (k : Nat) {s : State} (F : ExitFrame k s) (rows : StockArchiveBanks.Bank → Nat) :
    Relates (leading WindowFieldParity.setup) (leading StairSchedule.paritySetup)
      (RStart F.x rows s) (RCut F.x rows) := by
  rintro a r ⟨pair,u,rfl⟩ m
  obtain ⟨n,h⟩ := ok _ _ _ _ m pair
  exact ⟨n,h,cutAfter k F u n⟩

private theorem windowRel (x : Nat) (rows : StockArchiveBanks.Bank → Nat) :
    Relates gW gR (RCut x rows) (Fits (fieldRows rows) C1) := by
  rintro a r ⟨pair,pin,loan⟩ m
  exact ⟨_,hostedGroup x a r m rows pair.labels (fits pair) pin loan⟩

private theorem template (A P G T U : Program) :
    (A ++ ((P ++ G) ++ T)) ++ U = (((A ++ P) ++ G) ++ (T ++ U)) := by
  simp only [List.append_assoc]

private theorem newPath : WindowMiddleContract.mulHead =
    (((beginW ++ leading WindowFieldParity.setup) ++ gW) ++ (afterGroup ++ unpack)) := by
  rw [newShape,newP,corrected]
  exact template _ _ _ _ _
private theorem oldPath : WindowMiddleContract.oldMulHead =
    (((beginR ++ leading StairSchedule.paritySetup) ++ gR) ++ (afterGroup ++ unpack)) := by
  rw [oldShape,oldP,ordinary]
  exact template _ _ _ _ _

theorem exit (leadingLaw : leadingOK) (endClear : Clear (afterGroup ++ unpack)) : WindowMiddleContract.exit := by
  intro k s F m
  have keep := pass (rows:=fieldRows (StockRowVector.rows F.x p)) (cs:=C1) (P:=afterGroup ++ unpack) (fun q h=>endClear q ((whole_iff q).mp h))
  have total := compose (compose (compose (beginRel k F) (leadingRel leadingLaw k F _)) (windowRel _ _)) keep
  obtain ⟨n,out⟩ := total s s ⟨rfl,rfl⟩ m
  rw [←newPath,←oldPath] at out
  have paired := fitsPull phaseHost phaseHost.injective phaseFix out
  have native := WindowEndBytes.mul_native k F n
  exact ⟨n,pairFinished paired native.ids native.bytes⟩
end ECDSAAdd.Entrant.StairPacket.WindowExitReplay

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

private theorem convert {P Q : Program}
    (env : wires P ⊆ wires Q ∪ StairBoundaryLoan.converterHosts.toFinset)
    (rec : wires Q ⊆ StairBoundaryLoan.converterLayout760.wires.toFinset) : Clear P := by
  have ok : (StairBoundaryLoan.converterLayout760.wires ++ StairBoundaryLoan.converterHosts).all free=true := by decide +kernel
  apply viaFree
  intro q hq
  apply List.all_eq_true.mp ok
  rcases Finset.mem_union.mp (env hq) with l|r
  · exact List.mem_append_left _ (List.mem_toFinset.mp (rec l))
  · exact List.mem_append_right _ (List.mem_toFinset.mp r)

theorem canon : Clear StairConcrete.bestLoans.canon :=
  convert StairBoundaryLoan.canon760Loan_envelope (by
    rw [StairBoundaryLoan.canon760_eq]
    exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).2)
theorem center : Clear StairConcrete.bestLoans.center :=
  convert StairBoundaryLoan.center760Loan_envelope (by
    rw [StairBoundaryLoan.center760_eq]
    exact (HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).1)

theorem copy : Clear HalfFieldOB5.copyN := checked (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem mulEndpoint : Clear (hostedEndpoint hostPlan false 68) := by
  have ok : StairSiteEasy.multEndL.all (fun q=>free (OB5.sig 511 q))=true := by decide +kernel
  apply viaFree
  intro q h
  have e : StairConcrete.bestLoans.endPacket false 68=StairEndpointLoan44.endPacket760Loan44 false := by
    simp only [StairConcrete.bestLoans,StairConcrete.endPacket,Bool.false_eq_true,if_false,if_true]
  rw [hostedEndpoint,StairSchedule.placedEndPacket,e,renameProgram_support] at h
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
  exact List.all_eq_true.mp ok q (StairSiteEasy.endPacket760_false_mem q (StairEndpointLoan44.endPacket760Loan44_support hq))

private def outward (q : Wire) := OB5.sig 511 (Equiv.swap (base 760) (base 717) (shifted Placement5.pi0 q))
private def inner (q : Wire) := Equiv.swap (base 719) (base 510) q

theorem divEndpoint : Clear (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint) := by
  have ok : DecoderBiasReuse.fixedLayout.wires.all (fun q=>free (outward (inner q)))=true := by decide +kernel
  apply viaFree
  intro q h
  rw [renameProgram_support,StairConcrete.bestLoans_divEndpoint] at h
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
  unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hy
  rw [renameProgram_support] at hy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
  rw [renameProgram_support] at ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
  rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hb) with h|h
  · rw [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl <;> decide +kernel
  · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
    rw [wires_append,Finset.mem_union] at hz
    rcases hz with hz|hz
    · exact List.all_eq_true.mp ok z (List.mem_toFinset.mp (CompareDecoder.support (CompareDecoder.BoundaryLoan.Inclusion.cellDecoderLoan_sub hz)))
    · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
      rw [Finset.mem_singleton] at hc
      rw [hc]
      decide +kernel

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel StairWireCheck
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem firstNo : ∀(b : Bank)(i : Fin 16), fpSup (siteAt b i)=false := by decide +kernel
theorem noRole : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairSchedule.exclusiveRoles := by decide +kernel
theorem noHost : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairPhysicalLayout.hosts 87 := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitClear
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime StairConcreteAssembly
open StockArchiveBanks WindowExitPieces WindowExitStages ExteriorPorts StairField13V3
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires run measurementCount

theorem renameClear (fn : Wire → Wire) (inj : Function.Injective fn) (fixed : Fixed fn) {P : Program}
    (clear : Clear P) : Clear (renameProgram fn P) := by
  intro q hq used
  rw [renameProgram_support] at used
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp used
  by_cases orig : r∈StockArchiveBanks.archives
  · exact clear r orig hr
  · exact archive_pre inj fixed r orig hq

theorem fieldClear {P : Program} (clear : Clear P) : Clear (StairSchedule.fieldRename P) := by
  rw [fieldRename_eq]
  exact renameClear fieldMap fieldMap_injective (by unfold Fixed; decide +kernel) clear

theorem after (f : Clear FourScratchWindow.unprefix)
    (g : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
        (Rolling1588.placedFirstPacket false))) : Clear (afterGroup ++ unpack) :=
  both (fieldClear (both f g)) (renameClear phaseHost phaseHost.injective phaseFix firstUnpack_free)

private theorem pass {d x rows P} (clear : Clear P) :
    Relates P P (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,pair.through P clear m⟩

private theorem parity {d x rows} : Relates WindowFieldParity.setup StairSchedule.paritySetup
    (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,WindowFieldParity.setup_through pair m m⟩

theorem leading (pre : Clear beforeParity) (next : Clear beforeGroup) : WindowExitReplay.leadingOK := by
  intro x rows a r m pair
  exact compose (compose (compose parity (pass pre)) parity) (pass next) a r pair m

theorem exit (a : Clear beforeParity) (b : Clear beforeGroup) (f : Clear FourScratchWindow.unprefix)
    (g : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
        (Rolling1588.placedFirstPacket false))) : WindowMiddleContract.exit :=
  WindowExitReplay.exit (leading a b) (after f g)
end ECDSAAdd.Entrant.StairPacket.WindowExitClear

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel StairWireCheck
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

private theorem table (d : Bool) : allSites fpSup (Rolling1588.placedFirstPacket d)=true := by
  cases d
  · exact passSup_false
  · exact passSup_true

private theorem exclude (q : Wire) (h : q∈StockArchiveBanks.archives) :
    q∉StairPhysicalLayout.hosts 87 ∧ q∉StairSchedule.exclusiveRoles ∧ fpSup q=false := by
  obtain ⟨b,i,rfl⟩ := StockArchiveBanks.bank_rep q h
  exact ⟨noHost b i,noRole b i,firstNo b i⟩

private theorem rebind {P : Program} (hs : List Wire) (eq : hs=StairPhysicalLayout.hosts 87)
    (ok : allSites fpSup P=true) : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles hs P) := by
  intro q h used
  have neg := exclude q h
  rcases rebindMany_support StairSchedule.exclusiveRoles hs P q used with host | role | orig
  · exact neg.1 (eq ▸ host)
  · exact neg.2.1 role
  · exact Bool.noConfusion (neg.2.2.symm.trans (allSites_sound fpSup P ok q orig))

theorem first (d : Bool) : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (Rolling1588.placedFirstPacket d)) :=
  rebind (hostPlan.firstPacket d) rfl (table d)

end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairHostsSchedule ExteriorPorts
open StockArchiveBanks StairFirstPacketKernel
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem tail (other : Clear (hostedGroup hostPlan true 43 100 2)) : Clear (entryTailSuffix hostPlan) :=
  both (both (both other divEndpoint) copy) canon
theorem head (other : Clear (hostedGroup hostPlan false 43 100 2)) : Clear (exitHeadPrefix hostPlan) :=
  both (both (both center copy) mulEndpoint) other
end ECDSAAdd.Entrant.StairPacket.WindowExteriorFixed

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitOuter
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts WindowExitPieces
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires

theorem hostedX : Clear StairSchedule.hostedX := checked (by decide +kernel)

theorem ordinaryGroup (d : Bool) (k j n : Nat) (start : 85≤j) (bound : j+n≤102) (budget : k≤68)
    (tab : (hostPlan.group d k j n).all free=true) : Clear (hostedGroup hostPlan d k j n) :=
  groups d k j n start bound budget (List.all_eq_true.mp tab)

theorem other (d : Bool) : Clear (hostedGroup hostPlan d 43 100 2) :=
  ordinaryGroup d 43 100 2 (by decide) (by decide) (by decide) (by cases d <;> decide +kernel)

theorem pre : Clear beforeParity := by
  apply both hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  -- The outer field placement is applied once more by the caller.
  exact WindowExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel) (WindowExteriorFixed.head (other false))

theorem endPart : Clear (afterGroup ++ WindowExitStages.unpack) :=
  WindowExitClear.after unprefixSafe (WindowExteriorFixed.first false)
end ECDSAAdd.Entrant.StairPacket.WindowExitOuter

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowExitReady
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts WindowExitPieces WindowExitOuter
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires

theorem before : Clear beforeGroup := by
  apply both (both hostedX (fieldRename_free clearSafe))
  rw [placedShape]
  apply fieldMapped
  apply both _ reverse425
  apply both _ (ordinaryGroup false 13 85 5 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse450
  apply both _ (ordinaryGroup false 22 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse465
  apply both _ (ordinaryGroup false 30 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse480
  apply both _ (ordinaryGroup false 36 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ reverse490
  apply both _ (ordinaryGroup false 41 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
  exact reverseLast

theorem exit : WindowMiddleContract.exit :=
  WindowExitReplay.exit (WindowExitClear.leading pre before) endPart
end ECDSAAdd.Entrant.StairPacket.WindowExitReady

end
end
-- ==== end PrizeTaila22007f05 ====

-- ==== begin Main ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3Seg StairField2V3LastRecX StairField2V3Delta
open StairField2V3EntryPlanR StairOpenWiring StairOuterPlacement StairPhysicalLayout
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] run measurementCount

private theorem pin (x:Nat) (r record:State) (h:RowRelEn x 87 (R0++firstPkt) r record):
    FrameAt x 1 record ∧ AgreeOutside (Δv 87) r record:=by
  obtain ⟨rel,root,tape,⟨F,fx⟩,reach⟩:=h
  have pinned:=g_first root F tape
  rw [fx] at pinned
  exact ⟨reach.symm ▸ pinned.1,rel.1⟩

def stockPrefix:Program:=(((entryPieces cp hostPlan).take 3).map Piece.H).flatten
def Pinned (x:Nat) (ref:State):Prop:=∃record,FrameAt x 1 record ∧ AgreeOutside (Δv 87) ref record
def Loan (ref : State) : Prop := ∀q ∈ StairSchedule.exclusiveRoles ++ hosts 87, ref.basis (fieldPlace q) = false

private theorem loanSite (q : Wire) (hq : q∈StairSchedule.exclusiveRoles ++ hosts 87) :
    fieldPlace q ∈ ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap) := by
  rw [hp_group true 0 1 84 (by decide)]
  exact List.mem_map.mpr ⟨q,hq,rfl⟩

private theorem fullCutClean (parts:StairField13V3Fresh.EntryClean):
    CutClean EntryPre (cut eps 3) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap):=
  parts.groupsBefore (3,0,1,84) (by simp)
private theorem cutLoan {P : Program} {pre : State → Prop}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) : Loan (run P m s) := by
  intro q hq
  exact clean s h m _ (loanSite q hq)


theorem at_cut {s:State} (F:EntryFrame s) (m:List Bool):Pinned F.x (run stockPrefix m s) ∧ Loan (run stockPrefix m s):=by
  have eq:=Stair44HostedCut.entry 3 s ⟨F⟩ m
  change run stockPrefix m s=run (cut eps 3) m s at eq
  rw [eq]
  refine ⟨?_,cutLoan (fullCutClean (entryClean_of_planR entryPlans half760)) s ⟨F⟩ m⟩
  obtain ⟨Q,step⟩:=ern3 F.x (entryPlans F.x)
  obtain ⟨n,h⟩:=step s s ⟨⟨F,rfl⟩,rfl⟩ m
  rw [ecut3]
  exact ⟨_,pin _ _ _ h⟩
theorem tag {s:State} (F:EntryFrame s) (m:List Bool):
    (run stockPrefix m s).basis (fieldPlace (base 720))=false:=(at_cut F m).2 _ (by decide +kernel)
end ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowReturningBytes
open Arithmetic MappedCompressed Secp256k1 FrontierEntry1591Field StockArchiveBanks ExteriorPorts
open WindowParityDirty WindowFieldParity
set_option maxRecDepth 6000
attribute [local irreducible] run measurementCount wires
def Keeps (P : Program) : Prop := ∀(s : State) (m : List Bool) (b : Bank) (i : Fin 16),
  (run P m s).basis (siteAt b i) = s.basis (siteAt b i)

theorem untouched {P : Program} (clear : Clear P) : Keeps P :=
  fun s m b i=>run_preserves_outside P m s _ (clear _ (StockArchiveBanks.mem b i))

theorem both {P Q : Program} (hp : Keeps P) (hq : Keeps Q) : Keeps (P ++ Q) := by
  intro s m b i
  rw [run_append]
  exact (hq _ _ _ _).trans (hp _ _ _ _)

theorem parity : Keeps StairSchedule.paritySetup := by
  intro s m b i
  have outside : ∀(v : Bank)(j : Fin 16), siteAt v j≠host := by decide +kernel
  have eq : run StairSchedule.paritySetup m s = flip host (stockParity s) s :=
    ParityHost5.setup_run controls host s m host_not_controls
  rw [eq]
  exact at_other _ _ _ _ (outside b i)

theorem nativeBack {d : Bool} {rows : Bank → Nat} {r m P} (hp : Keeps P)
    (old : ∀b,nativeAt d b (rows b) (run P m r)) : ∀b,nativeAt d b (rows b) r :=
  fun b i=>(hp r m b i).symm.trans (old b i)

theorem nativeUnpull {d : Bool} {rows : Bank → Nat} {r} (old : ∀b,nativeAt d b (rows b) (pullState Rolling1588Lifetime.phaseHost r)) :
    ∀b,nativeAt d b (rows b) r := by
  intro b i
  have v := old b i
  change r.basis (Rolling1588Lifetime.phaseHost (siteAt b i))=_ at v
  rwa [host_ports] at v
end ECDSAAdd.Entrant.StairPacket.WindowReturningBytes

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField2V3Seg
open WindowFieldMask WindowFieldJourney WindowFieldCosts ExteriorPorts StockArchiveBanks
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
attribute [local irreducible] run measurementCount
theorem history {x rows} (labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b)):
    (∀j∈bankIds,fieldRows rows j<63145) ∧
    (∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x p (fieldRows rows j)):=by
  have times:∀b:Bank,5*groupId b-5=tick b:=by decide +kernel
  constructor <;> intro j hj <;> obtain ⟨b,rfl⟩:=idAt _ hj <;> rw [rowsAt]
  · exact (labels b).1
  · rw [times];exact (labels b).2

private theorem entered (x:Nat) (rows:Bank→Nat) (a ref:State) (m:List Bool)
    (same:Paired true x a ref rows) (pin:Pinned x ref) (loans:Loan ref):
    Fits (fieldRows rows) (finalCode true (plan true) (initialCode true))
      (run (renameProgram fieldEquiv (group84 true)) m a)
      (run (renameProgram fieldEquiv (group true 1 84)) (referenceTape true (plan true) m) ref):=by
  obtain ⟨record,frame,agree⟩:=pin
  obtain ⟨bound,trace⟩:=history same.labels
  apply hosted
  exact WindowFieldView.caller true x _ bound trace (pullState fieldEquiv a) ref record m
    (fitsPull fieldEquiv fieldEquiv.injective fieldFix (fits same)) frame agree
    (loans _ (by decide +kernel)) loans

theorem group_run {s:State} (F:EntryFrame s) (before m:List Bool) (a:State) (rows:Bank→Nat)
    (same:Paired true F.x a (run stockPrefix before s) rows):
    Fits (fieldRows rows) (finalCode true (plan true) (initialCode true))
      (run (renameProgram fieldEquiv (group84 true)) m a)
      (run (renameProgram fieldEquiv (group true 1 84)) (referenceTape true (plan true) m) (run stockPrefix before s)):=by
  have h:=at_cut F before
  exact entered F.x rows a _ m same h.1 h.2
end ECDSAAdd.Entrant.StairPacket.ExteriorEntryCut

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowReturningTail
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StockArchiveBanks
open WindowReturningBytes WindowFieldMask WindowFieldJourney ExteriorPorts
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
attribute [local irreducible] run measurementCount wires

def program (pre between post setup : Program) := (((pre ++ setup) ++ between) ++ setup) ++ post
private theorem keepTail {pre between post : Program} (hp : Clear pre) (hb : Clear between) (ht : Clear post) :
    Keeps (program pre between post StairSchedule.paritySetup) :=
  WindowReturningBytes.both (WindowReturningBytes.both (WindowReturningBytes.both
    (WindowReturningBytes.both (untouched hp) WindowReturningBytes.parity) (untouched hb)) WindowReturningBytes.parity) (untouched ht)

private theorem stable {d x rows P} (c : Clear P) :
    Relates P P (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,pair.through P c m⟩

private theorem switchParity {d x rows} : Relates WindowFieldParity.setup StairSchedule.paritySetup
    (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) := by
  intro a r pair m
  exact ⟨m,WindowFieldParity.setup_through pair m m⟩

theorem carry {pre between post : Program} (hp : Clear pre) (hb : Clear between) (ht : Clear post)
    {d x rows} : Relates (program pre between post WindowFieldParity.setup) (program pre between post StairSchedule.paritySetup)
      (fun a r=>Paired d x a r rows) (fun a r=>Paired d x a r rows) :=
  compose (compose (compose (compose (stable hp) switchParity) (stable hb)) switchParity) (stable ht)

theorem runTail {pre between post oldPrefix : Program} {s : State} (F : EntryFrame s)
    (shape : WindowMiddleContract.oldDivHead=oldPrefix ++ program pre between post StairSchedule.paritySetup)
    (hp : Clear pre) (hb : Clear between) (ht : Clear post) (a : State) (old m : List Bool)
    (ff : Fits (fieldRows (StockRowVector.rows F.x p)) (finalCode true (plan true) (initialCode true)) a (run oldPrefix old s)) :
    ∃n, Paired false F.x (run (program pre between post WindowFieldParity.setup) m a)
      (run (program pre between post StairSchedule.paritySetup) n (run oldPrefix old s)) (StockRowVector.rows F.x p) := by
  let tape := joinTapes oldPrefix old []
  have native := WindowEndBytes.div_native F tape
  have known := nativeUnpull native.bytes
  unfold tape at known
  rw [shape,joined] at known
  have here := nativeBack (keepTail hp hb ht) known
  have source : Paired false F.x a (run oldPrefix old s) (StockRowVector.rows F.x p) := pairFinished ff native.ids here
  exact carry hp hb ht _ _ source m

theorem entryOfPrefix {pre between post newPrefix oldPrefix : Program}
    (newShape : WindowMiddleContract.divHead=newPrefix ++ program pre between post WindowFieldParity.setup)
    (oldShape : WindowMiddleContract.oldDivHead=oldPrefix ++ program pre between post StairSchedule.paritySetup)
    (hp : Clear pre) (hb : Clear between) (ht : Clear post)
    (starts : ∀ {s : State} (F : EntryFrame s) (m : List Bool), ∃old,
      Fits (fieldRows (StockRowVector.rows F.x p)) (finalCode true (plan true) (initialCode true))
        (run newPrefix m s) (run oldPrefix old s)) : WindowMiddleContract.entry := by
  intro s F m
  obtain ⟨old,ff⟩ := starts F m
  obtain ⟨n,pair⟩ := runTail F oldShape hp hb ht _ old (m.drop (measurementCount newPrefix)) ff
  refine ⟨joinTapes oldPrefix old n,?_⟩
  rw [newShape,oldShape,joined,run_append,run_take]
  exact pairPull Rolling1588Lifetime.phaseHost Rolling1588Lifetime.phaseHost.injective phaseFix pair
end ECDSAAdd.Entrant.StairPacket.WindowReturningTail

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts Rolling1588Lifetime
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount wires

def beforeGroup := StairSchedule.fieldRename (StairLoan.rebindMany StairSchedule.exclusiveRoles
  (hostPlan.firstPacket true) (Rolling1588.placedFirstPacket true) ++ FourScratchWindow.clearProgram)
def rawTail := StairSchedule.forwardSegment cp 87 62 425 450 ++ hostedGroup hostPlan true 13 85 5 ++
    StairSchedule.forwardSegment cp 62 47 450 465 ++ hostedGroup hostPlan true 22 90 3 ++
    StairSchedule.forwardSegment cp 47 32 465 480 ++ hostedGroup hostPlan true 30 93 3 ++
    StairSchedule.forwardSegment cp 32 22 480 490 ++ hostedGroup hostPlan true 36 96 2 ++
    StairSchedule.forwardSegment cp 22 12 490 500 ++ hostedGroup hostPlan true 41 98 2 ++ StairSchedule.forwardLast cp
def pre := renameProgram fieldEquiv rawTail ++ StairSchedule.fieldRename FourScratchWindow.unprefix
def between := StairSchedule.hostedX ++ StairSchedule.fieldRename (entryLowSuffix hostPlan) ++ StairSchedule.hostedX
def post := renameProgram phaseHost Stair44Outer.reverseEnd
def field (S G : Program) := (((beforeGroup ++ renameProgram fieldEquiv G) ++ pre) ++ S) ++ between ++ S

theorem ordinary : StairHostsSchedule.entryFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (WindowFieldCosts.group true 1 84) := by
  simp only [field,beforeGroup,pre,between,rawTail,StairHostsSchedule.entryFieldHosted,
    entryLowPrefix,entryTailPrefix,WindowFieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : WindowParityCaller.entryFieldHosted cp =
    field WindowFieldParity.setup (WindowFieldCosts.group84 true) := by
  simp only [field,beforeGroup,pre,between,rawTail,WindowParityCaller.entryFieldHosted,
    WindowCallerCosts.entryLowPrefix,WindowCallerCosts.entryTailPrefix,←placedShape,fieldRename_append,rename_append,List.append_assoc]

def stockBegin := renameProgram phaseHost (StairSchedule.firstPhase checkpointPrimitives)
theorem cutShape : ExteriorEntryCut.stockPrefix = stockBegin ++ beforeGroup := by
  simp only [ExteriorEntryCut.stockPrefix,stockBegin,beforeGroup,entryPieces,List.take_succ_cons,
    List.take_zero,common,firstSlot,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,fieldRename_append,List.append_assoc]
end ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts Rolling1588Lifetime
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires
theorem beforeFree : Clear beforeGroup := fieldRename_free (both (WindowExteriorFixed.first true) clearSafe)
theorem preFree : Clear pre := by
  apply both _ (fieldRename_free unprefixSafe)
  apply fieldMapped
  apply both _ forwardLast
  apply both _ (WindowExitOuter.ordinaryGroup true 41 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward490
  apply both _ (WindowExitOuter.ordinaryGroup true 36 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward480
  apply both _ (WindowExitOuter.ordinaryGroup true 30 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward465
  apply both _ (WindowExitOuter.ordinaryGroup true 22 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward450
  exact both forward425 (WindowExitOuter.ordinaryGroup true 13 85 5 (by decide) (by decide) (by decide) (by decide +kernel))
theorem betweenFree : Clear between := by
  apply both _ WindowExitOuter.hostedX
  apply both WindowExitOuter.hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  exact WindowExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel) (WindowExteriorFixed.tail (WindowExitOuter.other true))
theorem postFree : Clear post := mapped _ phaseHost.injective phaseFix reverseEnd_free
end ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivReady
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates ExteriorPorts ExteriorDivPieces WindowFieldMask WindowFieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount wires

def pack := renameProgram phaseHost checkpointPrimitives.firstPack
def beginW := opening true 154 ++ pack
def beginR := original true 154 ++ pack
def prefixW := (beginW ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group84 true)
def prefixR := (beginR ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group true 1 84)

theorem refBegin : beginR = Stair44Kernel.divLead := by
  simp only [beginR,original,pack,Stair44Kernel.divLead,Six505.rename_append]

theorem begin_pair {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃n, Paired true F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening true 154
  let B := original true 154
  let t := m.drop (measurementCount A)
  refine ⟨joinTapes B m t,?_⟩
  rw [beginW,beginR,joined,run_append,run_take]
  apply pairUnpull phaseHost phaseFix
  rw [pack,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  exact (WindowStartStates.division F m).through _ firstPack_free _

theorem cut {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃old rec, Paired true F.x (run (beginW ++ beforeGroup) m s) (run (beginR ++ beforeGroup) old s)
        (StockRowVector.rows F.x p) ∧ run (beginR ++ beforeGroup) old s = run ExteriorEntryCut.stockPrefix rec s := by
  obtain ⟨n,pair⟩ := begin_pair F m
  let t := m.drop (measurementCount beginW)
  refine ⟨joinTapes beginR n t,joinTapes stockBegin n t,?_,?_⟩
  · rw [joined,run_append,run_take]
    exact pair.through _ beforeFree _
  · rw [cutShape,joined,joined,refBegin,WindowStockHead.leadD F]
    rfl

theorem starts {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃old, Fits (fieldRows (StockRowVector.rows F.x p)) (finalCode true (plan true) (initialCode true))
      (run prefixW m s) (run prefixR old s) := by
  obtain ⟨n,k,pair,eq⟩ := cut F m
  let t := m.drop (measurementCount (beginW ++ beforeGroup))
  let tape := referenceTape true (plan true) t
  refine ⟨joinTapes (beginR ++ beforeGroup) n tape,?_⟩
  rw [prefixR,prefixW,joined,run_append,run_take,eq]
  rw [eq] at pair
  exact ExteriorEntryCut.group_run F k t _ _ pair

theorem newShape : WindowMiddleContract.divHead = prefixW ++ WindowReturningTail.program pre between post WindowFieldParity.setup := by
  simp only [WindowMiddleContract.divHead,WindowKernelPrograms.divBefore,corrected,field,prefixW,beginW,
    opening,pack,post,WindowReturningTail.program,Six505.rename_append,List.append_assoc]
theorem oldShape : WindowMiddleContract.oldDivHead = prefixR ++ WindowReturningTail.program pre between post StairSchedule.paritySetup := by
  simp only [WindowMiddleContract.oldDivHead,Stair44Kernel.fieldD,ordinary,field,prefixR,refBegin,
    post,WindowReturningTail.program,List.append_assoc]
theorem entry : WindowMiddleContract.entry :=
  WindowReturningTail.entryOfPrefix newShape oldShape preFree betweenFree postFree starts
end ECDSAAdd.Entrant.StairPacket.ExteriorDivReady

end

section

namespace ECDSAAdd.Entrant

def entry : Challenge.Entry := StairPacket.WindowParityRelease.entry
def bounds : Challenge.Bounds := StairPacket.WindowParityRelease.bounds
theorem certificate : Challenge.Certificate entry bounds :=
  StairPacket.WindowReleaseProof.certificate StairPacket.ExteriorDivReady.entry StairPacket.WindowExitReady.exit

end ECDSAAdd.Entrant





end
end
-- ==== end Main ====
