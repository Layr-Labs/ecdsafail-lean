import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.PrizeHighBankFirstHit91f0292
import ECDSAAdd.Submission.Entrant.PrizeHighBankJoin5ab3264
import ECDSAAdd.Submission.Entrant.PrizeStair44PointMap486a9e3
import ECDSAAdd.Submission.Entrant.PrizeTail10d9efffc
import ECDSAAdd.Submission.Entrant.PrizeTail2024ba497
import ECDSAAdd.Submission.Entrant.PrizeTail227303371
import ECDSAAdd.Submission.Entrant.PrizeTail46901f669
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import ECDSAAdd.Submission.Entrant.StairSideA
import Mathlib.Tactic

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
    toffoliCount (program k) = toffoliCount (A161Generic.squareEntry L0 k) + 328 ∧
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

theorem totals (C : Point) : toffoliCount (program C) ≤ 2169965 ∧ measurementCount (program C) ≤ 1520924 := by
  have h := StairCountsHosted.count_totals C
  change toffoliCount (concreteProgram C) ≤ 2169965 ∧ measurementCount (concreteProgram C) ≤ 1520924 at h
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
    have sum : dE + dX = 344736 := v3_slotDelta_1806
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
  · exact Stair44Groups.hostedGroup44 true 14 85 5 (by decide)
  · exact forwardSegment_ok hsub 62 47 (by decide) (by decide) (by decide) pk.2.1
  · exact Stair44Groups.hostedGroup44 true 23 90 3 (by decide)
  · exact forwardSegment_ok hsub 47 32 (by decide) (by decide) (by decide) pk.2.2.1
  · exact Stair44Groups.hostedGroup44 true 31 93 3 (by decide)
  · exact forwardSegment_ok hsub 32 22 (by decide) (by decide) (by decide) pk.2.2.2.1
  · exact Stair44Groups.hostedGroup44 true 37 96 2 (by decide)
  · exact forwardSegment_ok hsub 22 12 (by decide) (by decide) (by decide) pk.2.2.2.2
  · exact Stair44Groups.hostedGroup44 true 42 98 2 (by decide)
  · exact forwardLast_ok hsub

private theorem exitHead : PieceOK holes TP (StairHostsSchedule.exitHeadSuffix pr hp) := by
  have up := unpackEnd_rows
  unfold StairHostsSchedule.exitHeadSuffix
  refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
    ?_).append ?_).append ?_).append ?_).append ?_)
  · exact reverseLast_ok hsub
  · exact Stair44Groups.hostedGroup44 false 42 98 2 (by decide)
  · exact reverseSegment_ok hsub 22 12 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.2
  · exact Stair44Groups.hostedGroup44 false 37 96 2 (by decide)
  · exact reverseSegment_ok hsub 32 22 (by decide) (by decide) (by decide) (by decide)
      up.2.2.2.1
  · exact Stair44Groups.hostedGroup44 false 31 93 3 (by decide)
  · exact reverseSegment_ok hsub 47 32 (by decide) (by decide) (by decide) (by decide)
      up.2.2.1
  · exact Stair44Groups.hostedGroup44 false 23 90 3 (by decide)
  · exact reverseSegment_ok hsub 62 47 (by decide) (by decide) (by decide) (by decide)
      up.2.1
  · exact Stair44Groups.hostedGroup44 false 14 85 5 (by decide)
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
    exact ((Stair44Groups.hostedGroup44 true 44 100 2 (by decide)).append endpointD |>.append (ok_of_all hsub copyN_all)).append
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
      (Stair44Groups.hostedGroup44 false 44 100 2 (by decide))
  · apply ok_field
    unfold StairHostsSchedule.exitLowSuffix
    exact (((ok_of_all hsub scratchClear_all).append (ok_borrow (exitHead))).append
      (ok_of_all hsub scratchUnprefix_all)).append (StairFirstPacketHosted.hostedFirstPacket_pieceOK holes hsub false)

private theorem phase {P : Program} (v : PieceOK holes PP P) : PieceOK holes UG (Stair44Outer.phasePlace P) :=
  ok_kernel (ok_phase v)

theorem divide : PieceOK holes UG Stair44Outer.divide :=
  (((((phase (Stair44PhaseSites.forward true 409 (by decide))).append (phase Stair44FirstRow.pack)).append
    (ok_kernel entry)).append (phase Stair44PhaseSites.reverseTail)).append
    (phase (Stair44PhaseSites.backward false 490 (by decide)))).append (phase Stair44PhaseSites.native)

theorem multiply (k : Nat) : PieceOK holes UG (Stair44Outer.multiply k) :=
  (((((phase (Stair44PhaseSites.forward false 489 (by decide))).append (phase Stair44PhaseSites.forwardTail)).append
    (ok_kernel exit)).append (phase Stair44FirstRow.unpack)).append
    (phase (Stair44PhaseSites.backward true 409 (by decide)))).append (Stair44PhaseSites.exitX k)
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

theorem qubitBound (de : PieceOK holes UG divide) (mu : ∀ k, PieceOK holes UG (multiply k))
    (C : Point) : qubits (program C) ≤ 1542 := by
  have listOK := StairCertificate.holeList_of_physical_sub holes
    (by rw [show holes = StairPhysicalLayout.newHolesNat from StairPhysicalLayout.physicalHoles_eq_nat]; decide)
    (fun _ h => h)
  have len : 1586 - holes.length = 1542 := by
    rw [show holes = StairPhysicalLayout.newHolesNat from StairPhysicalLayout.physicalHoles_eq_nat]
    decide
  rw [←len]
  apply StairCertificate.qubits_le_holes _ listOK _
  apply holePlacement_of_ok
  cases C with
  | zero => exact pieceOK_nil holes _
  | @some cx cy hc =>
    apply ok_wrapper
    exact ((Stair44OuterSites.initial hc).append (ok_generic
      ((((((Stair44OuterSites.entryY (-cy)).append (Stair44OuterSites.entryX (-cx))).append de).append
        (squareSites (ReflectionE1.correction cx))).append (mu cx.val)).append (Stair44OuterSites.exitY cy)))).append
      (Stair44OuterSites.finalPart hc)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)

def bounds : Challenge.Bounds := ⟨2169965,1520924,1542,50860482⟩

theorem certificateOf
    (sem : ∀ C b R, Triple (encodes b R) (program C) (encodes b (if b then R+C else R)))
    (de : PieceOK holes UG divide) (mu : ∀ k, PieceOK holes UG (multiply k)) :
    Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (Stair44Physical.physical C)
  toffoli_le C := (normalize_toffoli _).trans (Stair44Resources.totals C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1520924
    rw [normalize_measurements]; exact (Stair44Resources.totals C).2
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1542
    rw [normalize_qubits]; exact qubitBound de mu C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 50860482
    rw [normalize_slots]; exact Stair44Resources.slotBound C
theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (program C) (encodes b (if b then R+C else R))) :
    Certificate entry bounds :=
  certificateOf sem Stair44FieldSites.divide Stair44FieldSites.multiply
end ECDSAAdd.Entrant.Stair44Release

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Partial Arithmetic MappedCompressed StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def domain (q : Nat) := (236 ≤ q && q ≤ 529) || (786 ≤ q && q ≤ 1042) || (1264 ≤ q && q ≤ 1300) || (1556 ≤ q && q ≤ 1798) || (1799 ≤ q && q ≤ 1812)

def Covered (P : Program) : Prop := ∀ q ∈ wires P, domain q = true

theorem covered_append {P Q : Program} (a : Covered P) (b : Covered Q) : Covered (P ++ Q) := by
  intro q h
  rw [wires_append,Finset.mem_union] at h
  exact h.elim (a q) (b q)

theorem from_check {P : Program} (h : allSites domain P = true) : Covered P := allSites_sound h

private theorem interval0 : (List.range' 236 294).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval1 : (List.range' 786 257).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval2 : (List.range' 1264 37).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval3 : (List.range' 1556 243).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel
private theorem interval4 : (List.range' 1799 14).all (fun q => Stair44PhaseSites.valid (Stair44WalkMap.rest q)) = true := by decide +kernel

theorem valid {q : Wire} (h : domain q = true) : Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true := by
  simp only [domain,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩ | ⟨lo,hi⟩
  · exact List.all_eq_true.mp interval0 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval1 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval2 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval3 q (by simp only [List.mem_range'_1]; omega)
  · exact List.all_eq_true.mp interval4 q (by simp only [List.mem_range'_1]; omega)

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

/-- The three suffixes of the integer windows 225, 240, 255 start at field ticks 230, 245, 260. -/
def group84 (d : Bool) : Program :=
  ordered d (group d 1 45) (ordered d (ten 46 (!d)) (ordered d (group d 48 1)
    (ordered d (ten 49 (!d)) (ordered d (group d 51 1)
      (ordered d (ten 52 (!d)) (group d 54 31))))))

private theorem ord (c : Cost) (d : Bool) (a b : Program) :
    c.measure (ordered d a b)=c.measure a+c.measure b := by
  cases d <;> simp [ordered,c.append,Nat.add_comm]

theorem overhead (j : Nat) (d : Bool) :
    toffoliCount (ten j (!d)) = toffoliCount (group d j 2)+208 ∧
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
    c.measure (group d 1 84) = c.measure (group d 1 45)+c.measure (group d 46 2)+
      c.measure (group d 48 1)+c.measure (group d 49 2)+c.measure (group d 51 1)+
      c.measure (group d 52 2)+c.measure (group d 54 31) := by
  simp only [group,distribute]
  have a := split c d 1 45 39
  have b := split c d 46 2 37
  have e := split c d 48 1 36
  have f := split c d 49 2 34
  have g := split c d 51 1 33
  have h := split c d 52 2 31
  norm_num only [] at a b e f g h
  omega

theorem group_cost (d : Bool) :
    toffoliCount (group84 d) = toffoliCount (group d 1 84)+624 ∧
    measurementCount (group84 d) = measurementCount (group d 1 84)+831 := by
  have solve (c : Cost) (delta : Nat) (h : ∀j,c.measure (ten j (!d))=c.measure (group d j 2)+delta) :
      c.measure (group84 d) = c.measure (group d 1 84)+3*delta := by
    simp only [group84,ord,h,partition]
    omega
  exact ⟨solve tc 208 (fun j => (overhead j d).1),solve mc 277 (fun j => (overhead j d).2)⟩
/-- Static syntax counts include both correction lists of every measurement. -/
theorem group_slots (d : Bool) :
    slots.measure (group84 d) = slots.measure (group d 1 84)+3*(if d then 6042 else 6053) := by
  have h (j : Nat) : slots.measure (ten j (!d)) =
      slots.measure (group d j 2)+(if d then 6042 else 6053) := by
    rw [show slots.measure=Challenge.gateSlots from rfl,group,distribute]
    cases d <;>
      simp only [distributed,PacketSequence.program,Bool.not_true,Bool.not_false,ten,first,second,
        enter,shift,leave,fieldHook,program,if_true,if_false,Bool.false_eq_true,List.nil_append,
        List.append_nil,Challenge.gateSlots_append,Baselines.rename_gateSlots,enter0_gateSlots,
        switch0_gateSlots,leave0_gateSlots,enter1_gateSlots,switch1_gateSlots,leave1_gateSlots] <;> omega
  simp only [group84,ord,h,partition]
  omega
end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [225,271); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 209 ++
    forward45plus1 d ++ Rolling1588TickGap.forward d 271 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 271 tail ++
    reverse45plus1 d ++ Rolling1588.reverse d 16 209) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

private theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (forward45plus1 d)+f=c.measure (Rolling1588TickGap.forward d 225 46))
    (hr : c.measure (reverse45plus1 d)+r=c.measure (Rolling1588.reverse d 225 46)) :
    c.measure (forward d tail)+f=c.measure (Stair44WalkRun.forward d (255+tail)) ∧
    c.measure (backward d tail)+r=c.measure (Stair44WalkRun.backward d (255+tail)) := by
  have a := StairRestSupport.forward_append d 209 16 (46+tail)
  have b := StairRestSupport.forward_append d 46 225 tail
  have x := StairRestSupport.reverse_append d 209 16 (46+tail)
  have y := StairRestSupport.reverse_append d 46 225 tail
  change Rolling1588TickGap.forward d 16 (209+(46+tail)) =
    Rolling1588TickGap.forward d 16 209 ++ Rolling1588TickGap.forward d 225 (46+tail) at a
  change Rolling1588.reverse d 16 (209+(46+tail)) =
    Rolling1588.reverse d 225 (46+tail) ++ Rolling1588.reverse d 16 209 at x
  rw [b] at a
  rw [y] at x
  have num : 255+tail=209+(46+tail) := by omega
  simp only [Stair44WalkRun.forward, Stair44WalkRun.backward,forward,backward,num,a,x,
    c.append,c.rename]
  norm_num only []
  constructor <;> omega

attribute [local irreducible] Partial.forward45plus1 Partial.reverse45plus1 Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 5001 else 5004)=
      toffoliCount (Stair44WalkRun.forward d (255+tail)) ∧
    toffoliCount (backward d tail)+(if d then 4993 else 4996)=
      toffoliCount (Stair44WalkRun.backward d (255+tail)) ∧
    measurementCount (forward d tail)+2546=measurementCount (Stair44WalkRun.forward d (255+tail)) ∧
    measurementCount (backward d tail)+2552=measurementCount (Stair44WalkRun.backward d (255+tail)) := by
  cases d
  · have sf := StockWindowCosts.stock false
    have a := forward45plus1_false
    have b := reverse45plus1_false
    have t := walk tc false tail 5004 4996
      (subEq 5004 a.1 sf.1 rfl) (subEq 4996 b.1 sf.2.2.1 rfl)
    have m := walk mc false tail 2546 2552
      (subEq 2546 a.2 sf.2.1 rfl) (subEq 2552 b.2 sf.2.2.2 rfl)
    exact ⟨t.1,t.2,m⟩
  · have sf := StockWindowCosts.stock true
    have a := forward45plus1_true
    have b := reverse45plus1_true
    have t := walk tc true tail 5001 4993
      (subEq 5001 a.1 sf.1 rfl) (subEq 4993 b.1 sf.2.2.1 rfl)
    have m := walk mc true tail 2546 2552
      (subEq 2546 a.2 sf.2.1 rfl) (subEq 2552 b.2 sf.2.2.2 rfl)
    exact ⟨t.1,t.2,m⟩

/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 255+tail=n)
    (hf : (if d then 5001 else 5004)=f) (hr : (if d then 4993 else 4996)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+2546=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+2552=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact exactWalks d tail
end ECDSAAdd.Entrant.StairPacket.WindowWalkCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic Partial
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def portsPass (j : Fin 23) (a : Nat) :=
  (IntegerPacket.ports (shape j) a).wires.all (fun q => domain (net j a q))

theorem routeSites {j : Fin 23} (table : ∀ i : Fin 15, portsPass j i = true)
    (a n : Nat) (bound : a+n ≤ 15) :
    Covered (routed j a n) ∧ Covered (unrouted j a n) := by
  induction n generalizing a with
  | zero => constructor <;> intro q h <;> simp [routed,unrouted,wires] at h
  | succ n ih =>
    have h : a < 15 := by omega
    have step := skywalkIntegerTick_wires_subset _ (IntegerPacket.ok (shape j) ⟨a,h⟩)
    have sub := ih (a+1) (by omega)
    have ok (P : Program) (hp : wires P ⊆ (IntegerPacket.ports (shape j) a).wires.toFinset) :
        Covered (renameProgram (net j a) P) := by
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
      exact List.all_eq_true.mp (table ⟨a,h⟩) x (List.mem_toFinset.mp (hp hx))
    exact ⟨covered_append (ok _ step.1) sub.1, covered_append sub.2 (ok _ step.2)⟩

theorem ports10 : ∀ a : Fin 15, portsPass ⟨10,by decide⟩ a = true := by decide +kernel
theorem ports11 : ∀ a : Fin 15, portsPass ⟨11,by decide⟩ a = true := by decide +kernel
theorem ports12 : ∀ a : Fin 15, portsPass ⟨12,by decide⟩ a = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site0 : Covered (portal225) := by
  exact from_check (by decide +kernel)

theorem site1 : Covered (enter225) := by
  exact from_check (by decide +kernel)

theorem site2 : Covered (routed ⟨10,by decide⟩ 0 1) := by
  exact (routeSites ports10 0 1 (by decide)).1

theorem site3 : Covered (renameProgram (OB5.sig 225) (Rolling1588.packAtTick false 225)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site4 : Covered (routed ⟨10,by decide⟩ 1 14) := by
  exact (routeSites ports10 1 14 (by decide)).1

theorem site5 : Covered (leave225) := by
  exact from_check (by decide +kernel)

theorem site6 : Covered (enter240) := by
  exact from_check (by decide +kernel)

theorem site7 : Covered (routed ⟨11,by decide⟩ 0 1) := by
  exact (routeSites ports11 0 1 (by decide)).1

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site40 : Covered (enter255Inv) := by
  exact from_check (by decide +kernel)

theorem site41 : Covered (leave240Inv) := by
  exact from_check (by decide +kernel)

theorem site42 : Covered (unrouted ⟨11,by decide⟩ 1 14) := by
  exact (routeSites ports11 1 14 (by decide)).2

theorem site43 : Covered (archiveRestore240 false) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site44 : Covered (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick false 230)) := by
  exact from_check (by decide +kernel)

theorem site45 : Covered (unrouted ⟨11,by decide⟩ 0 1) := by
  exact (routeSites ports11 0 1 (by decide)).2

theorem site46 : Covered (enter240Inv) := by
  exact from_check (by decide +kernel)

theorem site47 : Covered (leave225Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site48 : Covered (unrouted ⟨10,by decide⟩ 1 14) := by
  exact (routeSites ports10 1 14 (by decide)).2

theorem site49 : Covered (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick false 225)) := by
  exact from_check (by decide +kernel)

theorem site50 : Covered (unrouted ⟨10,by decide⟩ 0 1) := by
  exact (routeSites ports10 0 1 (by decide)).2

theorem site51 : Covered (enter225Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site52 : Covered (portal225Inv) := by
  exact from_check (by decide +kernel)

theorem site53 : Covered (archiveRestore270 true) := by
  exact from_check (by decide +kernel)

theorem site54 : Covered (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick true 260)) := by
  exact from_check (by decide +kernel)

theorem site55 : Covered (archiveRestore255 true) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site56 : Covered (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick true 245)) := by
  exact from_check (by decide +kernel)

theorem site57 : Covered (archiveRestore240 true) := by
  exact from_check (by decide +kernel)

theorem site58 : Covered (renameProgram (OB5.sig 240) (Rolling1588.unpackAtTick true 230)) := by
  exact from_check (by decide +kernel)

theorem site59 : Covered (renameProgram (OB5.sig 225) (Rolling1588.unpackAtTick true 225)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site8 : Covered (renameProgram (OB5.sig 240) (Rolling1588.packAtTick false 230)) := by
  exact from_check (by decide +kernel)

theorem site9 : Covered (archiveLoad240 false) := by
  exact from_check (by decide +kernel)

theorem site10 : Covered (routed ⟨11,by decide⟩ 1 14) := by
  exact (routeSites ports11 1 14 (by decide)).1

theorem site11 : Covered (leave240) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site12 : Covered (enter255) := by
  exact from_check (by decide +kernel)

theorem site13 : Covered (routed ⟨12,by decide⟩ 0 1) := by
  exact (routeSites ports12 0 1 (by decide)).1

theorem site14 : Covered (renameProgram (OB5.sig 255) (Rolling1588.packAtTick false 245)) := by
  exact from_check (by decide +kernel)

theorem site15 : Covered (archiveLoad255 false) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site16 : Covered (routed ⟨12,by decide⟩ 1 14) := by
  exact (routeSites ports12 1 14 (by decide)).1

theorem site17 : Covered (leave255) := by
  exact from_check (by decide +kernel)

theorem site18 : Covered (park270) := by
  exact from_check (by decide +kernel)

theorem site19 : Covered (portal270Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site20 : Covered (renameProgram (OB5.sig 270) (TickRanges.tick base 270)) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  have table : (W.compactSkywalkTickLayout base 270).wires.all (fun z => domain (OB5.sig 270 z)) = true := by decide +kernel
  exact List.all_eq_true.mp table x (List.mem_toFinset.mp (W.repairedTick_support base 270 (by decide) base_pool_nodup (TickRanges.tick_support base 270 (by decide) base_pool_nodup hx)))

theorem site21 : Covered (renameProgram (OB5.sig 270) (Rolling1588.packAtTick false 260)) := by
  exact from_check (by decide +kernel)

theorem site22 : Covered (archiveLoad270 false) := by
  exact from_check (by decide +kernel)

theorem site23 : Covered (renameProgram (OB5.sig 225) (Rolling1588.packAtTick true 225)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site24 : Covered (renameProgram (OB5.sig 240) (Rolling1588.packAtTick true 230)) := by
  exact from_check (by decide +kernel)

theorem site25 : Covered (archiveLoad240 true) := by
  exact from_check (by decide +kernel)

theorem site26 : Covered (renameProgram (OB5.sig 255) (Rolling1588.packAtTick true 245)) := by
  exact from_check (by decide +kernel)

theorem site27 : Covered (archiveLoad255 true) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site28 : Covered (renameProgram (OB5.sig 270) (Rolling1588.packAtTick true 260)) := by
  exact from_check (by decide +kernel)

theorem site29 : Covered (archiveLoad270 true) := by
  exact from_check (by decide +kernel)

theorem site30 : Covered (archiveRestore270 false) := by
  exact from_check (by decide +kernel)

theorem site31 : Covered (renameProgram (OB5.sig 270) (Rolling1588.unpackAtTick false 260)) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site32 : Covered (renameProgram (OB5.sig 270) (W.ReverseCarry.compactReceiverTick base 270)) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  have table : (W.compactSkywalkTickLayout base 270).wires.all (fun z => domain (OB5.sig 270 z)) = true := by decide +kernel
  exact List.all_eq_true.mp table x (List.mem_toFinset.mp (W.ReverseCarry.compactReceiverTick_support base 270 (by decide) base_pool_nodup hx))

theorem site33 : Covered (portal270) := by
  exact from_check (by decide +kernel)

theorem site34 : Covered (park270Inv) := by
  exact from_check (by decide +kernel)

theorem site35 : Covered (leave255Inv) := by
  exact from_check (by decide +kernel)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

theorem site36 : Covered (unrouted ⟨12,by decide⟩ 1 14) := by
  exact (routeSites ports12 1 14 (by decide)).2

theorem site37 : Covered (archiveRestore255 false) := by
  exact from_check (by decide +kernel)

theorem site38 : Covered (renameProgram (OB5.sig 255) (Rolling1588.unpackAtTick false 245)) := by
  exact from_check (by decide +kernel)

theorem site39 : Covered (unrouted ⟨12,by decide⟩ 0 1) := by
  exact (routeSites ports12 0 1 (by decide)).2

end ECDSAAdd.Entrant.StairPacket.PartialSites

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
    hostedGroup hostPlan true 14 85 5 ++
    StairSchedule.forwardSegment p 62 47 450 465 ++
    hostedGroup hostPlan true 23 90 3 ++
    StairSchedule.forwardSegment p 47 32 465 480 ++
    hostedGroup hostPlan true 31 93 3 ++
    StairSchedule.forwardSegment p 32 22 480 490 ++
    hostedGroup hostPlan true 37 96 2 ++
    StairSchedule.forwardSegment p 22 12 490 500 ++
    hostedGroup hostPlan true 42 98 2 ++ StairSchedule.forwardLast p

def exitHeadSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.reverseLast p ++
    hostedGroup hostPlan false 42 98 2 ++
    StairSchedule.reverseSegment p 22 12 490 500 ++
    hostedGroup hostPlan false 37 96 2 ++
    StairSchedule.reverseSegment p 32 22 480 490 ++
    hostedGroup hostPlan false 31 93 3 ++
    StairSchedule.reverseSegment p 47 32 465 480 ++
    hostedGroup hostPlan false 23 90 3 ++
    StairSchedule.reverseSegment p 62 47 450 465 ++
    hostedGroup hostPlan false 14 85 5 ++
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
theorem reverse45plus1_domain (d : Bool) : Covered (reverse45plus1 d) := by
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

private theorem fieldTc (d : Bool) :
    tc.measure (WindowFieldCosts.group84 d)=tc.measure (WindowFieldCosts.group d 1 84)+624 := by
  rw [show tc.measure=toffoliCount from rfl]
  exact (WindowFieldCosts.group_cost d).1
private theorem fieldMc (d : Bool) :
    mc.measure (WindowFieldCosts.group84 d)=mc.measure (WindowFieldCosts.group d 1 84)+831 := by
  rw [show mc.measure=measurementCount from rfl]
  exact (WindowFieldCosts.group_cost d).2
private theorem sum_delta {a b x y g h f r : Nat}
    (l : a+g+h=x+f) (rr : b+g+h=y+f) (v : 2*(g+h)=r+2*f) : a+b+r=x+y := by omega
private theorem pair_delta {a b x y g h i j f r : Nat}
    (l : a+g+h=x+f) (rr : b+i+j=y+f) (v : g+h+i+j=r+2*f) : a+b+r=x+y := by omega

attribute [local irreducible] Stair44Outer.divide Stair44Outer.multiply divide multiply
  finite Stair44Outer.finite WindowWalkCosts.forward WindowWalkCosts.backward
  WindowFieldCosts.group84 WindowFieldCosts.group Stair44WalkRun.forward Stair44WalkRun.backward
  toffoliCount measurementCount

theorem tc_div : tc.measure divide+5001+4996=tc.measure Stair44Outer.divide+624 :=
  kernels tc 5001 4996 624 (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).1
    (WindowWalkCosts.inst false 235 490 5004 4996 rfl rfl rfl).2.1 (fieldTc true)

theorem tc_mul (k : Nat) : tc.measure (multiply k)+5004+4993=tc.measure (Stair44Outer.multiply k)+624 :=
  kernelsM tc k 5004 4993 624 (WindowWalkCosts.inst false 234 489 5004 4996 rfl rfl rfl).1
    (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).2.1 (fieldTc false)

theorem mc_div : mc.measure divide+2546+2552=mc.measure Stair44Outer.divide+831 :=
  kernels mc 2546 2552 831 (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst false 235 490 5004 4996 rfl rfl rfl).2.2.2 (fieldMc true)

theorem mc_mul (k : Nat) : mc.measure (multiply k)+2546+2552=mc.measure (Stair44Outer.multiply k)+831 :=
  kernelsM mc k 2546 2552 831 (WindowWalkCosts.inst false 234 489 5004 4996 rfl rfl rfl).2.2.1
    (WindowWalkCosts.inst true 154 409 5001 4993 rfl rfl rfl).2.2.2 (fieldMc false)

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+18746=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+8534=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 18746 (pair_delta tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 8534 (sum_delta mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2151219 ∧
    measurementCount (program C) ≤ 1512390 := by
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
  have a := StairRestSupport.forward_append d 209 16 (46+tail)
  have b := StairRestSupport.forward_append d 46 225 tail
  have x := StairRestSupport.reverse_append d 209 16 (46+tail)
  have y := StairRestSupport.reverse_append d 46 225 tail
  change Rolling1588TickGap.forward d 16 (209+(46+tail)) =
    Rolling1588TickGap.forward d 16 209 ++ Rolling1588TickGap.forward d 225 (46+tail) at a
  change Rolling1588.reverse d 16 (209+(46+tail)) =
    Rolling1588.reverse d 225 (46+tail) ++ Rolling1588.reverse d 16 209 at x
  rw [b] at a
  rw [y] at x
  have num : 255+tail=209+(46+tail) := by omega
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
private theorem groupCap (d : Bool) (n : Nat) (hn : 3*(if d then 6042 else 6053)=n) :
    slots.measure (WindowFieldCosts.group84 d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  subst n
  exact WindowFieldCosts.group_slots d
private theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+257077+257873+18126 :=
  kernels slots 257077 257873 18126
    (walk slots true 154 257077 257861 409 rfl (casts forward45plus1_true) (casts reverse45plus1_true)).1
    (walk slots false 235 257059 257873 490 rfl (casts forward45plus1_false) (casts reverse45plus1_false)).2
    (groupCap true 18126 rfl)

private theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+257059+257861+18159 :=
  kernelsM slots k 257059 257861 18159
    (walk slots false 234 257059 257873 489 rfl (casts forward45plus1_false) (casts reverse45plus1_false)).1
    (walk slots true 154 257077 257861 409 rfl (casts forward45plus1_true) (casts reverse45plus1_true)).2
    (groupCap false 18159 rfl)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+257077+257873+18126)
    (hm : b ≤ y+257059+257861+18159) : a+b ≤ x+y+1066155 := by omega

private theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+1066155 :=
  finite_upper slots C cx cy 1066155 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 51926637 := by
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

private theorem hook (j : Nat) (hj : j∈[46,49,52]) (op : Stage) :
    Sound (fieldHook j op) := by
  have span : j∈List.range' 1 83 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; apply List.mem_range'_1.mpr; omega
  have chk : (fieldSites j).all (fun q => decide (InDom q))=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide +kernel
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

private theorem pair (d : Bool) (j : Nat) (pick : j∈[46,49,52]) (lo : 1≤j) (hi : j≤83) :
    Sound (ten j (!d)) := by
  have here := whole d j lo (by omega)
  have next := whole d (j+1) (by omega) (by omega)
  have firstOK : Sound (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (second j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))

theorem group84_ok (d : Bool) : Sound (group84 d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  exact ord (ordinary d 1 45 (by decide) (by decide)) (ord (pair d 46 (by decide) (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide) (by decide)) (ord (pair d 49 (by decide) (by decide) (by decide))
      (ord (ordinary d 51 1 (by decide) (by decide)) (ord (pair d 52 (by decide) (by decide) (by decide))
        (ordinary d 54 31 (by decide) (by decide)))))))

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
  exact weaken (Stair44Groups.hostedGroup44 d 0 1 84 (by decide))

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
  exact ord (ordinary d 1 45 (by decide) (by decide)) (ord (pair d 46 (by decide) (by decide))
    (ord (ordinary d 48 1 (by decide) (by decide)) (ord (pair d 49 (by decide) (by decide))
      (ord (ordinary d 51 1 (by decide) (by decide)) (ord (pair d 52 (by decide) (by decide))
        (ordinary d 54 31 (by decide) (by decide)))))))

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
  have g14 := sound_hostedGroup H hs true 14 85 5 (by decide) (by omega) (by omega) (by omega)
  have g23 := sound_hostedGroup H hs true 23 90 3 (by decide) (by omega) (by omega) (by omega)
  have g31 := sound_hostedGroup H hs true 31 93 3 (by decide) (by omega) (by omega) (by omega)
  have g37 := sound_hostedGroup H hs true 37 96 2 (by decide) (by omega) (by omega) (by omega)
  have g42 := sound_hostedGroup H hs true 42 98 2 (by decide) (by omega) (by omega) (by omega)
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
  have g14 := sound_hostedGroup H hs false 14 85 5 (by decide) (by omega) (by omega) (by omega)
  have g23 := sound_hostedGroup H hs false 23 90 3 (by decide) (by omega) (by omega) (by omega)
  have g31 := sound_hostedGroup H hs false 31 93 3 (by decide) (by omega) (by omega) (by omega)
  have g37 := sound_hostedGroup H hs false 37 96 2 (by decide) (by omega) (by omega) (by omega)
  have g42 := sound_hostedGroup H hs false 42 98 2 (by decide) (by omega) (by omega) (by omega)
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
    have g := sound_hostedGroup H hs true 44 100 2 (by decide) (by omega) (by omega)
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
    have g := sound_hostedGroup H hs false 44 100 2 (by decide) (by omega) (by omega)
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
  have a := StairRestSupport.forward_append d 209 16 (46+tail)
  have b := StairRestSupport.forward_append d 46 225 tail
  change Rolling1588TickGap.forward d 16 (209+(46+tail)) =
    Rolling1588TickGap.forward d 16 209 ++ Rolling1588TickGap.forward d 225 (46+tail) at a
  rw [b] at a
  have num : 255+tail=209+(46+tail) := by omega
  simp only [Stair44WalkRun.forward,num,a,app,ren] at old
  simp only [WindowWalkCosts.forward,app,ren]
  exact ⟨old.1,⟨old.2.1,native new⟩,old.2.2.2⟩

theorem walkR (d : Bool) (tail : Nat) (bound : 16+(255+tail)≤506)
    (new : GoodWindow (Partial.reverse45plus1 d)) :
    PieceOK reserved PP (WindowWalkCosts.backward d tail) := by
  have old := weaken (Stair44PhaseSites.backward d (255+tail) bound)
  have a := StairRestSupport.reverse_append d 209 16 (46+tail)
  have b := StairRestSupport.reverse_append d 46 225 tail
  change Rolling1588.reverse d 16 (209+(46+tail)) =
    Rolling1588.reverse d 225 (46+tail) ++ Rolling1588.reverse d 16 209 at a
  rw [b] at a
  have num : 255+tail=209+(46+tail) := by omega
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
  rw [show 255+tail=209+(46+tail) by omega,forward_append d 209 16 (46+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 225 (46+tail)) at ms
  rw [forward_append d 46 225 tail] at ms
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
  rw [show 255+tail=209+(46+tail) by omega,reverse_append d 209 16 (46+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 225 (46+tail)) at ms
  rw [reverse_append d 46 225 tail] at ms
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
  have h := weaken Stair44FieldSites.entry
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
  have h := weaken Stair44FieldSites.exit
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
  WindowPhysical.physical PartialPhysical.forward45plus1_physical PartialPhysical.reverse45plus1_physical C

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
def bounds : Challenge.Bounds := ⟨2151219,1512390,1543,51926637⟩

theorem certificateOfSemantics
    (sem : ∀ C b R, Triple (encodes b R) (WindowCallerCosts.program C)
      (encodes b (if b then R+C else R))) : Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (sem C b R)
  physical C := Baselines.normalize_physical _ (WindowCallerCosts.physical C)
  toffoli_le C := (normalize_toffoli _).trans (WindowCallerCosts.totals C).1
  measurements_le C := by
    change measurementCount (normalizeProgram _) ≤ 1512390
    rw [normalize_measurements]
    exact (WindowCallerCosts.totals C).2
  qubits_le C := by
    change qubits (normalizeProgram _) ≤ 1543
    rw [normalize_qubits]
    exact WindowCallerCosts.qubitBound C
  gateSlots_le C := by
    change gateSlots (normalizeProgram _) ≤ 51926637
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
def banks := [46,49,52]
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
  rcases hm with rfl|rfl|rfl
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
def bankIds : Finset Nat := {46,49,52}
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
def nativeRanges (j n : Nat) := (j=1 ∧ n=45) ∨ (j=48 ∧ n=1) ∨ (j=51 ∧ n=1) ∨ (j=54 ∧ n=31)
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
  rcases h with rfl|rfl|rfl <;> decide
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
  | true => [.native 1 45,.paired 46,.native 48 1,.paired 49,.native 51 1,.paired 52,.native 54 31]
  | false => [.native 54 31,.paired 52,.native 51 1,.paired 49,.native 48 1,.paired 46,.native 1 45]
def initialCode (d : Bool) : Nat→Cols := fun _=>inputCols (enter (!d))
private theorem emits (d : Bool) : group84 d=concatenate d (plan d) := by
  cases d <;> simp only [group84,ordered,concatenate,emitted,plan,if_true,if_false,Bool.false_eq_true,
    List.append_assoc,List.append_nil]
private theorem valid_plan (d : Bool) : valid d (plan d) (initialCode d) := by
  cases d <;> simp [valid,plan,validLeg,nativeRanges,bankIds,codes,update,initialCode]
theorem group_run (d : Bool) (row : Nat→Nat) (bounded : ∀j∈bankIds,row j<63145)
    (m : List Bool) (a r : State) (initial : Fits row (initialCode d) a r)
    (native : NativeTrail d row (plan d) m r) :
    Fits row (finalCode d (plan d) (initialCode d)) (run (group84 d) m a) (destination d (plan d) m r) := by
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
