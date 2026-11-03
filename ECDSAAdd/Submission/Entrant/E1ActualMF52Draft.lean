import ECDSAAdd.Submission.Entrant.ExitMerge
import ECDSAAdd.Submission.Entrant.E1CallerAffineFacts52
import ECDSAAdd.Submission.Entrant.E1WholeKAdd52Draft

/-! SOURCE ONLY: ordinary E1Merge actual-MF semantic wrappers for tail52.
No caller instantiation, resource propagation, strong physicality, or candidate
qualification is asserted. H/X are the real MF register values, not D/2 aliases. -/
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ActualMF52Research
open Arithmetic RecordedQuantum KAddCallerBridgeResearch
open E1CallerValueFactsResearch E1WholeKAdd52Research

-- Use named interpreter/register lemmas; never unfold258 gates or a258-bit fold.
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.regValue

theorem kAdd_literal52 (w : Nat → Wire) : E1Merge.kAddM w=literalKAdd w := by rfl

private theorem carry_clean_at52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (s : BasisState)
    (hs : E1Merge.MF w b0 H X T par f gp fp s)
    (i : Nat) (hi : 1794 ≤ i ∧ i < 1797) : s (w i)=false := by
  have away : w i∉E1Merge.mutL w := by
    simp only [E1Merge.mutL,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    refine ⟨⟨⟨E1Merge.nb w hn i 0 258 (by omega) (by omega) (by omega),
      E1Merge.nb w hn i 770 258 (by omega) (by omega) (by omega)⟩,
      E1Merge.nb w hn i 1029 256 (by omega) (by omega) (by omega)⟩,?_,?_,?_,?_⟩
    all_goals exact E1Merge.w_ne w hn _ _ (by omega) (by omega) (by omega)
  have member : w i∈E1Merge.aC w := by
    apply List.mem_map.mpr
    refine ⟨i,?_,rfl⟩
    simp only [List.mem_range'_1]
    omega
  exact (hs.2.2.2.2.2.2.2 _ away).trans (hc _ member)

/-- The three new clean inputs are derived from the OLD MF frame and bank premise. -/
theorem highCarryClean_from_MF52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (s : BasisState)
    (hs : E1Merge.MF w b0 H X T par f gp fp s) : highCarryClean52 w s := by
  change s (w 1794)=false ∧ s (w 1795)=false ∧ s (w 1796)=false
  exact ⟨carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1794 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1795 ⟨by decide,by decide⟩,
    carry_clean_at52 w hn b0 H X T par f gp fp hc s hs 1796 ⟨by decide,by decide⟩⟩

private theorem register_get_bit52 (r : List Wire) (b : BasisState) (j : Nat)
    (hj : j<r.length) : b (r.getD j 0)=(regValue r b).testBit j := by
  have h := regValue_bit r j 0 b hj
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases hb : b (r.getD j 0) <;>
    simp only [hb,Bool.toNat_false,Bool.toNat_true] at h ⊢ <;> simp [←h]

private theorem block_getD52 (w : Nat → Wire) (start count j : Nat) (hj : j<count) :
    (wireBlock w start count).getD j 0=w (start+j) := by
  simp [wireBlock,List.getD_eq_getElem?_getD,hj]

/-- Generic index keeps every division/testBit rewrite symbolic, including at257. -/
private theorem postWord_bit52 (w : Nat → Wire) (b : BasisState) (W : Nat)
    (postWord : regValue (wireBlock w 770 258) b=W) (j : Nat) (hj : j<258) :
    b (w (770+j))=W.testBit j := by
  have h := register_get_bit52 (wireBlock w 770 258) b j
    (by simpa only [wireBlock_length] using hj)
  rw [block_getD52 w 770 258 j hj] at h
  exact h.trans (congrArg (fun n : Nat => n.testBit j) postWord)

/-- All port/index conversions happen while the basis parameter is abstract. -/
private theorem forward_bits_from_postWord52 (w : Nat → Wire) (b : BasisState)
    (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool) (hp : par=decide (D%2=1))
    (postWord : regValue (wireBlock w 770 258) b=Kword D par) :
    b (w 1027)=par ∧ (b (w 1026) ^^ b (w 1025))=!par := by
  have b1 := postWord_bit52 w b (Kword D par) postWord 255 (by decide)
  have b2 := postWord_bit52 w b (Kword D par) postWord 256 (by decide)
  have b3 := postWord_bit52 w b (Kword D par) postWord 257 (by decide)
  have facts := Kword_top_affine D hD par hp
  exact ⟨b3.trans facts.1,(congrArg₂ (fun a c : Bool => a^^c) b2 b1).trans facts.2⟩

private theorem exit_bits_from_postWord52 (w : Nat → Wire) (b : BasisState)
    (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) b=Y/2) :
    b (w 1025)=false ∧ b (w 1026)=false ∧ b (w 1027)=false := by
  have b1 := postWord_bit52 w b (Y/2) postWord 255 (by decide)
  have b2 := postWord_bit52 w b (Y/2) postWord 256 (by decide)
  have b3 := postWord_bit52 w b (Y/2) postWord 257 (by decide)
  have facts := E1CallerValueFactsResearch.exit_top3 Y hY
  exact ⟨b1.trans facts.1,b2.trans facts.2.1,b3.trans facts.2.2⟩

/-- Promise uses the actual OLD complete run and the actual canonical D/parity. -/
theorem forward_outputs_from_postWord52 (w : Nat → Wire) (s : State)
    (D : Nat) (hD : D<ECDSAAdd.p) (par : Bool) (hp : par=decide (D%2=1))
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Kword D par) :
    ForwardOldOutputs52 w par s := by
  exact forward_bits_from_postWord52 w (run (literalKAdd w) [] s).basis D hD par hp postWord

/-- Exit needs the real old Y/2 word and Y<p; no arbitrary intermediate is canonical. -/
theorem exit_outputs_from_postWord52 (w : Nat → Wire) (s : State)
    (Y : Nat) (hY : Y<ECDSAAdd.p)
    (postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2) :
    ExitOldOutputs52 w s := by
  exact exit_bits_from_postWord52 w (run (literalKAdd w) [] s).basis Y hY postWord

/-- Ordinary actual MF Triple, transported from the ORIGINAL stepKAdd.
The caller must still prove its actual word and parity equations. -/
theorem stepKAddFlag52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (D : Nat) (hD : D<ECDSAAdd.p) (hp : par=decide (D%2=1))
    (hWord : (H+X)%2^258=Kword D par) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (flagKAdd52 w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal52] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Kword D par :=
    oldEmpty.2.2.1.trans hWord
  have clean := highCarryClean_from_MF52 w hn b0 H X T par f gp fp hc s.basis hs
  have outputs := forward_outputs_from_postWord52 w s D hD par hp postWord
  have equal := flag_run_eq52 w hn s m clean par hs.2.2.2.1 outputs
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mpr (old s m hs)

/-- Ordinary-MF exit wrapper. Actual exit arithmetic proving hWord and hY is still a caller task. -/
theorem stepKAddZero52 (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (b0 : BasisState) (H X T : Nat) (par f gp fp : Bool)
    (hc : ∀q∈E1Merge.aC w,b0 q=false) (hcin : b0 (w 1797)=false)
    (Y : Nat) (hY : Y<ECDSAAdd.p) (hWord : (H+X)%2^258=Y/2) :
    Triple (E1Merge.MF w b0 H X T par f gp fp) (zeroKAdd52 w)
      (E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp) := by
  intro s m hs
  have old := E1Merge.stepKAdd w hn b0 H X T par f gp fp hc hcin
  rw [kAdd_literal52] at old
  have oldEmpty := old s [] hs
  have postWord : regValue (wireBlock w 770 258) (run (literalKAdd w) [] s).basis=Y/2 :=
    oldEmpty.2.2.1.trans hWord
  have clean := highCarryClean_from_MF52 w hn b0 H X T par f gp fp hc s.basis hs
  have outputs := exit_outputs_from_postWord52 w s Y hY postWord
  have equal := zero_run_eq52 w hn s m clean outputs
  exact (congrArg (fun t : State => t.phase=s.phase ∧
    E1Merge.MF w b0 H ((H+X)%2^258) T par f gp fp t.basis) equal).mpr (old s m hs)

end ECDSAAdd.Entrant.ActualMF52Research
