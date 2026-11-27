import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Submission.Entrant.CRT
import ECDSAAdd.Submission.Entrant.OddField
import ECDSAAdd.Framework.RecordedPaths
import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Submission.Entrant.MainP1
import ECDSAAdd.Submission.Entrant.Mixed20D
import ECDSAAdd.Submission.Entrant.MainQ1

section


section


section


section

namespace ECDSAAdd.Entrant.StairPacket.Shadow20.MixedChain

open ECDSAAdd.Arithmetic
open ECDSAAdd.Arithmetic.MappedCompressed
open ECDSAAdd.Secp256k1
open ECDSAAdd.Entrant.IntegerPacket
open ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open ECDSAAdd.Entrant.StairPacket.ArchiveStockRows
open ECDSAAdd.Entrant.StairPacket.WideReference
open ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open ECDSAAdd.Entrant.StairPacket.WindowFold
open ECDSAAdd.Entrant.StairPacket.WindowChain
open ECDSAAdd.Entrant.StairPacket.StockCanonicalRow
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open ECDSAAdd.Entrant.StairPacket.StockStrongChain
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.NativeJ20
open ECDSAAdd.Entrant.StairPacket.Shadow20.LeaveCut20
open ECDSAAdd.Entrant.StairPacket.Shadow20.Trans150
open ECDSAAdd.Entrant.StairPacket.Shadow20.Reentry345
open SkywalkRails

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] run Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.enterP Shadow7.enterInvP Shadow7.routed Shadow7.unrouted
  Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.exitLoadP Shadow7.exitRestoreP
  CRTBarrel.leave CRTBarrel.unleave leave150To20 leaveInv150To20 leave150To20Red leaveInv150To20Red
  enterP20 enterInvP20 routed20 unrouted20 leaveP20 leaveInvP20 leaveP20Red leaveInvP20Red
  archiveLoadP20 archiveRestoreP20 archiveLoad150To20 archiveRestore150To20
  Rolling1588.packAtTick Rolling1588.unpackAtTick

/-! ### Section 1: Canonical 22-Bank Keys & Bank Cell Ranges -/

/-- Canonical archive key for each of the 22 mixed-window banks. -/
noncomputable def mixedKey (x p : Nat) (b : MixedGeo.Bank) : Nat → Bool :=
  if h1 : b.val < 7 then
    value x p (start ⟨b.val, by omega⟩) (Shadow7.sbP (start ⟨b.val, by omega⟩))
      (StockRowVectorW.crossW ⟨b.val, by omega⟩)
  else if h2 : b.val = 7 then
    value x p 150 (Shadow7.sbP 150) (StockRowVectorW.crossW MixedWindow.j7)
  else if h3 : b.val < 17 then
    Reentry345.value20 x p ⟨b.val - 8, by omega⟩
  else
    value x p (start ⟨b.val + 3, by have := b.isLt; omega⟩)
      (Shadow7.sbP (start ⟨b.val + 3, by have := b.isLt; omega⟩))
      (StockRowVectorW.crossW ⟨b.val + 3, by have := b.isLt; omega⟩)

noncomputable def mixedRow (x p : Nat) (b : MixedGeo.Bank) : Nat :=
  select (mixedKey x p b)

/-- Every bank `b : Fin 22` holds its key-selected row at `MixedGeo.bankPorts exitPorts b`. -/
def mixedFinal (exitPorts : Ports) (d : Bool) (x p : Nat) (s : State) : Prop :=
  ∀ b : MixedGeo.Bank, SavedKey (mixedKey x p b) (MixedGeo.bankPorts exitPorts b) d s

def BankKey (d : Bool) (x p : Nat) (b : MixedGeo.Bank) (s : State) : Prop :=
  SavedKey (mixedKey x p b) (MixedGeo.bankPorts StockWindowChainP.ExitPorts420 b) d s

def SavedBefore (d : Bool) (x p n : Nat) (s : State) : Prop :=
  ∀ b : MixedGeo.Bank, b.val < n → BankKey d x p b s

private theorem bank_tick_match : ∀ b : MixedGeo.Bank,
    (∀ h : b.val < 7, MixedGeo.bankTick b = start ⟨b.val, by omega⟩) ∧
    (b.val = 7 → MixedGeo.bankTick b = 150) ∧
    (∀ h1 : 8 ≤ b.val, ∀ h2 : b.val < 17, MixedGeo.bankTick b = start20 ⟨b.val - 8, by omega⟩ + 5) ∧
    (∀ h1 : 17 ≤ b.val, MixedGeo.bankTick b = start ⟨b.val + 3, by have := b.isLt; omega⟩) ∧
    60 ≤ MixedGeo.endTick b ∧ MixedGeo.endTick b ≤ 420 := by
  decide +kernel

theorem mixedKey_chronology (x p : Nat) (b : MixedGeo.Bank) (r : Nat)
    (h : Encodes (mixedKey x p b) r) :
    ArchiveStockRows.Chronology (MixedGeo.bankTick b) x p r := by
  have tm := bank_tick_match b
  unfold mixedKey at h
  split_ifs at h with h1 h2 h3
  · rw [tm.1 h1]; exact StockRowVector.historical _ _ x p _ _ h
  · rw [tm.2.1 h2]; exact StockRowVector.historical _ _ x p _ _ h
  · rw [tm.2.2.1 (by omega) h3]; exact value20_chronology x p ⟨b.val - 8, by omega⟩ r h
  · rw [tm.2.2.2.1 (by omega)]; exact StockRowVector.historical _ _ x p _ _ h

theorem mixedFinal_trace {exitPorts d x p s} (h : mixedFinal exitPorts d x p s) (b : MixedGeo.Bank) :
    ArchiveStockRows.Chronology (MixedGeo.bankTick b) x p (mixedRow x p b) :=
  mixedKey_chronology x p b _ (h b).2.1

private theorem bank_cells_mem (b : MixedGeo.Bank) (q : Wire)
    (hq : q ∈ ArchiveWindowPreserve.bank (MixedGeo.bankPorts StockWindowChainP.ExitPorts420 b)) :
    q ∈ cellsRestoreP (MixedGeo.endTick b) := by
  simp only [ArchiveWindowPreserve.bank, List.mem_map, List.mem_finRange, true_and] at hq
  obtain ⟨i, rfl⟩ := hq
  have eq := MixedGeo.site_eq StockWindowChainP.ExitPorts420 StockArchiveBanks.exitCells b i
  change MixedGeo.siteAt StockWindowChainP.ExitPorts420 b i ∈ cellsRestoreP (MixedGeo.endTick b)
  rw [eq, MixedGeo.bankSite, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp [cellsRestoreP]), Option.getD_some]
  exact List.getElem_mem _

private theorem bank_range (b : MixedGeo.Bank) (q : Wire)
    (hq : q ∈ ArchiveWindowPreserve.bank (MixedGeo.bankPorts StockWindowChainP.ExitPorts420 b)) :
    let t := MixedGeo.endTick b
    (t + 6 ≤ (q : Nat) ∧ (q : Nat) ≤ t + 15) ∨
    (t + 1034 ≤ (q : Nat) ∧ (q : Nat) ≤ t + 1042 ∧ (q : Nat) ≤ 1300) ∨
    (2071 ≤ (q : Nat) + t ∧ (q : Nat) + t ≤ 2079 ∧ (q : Nat) ≤ 1812) :=
  StockWindowW7.cells_rangeG (MixedGeo.endTick b) (bank_tick_match b).2.2.2.2.2 q (bank_cells_mem b q hq)

private theorem keep_savedKey {k : Nat → Bool} {ps : Ports} {d : Bool} {s t : State}
    (h : SavedKey k ps d s) (eq : ∀ q ∈ ArchiveWindowPreserve.bank ps, t.basis q = s.basis q) :
    SavedKey k ps d t :=
  ⟨h.1, h.2.1, ArchiveWindowPreserve.keep h.2.2 eq⟩

/-! ### Section 2: Hand-Off Predicates `At20`, `Ready20`, `At345`, `Ready345` -/

def prevTick20 (j : Fin 9) : Nat := if j.val = 0 then 150 else start20 (prev20 j)

def prevCross20 (j : Fin 9) (x p : Nat) : Bool :=
  if j.val = 0 then
    HighBankSum.crossBit (LeaveJ7.TrueMiddle.d MixedWindow.j7 (unsigned 150 x p))
  else
    HighBankSum.crossBit (TrueMiddle20.d (prev20 j) (unsigned (start20 (prev20 j)) x p))

structure At20 (j : Fin 9) (d : Bool) (x p : Nat) (raw s : State) (g sg pg ps : Bool) : Prop where
  domain : Domain (start20 j) x p raw
  input : InputAt (start20 j) (signedAt (start20 j) x p g sg) raw
  cut : PackedCut (EnterJ20.lowerPairs j) (EnterJ20.upperPairs j) (EnterJ20.gate j) (EnterJ20.flagN j)
    (EnterJ20.flagF j) (EnterJ20.flagU j) (PortalValues.negative sg (unsigned (start20 j) x p).u)
    (decide (Shadow.far (sbP20 (start20 j)) 20 (unsigned (start20 j) x p)))
    (decide (Shadow.far (sbP20 (start20 j)) 20 (unsigned (start20 j) x p) ∧
      2 ^ sbP20 (start20 j) ≤ (unsigned (start20 j) x p).u))
    (pullState (EnterJ20.pull j) raw) (eraseSites (EnterJ20.pending j) s)
  facts : PrevPast20 j (unsigned (prevTick20 j) x p) pg ps (prevCross20 j x p) s
  pastCanonical : signedAt (prevTick20 j) x p pg ps = WideReference.canonical (prevTick20 j) x p

def Ready20 (j : Fin 9) (d : Bool) (x p : Nat) (s : State) : Prop :=
  ∃ raw g sg pg ps, At20 j d x p raw s g sg pg ps

structure At345 (d : Bool) (x p : Nat) (raw s : State) (g sg pg ps : Bool) : Prop where
  domain : Domain 345 x p raw
  input : InputAt 345 (signedAt 345 x p g sg) raw
  cut : PackedCut (EnterJ7.lowerPairs MixedWindow.j20) (EnterJ7.upperPairs MixedWindow.j20)
    (EnterJ7.gate MixedWindow.j20) (EnterJ7.flagN MixedWindow.j20) (EnterJ7.flagF MixedWindow.j20)
    (EnterJ7.flagU MixedWindow.j20) (PortalValues.negative sg (unsigned 345 x p).u)
    (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p)))
    (decide (Shadow.far (Shadow7.sbP 345) 15 (unsigned 345 x p) ∧
      2 ^ Shadow7.sbP 345 ≤ (unsigned 345 x p).u))
    (pullState (EnterJ7.pull MixedWindow.j20) raw) (eraseSites (EnterJ7.pending MixedWindow.j20) s)
  facts : PastFacts20 MixedWindow.k8 (ArchiveJ20.rawPorts MixedWindow.k8) (unsigned 325 x p) pg ps
    (HighBankSum.crossBit (TrueMiddle20.d MixedWindow.k8 (unsigned 325 x p))) s
  pastCanonical : signedAt 325 x p pg ps = WideReference.canonical 325 x p

def Ready345 (d : Bool) (x p : Nat) (s : State) : Prop :=
  ∃ raw g sg pg ps, At345 d x p raw s g sg pg ps

/-! ### Section 3: 20-Tick Selected Receipt (`selected_receipt20`) -/

private theorem prev20_chron :
    (∀ i : Fin 20, Archive150.rawPorts ⟨i, by omega⟩ = nativeRawPort MixedWindow.j7 i) ∧
    (∀ j : Fin 9, 1 ≤ j.val → ∀ i : Fin 20, ArchiveJ20.rawPorts (prev20 j) ⟨i, by omega⟩ = nativeRawPort20 (prev20 j) i) ∧
    (∀ j : Fin 9, ∀ i : Fin 16, oldRange (start20 j + 1) (windowNet20 j (prevCodePorts20 j ⟨i.val, by omega⟩))) := by
  decide +kernel

attribute [local irreducible] SkywalkNat.step Shadow.far nextWindow20 window20 withArchive20 body20 in
theorem selected_receipt20 (j : Fin 9) (d : Bool) (x p : Nat) (good : Bounds x p)
    (raw s : State) (g sg pg ps : Bool) (m : List Bool)
    (pre : At20 j d x p raw s g sg pg ps) :
    SavedKey (mixedKey x p ⟨7 + j.val, by have := j.isLt; omega⟩)
      (prevCodePorts20 j) d (run (nextWindow20 j d) m s) := by
  have hj := j.isLt
  have nums := actualNumbers20 j x p good
  have hist := WideReference20.pulled_history20 j pre.domain
  have inp : SkywalkIntegerInput (EnterJ20.lay j)
      (encode g sg (unsigned (start20 j) x p).u (unsigned (start20 j) x p).v).a
      (encode g sg (unsigned (start20 j) x p).u (unsigned (start20 j) x p).v).b g raw.basis :=
    readInput (start20 j) x p raw g sg pre.input
  let preS := run (enterP20 j) m s
  let tape := m.drop (measurementCount (enterP20 j))
  let T := Shadow.reduced (sbP20 (start20 j)) 20 (unsigned (start20 j) x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 (start20 j)) (unsigned (start20 j) x p) nums.small.1 nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ20.ready_pending_at j raw s (unsigned (start20 j) x p) g sg m nums.small.1 pre.cut inp hist
  have scr := scratch_raw_clean20 j d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut
  have hold := bank_kept20 j d s m tape (tape.drop (measurementCount (routed20 j 0 1))) Z parity ready.2.1
  have prevOdd : (unsigned (prevTick20 j) x p).v % 2 = 1 := by
    unfold prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).odd
    · exact (actualNumbers20 (prev20 j) x p good).odd
  have prevSm : PrevSmall20 j (unsigned (prevTick20 j) x p) := by
    unfold PrevSmall20 prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).farSmall
    · exact (actualNumbers20 (prev20 j) x p good).small.1
  obtain ⟨_, row, limit, _, frame⟩ := admits20 j d s m tape (tape.drop (measurementCount (routed20 j 0 1)))
    Z parity ready.2.1 scr (unsigned (prevTick20 j) x p) pg ps (prevCross20 j x p) prevOdd prevSm pre.facts
  have hEnc : Encodes (mixedKey x p ⟨7 + j.val, by omega⟩) row := by
    by_cases h0 : j.val = 0
    · have hj0 : j = ⟨0, by decide⟩ := Fin.ext h0
      subst hj0
      have all := StockCanonicalRow.frame_key MixedWindow.j7 Archive150.rawPorts prev20_chron.1 row
        (Shadow7.sbP 150) (unsigned 150 x p) pg ps _ s _ pre.facts hold frame
      have hcanon := pre.pastCanonical
      simp only [prevTick20, ↓reduceIte, signedAt] at hcanon
      dsimp only [mixedKey, prevCross20] at all ⊢
      rw [hcanon] at all
      exact all
    · have all := frame_key20 (prev20 j) (ArchiveJ20.rawPorts (prev20 j)) (prev20_chron.2.1 j (by omega)) row
        (unsigned (start20 (prev20 j)) x p) pg ps _ s _
        (by simpa only [PrevPast20, prevTick20, prevCross20, if_neg h0] using pre.facts)
        (by simpa only [prevRawPorts20, if_neg h0] using hold)
        (by simpa only [prevRawPorts20, if_neg h0] using frame)
      have hcanon := pre.pastCanonical
      simp only [prevTick20, if_neg h0, signedAt] at hcanon
      dsimp only at all
      rw [hcanon] at all
      have hmk : mixedKey x p ⟨7 + j.val, by omega⟩ = Reentry345.value20 x p (prev20 j) := by
        unfold mixedKey
        rw [dif_neg (by dsimp; omega), dif_neg (by dsimp; omega), dif_pos (by dsimp; omega)]
        congr 1; apply Fin.ext; simp [prev20]; omega
      rw [hmk]; exact all
  have spec := select_spec ⟨row, limit, hEnc⟩
  have rf := reframe limit hEnc (prevRawPorts20 j) _ frame
  have final := archive_result20 j d _ spec.1 _ _ rf
  have runEq : run (nextWindow20 j d) m s = run (body20 j (withArchive20 j d)) tape preS := by
    simp only [nextWindow20, window20, run_append, run_take, preS, tape]
  rw [runEq]
  exact ⟨spec.1, spec.2, body20_keeps j (withArchive20 j d) (prevCodePorts20 j) d _ preS tape
    (fun i => old_clear20 (by decide) (prev20_chron.2.2 j i)) final⟩

/-! ### Section 4: Bank Preservation Across 15-Tick, Transition-150, 20-Tick, Reentry-345 & Exit-420 -/

private theorem keep_cells_15 (i k : Fin 26) (hk : k.val = i.val + 1) (h1 : 1 ≤ k.val) (h24 : k.val ≤ 24)
    (d : Bool) (t : Nat) (ht0 : 60 ≤ t) (ht1 : t + 15 ≤ start k) (q : Wire) (hq : q ∈ cellsRestoreP t)
    (s : State) (m : List Bool) :
    (run (MixedWindow.block15F d i k).flatten m s).basis q = s.basis q := by
  have c := StockWindowW7.cells_rangeG t (by simp only [start] at ht1; omega) q hq
  have w1 : 45 ≤ start k := by simp only [start]; omega
  have w2 : start k ≤ 405 := by simp only [start]; omega
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have sk : start k ≤ 405 := by simp only [start]; omega
  have pk : NativeJ7.prev k = i := Fin.ext (by simp only [NativeJ7.prev]; omega)
  have hfl : (MixedWindow.block15F d i k).flatten = NativeJ7.nextWindow k d ++ CRTBarrel.leave k := by
    rw [← pk]
    simp only [MixedWindow.block15F, MixedWindow.packW, NativeJ7.nextWindow, NativeJ7.window,
      Shadow7.body, NativeJ7.withArchive, NativeJ7.program, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.append_assoc]
  rw [hfl, run_append, run_take]
  rw [CRTWindow.leave_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega)]
  simp only [NativeJ7.nextWindow, NativeJ7.window, run_append, run_take]
  have native : ¬ Shadow7.MayTouch k (windowNet k q) := by
    have mid : (Shadow7.shape k).mid = Shadow7.sbP (start k) + 15 := rfl
    rcases c with c | c | c
    · rw [show windowNet k q = q from NativeJ7.sig_kept _ _ (by omega) (by omega)]
      unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · rw [show windowNet k q = q from NativeJ7.sig_kept _ _ (by omega) (by omega)]
      unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · rw [show windowNet k q = 3113 - q from NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, c.2.2⟩)]
      unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
  have port : q ∉ EnterJ7.ports k := fun hm => by
    have r := EnterJ7.portsRegion k hm
    simp only [Wire] at *; omega
  have admin : q ∉ NativeJ7.support k ++ ArchiveJ7.rawPortsList (NativeJ7.prev k) := by
    rw [List.mem_append, ArchiveJ7.raw_split]
    intro mem
    rcases mem with mem | mem
    · simp only [NativeJ7.support, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at mem
      obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
      · rw [NativeJ7.sig_kept _ _ (by simp only [base, Wire] at *; omega) (by simp only [base, Wire] at *; omega)] at e
        simp only [base, Wire] at *; omega
      · by_cases mv : 1301 ≤ 1044 + v
        · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨by simp only [base, Wire] at *; omega, by simp only [base, Wire] at *; omega⟩)] at e
          simp only [base, Wire] at *; omega
        · rw [NativeJ7.sig_kept _ _ (by simp only [base, Wire] at *; omega) (by simp only [base, Wire] at *; omega)] at e
          simp only [base, Wire] at *; omega
    · rw [List.mem_append] at mem
      rcases mem with mem | mem
      · rw [ArchiveJ7.rawHead, cellsLoadP, List.mem_append] at mem
        have hs : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, start]; omega
        rcases mem with mem | mem
        · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at mem
          obtain ⟨v, hv, e | e⟩ := mem
          · rw [hs] at e; simp only [Wire] at *; omega
          · rw [hs] at e
            by_cases mv : 1301 ≤ start k + 1034 + v
            · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e; simp only [Wire] at *; omega
            · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)] at e; simp only [Wire] at *; omega
        · simp only [List.mem_cons, List.not_mem_nil, or_false, hs] at mem
          rcases mem with rfl | rfl | rfl <;> (simp only [Shadow7.e0P, Wire] at *; omega)
      · obtain ⟨v, hv, eq⟩ := List.mem_map.mp mem
        have hv' := List.mem_range.mp hv
        have hs : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, start]; omega
        rw [hs] at eq
        have qv : (q : Nat) = Shadow7.scratchS (start k) v := eq.symm
        rcases Shadow7.scratchS_cases (start k) v (by omega) hv' with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;>
          (simp only [Wire] at *; omega)
  exact Shadow7.ext_head (Shadow7.enterP k) k (NativeJ7.withArchive k d) _ s _ _ q native
    (EnterJ7.notWire k port) admin (NativeJ7.admin_cover k (by omega) h24 d)

private theorem keep_leave150 (t : Nat) (ht0 : 60 ≤ t) (ht1 : t ≤ 150) (q : Wire) (hq : q ∈ cellsRestoreP t)
    (s : State) (m : List Bool) :
    (run leave150To20Red m s).basis q = s.basis q := by
  have c := StockWindowW7.cells_rangeG t (by omega) q hq
  rcases c with c | c | c
  · exact leave150To20Red_keeps q (by unfold Shadow7.leaveBox2 Shadow7.a0P Shadow7.b0P Shadow7.sbP railP; simp only [Wire] at *; split_ifs <;> omega) m s
  · exact leave150To20Red_keeps q (by unfold Shadow7.leaveBox2 Shadow7.a0P Shadow7.b0P Shadow7.sbP railP; simp only [Wire] at *; split_ifs <;> omega) m s
  · exact leave150To20Red_keeps_mirror q (by simp only [Wire] at *; omega) m s

private theorem keep_leave20 (j : Fin 9) (t : Nat) (ht0 : 60 ≤ t) (ht1 : t ≤ start20 j) (q : Wire) (hq : q ∈ cellsRestoreP t)
    (s : State) (m : List Bool) :
    (run (leaveP20Red j) m s).basis q = s.basis q := by
  have hg := geom20_facts j
  have hbt : bTopP (start20 j) ≤ 1043 := by unfold bTopP railP; split_ifs <;> omega
  have c := StockWindowW7.cells_rangeG t (by omega) q hq
  rcases c with c | c | c
  · exact leaveP20Red_keeps j q (by unfold leaveBox20 a0P20 b0P20; simp only [Wire] at *; omega) m s
  · exact leaveP20Red_keeps j q (by unfold leaveBox20 a0P20 b0P20; simp only [Wire] at *; omega) m s
  · exact leaveP20Red_keeps_mirror j q (by simp only [Wire] at *; omega) m s

private theorem keep_cells_20 (j : Fin 9) (d : Bool) (t : Nat) (ht0 : 60 ≤ t)
    (ht1 : t + prevLen20 j ≤ start20 j) (q : Wire) (hq : q ∈ cellsRestoreP t)
    (s : State) (m : List Bool) :
    (run (nextWindow20 j d ++ leaveP20Red j) m s).basis q = s.basis q := by
  have hg := geom20_facts j
  have hpl : 15 ≤ prevLen20 j ∧ prevLen20 j ≤ 20 := by unfold prevLen20; split_ifs <;> omega
  have c := StockWindowW7.cells_rangeG t (by omega) q hq
  rw [run_append, run_take, keep_leave20 j t ht0 (by omega) q hq]
  simp only [nextWindow20, window20, run_append, run_take]
  have native : ¬ MayTouch20 j (windowNet20 j q) := by
    have mid : (shape20 j).mid = sbP20 (start20 j) + 20 := rfl
    rcases c with c | c | c
    · rw [show windowNet20 j q = q from NativeJ7.sig_kept _ _ (by omega) (by omega)]
      unfold MayTouch20; rw [mid]; simp only [Wire] at *; omega
    · rw [show windowNet20 j q = q from NativeJ7.sig_kept _ _ (by omega) (by omega)]
      unfold MayTouch20; rw [mid]; simp only [Wire] at *; omega
    · rw [show windowNet20 j q = 3113 - q from NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, c.2.2⟩)]
      unfold MayTouch20; rw [mid]; simp only [Wire] at *; omega
  have port : q ∉ EnterJ20.ports j := fun hm => by
    have r := EnterJ20.portsRegion j hm
    have hsum : ∀ m : Fin 9, e0P20 (start20 m) + start20 m ≤ 2045 := by decide +kernel
    have := hsum j; simp only [EnterJ20.h20, e0P20, Wire] at *; omega
  have admin : q ∉ support20 j ++ prevRawPortsList20 j := by
    rw [List.mem_append, prevRaw_split, List.mem_append]
    rintro (mem | mem | mem)
    · simp only [support20, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at mem
      obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
      · have hv : start20 j - prevLen20 j ≤ v ∧ v < start20 j := by
          unfold prevLen20 at *; split_ifs at v1 v2 ⊢ <;> (try simp only [start20] at *) <;> omega
        rw [NativeJ7.sig_kept _ _ (by simp only [base, Wire] at *; omega) (by simp only [base, Wire] at *; omega)] at e
        simp only [base, Wire] at *; omega
      · have hv : start20 j - prevLen20 j ≤ v ∧ v < start20 j := by
          unfold prevLen20 at *; split_ifs at v1 v2 ⊢ <;> (try simp only [start20] at *) <;> omega
        by_cases mv : 1301 ≤ 1044 + v
        · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨by simp only [base, Wire] at *; omega, by simp only [base, Wire] at *; omega⟩)] at e
          simp only [base, Wire] at *; omega
        · rw [NativeJ7.sig_kept _ _ (by simp only [base, Wire] at *; omega) (by simp only [base, Wire] at *; omega)] at e
          simp only [base, Wire] at *; omega
    · have hhead : prevRawHead20 j = cellsLoadP (start20 j) ++ [e0P20 (start20 j) + 6, e0P20 (start20 j) + 7, e0P20 (start20 j) + 8] := by
        unfold prevRawHead20; split_ifs with h0
        · simp only [Archive150.rawHead, Archive150.flagBase, show start20 j = 165 by simp [start20, h0]]
        · simp only [ArchiveJ20.rawHead, ArchiveJ20.endTick, ArchiveJ20.flagBase]
          have hpv : (prev20 j).val = j.val - 1 := rfl
          have he : start20 (prev20 j) + 20 = start20 j := by unfold start20; rw [hpv]; omega
          have hn : nextE0_20 (start20 (prev20 j)) = e0P20 (start20 j) := by unfold nextE0_20; rw [he, if_pos (by omega)]
          rw [he, hn]
      rw [hhead, cellsLoadP, List.mem_append] at mem
      rcases mem with mem | mem
      · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at mem
        obtain ⟨v, hv, e | e⟩ := mem
        · simp only [Wire] at *; omega
        · by_cases mv : 1301 ≤ start20 j + 1034 + v
          · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e; simp only [Wire] at *; omega
          · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)] at e; simp only [Wire] at *; omega
      · have hsum : ∀ m : Fin 9, e0P20 (start20 m) + start20 m ≤ 2045 := by decide +kernel
        have := hsum j
        simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl <;> (simp only [Wire] at *; omega)
    · have sb : 1556 ≤ (q : Nat) ∧ (q : Nat) < 1700 := by
        unfold prevScratch20 at mem; split_ifs at mem with h0
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp mem; rw [List.mem_range] at hv
          unfold archScratch150; split_ifs <;> (unfold Wire; omega)
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp mem; rw [List.mem_range] at hv
          unfold archScratch20; dsimp only; split_ifs <;> (unfold Wire; omega)
      simp only [Wire] at *; omega
  exact ext_head20 (enterP20 j) j (withArchive20 j d) _ s _ _ q native (EnterJ20.notWire j port) admin (admin_cover20 j d)

private theorem keep_cells_345 (d : Bool) (t : Nat) (ht0 : 60 ≤ t) (ht1 : t ≤ 325)
    (q : Wire) (hq : q ∈ cellsRestoreP t) (s : State) (m : List Bool) :
    (run (nextWindow345 d ++ CRTBarrel.leave MixedWindow.j20) m s).basis q = s.basis q := by
  have c := StockWindowW7.cells_rangeG t (by omega) q hq
  rw [run_append, run_take]
  rw [CRTWindow.leave_keeps MixedWindow.j20 (by decide) (by decide) q (by
    unfold Shadow7.leaveBox2 Shadow7.a0P Shadow7.b0P Shadow7.sbP railP
    rw [show start MixedWindow.j20 = 345 from rfl]; simp only [Wire] at *; split_ifs <;> omega)]
  simp only [nextWindow345, window345, run_append, run_take]
  have native : ¬ Shadow7.MayTouch MixedWindow.j20 (windowNet MixedWindow.j20 q) := by
    have mid : (Shadow7.shape MixedWindow.j20).mid = 91 := by decide
    rcases c with c | c | c
    · rw [show windowNet MixedWindow.j20 q = q from NativeJ7.sig_kept 359 q (by omega) (by omega)]
      unfold Shadow7.MayTouch; rw [mid]; rw [show start MixedWindow.j20 = 345 from rfl]; simp only [Wire] at *; omega
    · rw [show windowNet MixedWindow.j20 q = q from NativeJ7.sig_kept 359 q (by omega) (by omega)]
      unfold Shadow7.MayTouch; rw [mid]; rw [show start MixedWindow.j20 = 345 from rfl]; simp only [Wire] at *; omega
    · rw [show windowNet MixedWindow.j20 q = 3113 - q from NativeJ7.sig_moved 359 q (Or.inr ⟨by omega, c.2.2⟩)]
      unfold Shadow7.MayTouch; rw [mid]; rw [show start MixedWindow.j20 = 345 from rfl]; simp only [Wire] at *; omega
  have port : q ∉ EnterJ7.ports MixedWindow.j20 := fun hm => by
    have r := EnterJ7.portsRegion MixedWindow.j20 hm
    rw [show start MixedWindow.j20 = 345 from rfl, show Shadow7.sbP 345 = 76 by decide] at r
    simp only [Wire] at *; omega
  have admin : q ∉ support345 ++ ArchiveJ20.rawPortsList MixedWindow.k8 := by
    rw [List.mem_append, ArchiveJ20.raw_split, List.mem_append]
    have hall : (support345 ++ ArchiveJ20.rawHead MixedWindow.k8).all (fun w =>
        decide ((341 ≤ (w : Nat) ∧ (w : Nat) ≤ 360) ∨ (1725 ≤ (w : Nat) ∧ (w : Nat) ≤ 1744) ∨
          (1656 ≤ (w : Nat) ∧ (w : Nat) ≤ 1658))) = true := by decide +kernel
    rintro (h | h | h)
    · have := of_decide_eq_true (List.all_eq_true.mp hall q (List.mem_append_left _ h)); simp only [Wire] at *; omega
    · have := of_decide_eq_true (List.all_eq_true.mp hall q (List.mem_append_right _ h)); simp only [Wire] at *; omega
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h; rw [List.mem_range] at hv
      have sb : 1556 ≤ (archScratch20 (start20 MixedWindow.k8) v : Nat) ∧
          (archScratch20 (start20 MixedWindow.k8) v : Nat) < 1700 := by
        unfold archScratch20; dsimp only; split_ifs <;> (unfold Wire; omega)
      simp only [Wire] at *; omega
  exact Shadow7.ext_head (Shadow7.enterP j20) j20 (withArchive345 d) _ s _ _ q native
    (EnterJ7.notWire MixedWindow.j20 port) admin (admin_cover345 d)

private theorem keep_cells_exit420 (d : Bool) (t : Nat) (ht0 : 60 ≤ t) (ht1 : t ≤ 405)
    (q : Wire) (hq : q ∈ cellsRestoreP t) (s : State) (m : List Bool) :
    (run (exitF CRTBarrel.params d 420).flatten m s).basis q = s.basis q := by
  have c := StockWindowW7.cells_rangeG t (by omega) q hq
  simp only [exitF, CRTBarrel.params, Shadow7.params, ofParts, List.flatten_cons, List.flatten_nil,
    List.append_nil, run_append, run_take]
  rw [run_preserves_outside (Shadow7.exitLoadP 420 d) _ _ q (fun hit => by
    have r := StockWindowW7.raw420_ranges q (List.mem_toFinset.mp (ArchiveBoundary4207.load_cover d hit))
    simp only [Wire] at *; omega)]
  rw [run_preserves_outside _ _ _ q (fun hit => by
    rw [renameProgram_support] at hit
    obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hit
    have pc := (WindowCovered.pack_cells d 410 (by decide) (by decide)).1 w hw
    obtain ⟨r, r1, r2, er | er⟩ := pc
    · rw [er, NativeJ7.sig_kept 420 _ (by simp only [base, Wire]; omega) (by simp only [base, Wire]; omega)] at e
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> (simp only [base, Wire] at *; omega)
    · rw [er, NativeJ7.sig_moved 420 _ (Or.inl ⟨by simp only [base, Wire]; omega, by simp only [base, Wire]; omega⟩)] at e
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> (simp only [base, Wire] at *; omega))]
  have nt : q ∉ wires (renameProgram (OB5.sig 420) (TickRanges.tick base 420)) :=
    EndTick4207.physical_free EndTick4207.P EndTick4207.supports.1 q (by
      apply WideReference.away (by decide)
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        exact ⟨q - 16, by omega, Or.inl (by simp only [base, Wire]; omega)⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        exact ⟨q - 1044, by omega, Or.inr (by simp only [base, Wire]; omega)⟩
      · rw [NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, hh⟩)]
        exact ⟨2069 - q, by omega, Or.inr (by simp only [base, Wire]; omega)⟩)
  rw [run_preserves_outside _ _ _ q nt]
  rw [run_preserves_outside (Shadow7.portalInvP 420) _ _ q (fun hit => by
    have f := StockWindowW7.portalInv_low420 q hit
    have f2 := (Shadow7.portal_wires 420 (by decide) (by decide)).2 q hit
    have hr : railP 420 = 93 := by decide
    unfold footP at f2; rw [hr] at f2
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> (simp only [Wire] at *; omega))]
  rw [run_preserves_outside (Shadow7.parkP 420) _ _ q (fun hit => by
    have f := StockWindowW7.park_low420 q hit
    have f2 := (Shadow7.park_wires 420 (by decide) (by decide)).1 q hit
    have hr : railP 420 = 93 := by decide
    unfold parkFootP at f2; rw [hr] at f2
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> (simp only [Wire] at *; omega))]

/-! ### Section 5: 7-Chunk Strong Composition (`MixedChain.strong`) -/

private theorem chunk1_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked
      ([Shadow7.portalP 45, Shadow7.enterP MixedWindow.j0, Shadow7.routed MixedWindow.j0 0 1,
        MixedWindow.packW d 45 45, Shadow7.routed MixedWindow.j0 1 14, CRTBarrel.leave MixedWindow.j0]).flatten
      ([CRTBarrel.unleave MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
        MixedWindow.unpackW d 45 45, Shadow7.unrouted MixedWindow.j0 0 1,
        Shadow7.enterInvP MixedWindow.j0, Shadow7.portalInvP 45]).flatten
      (BeforeW d x p) (fun s => ReadyW d x p 60 s ∧ SavedBefore d x p 0 s) := by
  have h := StockWindowW7.firstStepG 24 StockWindowW7.leaves22 d x p good
  intro s m hb
  obtain ⟨ph, post, undo⟩ := h s m hb
  exact ⟨ph, ⟨post, fun b hb0 => by omega⟩, undo⟩

private theorem chunk15_step (d : Bool) (x : Nat) (good : Bounds x p)
    (i k : Fin 26) (hk : k.val = i.val + 1) (h1 : 1 ≤ k.val) (h24 : k.val ≤ 24)
    (n : Nat) (bNew : MixedGeo.Bank)
    (hbn : bNew.val = n)
    (hb_ports : MixedGeo.bankPorts StockWindowChainP.ExitPorts420 bNew = ArchiveJ7.codePorts i)
    (hb_key : mixedKey x p bNew = value x p (start i) (Shadow7.sbP (start i)) (StockRowVectorW.crossW i))
    (hprev : ∀ b : MixedGeo.Bank, b.val < n → MixedGeo.endTick b + 15 ≤ start k) :
    Checked (MixedWindow.block15F d i k).flatten (TickCut.Mixed.block15R d i k).flatten
      (fun s => ReadyW d x p (start k) s ∧ SavedBefore d x p n s)
      (fun s => ReadyW d x p (start k + 15) s ∧ SavedBefore d x p (n + 1) s) := by
  have step := StockWindowW7.interiorG 24 (by decide) StockWindowW7.leaves22 d x p good i k hk h1 h24
  have hrec := StockWindowChainP.receiptS d x p good i k hk h1 h24
  have hfe : (MixedWindow.block15F d i k).flatten = (nextF CRTBarrel.params d i k).flatten := by
    simp only [MixedWindow.block15F, MixedWindow.packW, nextF, CRTBarrel.params, Shadow7.params, ofParts,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  have hre : (TickCut.Mixed.block15R d i k).flatten = (nextR CRTBarrel.params d i k).flatten := by
    simp only [TickCut.Mixed.block15R, MixedWindow.unpackW, nextR, CRTBarrel.params, Shadow7.params, ofParts,
      TickCut.Tail.selected14_eq, TickCut.Tail.sel01, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
  rw [hfe, hre]
  intro s m ⟨hr, hs⟩
  obtain ⟨ph, post, undo⟩ := step s m hr
  refine ⟨ph, ⟨post, fun b hb => ?_⟩, undo⟩
  by_cases he : b.val = n
  · have hbeq : b = bNew := Fin.ext (he.trans hbn.symm)
    subst hbeq
    unfold BankKey
    rw [hb_ports, hb_key]
    exact hrec s m hr
  · have hlt : b.val < n := by omega
    exact keep_savedKey (hs b hlt) (fun q hq => by
      rw [← hfe]; exact keep_cells_15 i k hk h1 h24 d (MixedGeo.endTick b) (bank_tick_match b).2.2.2.2.1
        (hprev b hlt) q (bank_cells_mem b q hq) s m)

private theorem chunk2_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (MixedWindow.prefixPairs.flatMap fun p => MixedWindow.block15F d p.1 p.2).flatten
      (MixedWindow.prefixPairs.reverse.flatMap fun p => TickCut.Mixed.block15R d p.1 p.2).flatten
      (fun s => ReadyW d x p 60 s ∧ SavedBefore d x p 0 s)
      (fun s => ReadyW d x p 150 s ∧ SavedBefore d x p 6 s) := by
  have mk (n : Nat) (hn : n < 6) :=
    chunk15_step d x good ⟨n, by omega⟩ ⟨n + 1, by omega⟩ rfl (by dsimp; omega) (by dsimp; omega) n ⟨n, by omega⟩ rfl
      (by simp only [MixedGeo.bankPorts, dif_pos (show n < 7 by omega)])
      (by unfold mixedKey; rw [dif_pos (show n < 7 by omega)])
      (fun b hb => by
        have h : ∀ k : MixedGeo.Bank, k.val < 6 → ∀ m : Nat, m < 6 → k.val < m → MixedGeo.endTick k + 15 ≤ 45 + 15 * (m + 1) := by
          decide +kernel
        exact h b (by omega) n hn hb)
  have c := composition (mk 0 (by decide)) (composition (mk 1 (by decide)) (composition (mk 2 (by decide))
    (composition (mk 3 (by decide)) (composition (mk 4 (by decide)) (mk 5 (by decide))))))
  simpa only [MixedWindow.prefixPairs, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatten_append, List.append_assoc] using c

theorem flags15_eq (s x p : Nat) (g sg : Bool) :
    LeaveJ7.Admission.flags (unsigned s x p) g sg =
      SharedSigned.flags g sg (SkywalkTrace.trace 15 (signedAt s x p g sg)) := rfl

theorem flags20_eq (s x p : Nat) (g sg : Bool) :
    flags20 (unsigned s x p) g sg =
      SharedSigned.flags g sg (SkywalkTrace.trace 20 (signedAt s x p g sg)) := rfl

private theorem eraseSites_phase (ws : List Wire) (s : State) : (eraseSites ws s).phase = s.phase := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih => exact ih _

private theorem pullState_phase (f : Wire → Wire) (s : State) : (pullState f s).phase = s.phase := rfl

private theorem chunk3_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked
      ([Shadow7.enterP MixedWindow.j7, Shadow7.routed MixedWindow.j7 0 1, MixedWindow.packW d 150 140,
        Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, leave150To20Red]).flatten
      ([leaveInv150To20Red, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14, Shadow7.archiveRestoreP MixedWindow.j6 d,
        MixedWindow.unpackW d 150 140, Shadow7.unrouted MixedWindow.j7 0 1, Shadow7.enterInvP MixedWindow.j7]).flatten
      (fun s => ReadyW d x p 150 s ∧ SavedBefore d x p 6 s)
      (fun s => Ready20 ⟨0, by decide⟩ d x p s ∧ SavedBefore d x p 7 s) := by
  have hfl : ([Shadow7.enterP MixedWindow.j7, Shadow7.routed MixedWindow.j7 0 1, MixedWindow.packW d 150 140,
      Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, leave150To20Red]).flatten =
      NativeJ7.nextWindow MixedWindow.j7 d ++ leave150To20Red := by
    simp only [NativeJ7.nextWindow, NativeJ7.window, Shadow7.body, NativeJ7.withArchive, NativeJ7.program,
      MixedWindow.packW, show NativeJ7.prev MixedWindow.j7 = MixedWindow.j6 from rfl,
      show start MixedWindow.j7 = 150 from rfl,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  have hrl : ([leaveInv150To20Red, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14, Shadow7.archiveRestoreP MixedWindow.j6 d,
      MixedWindow.unpackW d 150 140, Shadow7.unrouted MixedWindow.j7 0 1, Shadow7.enterInvP MixedWindow.j7]).flatten =
      leaveInv150To20Red ++ NativeJ7.nextUnwind MixedWindow.j7 d := by
    simp only [NativeJ7.nextUnwind, NativeJ7.unwind, TickCut.Tail.unbodySelected, TickCut.Tail.selected14_eq,
      TickCut.Tail.sel01,
      NativeJ7.fromArchive, NativeJ7.reverse,
      MixedWindow.unpackW, show NativeJ7.prev MixedWindow.j7 = MixedWindow.j6 from rfl,
      show start MixedWindow.j7 = 150 from rfl,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  rw [hfl, hrl]
  intro s m ⟨hr, hs⟩
  obtain ⟨k, ek, raw, g, sg, pg, ps, pre⟩ := hr
  have hk7 : k = MixedWindow.j7 := Fin.ext (by simp only [start] at ek; show k.val = 7; omega)
  subst hk7
  have hs150 : start MixedWindow.j7 = 150 := rfl
  have hdom150 : Domain 150 x p raw := hs150 ▸ pre.domain
  have hinp150 : InputAt 150 (signedAt 150 x p g sg) raw := hs150 ▸ pre.input
  have hcut150 := pre.cut
  rw [hs150] at hcut150
  have nums := LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good
  have old := LeaveJ7.Admission.actualNumbers MixedWindow.j6 (by decide) (by decide) x p good
  have hist := WideReference.pulled_history MixedWindow.j7 rfl pre.domain
  have inp := readInput 150 x p raw g sg hinp150
  have scr := StockWindowW7.leaves22.scratch MixedWindow.j7 (by decide) (by decide) d x p good raw s g sg pg ps m pre
  have nat := NativeJ7.from_domain_matched MixedWindow.j7 (by decide) (by decide) d x p good raw s m pre.domain g sg pre.cut (hs150.symm ▸ inp) scr pg ps _ pre.facts
  have ep := endpoint150To20 d x p good raw s m (m.drop (measurementCount (NativeJ7.nextWindow MixedWindow.j7 d)))
    hdom150 g sg hcut150 inp scr pg ps _ pre.facts
  have carried := stepInput_gen_shadow7 150 (Shadow7.sbP 150) x p (by decide) (by decide) good raw
    (run (NativeJ7.nextWindow MixedWindow.j7 d) m s) g sg hdom150 hinp150 (hs150 ▸ nums.farSmall)
  have canon := unique_input hinp150 (fixed_input 150 x p (by decide) good raw hdom150)
  have hnextSmall20 : Shadow7.SmallIfFar 163 20 (SkywalkNat.step^[15] (unsigned 150 x p)) := by
    have hs165 : start20 ⟨0, by decide⟩ = 165 := rfl
    have hsb163 : sbP20 (start20 ⟨0, by decide⟩) = 163 := rfl
    have h1 := (actualNumbers20 ⟨0, by decide⟩ x p good).small.1
    rw [hsb163, hs165] at h1
    have he165 : SkywalkNat.step^[15] (unsigned 150 x p) = unsigned 165 x p := by
      show SkywalkNat.step^[15] (SkywalkNat.step^[150] (SkywalkNat.init x p)) = SkywalkNat.step^[165] (SkywalkNat.init x p)
      rw [show (165 : Nat) = 150 + 15 by decide, Nat.add_comm, Function.iterate_add_apply]
    rw [he165]; exact h1
  have hred150 := leave150To20Red_pair (run (NativeJ7.nextWindow MixedWindow.j7 d) m s) (unsigned 150 x p) g sg nat.1 hnextSmall20
  have hph : (run (NativeJ7.nextWindow MixedWindow.j7 d ++ leave150To20Red) m s).phase = s.phase := by
    rw [run_append, run_take, hred150.1]
    have cph := ep.1.phase
    rw [eraseSites_phase, pullState_phase] at cph
    have hcp := hcut150.phase
    rw [eraseSites_phase, pullState_phase] at hcp
    have eph := WideReference.endRaw_phase 150 x p (by decide) good raw (run (NativeJ7.nextWindow MixedWindow.j7 d) m s) hdom150
    exact cph.trans (eph.trans hcp.symm)
  refine ⟨hph, ⟨?_, ?_⟩, ?_⟩
  · rw [run_append, run_take, hred150.1]
    have h165 : (150 : Nat) + 15 = start20 ⟨0, by decide⟩ := rfl
    have hpt0 : (150 : Nat) = prevTick20 ⟨0, by decide⟩ := rfl
    refine ⟨WideReference.endRaw 150 raw (run (NativeJ7.nextWindow MixedWindow.j7 d) m s),
      (LeaveJ7.Admission.flags (unsigned 150 x p) g sg).1,
      (LeaveJ7.Admission.flags (unsigned 150 x p) g sg).2, g, sg,
      ⟨h165 ▸ carried.1, ?_, ?_, ?_, hpt0 ▸ canon⟩⟩
    · rw [← h165, flags15_eq]; exact carried.2
    · simpa only [← h165] using ep.1
    · simpa only [PrevPast20, prevTick20, prevCross20, ↓reduceIte] using ep.2.1
  · intro b hb
    rw [run_append, run_take]
    by_cases h6 : b.val = 6
    · have hbeq : b = ⟨6, by decide⟩ := Fin.ext h6
      subst hbeq
      have cert := NativeJ7.selected_receipt MixedWindow.j7 (by decide) (by decide) d raw s m
        (unsigned 150 x p) g sg (hs150 ▸ nums.odd) (hs150 ▸ nums.farSmall) (hs150 ▸ pre.cut) (hs150.symm ▸ inp) hist scr
        (unsigned 135 x p) pg ps _ (by simpa only [show start MixedWindow.j6 = 135 from rfl] using old.odd)
        (by simpa only [show start MixedWindow.j6 = 135 from rfl] using old.farSmall)
        (by simpa only [show start (NativeJ7.prev MixedWindow.j7) = 135 from rfl] using pre.facts)
      have hpc := pre.pastCanonical
      rw [show start (NativeJ7.prev MixedWindow.j7) = 135 from rfl] at hpc
      unfold signedAt at hpc; dsimp only at cert; rw [hpc] at cert
      have hk6 : BankKey d x p ⟨6, by decide⟩ (run (NativeJ7.nextWindow MixedWindow.j7 d) m s) := by
        unfold BankKey MixedGeo.bankPorts mixedKey
        simp only [show (6 : Nat) < 7 by decide, ↓reduceDIte]
        rw [show NativeJ7.prev MixedWindow.j7 = ⟨6, by decide⟩ from rfl] at cert
        exact ⟨cert.1, cert.2.1, cert.2.2⟩
      exact keep_savedKey hk6 (fun q hq => keep_leave150 150 (by decide) (by decide) q (bank_cells_mem ⟨6, by decide⟩ q hq) _ _)
    · have hlt : b.val < 6 := by omega
      have hend : MixedGeo.endTick b ≤ 135 := by
        have h : ∀ k : MixedGeo.Bank, k.val < 6 → MixedGeo.endTick k ≤ 135 := by decide +kernel
        exact h b hlt
      exact keep_savedKey (hs b hlt) (fun q hq => by
        rw [keep_leave150 (MixedGeo.endTick b) (bank_tick_match b).2.2.2.2.1 (by omega) q (bank_cells_mem b q hq)]
        have h15 := keep_cells_15 MixedWindow.j6 MixedWindow.j7 rfl (by decide) (by decide) d
          (MixedGeo.endTick b) (bank_tick_match b).2.2.2.2.1 (by show MixedGeo.endTick b + 15 ≤ 150; omega)
          q (bank_cells_mem b q hq) s m
        have hfl15 : (MixedWindow.block15F d MixedWindow.j6 MixedWindow.j7).flatten =
            NativeJ7.nextWindow MixedWindow.j7 d ++ CRTBarrel.leave MixedWindow.j7 := by
          simp only [MixedWindow.block15F, MixedWindow.packW, NativeJ7.nextWindow, NativeJ7.window,
            Shadow7.body, NativeJ7.withArchive, NativeJ7.program,
            show NativeJ7.prev MixedWindow.j7 = MixedWindow.j6 from rfl,
            show start MixedWindow.j7 = 150 from rfl,
            List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
        rw [hfl15, run_append, run_take, CRTWindow.leave_keeps MixedWindow.j7 (by decide) (by decide) q (by
          have c := bank_range b q hq
          have h60 := (bank_tick_match b).2.2.2.2.1
          unfold Shadow7.leaveBox2 Shadow7.a0P Shadow7.b0P Shadow7.sbP railP
          rw [show start MixedWindow.j7 = 150 from rfl]
          simp only [Wire] at *; split_ifs <;> omega)] at h15
        exact h15)
  · intro t
    rw [run_append, run_take, run_append, run_take, hred150.2 _ t, nat.2.2.2]

private theorem endRaw_phase20 (s prevLen x p : Nat) (lim : s + 20 ≤ 512) (good : Bounds x p)
    (raw history : State) (dom : Domain s x p raw) :
    (WideReference20.endRaw s prevLen 20 raw history).phase = raw.phase := by
  show (run (span s 20) [] raw).phase = raw.phase
  obtain ⟨ref, same, stage⟩ := dom
  have match' := WideReference.fixed_span s s 20 (Nat.le_refl _) lim raw ref [] same
  exact match'.1.trans ((WideReference.span_phase s 20 x p lim good ref [] stage).trans same.1.symm)

private theorem endTick20_eq :
    ∀ r : Fin 9, MixedGeo.endTick ⟨7 + r.val, by have := r.isLt; omega⟩ = start20 r := by
  decide +kernel

private theorem block20_flatten (d : Bool) (j : Fin 9) :
    (MixedWindow.block20F d j).flatten = nextWindow20 j d ++ leaveP20Red j ∧
    (TickCut.Mixed.block20R d j).flatten = leaveInvP20Red j ++ TickCut.Wide.nextUnwind20 j d := by
  unfold MixedWindow.block20F TickCut.Mixed.block20R nextWindow20 window20 body20 withArchive20 packProg20 archLoad20
    TickCut.Wide.nextUnwind20 TickCut.Wide.unwind20 TickCut.Wide.unbodySelected fromArchive20 packRev20 archRestore20
    prev20
  by_cases h0 : j.val = 0
  · simp only [h0, ↓reduceDIte, ↓reduceIte, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
      and_self]
  · simp only [h0, ↓reduceDIte, ↓reduceIte, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc,
      and_self]

private theorem step20_next_checked (d : Bool) (x : Nat) (good : Bounds x p)
    (j k : Fin 9) (hk : k.val = j.val + 1) :
    Checked (MixedWindow.block20F d j).flatten (TickCut.Mixed.block20R d j).flatten
      (fun s => Ready20 j d x p s ∧ SavedBefore d x p (7 + j.val) s)
      (fun s => Ready20 k d x p s ∧ SavedBefore d x p (7 + j.val + 1) s) := by
  have hj := j.isLt
  rw [(block20_flatten d j).1, (block20_flatten d j).2]
  intro s m ⟨⟨raw, g, sg, pg, ps, pre⟩, hs⟩
  have nums := actualNumbers20 j x p good
  have hist := WideReference20.pulled_history20 j pre.domain
  have inp := readInput (start20 j) x p raw g sg pre.input
  let preS := run (enterP20 j) m s
  let tape := m.drop (measurementCount (enterP20 j))
  let T := Shadow.reduced (sbP20 (start20 j)) 20 (unsigned (start20 j) x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 (start20 j)) (unsigned (start20 j) x p) nums.small.1 nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ20.ready_pending_at j raw s (unsigned (start20 j) x p) g sg m nums.small.1 pre.cut inp hist
  have scr := scratch_raw_clean20 j d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut
  have prevOdd : (unsigned (prevTick20 j) x p).v % 2 = 1 := by
    unfold prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).odd
    · exact (actualNumbers20 (prev20 j) x p good).odd
  have prevSm : PrevSmall20 j (unsigned (prevTick20 j) x p) := by
    unfold PrevSmall20 prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).farSmall
    · exact (actualNumbers20 (prev20 j) x p good).small.1
  have adm := TickCut.Leaf20.admitted20 j d x p good raw s m pre.domain g sg pre.cut inp scr
    (unsigned (prevTick20 j) x p) pg ps (prevCross20 j x p) prevOdd prevSm pre.facts
  have ep := endpoint20_next j k hk d x p good raw s m (m.drop (measurementCount (nextWindow20 j d)))
    pre.domain g sg pre.cut inp scr (unsigned (prevTick20 j) x p) pg ps (prevCross20 j x p) prevOdd prevSm pre.facts
  have hprev_le : prevLen20 j ≤ start20 j := by unfold prevLen20 start20; split_ifs <;> omega
  have carried := WideReference20.stepInput20 (start20 j) (prevLen20 j) (sbP20 (start20 j)) x p hprev_le (by unfold start20; omega)
    good raw (run (nextWindow20 j d) m s) g sg pre.domain pre.input nums.small.1
  have canon := unique_input pre.input (fixed_input (start20 j) x p (by unfold start20; omega) good raw pre.domain)
  have hsk : start20 k = start20 j + 20 := by unfold start20; omega
  have hpk : prev20 k = j := Fin.ext (by simp only [prev20]; omega)
  have hred20 := leaveP20Red_pair j (run (nextWindow20 j d) m s) (unsigned (start20 j) x p) g sg adm.1
  have hph : (run (nextWindow20 j d ++ leaveP20Red j) m s).phase = s.phase := by
    rw [run_append, run_take, hred20.1]
    have cph := ep.1.phase
    rw [eraseSites_phase, pullState_phase] at cph
    have hcp := pre.cut.phase
    rw [eraseSites_phase, pullState_phase] at hcp
    have eph := endRaw_phase20 (start20 j) (prevLen20 j) x p (by unfold start20; omega) good raw
      (run (nextWindow20 j d) m s) pre.domain
    exact cph.trans (eph.trans hcp.symm)
  refine ⟨hph, ⟨?_, ?_⟩, ?_⟩
  · rw [run_append, run_take, hred20.1]
    refine ⟨WideReference20.endRaw (start20 j) (prevLen20 j) 20 raw (run (nextWindow20 j d) m s),
      (flags20 (unsigned (start20 j) x p) g sg).1, (flags20 (unsigned (start20 j) x p) g sg).2, g, sg,
      ⟨hsk ▸ carried.1, by rw [flags20_eq]; exact hsk ▸ carried.2, ep.1, ?_, ?_⟩⟩
    · simp only [PrevPast20, prevTick20, prevCross20, if_neg (show k.val ≠ 0 by omega), hpk]; exact ep.2
    · simp only [prevTick20, if_neg (show k.val ≠ 0 by omega), hpk]; exact canon
  · intro b hb
    rw [run_append, run_take]
    by_cases he : b.val = 7 + j.val
    · have hbeq : b = ⟨7 + j.val, by omega⟩ := Fin.ext he
      rw [hbeq]
      have hrec := selected_receipt20 j d x p good raw s g sg pg ps m pre
      have hp : MixedGeo.bankPorts StockWindowChainP.ExitPorts420 ⟨7 + j.val, by omega⟩ = prevCodePorts20 j := by
        unfold MixedGeo.bankPorts prevCodePorts20
        by_cases h0 : j.val = 0
        · simp only [h0, Nat.add_zero, show ¬ ((7 : Nat) < 7) by decide, ↓reduceDIte, ↓reduceIte]
        · simp only [h0, show ¬ (7 + j.val < 7) by omega, show ¬ (7 + j.val = 7) by omega,
            show 7 + j.val < 17 by omega, ↓reduceDIte, ↓reduceIte]
          congr 1; apply Fin.ext; simp [prev20]; omega
      have hbk : BankKey d x p ⟨7 + j.val, by omega⟩ (run (nextWindow20 j d) m s) := by
        unfold BankKey; rw [hp]; exact hrec
      have hend : MixedGeo.endTick ⟨7 + j.val, by omega⟩ = start20 j := endTick20_eq j
      exact keep_savedKey hbk (fun q hq => keep_leave20 j (MixedGeo.endTick ⟨7 + j.val, by omega⟩)
        (bank_tick_match _).2.2.2.2.1 (by omega) q (bank_cells_mem _ q hq) _ _)
    · have hlt : b.val < 7 + j.val := by omega
      have hend : MixedGeo.endTick b + prevLen20 j ≤ start20 j := by
        have h : ∀ r : Fin 9, ∀ k' : MixedGeo.Bank, k'.val < 7 + r.val → MixedGeo.endTick k' + prevLen20 r ≤ start20 r := by
          decide +kernel
        exact h j b hlt
      exact keep_savedKey (hs b hlt) (fun q hq => by
        have hk := keep_cells_20 j d (MixedGeo.endTick b) (bank_tick_match b).2.2.2.2.1 hend q (bank_cells_mem b q hq) s m
        rw [run_append, run_take] at hk; exact hk)
  · intro t
    rw [run_append, run_take, run_append, run_take,
      hred20.2 _ t, adm.2.2.2.2]

private theorem step20_last_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (MixedWindow.block20F d MixedWindow.k8).flatten (TickCut.Mixed.block20R d MixedWindow.k8).flatten
      (fun s => Ready20 MixedWindow.k8 d x p s ∧ SavedBefore d x p 15 s)
      (fun s => Ready345 d x p s ∧ SavedBefore d x p 16 s) := by
  rw [(block20_flatten d MixedWindow.k8).1, (block20_flatten d MixedWindow.k8).2]
  intro s m ⟨⟨raw, g, sg, pg, ps, pre⟩, hs⟩
  have hs325 : start20 MixedWindow.k8 = 325 := rfl
  have hdom325 : Domain 325 x p raw := hs325 ▸ pre.domain
  have hinp325 : InputAt 325 (signedAt 325 x p g sg) raw := hs325 ▸ pre.input
  have hcut325 := pre.cut
  rw [hs325] at hcut325
  have nums := actualNumbers20 MixedWindow.k8 x p good
  have hnums_sm : Shadow7.SmallIfFar (sbP20 325) 20 (unsigned 325 x p) := hs325 ▸ nums.small.1
  have hnums_odd : (unsigned 325 x p).v % 2 = 1 := hs325 ▸ nums.odd
  have hist := WideReference20.pulled_history20 MixedWindow.k8 pre.domain
  have inp := readInput 325 x p raw g sg hinp325
  let preS := run (enterP20 MixedWindow.k8) m s
  let tape := m.drop (measurementCount (enterP20 MixedWindow.k8))
  let T := Shadow.reduced (sbP20 325) 20 (unsigned 325 x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 325) (unsigned 325 x p) hnums_sm hnums_odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ20.ready_pending_at MixedWindow.k8 raw s (unsigned (start20 MixedWindow.k8) x p) g sg m nums.small.1 pre.cut (hs325.symm ▸ inp) hist
  have scr := scratch_raw_clean20 MixedWindow.k8 d raw s m x p good pre.domain _ _ _ Z parity (by simpa only [hs325] using ready.2.1) pre.cut
  have hpt305 : prevTick20 MixedWindow.k8 = start20 (prev20 MixedWindow.k8) := rfl
  have prevOdd : (unsigned (prevTick20 MixedWindow.k8) x p).v % 2 = 1 :=
    hpt305.symm ▸ (actualNumbers20 (prev20 MixedWindow.k8) x p good).odd
  have prevSm : PrevSmall20 MixedWindow.k8 (unsigned (prevTick20 MixedWindow.k8) x p) :=
    hpt305.symm ▸ (actualNumbers20 (prev20 MixedWindow.k8) x p good).small.1
  have adm := TickCut.Leaf20.admitted20 MixedWindow.k8 d x p good raw s m pre.domain g sg pre.cut (hs325.symm ▸ inp) scr
    (unsigned (prevTick20 MixedWindow.k8) x p) pg ps (prevCross20 MixedWindow.k8 x p) prevOdd prevSm pre.facts
  have ep := endpoint20_reentry d x p good raw s m (m.drop (measurementCount (nextWindow20 MixedWindow.k8 d)))
    hdom325 g sg hcut325 inp scr (unsigned (prevTick20 MixedWindow.k8) x p) pg ps (prevCross20 MixedWindow.k8 x p) prevOdd prevSm pre.facts
  have carried := WideReference20.stepInput20 325 20 (sbP20 325) x p (by decide) (by decide)
    good raw (run (nextWindow20 MixedWindow.k8 d) m s) g sg hdom325 hinp325 hnums_sm
  have canon := unique_input hinp325 (fixed_input 325 x p (by decide) good raw hdom325)
  have hred20 := leaveP20Red_pair MixedWindow.k8 (run (nextWindow20 MixedWindow.k8 d) m s) (unsigned (start20 MixedWindow.k8) x p) g sg adm.1
  have hph : (run (nextWindow20 MixedWindow.k8 d ++ leaveP20Red MixedWindow.k8) m s).phase = s.phase := by
    rw [run_append, run_take, hred20.1]
    have cph := ep.1.phase
    rw [eraseSites_phase, pullState_phase] at cph
    have hcp := hcut325.phase
    rw [eraseSites_phase, pullState_phase] at hcp
    have eph := endRaw_phase20 325 20 x p (by decide) good raw
      (run (nextWindow20 MixedWindow.k8 d) m s) hdom325
    exact cph.trans (eph.trans hcp.symm)
  refine ⟨hph, ⟨?_, ?_⟩, ?_⟩
  · rw [run_append, run_take, hred20.1]
    have h345 : (325 : Nat) + 20 = 345 := rfl
    exact ⟨WideReference20.endRaw 325 20 20 raw (run (nextWindow20 MixedWindow.k8 d) m s),
      (flags20 (unsigned 325 x p) g sg).1, (flags20 (unsigned 325 x p) g sg).2, g, sg,
      ⟨h345 ▸ carried.1, by rw [← h345, flags20_eq]; exact carried.2, ep.1, ep.2, canon⟩⟩
  · intro b hb
    rw [run_append, run_take]
    by_cases h15 : b.val = 15
    · have hbeq : b = ⟨15, by decide⟩ := Fin.ext h15
      subst hbeq
      have hrec := selected_receipt20 MixedWindow.k8 d x p good raw s g sg pg ps m pre
      have hp : MixedGeo.bankPorts StockWindowChainP.ExitPorts420 ⟨15, by decide⟩ = prevCodePorts20 MixedWindow.k8 := by
        unfold MixedGeo.bankPorts prevCodePorts20
        simp only [show ¬ ((15 : Nat) < 7) by decide, show ¬ ((15 : Nat) = 7) by decide,
          show (15 : Nat) < 17 by decide, show MixedWindow.k8.val ≠ 0 by decide, ↓reduceDIte, ↓reduceIte]
        rfl
      have hbk : BankKey d x p ⟨15, by decide⟩ (run (nextWindow20 MixedWindow.k8 d) m s) := by
        unfold BankKey; rw [hp]; exact hrec
      exact keep_savedKey hbk (fun q hq => keep_leave20 MixedWindow.k8 325 (by decide) (by decide) q (bank_cells_mem ⟨15, by decide⟩ q hq) _ _)
    · have hlt : b.val < 15 := by omega
      have hend : MixedGeo.endTick b + prevLen20 MixedWindow.k8 ≤ start20 MixedWindow.k8 := by
        have h : ∀ k' : MixedGeo.Bank, k'.val < 15 → MixedGeo.endTick k' + prevLen20 MixedWindow.k8 ≤ start20 MixedWindow.k8 := by
          decide +kernel
        exact h b hlt
      exact keep_savedKey (hs b hlt) (fun q hq => by
        have hk := keep_cells_20 MixedWindow.k8 d (MixedGeo.endTick b) (bank_tick_match b).2.2.2.2.1 hend q (bank_cells_mem b q hq) s m
        rw [run_append, run_take] at hk; exact hk)
  · intro t
    rw [run_append, run_take, run_append, run_take,
      hred20.2 _ t, adm.2.2.2.2]

private theorem chunk4_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked ((List.finRange 9).flatMap (MixedWindow.block20F d)).flatten
      ((List.finRange 9).reverse.flatMap (TickCut.Mixed.block20R d)).flatten
      (fun s => Ready20 ⟨0, by decide⟩ d x p s ∧ SavedBefore d x p 7 s)
      (fun s => Ready345 d x p s ∧ SavedBefore d x p 16 s) := by
  have c := composition (step20_next_checked d x good ⟨0, by decide⟩ ⟨1, by decide⟩ rfl)
    (composition (step20_next_checked d x good ⟨1, by decide⟩ ⟨2, by decide⟩ rfl)
    (composition (step20_next_checked d x good ⟨2, by decide⟩ ⟨3, by decide⟩ rfl)
    (composition (step20_next_checked d x good ⟨3, by decide⟩ ⟨4, by decide⟩ rfl)
    (composition (step20_next_checked d x good ⟨4, by decide⟩ ⟨5, by decide⟩ rfl)
    (composition (step20_next_checked d x good ⟨5, by decide⟩ ⟨6, by decide⟩ rfl)
    (composition (step20_next_checked d x good ⟨6, by decide⟩ ⟨7, by decide⟩ rfl)
    (composition (step20_next_checked d x good ⟨7, by decide⟩ ⟨8, by decide⟩ rfl)
      (step20_last_checked d x good))))))))
  have hfr : List.finRange 9 =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
       ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩] := by decide
  rw [hfr]
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatten_append, List.append_assoc] using c

private theorem chunk5_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked
      ([Shadow7.enterP MixedWindow.j20, Shadow7.routed MixedWindow.j20 0 1,
        MixedWindow.packW d 345 330, MixedWindow.packW d 345 335, archiveLoadP20 MixedWindow.k8 d,
        Shadow7.routed MixedWindow.j20 1 14, CRTBarrel.leave MixedWindow.j20]).flatten
      ([CRTBarrel.unleave MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
        archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
        Shadow7.unrouted MixedWindow.j20 0 1, Shadow7.enterInvP MixedWindow.j20]).flatten
      (fun s => Ready345 d x p s ∧ SavedBefore d x p 16 s)
      (fun s => ReadyW d x p 360 s ∧ SavedBefore d x p 17 s) := by
  have hfl : ([Shadow7.enterP MixedWindow.j20, Shadow7.routed MixedWindow.j20 0 1,
      MixedWindow.packW d 345 330, MixedWindow.packW d 345 335, archiveLoadP20 MixedWindow.k8 d,
      Shadow7.routed MixedWindow.j20 1 14, CRTBarrel.leave MixedWindow.j20]).flatten =
      nextWindow345 d ++ CRTBarrel.leave MixedWindow.j20 := by
    simp only [nextWindow345, window345, Shadow7.body, withArchive345, packProg345,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  have hrl : ([CRTBarrel.unleave MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
      archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
      Shadow7.unrouted MixedWindow.j20 0 1, Shadow7.enterInvP MixedWindow.j20]).flatten =
      CRTBarrel.unleave MixedWindow.j20 ++ TickCut.Reentry20.nextUnwind345 d := by
    simp only [TickCut.Reentry20.nextUnwind345, TickCut.Reentry20.unwind345, TickCut.Tail.unbodySelected,
      TickCut.Tail.selected14_eq, TickCut.Tail.sel01, fromArchive345, packRev345,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  rw [hfl, hrl]
  intro s m ⟨⟨raw, g, sg, pg, ps, pre⟩, hs⟩
  have nums := LeaveJ7.Admission.actualNumbers MixedWindow.j20 (by decide) (by decide) x p good
  have inp := readInput 345 x p raw g sg pre.input
  have ep := endpoint345 d x p good raw s m (m.drop (measurementCount (nextWindow345 d)))
    pre.domain g sg pre.cut inp pg ps _ pre.facts
  have domP := rawPack325_domain d x p raw pre.domain
  have inpP := rawPack325_input d raw _ pre.input
  have carried := stepInput_gen_shadow7 345 (Shadow7.sbP 345) x p (by decide) (by decide) good (rawPack325 d raw)
    (run (nextWindow345 d) m s) g sg domP inpP nums.farSmall
  have canon := unique_input pre.input (fixed_input 345 x p (by decide) good raw pre.domain)
  refine ⟨by rw [run_append, run_take]; exact ep.1, ⟨?_, ?_⟩, ?_⟩
  · rw [run_append, run_take]
    exact ⟨⟨21, by decide⟩, rfl, WideReference.endRaw 345 (rawPack325 d raw) (run (nextWindow345 d) m s),
      (LeaveJ7.Admission.flags (unsigned 345 x p) g sg).1,
      (LeaveJ7.Admission.flags (unsigned 345 x p) g sg).2, g, sg,
      ⟨carried.1, by rw [flags15_eq]; exact carried.2, ep.2.1, ep.2.2.1, canon⟩⟩
  · intro b hb
    by_cases h16 : b.val = 16
    · have hbeq : b = ⟨16, by decide⟩ := Fin.ext h16
      subst hbeq
      rw [run_append, run_take]
      have hrec := selected_receipt345 d x p good raw s m pre.domain g sg pre.cut inp pg ps pre.pastCanonical pre.facts
      have hbk : BankKey d x p ⟨16, by decide⟩ (run (nextWindow345 d) m s) := by
        unfold BankKey MixedGeo.bankPorts mixedKey
        simp only [show ¬ ((16 : Nat) < 7) by decide, show ¬ ((16 : Nat) = 7) by decide,
          show (16 : Nat) < 17 by decide, ↓reduceDIte]
        exact hrec
      exact keep_savedKey hbk (fun q hq => CRTWindow.leave_keeps MixedWindow.j20 (by decide) (by decide) q (by
        have c := bank_range ⟨16, by decide⟩ q hq
        unfold Shadow7.leaveBox2 Shadow7.a0P Shadow7.b0P Shadow7.sbP railP
        rw [show start MixedWindow.j20 = 345 from rfl, show MixedGeo.endTick ⟨16, by decide⟩ = 345 by decide] at *
        simp only [Wire] at *; split_ifs <;> omega) _ _)
    · have hlt : b.val < 16 := by omega
      have hend : MixedGeo.endTick b ≤ 325 := by
        have h : ∀ k' : MixedGeo.Bank, k'.val < 16 → MixedGeo.endTick k' ≤ 325 := by decide +kernel
        exact h b hlt
      exact keep_savedKey (hs b hlt) (fun q hq => keep_cells_345 d (MixedGeo.endTick b)
        (bank_tick_match b).2.2.2.2.1 hend q (bank_cells_mem b q hq) s m)
  · intro t
    rw [run_append, run_take, run_append, run_take, ep.2.2.2.1 t, ep.2.2.2.2]

private theorem chunk6_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked (MixedWindow.suffixPairs.flatMap fun p => MixedWindow.block15F d p.1 p.2).flatten
      (MixedWindow.suffixPairs.reverse.flatMap fun p => TickCut.Mixed.block15R d p.1 p.2).flatten
      (fun s => ReadyW d x p 360 s ∧ SavedBefore d x p 17 s)
      (fun s => ReadyW d x p 420 s ∧ SavedBefore d x p 21 s) := by
  have mk (r : Nat) (hr : r < 4) :=
    chunk15_step d x good ⟨20 + r, by omega⟩ ⟨21 + r, by omega⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
      (17 + r) ⟨17 + r, by omega⟩ rfl
      (by unfold MixedGeo.bankPorts
          rw [dif_neg (by dsimp; omega), dif_neg (by dsimp; omega), dif_neg (by dsimp; omega), dif_pos (by dsimp; omega)]
          congr 1; apply Fin.ext; dsimp; omega)
      (by unfold mixedKey
          rw [dif_neg (by dsimp; omega), dif_neg (by dsimp; omega), dif_neg (by dsimp; omega)]
          have hfe : (⟨(⟨17 + r, by omega⟩ : MixedGeo.Bank).val + 3, by dsimp; omega⟩ : Fin 26) = ⟨20 + r, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hfe])
      (fun b hb => by
        have h : ∀ k : MixedGeo.Bank, ∀ m : Nat, m < 4 → k.val < 17 + m → MixedGeo.endTick k + 15 ≤ 45 + 15 * (21 + m) := by
          decide +kernel
        exact h b r hr hb)
  have c := composition (mk 0 (by decide)) (composition (mk 1 (by decide))
    (composition (mk 2 (by decide)) (mk 3 (by decide))))
  simpa only [MixedWindow.suffixPairs, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatten_append, List.append_assoc] using c

private theorem chunk7_checked (d : Bool) (x : Nat) (good : Bounds x p) :
    Checked
      ([Shadow7.parkP 420, Shadow7.portalInvP 420, MixedWindow.tickW 420, MixedWindow.packW d 420 410,
        Shadow7.exitLoadP 420 d]).flatten
      ([Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, MixedWindow.recvW 420,
        Shadow7.portalP 420, Shadow7.parkInvP 420]).flatten
      (fun s => ReadyW d x p 420 s ∧ SavedBefore d x p 21 s)
      (mixedFinal StockWindowChainP.ExitPorts420 d x p) := by
  have hfe : ([Shadow7.parkP 420, Shadow7.portalInvP 420, MixedWindow.tickW 420, MixedWindow.packW d 420 410,
      Shadow7.exitLoadP 420 d]).flatten = (exitF CRTBarrel.params d 420).flatten := by
    simp only [exitF, CRTBarrel.params, Shadow7.params, ofParts, MixedWindow.tickW, MixedWindow.packW,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  have hre : ([Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, MixedWindow.recvW 420,
      Shadow7.portalP 420, Shadow7.parkInvP 420]).flatten = (exitR CRTBarrel.params d 420).flatten := by
    simp only [exitR, CRTBarrel.params, Shadow7.params, ofParts, MixedWindow.recvW, MixedWindow.unpackW,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  rw [hfe, hre]
  intro s m ⟨hr, hs⟩
  have e := StockWindowW7.exitLeaves420.step d x good s m hr
  refine ⟨e.1, fun b => ?_, e.2.2⟩
  by_cases h21 : b.val = 21
  · have hbeq : b = ⟨21, by decide⟩ := Fin.ext h21
    subst hbeq
    have fk := StockWindowChainP.finalKey420 d x good s m hr
    unfold MixedGeo.bankPorts mixedKey
    simp only [show ¬ ((21 : Nat) < 7) by decide, show ¬ ((21 : Nat) = 7) by decide,
      show ¬ ((21 : Nat) < 17) by decide, show ¬ ((21 : Nat) < 21) by decide, ↓reduceDIte]
    exact fk
  · have hlt : b.val < 21 := by have := b.isLt; omega
    have hend : MixedGeo.endTick b ≤ 405 := by
      have h : ∀ k' : MixedGeo.Bank, k'.val < 21 → MixedGeo.endTick k' ≤ 405 := by decide +kernel
      exact h b hlt
    exact keep_savedKey (hs b hlt) (fun q hq => keep_cells_exit420 d (MixedGeo.endTick b)
      (bank_tick_match b).2.2.2.2.1 hend q (bank_cells_mem b q hq) s m)

/-- End-to-end mixed 15/20-tick strong chain: phase preservation, all 22 saved archive keys,
and exact roundtrip under `MixedWindow.reverseMixed d`. -/
theorem strong (d : Bool) (x : Nat) (good : Bounds x p) (raw : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    let start0 := pullState (OB5.sig 44) raw
    let out := run (MixedWindow.forwardMixed d) m start0
    out.phase = raw.phase ∧
    mixedFinal StockWindowChainP.ExitPorts420 d x p out ∧
    ∀ n, run (TickCut.Mixed.reverseUncut d) n out = start0 := by
  have all := composition (chunk1_checked d x good)
    (composition (chunk2_checked d x good)
    (composition (chunk3_checked d x good)
    (composition (chunk4_checked d x good)
    (composition (chunk5_checked d x good)
    (composition (chunk6_checked d x good)
      (chunk7_checked d x good))))))
  have hf : MixedWindow.forwardMixed d =
      ([Shadow7.portalP 45, Shadow7.enterP MixedWindow.j0, Shadow7.routed MixedWindow.j0 0 1,
        MixedWindow.packW d 45 45, Shadow7.routed MixedWindow.j0 1 14, CRTBarrel.leave MixedWindow.j0]).flatten ++
      ((MixedWindow.prefixPairs.flatMap fun p => MixedWindow.block15F d p.1 p.2).flatten ++
      (([Shadow7.enterP MixedWindow.j7, Shadow7.routed MixedWindow.j7 0 1, MixedWindow.packW d 150 140,
        Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, leave150To20Red]).flatten ++
      (((List.finRange 9).flatMap (MixedWindow.block20F d)).flatten ++
      (([Shadow7.enterP MixedWindow.j20, Shadow7.routed MixedWindow.j20 0 1,
        MixedWindow.packW d 345 330, MixedWindow.packW d 345 335, archiveLoadP20 MixedWindow.k8 d,
        Shadow7.routed MixedWindow.j20 1 14, CRTBarrel.leave MixedWindow.j20]).flatten ++
      ((MixedWindow.suffixPairs.flatMap fun p => MixedWindow.block15F d p.1 p.2).flatten ++
      ([Shadow7.parkP 420, Shadow7.portalInvP 420, MixedWindow.tickW 420, MixedWindow.packW d 420 410,
        Shadow7.exitLoadP 420 d]).flatten))))) := by
    simp only [MixedWindow.forwardMixed, MixedWindow.forwardL, List.flatten_append, List.append_assoc]
  have hr : TickCut.Mixed.reverseUncut d =
      (((((([Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, MixedWindow.recvW 420,
        Shadow7.portalP 420, Shadow7.parkInvP 420]).flatten ++
      (MixedWindow.suffixPairs.reverse.flatMap fun p => TickCut.Mixed.block15R d p.1 p.2).flatten) ++
      ([CRTBarrel.unleave MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
        archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
        Shadow7.unrouted MixedWindow.j20 0 1, Shadow7.enterInvP MixedWindow.j20]).flatten) ++
      ((List.finRange 9).reverse.flatMap (TickCut.Mixed.block20R d)).flatten) ++
      ([leaveInv150To20Red, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14, Shadow7.archiveRestoreP MixedWindow.j6 d,
        MixedWindow.unpackW d 150 140, Shadow7.unrouted MixedWindow.j7 0 1, Shadow7.enterInvP MixedWindow.j7]).flatten) ++
      (MixedWindow.prefixPairs.reverse.flatMap fun p => TickCut.Mixed.block15R d p.1 p.2).flatten) ++
      ([CRTBarrel.unleave MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
        MixedWindow.unpackW d 45 45, Shadow7.unrouted MixedWindow.j0 0 1,
        Shadow7.enterInvP MixedWindow.j0, Shadow7.portalInvP 45]).flatten := by
    simp only [TickCut.Mixed.reverseUncut, TickCut.Mixed.reverseL, List.flatten_append, List.append_assoc]
  rw [hf, hr]
  exact all (pullState (OB5.sig 44) raw) m ⟨raw, stage, rfl⟩

end ECDSAAdd.Entrant.StairPacket.Shadow20.MixedChain
end
-- ==== end Shadow7Wide20Chain ====


-- ==== begin Shadow7Wide20Ord ====
section

/-!
# Mixed 15/20-Tick Ordinary Chain & 22-Bank Stock Comparison API (`Shadow7Wide20Ord`)

1. `MixedArchiveReference`: `ordinary d := StockGroupsW.batch 45 d MixedGeo.plain` and
   `common d raw := pullState (OB5.sig 420) (eraseSites MixedGeo.holes (run (ordinary d) [] (run (span 45 376) [] raw)))`.
2. `MixedOrdinary.wiresMixed`: proves `MixedWindow.forwardMixed d` agrees with
   `MixedArchiveReference.common d raw` off `MixedGeo.archives` (`352` archive cells).
3. `MixedBaseline.comparison`, `MixedArchiveBanks.Paired`, `MixedRowVector.binding`,
   `MixedNativeCompare.normalized`: drop-in 22-bank stock comparison API for `Main.lean`.
-/

namespace ECDSAAdd.Entrant.StairPacket.Shadow20.MixedOrd

open ECDSAAdd.Arithmetic
open ECDSAAdd.Arithmetic.MappedCompressed
open ECDSAAdd.Secp256k1
open ECDSAAdd.Entrant.IntegerPacket
open ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Entrant.StairPacket.Partial
open ECDSAAdd.Entrant.StairPacket.ArchivePortAction
open ECDSAAdd.Entrant.StairPacket.ArchiveStockRows
open ECDSAAdd.Entrant.StairPacket.WideReference
open ECDSAAdd.Entrant.StairPacket.ArchiveHistoryCompare
open ECDSAAdd.Entrant.StairPacket.StockWindowTicket
open ECDSAAdd.Entrant.StairPacket.WindowFold
open ECDSAAdd.Entrant.StairPacket.StockCanonicalRow
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.NativeJ20
open ECDSAAdd.Entrant.StairPacket.Shadow20.LeaveCut20
open ECDSAAdd.Entrant.StairPacket.Shadow20.Trans150
open ECDSAAdd.Entrant.StairPacket.Shadow20.Reentry345
open ECDSAAdd.Entrant.StairPacket.Shadow20.MixedChain
open SkywalkRails

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] run Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP
  Shadow7.enterP Shadow7.enterInvP Shadow7.routed Shadow7.unrouted
  Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.exitLoadP Shadow7.exitRestoreP
  CRTBarrel.leave CRTBarrel.unleave leave150To20 leaveInv150To20 leave150To20Red leaveInv150To20Red
  enterP20 enterInvP20 routed20 unrouted20 leaveP20 leaveInvP20 leaveP20Red leaveInvP20Red
  archiveLoadP20 archiveRestoreP20 archiveLoad150To20 archiveRestore150To20

/-! ### Section 1: `MixedArchiveReference` & Generalized Ordinary State `OrdInv` -/

def ordinary (d : Bool) : Program :=
  StockGroupsW.batch 45 d MixedGeo.plain

def common (d : Bool) (raw : State) : State :=
  pullState (OB5.sig 420) (eraseSites MixedGeo.holes (run (ordinary d) [] (run (span 45 376) [] raw)))

/-- Banks `0..n-1` masked cells. -/
def bankMask (n : Nat) : List Wire :=
  ((List.finRange 22).take n).flatMap fun b => MixedGeo.cells10 (MixedGeo.endTick b - 10)

/-- Banks `0..n-1` erased holes. -/
def bankHoles (n : Nat) : List Wire :=
  ((List.finRange 22).take n).flatMap fun b =>
    [base (1028 + (MixedGeo.endTick b - 8)), base (1028 + (MixedGeo.endTick b - 6)),
     base (1028 + (MixedGeo.endTick b - 3)), base (1028 + (MixedGeo.endTick b - 1))]

/-- Plain groups encoded before tick `t`. -/
def groupProg (d : Bool) (gs : List Nat) : Program :=
  StockGroupsW.batch 45 d gs

private theorem groupProg_append (d : Bool) (a b : List Nat) :
    groupProg d (a ++ b) = groupProg d a ++ groupProg d b :=
  OrdinaryChainG.batch_append 45 d a b

private theorem groupProg_singleton (d : Bool) (i : Nat) :
    groupProg d [i] = Rolling1588.encodeAt base d (40 + 5 * i) := by
  simp only [groupProg, StockGroupsW.batch, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    StockGroupsW.one, StockWindowGeo.gstart]

private theorem bankMask_succ (b : MixedGeo.Bank) :
    bankMask (b.val + 1) = bankMask b.val ++ MixedGeo.cells10 (MixedGeo.endTick b - 10) := by
  have hb := b.isLt
  have ht : (List.finRange 22).take (b.val + 1) = (List.finRange 22).take b.val ++ [b] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hb]), Option.toList_some, List.getElem_finRange]
    simp only [Fin.cast_mk, Fin.eta, Fin.cast_eq_self]
  simp only [bankMask, ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

private theorem bankHoles_succ (b : MixedGeo.Bank) :
    bankHoles (b.val + 1) = bankHoles b.val ++
      [base (1028 + (MixedGeo.endTick b - 8)), base (1028 + (MixedGeo.endTick b - 6)),
       base (1028 + (MixedGeo.endTick b - 3)), base (1028 + (MixedGeo.endTick b - 1))] := by
  have hb := b.isLt
  have ht : (List.finRange 22).take (b.val + 1) = (List.finRange 22).take b.val ++ [b] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hb]), Option.toList_some, List.getElem_finRange]
    simp only [Fin.cast_mk, Fin.eta, Fin.cast_eq_self]
  simp only [bankHoles, ht, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

private theorem bankMask_cells (n : Nat) (bound : Nat)
    (hb : ∀ b : MixedGeo.Bank, b.val < n → MixedGeo.endTick b ≤ bound) :
    ∀ q ∈ bankMask n, ∃ r, r < bound ∧ (q = base r ∨ q = base (1028 + r)) := by
  intro q hq
  simp only [bankMask, List.mem_flatMap] at hq
  obtain ⟨b, hbt, hcq⟩ := hq
  have hblt : b.val < n := by
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp hbt
    have hlen : ((List.finRange 22).take n).length = min n 22 := by simp
    have hin : i < n := by rw [hlen] at hi; omega
    rw [List.getElem_take, List.getElem_finRange] at eq
    rw [← eq]; exact hin
  have hbe := hb b hblt
  simp only [MixedGeo.cells10, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false] at hcq
  obtain ⟨r, ⟨r1, r2⟩, e⟩ := hcq
  have hge : 10 ≤ MixedGeo.endTick b := by
    have : ∀ k : MixedGeo.Bank, 60 ≤ MixedGeo.endTick k := by decide +kernel
    have := this b; omega
  exact ⟨r, by omega, e⟩

private theorem bankHoles_cells (n : Nat) (bound : Nat)
    (hb : ∀ b : MixedGeo.Bank, b.val < n → MixedGeo.endTick b ≤ bound) :
    ∀ q ∈ bankHoles n, ∃ r, 50 ≤ r ∧ r < bound ∧ q = base (1028 + r) := by
  intro q hq
  simp only [bankHoles, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hq
  obtain ⟨b, hbt, e⟩ := hq
  have hblt : b.val < n := by
    obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp hbt
    have hlen : ((List.finRange 22).take n).length = min n 22 := by simp
    have hin : i < n := by rw [hlen] at hi; omega
    rw [List.getElem_take, List.getElem_finRange] at eq
    rw [← eq]; exact hin
  have hbe := hb b hblt
  have hge : 60 ≤ MixedGeo.endTick b := by
    have : ∀ k : MixedGeo.Bank, 60 ≤ MixedGeo.endTick k := by decide +kernel
    exact this b
  rcases e with rfl | rfl | rfl | rfl
  · exact ⟨MixedGeo.endTick b - 8, by omega, by omega, rfl⟩
  · exact ⟨MixedGeo.endTick b - 6, by omega, by omega, rfl⟩
  · exact ⟨MixedGeo.endTick b - 3, by omega, by omega, rfl⟩
  · exact ⟨MixedGeo.endTick b - 1, by omega, by omega, rfl⟩

private theorem groupProg_cells (d : Bool) (gs : List Nat) (bound : Nat)
    (hg : ∀ i ∈ gs, 40 + 5 * i + 5 ≤ bound) :
    ∀ q ∈ wires (groupProg d gs), ∃ r, r < bound ∧ (q = base r ∨ q = base (1028 + r)) := by
  induction gs with
  | nil => intro q h; simp [groupProg, StockGroupsW.batch, wires] at h
  | cons i gs ih =>
    intro q h
    change q ∈ wires (Rolling1588.encodeAt base d (40 + 5 * i) ++ groupProg d gs) at h
    rw [wires_append, Finset.mem_union] at h
    rcases h with h | h
    · obtain ⟨r, r1, r2, e⟩ := OrdinaryChainW.encode_cells d (40 + 5 * i) q h
      have hi := hg i List.mem_cons_self
      exact ⟨r, by omega, e⟩
    · exact ih (fun j hj => hg j (List.mem_cons_of_mem _ hj)) q h

/-- Generic ordinary-chain extension step of arbitrary tick length `len`, adding bank `b` (or none)
and plain groups `newGs`. -/
private theorem extend_step (d : Bool) (t len : Nat) (h45 : 45 ≤ t) (hlim : t + len ≤ 512)
    (mask addedMask : List Wire) (oldGs newGs : List Nat) (raw initial out : State)
    (old : Except mask raw (run (groupProg d oldGs) [] (run (span 45 (t - 45)) [] initial)))
    (step : Except addedMask out (run (groupProg d newGs) [] (run (span t len) [] raw)))
    (hmask : ∀ q ∈ mask, ∃ r, r + 2 ≤ t ∧ (q = base r ∨ q = base (1028 + r)))
    (hprog : ∀ q ∈ wires (groupProg d oldGs), ∃ r, r + 2 ≤ t ∧ (q = base r ∨ q = base (1028 + r)))
    (havoid : ∀ q ∈ mask, q ∉ wires (groupProg d newGs)) :
    Except (mask ++ addedMask) out
      (run (groupProg d (oldGs ++ newGs)) [] (run (span 45 (t + len - 45)) [] initial)) := by
  have h := extend t len hlim mask addedMask (groupProg d oldGs) (groupProg d newGs)
    raw (run (span 45 (t - 45)) [] initial) out old step
    (fun q hq => by obtain ⟨r, hr, e⟩ := hmask q hq; exact ⟨r, hr, e⟩)
    (fun q hq => by obtain ⟨r, hr, e⟩ := hprog q hq; exact ⟨r, hr, e⟩)
    havoid
  rw [groupProg_append]
  have hsp : run (span 45 (t + len - 45)) [] initial =
      run (span t len) [] (run (span 45 (t - 45)) [] initial) := by
    rw [show t + len - 45 = (t - 45) + len by omega, spanAppend 45 (t - 45) len,
      show 45 + (t - 45) = t by omega, run_append, run_take, List.drop_nil]
  rw [hsp]
  exact h

private theorem carry20_holes (s prevLen : Nat) (hprev1 : 1 ≤ prevLen) (hprev : prevLen ≤ s) (hs : s + 19 ≤ 511)
    (holes : List Wire) (hcells : ∀ q ∈ holes, ∃ r, r + prevLen < s ∧ q = base (1028 + r))
    (raw history : State) (clear : ∀ q ∈ holes, raw.basis q = false) :
    ∀ q ∈ holes, (WideReference20.endRaw s prevLen 20 raw history).basis q = false := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := hcells q hq
  have hoff : base (1028 + r) ∉ WideReference20.oldSites s prevLen := by
    intro hit
    obtain ⟨r', r1, r2, e | e⟩ := WideReference20.old_cell hit <;> simp only [base, Wire] at e <;> omega
  rw [WideReference20.endRaw_outside (by omega) raw history _ hoff,
    run_preserves_outside (span s 20) [] raw _ (pastOffSpan s 20 _ (by omega) ⟨r, by omega, Or.inr rfl⟩)]
  exact clear _ hq

/-! ### Section 2: Ordinary Step for 20-Tick Blocks & Re-Entry `j20` -/

private theorem packW_eq_local (s t : Nat) (hs : s ≤ 511) (ht1 : t ≠ 5) (ht2 : History5.packDue t = true) (d : Bool) :
    MixedWindow.packW d s t = Rolling1588.codeEncodeAt d (hist20 s (t - 5)) := by
  have h1 : Rolling1588.packAtTick d t = Rolling1588.encodeAt base d (t - 5) := by
    simp only [Rolling1588.packAtTick, Rolling1588.Integer.packFirst, if_neg ht1,
      History5.packAfter, ht2, ↓reduceIte]; rfl
  rw [MixedWindow.packW, h1, Rolling1588.encodeAt, Rolling1588.codeEncodeAt,
    Rolling1588.codeEncodeAt, renameProgram_comp]
  apply renameProgram_congr_support
  intro q hq
  have lt : q < 10 := Finset.mem_range.mp ((Rolling1588.code_support d).1 ▸ hq)
  simp only [Function.comp, MeasuredCodec5.label, dif_pos lt, hist20]

attribute [local irreducible] Rolling1588.packAtTick Rolling1588.unpackAtTick measurementCount

private theorem hist20_inj_local (s t : Nat) (hs : s ≤ 511) (ht : t + 5 ≤ 1028) :
    Function.Injective (hist20 s t) := by
  intro a b eq
  have inv := OB5.sig_invol s hs
  have e := congrArg (OB5.sig s) eq
  simp only [hist20, inv, History5.historyMap, History5.historyId, base] at e
  have ha := a.isLt; have hb := b.isLt
  apply Fin.ext
  split at e <;> split at e <;> simp only [Wire] at * <;> omega

private theorem hist20_geom : ∀ j : Fin 9, ∀ t : Nat,
    ((j.val = 0 ∧ t = 150) ∨ (1 ≤ j.val ∧ (t = start20 j - 20 ∨ t = start20 j - 15))) →
    ∀ i : Fin 10,
      OB5.sig (start20 j - 1) (hist20 (start20 j) t i) = History5.historyMap base t i ∧
      OB5.sig (start20 j + 19) (hist20 (start20 j) t i) = History5.historyMap base t i ∧
      oldRange (start20 j + 1) (windowNet20 j (hist20 (start20 j) t i)) ∧
      hist20 (start20 j) t i ∉ EnterJ20.pending j ∧
      hist20 (start20 j) t i ≠ EnterJ20.flagN j ∧
      hist20 (start20 j) t i ≠ EnterJ20.flagF j ∧
      hist20 (start20 j) t i ≠ EnterJ20.flagU j ∧
      hist20 (start20 j) t i ∉ RailPair.sites (EnterJ20.upperPairs j) ∧
      hist20 (start20 j) t i ∉ prevRawPortsList20 j ∧
      hist20 (start20 j) t i ∉ EnterJ20.ports j ∧
      (windowNet20 j (hist20 (start20 j) t i) = start20 j + 15 ∨
        ¬(windowNet20 j (hist20 (start20 j) t i) = start20 j + 1044 ∨
          start20 j + 16 ≤ windowNet20 j (hist20 (start20 j) t i) ∧
            windowNet20 j (hist20 (start20 j) t i) ≤ start20 j + sbP20 (start20 j) + 39 ∨
          786 ≤ windowNet20 j (hist20 (start20 j) t i) ∧
            windowNet20 j (hist20 (start20 j) t i) ≤ sbP20 (start20 j) + 808 ∨
          1556 ≤ windowNet20 j (hist20 (start20 j) t i) ∧
            windowNet20 j (hist20 (start20 j) t i) ≤ sbP20 (start20 j) + 1576)) := by
  intro j t ht i
  have hj := j.isLt
  have hcheck : ∀ (r : Fin 9) (k : Fin 10),
      let ts : List Nat := if r.val = 0 then [150] else [start20 r - 20, start20 r - 15]
      ts.all (fun u =>
        decide (
          OB5.sig (start20 r - 1) (hist20 (start20 r) u k) = History5.historyMap base u k ∧
          OB5.sig (start20 r + 19) (hist20 (start20 r) u k) = History5.historyMap base u k ∧
          oldRange (start20 r + 1) (windowNet20 r (hist20 (start20 r) u k)) ∧
          (StairLoan.maskOf (EnterJ20.pending r)).testBit (hist20 (start20 r) u k) = false ∧
          hist20 (start20 r) u k ≠ EnterJ20.flagN r ∧
          hist20 (start20 r) u k ≠ EnterJ20.flagF r ∧
          hist20 (start20 r) u k ≠ EnterJ20.flagU r ∧
          (StairLoan.maskOf (RailPair.sites (EnterJ20.upperPairs r))).testBit (hist20 (start20 r) u k) = false ∧
          (StairLoan.maskOf (prevRawHead20 r)).testBit (hist20 (start20 r) u k) = false ∧
          (StairLoan.maskOf (EnterJ20.ports r)).testBit (hist20 (start20 r) u k) = false ∧
          (hist20 (start20 r) u k < 1556 ∨ 1700 ≤ hist20 (start20 r) u k) ∧
          (windowNet20 r (hist20 (start20 r) u k) = start20 r + 15 ∨
            ¬(windowNet20 r (hist20 (start20 r) u k) = start20 r + 1044 ∨
              start20 r + 16 ≤ windowNet20 r (hist20 (start20 r) u k) ∧
                windowNet20 r (hist20 (start20 r) u k) ≤ start20 r + sbP20 (start20 r) + 39 ∨
              786 ≤ windowNet20 r (hist20 (start20 r) u k) ∧
                windowNet20 r (hist20 (start20 r) u k) ≤ sbP20 (start20 r) + 808 ∨
              1556 ≤ windowNet20 r (hist20 (start20 r) u k) ∧
                windowNet20 r (hist20 (start20 r) u k) ≤ sbP20 (start20 r) + 1576)))) = true := by
    decide +kernel
  have hm : t ∈ (if j.val = 0 then [150] else [start20 j - 20, start20 j - 15]) := by
    rcases ht with ⟨h0, rfl⟩ | ⟨h1, rfl | rfl⟩
    · simp [h0]
    · simp [show j.val ≠ 0 by omega]
    · simp [show j.val ≠ 0 by omega]
  have hp := of_decide_eq_true (List.all_eq_true.mp (hcheck j i) t hm)
  refine ⟨hp.1, hp.2.1, hp.2.2.1, StairLoan.not_mem_of_maskOf hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.1, StairLoan.not_mem_of_maskOf hp.2.2.2.2.2.2.2.1, ?_,
    StairLoan.not_mem_of_maskOf hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2⟩
  rw [prevRaw_split, List.mem_append]
  rintro (h | h)
  · exact StairLoan.not_mem_of_maskOf hp.2.2.2.2.2.2.2.2.1 h
  · have sb : 1556 ≤ (hist20 (start20 j) t i : Nat) ∧ (hist20 (start20 j) t i : Nat) < 1700 := by
      unfold prevScratch20 at h; split_ifs at h with h0
      · obtain ⟨v, hv, eq⟩ := List.mem_map.mp h; rw [List.mem_range] at hv
        rw [← eq]; unfold archScratch150; split_ifs <;> (unfold Wire; omega)
      · obtain ⟨v, hv, eq⟩ := List.mem_map.mp h; rw [List.mem_range] at hv
        rw [← eq]; unfold archScratch20; dsimp only; split_ifs <;> (unfold Wire; omega)
    have hnb := hp.2.2.2.2.2.2.2.2.2.2.1; simp only [Wire] at *; omega

def groups20 (j : Fin 9) : List Nat :=
  if j.val = 0 then [22] else [(start20 j - 20 - 40) / 5, (start20 j - 15 - 40) / 5]

attribute [local irreducible] SkywalkNat.step Shadow.far nextWindow20 window20 withArchive20 body20 in
private theorem ordinary20_step (j : Fin 9) (d : Bool) (x : Nat) (good : Bounds x p)
    (raw s : State) (g sg pg ps : Bool) (m : List Bool) (pre : At20 j d x p raw s g sg pg ps) :
    Except (MixedGeo.cells10 (start20 j - 10))
      (WideReference20.endRaw (start20 j) (prevLen20 j) 20 raw (run (nextWindow20 j d) m s))
      (run (groupProg d (groups20 j)) [] (run (span (start20 j) 20) [] raw)) := by
  have hj := j.isLt
  have hs_le : start20 j + 19 ≤ 511 := by unfold start20; omega
  have nums := actualNumbers20 j x p good
  have hist := WideReference20.pulled_history20 j pre.domain
  have inp := readInput (start20 j) x p raw g sg pre.input
  let preS := run (enterP20 j) m s
  let tape := m.drop (measurementCount (enterP20 j))
  let st1 := run (routed20 j 0 1) tape preS
  let t1 := tape.drop (measurementCount (routed20 j 0 1))
  let T := Shadow.reduced (sbP20 (start20 j)) 20 (unsigned (start20 j) x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 (start20 j)) (unsigned (start20 j) x p) nums.small.1 nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ20.ready_pending_at j raw s (unsigned (start20 j) x p) g sg m nums.small.1 pre.cut inp hist
  have runEq : run (nextWindow20 j d) m s = run (body20 j (withArchive20 j d)) tape preS := by
    simp only [nextWindow20, window20, run_append, run_take, preS, tape]
  have hIn (t : Nat) (ht : (j.val = 0 ∧ t = 150) ∨ (1 ≤ j.val ∧ (t = start20 j - 20 ∨ t = start20 j - 15))) (i : Fin 10) :
      st1.basis (hist20 (start20 j) t i) = raw.basis (History5.historyMap base t i) := by
    have g' := hist20_geom j t ht i
    have h1 := first_preserves20 j Z parity preS tape ready.2.1 (hist20 (start20 j) t i) (firstFree20 j g'.2.2.2.2.2.2.2.2.2.2)
    have h2 := run_preserves_outside (enterP20 j) m s (hist20 (start20 j) t i) (EnterJ20.notWire j g'.2.2.2.2.2.2.2.2.2.1)
    have h3 := pre.cut.unchanged _ g'.2.2.2.2.1 g'.2.2.2.2.2.1 g'.2.2.2.2.2.2.1 g'.2.2.2.2.2.2.2.1
    rw [h1, h2]
    have e : s.basis (hist20 (start20 j) t i) = (eraseSites (EnterJ20.pending j) s).basis (hist20 (start20 j) t i) := by
      simp [eraseSites, g'.2.2.2.1]
    rw [e, h3]; change raw.basis (OB5.sig (start20 j - 1) _) = _; rw [g'.1]
  have hPast (t : Nat) (ht1 : t + 7 ≤ start20 j) (i : Fin 10) :
      raw.basis (History5.historyMap base t i) = (run (span (start20 j) 20) [] raw).basis (History5.historyMap base t i) := by
    have hsp : History5.historyMap base t i ∉ wires (span (start20 j) 20) := by
      apply pastOffSpan (start20 j) 20 _ (by omega)
      refine ⟨t + i.val / 2, by have := i.isLt; omega, ?_⟩
      unfold History5.historyMap History5.historyId; split_ifs
      · left; rfl
      · right; congr 1; omega
    exact (run_preserves_outside _ _ _ _ hsp).symm
  have cellMap (t : Nat) (q : Wire) (hr : ∃ r, t ≤ r ∧ r ≤ t + 4 ∧ (q = base r ∨ q = base (1028 + r))) :
      ∃ i : Fin 10, q = History5.historyMap base t i := by
    obtain ⟨r, r1, r2, rfl | rfl⟩ := hr
    · refine ⟨⟨2 * (r - t), by omega⟩, ?_⟩
      simp only [History5.historyMap, History5.historyId, Fin.val_mk]; rw [if_pos (by omega)]; congr 1; omega
    · refine ⟨⟨2 * (r - t) + 1, by omega⟩, ?_⟩
      simp only [History5.historyMap, History5.historyId, Fin.val_mk]; rw [if_neg (by omega)]; congr 1; omega
  intro q hnot
  by_cases hold : q ∈ WideReference20.oldSites (start20 j) (prevLen20 j)
  · rw [WideReference20.endRaw_inside hs_le _ _ q hold, show start20 j + 20 - 1 = start20 j + 19 by omega]
    obtain ⟨r, r1, r2, er⟩ := WideReference20.old_cell hold
    have hpl_le : prevLen20 j ≤ start20 j := by unfold prevLen20 start20; split_ifs <;> omega
    have hr_lt : r < start20 j - 10 := by
      by_contra hge
      apply hnot
      simp only [MixedGeo.cells10, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨r, ⟨by omega, by omega⟩, by rcases er with e | e; exact Or.inl e; exact Or.inr (by simp only [base, Wire] at e ⊢; omega)⟩
    have hr_base : q = base r ∨ q = base (1028 + r) := by
      rcases er with e | e; exact Or.inl e; exact Or.inr (by simp only [base, Wire] at e ⊢; omega)
    by_cases h0 : j.val = 0
    · have hs0 : start20 j = 165 := by simp [start20, h0]
      have hpl0 : prevLen20 j = 15 := by simp [prevLen20, h0]
      rw [hs0, hpl0] at r1
      rw [hs0] at hr_lt
      obtain ⟨i, hi⟩ := cellMap 150 q ⟨r, by omega, by omega, hr_base⟩
      have g' := hist20_geom j 150 (Or.inl ⟨h0, rfl⟩) i
      have hsig : OB5.sig (start20 j + 19) q = hist20 (start20 j) 150 i := by
        rw [hi, ← g'.2.1, OB5.sig_invol (start20 j + 19) hs_le]
      rw [hsig, runEq, body20, run_append, run_take, run_append, run_take,
        route20_outside j 1 19 (by decide) _ (old_clear20 (by decide) g'.2.2.1),
        withArchive20, run_append, run_take,
        run_preserves_outside (archLoad20 j d) _ _ _ (fun h => g'.2.2.2.2.2.2.2.2.1 (List.mem_toFinset.mp (prevArch_load_cover j d h)))]
      have hp0 : packProg20 j d = Rolling1588.codeEncodeAt d (hist20 (start20 j) 150) := by
        unfold packProg20; rw [if_pos h0, ← hs0]
        exact packW_eq_local (start20 j) 155 (by omega) (by decide) (by decide) d
      have hg0 : groupProg d (groups20 j) = Rolling1588.encodeAt base d 150 := by
        unfold groups20; rw [if_pos h0, groupProg_singleton]
      rw [hp0, hg0, hi]
      exact ArchiveOrdinaryFive.stock_relocated d (hist20 (start20 j) 150) (History5.historyMap base 150)
        (hist20_inj_local (start20 j) 150 (by omega) (by decide))
        (History5.historyMap_injective base base_pool_nodup 150 (by decide))
        st1 (run (span (start20 j) 20) [] raw) _ []
        (fun k => (hIn 150 (Or.inl ⟨h0, rfl⟩) k).trans (hPast 150 (by omega) k)) i
    · have hpl : prevLen20 j = 20 := by simp [prevLen20, h0]
      have hs_rng : 185 ≤ start20 j ∧ start20 j ≤ 325 := by unfold start20; omega
      rw [hpl] at r1
      have hdue1 : History5.packDue (start20 j - 15) = true := by simp only [History5.packDue, start20, decide_eq_true_eq]; omega
      have hdue2 : History5.packDue (start20 j - 10) = true := by simp only [History5.packDue, start20, decide_eq_true_eq]; omega
      have he1 := packW_eq_local (start20 j) (start20 j - 15) (by omega) (by unfold start20; omega) hdue1 d
      have he2 := packW_eq_local (start20 j) (start20 j - 10) (by omega) (by unfold start20; omega) hdue2 d
      rw [show start20 j - 15 - 5 = start20 j - 20 by omega] at he1
      rw [show start20 j - 10 - 5 = start20 j - 15 by omega] at he2
      have hg_eq : groupProg d (groups20 j) =
          Rolling1588.encodeAt base d (start20 j - 20) ++ Rolling1588.encodeAt base d (start20 j - 15) := by
        unfold groups20; rw [if_neg h0]
        change groupProg d ([(start20 j - 20 - 40) / 5] ++ [(start20 j - 15 - 40) / 5]) = _
        rw [groupProg_append, groupProg_singleton, groupProg_singleton]
        congr 1 <;> (congr 1; unfold start20; omega)
      have hdisjH : ∀ a b : Fin 10, hist20 (start20 j) (start20 j - 20) a ≠ hist20 (start20 j) (start20 j - 15) b := by
        intro a b eq
        have e := congrArg (OB5.sig (start20 j)) eq
        simp only [hist20, OB5.sig_invol (start20 j) (by omega), History5.historyMap, History5.historyId, base] at e
        have := a.isLt; have := b.isLt; split at e <;> split at e <;> simp only [start20, Wire] at * <;> omega
      have hdisjP : Disjoint (wires (Rolling1588.encodeAt base d (start20 j - 20)))
          (wires (Rolling1588.encodeAt base d (start20 j - 15))) := by
        rw [Finset.disjoint_left]; intro w hw1 hw2
        obtain ⟨a, a1, a2, ea⟩ := OrdinaryChainW.encode_cells d (start20 j - 20) w hw1
        obtain ⟨b, b1, b2, eb⟩ := OrdinaryChainW.encode_cells d (start20 j - 15) w hw2
        rcases ea with rfl | rfl <;> rcases eb with eb | eb <;> simp only [base, Wire] at eb <;> omega
      by_cases hr1 : r < start20 j - 15
      · obtain ⟨i, hi⟩ := cellMap (start20 j - 20) q ⟨r, by omega, by omega, hr_base⟩
        have g' := hist20_geom j (start20 j - 20) (Or.inr ⟨by omega, Or.inl rfl⟩) i
        have hsig : OB5.sig (start20 j + 19) q = hist20 (start20 j) (start20 j - 20) i := by
          rw [hi, ← g'.2.1, OB5.sig_invol (start20 j + 19) hs_le]
        have hoff2 : hist20 (start20 j) (start20 j - 20) i ∉ wires (MixedWindow.packW d (start20 j) (start20 j - 10)) := by
          rw [he2, Rolling1588.codeEncodeAt, renameProgram_support, (Rolling1588.code_support d).1]
          intro hm; obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hm; have lt := Finset.mem_range.mp hw
          simp only [MeasuredCodec5.label, dif_pos lt] at eq; exact hdisjH i ⟨w, lt⟩ eq.symm
        have hoffR : q ∉ wires (Rolling1588.encodeAt base d (start20 j - 15)) := by
          intro hm; obtain ⟨b, b1, b2, eb⟩ := OrdinaryChainW.encode_cells d (start20 j - 15) q hm
          rcases hr_base with rfl | rfl <;> rcases eb with eb | eb <;> simp only [base, Wire] at eb <;> omega
        rw [hsig, runEq, body20, run_append, run_take, run_append, run_take,
          route20_outside j 1 19 (by decide) _ (old_clear20 (by decide) g'.2.2.1),
          withArchive20, run_append, run_take,
          run_preserves_outside (archLoad20 j d) _ _ _ (fun h => g'.2.2.2.2.2.2.2.2.1 (List.mem_toFinset.mp (prevArch_load_cover j d h))),
          packProg20, if_neg h0, run_append, run_take,
          run_preserves_outside _ _ _ _ hoff2, he1, hg_eq, run_append, run_take, List.drop_nil,
          run_preserves_outside _ _ _ _ hoffR, hi]
        exact ArchiveOrdinaryFive.stock_relocated d _ _ (hist20_inj_local _ _ (by omega) (by unfold start20; omega))
          (History5.historyMap_injective base base_pool_nodup _ (by unfold start20; omega))
          st1 (run (span (start20 j) 20) [] raw) _ []
          (fun k => (hIn _ (Or.inr ⟨by omega, Or.inl rfl⟩) k).trans (hPast _ (by omega) k)) i
      · obtain ⟨i, hi⟩ := cellMap (start20 j - 15) q ⟨r, by omega, by omega, hr_base⟩
        have g' := hist20_geom j (start20 j - 15) (Or.inr ⟨by omega, Or.inr rfl⟩) i
        have hsig : OB5.sig (start20 j + 19) q = hist20 (start20 j) (start20 j - 15) i := by
          rw [hi, ← g'.2.1, OB5.sig_invol (start20 j + 19) hs_le]
        have hoff1 (k : Fin 10) : hist20 (start20 j) (start20 j - 15) k ∉ wires (MixedWindow.packW d (start20 j) (start20 j - 15)) := by
          rw [he1, Rolling1588.codeEncodeAt, renameProgram_support, (Rolling1588.code_support d).1]
          intro hm; obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hm; have lt := Finset.mem_range.mp hw
          simp only [MeasuredCodec5.label, dif_pos lt] at eq; exact hdisjH ⟨w, lt⟩ k eq
        have hoffR (k : Fin 10) : History5.historyMap base (start20 j - 15) k ∉ wires (Rolling1588.encodeAt base d (start20 j - 20)) := by
          intro hm; obtain ⟨a, a1, a2, ea⟩ := OrdinaryChainW.encode_cells d (start20 j - 20) _ hm
          have := k.isLt; unfold History5.historyMap History5.historyId at ea
          split_ifs at ea <;> rcases ea with ea | ea <;> simp only [base, Wire] at ea <;> omega
        rw [hsig, runEq, body20, run_append, run_take, run_append, run_take,
          route20_outside j 1 19 (by decide) _ (old_clear20 (by decide) g'.2.2.1),
          withArchive20, run_append, run_take,
          run_preserves_outside (archLoad20 j d) _ _ _ (fun h => g'.2.2.2.2.2.2.2.2.1 (List.mem_toFinset.mp (prevArch_load_cover j d h))),
          packProg20, if_neg h0, run_append, run_take, he2, hg_eq, run_append, run_take, List.drop_nil, hi]
        exact ArchiveOrdinaryFive.stock_relocated d _ _ (hist20_inj_local _ _ (by omega) (by unfold start20; omega))
          (History5.historyMap_injective base base_pool_nodup _ (by unfold start20; omega)) _ _ _ []
          (fun k => (run_preserves_outside _ _ _ _ (hoff1 k)).trans
            ((hIn _ (Or.inr ⟨by omega, Or.inr rfl⟩) k).trans
              ((hPast _ (by omega) k).trans (run_preserves_outside _ _ _ _ (hoffR k)).symm))) i
  · rw [WideReference20.endRaw_outside hs_le _ _ q hold]
    symm; apply run_preserves_outside
    intro used
    apply hold
    have hcells : ∃ r, start20 j - prevLen20 j ≤ r ∧ r < start20 j - 10 ∧ (q = base r ∨ q = base (1028 + r)) := by
      unfold groups20 at used; split_ifs at used with h0
      · rw [groupProg_singleton] at used
        obtain ⟨r, r1, r2, e⟩ := OrdinaryChainW.encode_cells d 150 q used
        have hs0 : start20 j = 165 := by simp [start20, h0]
        have hpl0 : prevLen20 j = 15 := by simp [prevLen20, h0]
        exact ⟨r, by omega, by omega, e⟩
      · have hpl : prevLen20 j = 20 := by simp [prevLen20, h0]
        change q ∈ wires (groupProg d ([(start20 j - 20 - 40) / 5] ++ [(start20 j - 15 - 40) / 5])) at used
        rw [groupProg_append, wires_append, Finset.mem_union, groupProg_singleton, groupProg_singleton] at used
        rcases used with u | u
        · obtain ⟨r, r1, r2, e⟩ := OrdinaryChainW.encode_cells d _ q u
          exact ⟨r, by unfold start20 at *; omega, by unfold start20 at *; omega, e⟩
        · obtain ⟨r, r1, r2, e⟩ := OrdinaryChainW.encode_cells d _ q u
          exact ⟨r, by unfold start20 at *; omega, by unfold start20 at *; omega, e⟩
    obtain ⟨r, r1, r2, e⟩ := hcells
    simp only [WideReference20.oldSites, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨r, ⟨by omega, by omega⟩, e⟩

attribute [local irreducible] SkywalkNat.step Shadow.far nextWindow20 window20 withArchive20 body20 in
private theorem holes20_step (j : Fin 9) (d : Bool) (x : Nat) (good : Bounds x p)
    (raw s : State) (g sg pg ps : Bool) (m : List Bool) (pre : At20 j d x p raw s g sg pg ps)
    (r : Nat) (hr : r = start20 j - 8 ∨ r = start20 j - 6 ∨ r = start20 j - 3 ∨ r = start20 j - 1) :
    (WideReference20.endRaw (start20 j) (prevLen20 j) 20 raw (run (nextWindow20 j d) m s)).basis (base (1028 + r)) = false := by
  have hj := j.isLt
  have hs_le : start20 j + 19 ≤ 511 := by unfold start20; omega
  have nums := actualNumbers20 j x p good
  have hist := WideReference20.pulled_history20 j pre.domain
  have inp := readInput (start20 j) x p raw g sg pre.input
  let T := Shadow.reduced (sbP20 (start20 j)) 20 (unsigned (start20 j) x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 (start20 j)) (unsigned (start20 j) x p) nums.small.1 nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ20.ready_pending_at j raw s (unsigned (start20 j) x p) g sg m nums.small.1 pre.cut inp hist
  have scr := scratch_raw_clean20 j d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut
  have prevOdd : (unsigned (prevTick20 j) x p).v % 2 = 1 := by
    unfold prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).odd
    · exact (actualNumbers20 (prev20 j) x p good).odd
  have prevSm : PrevSmall20 j (unsigned (prevTick20 j) x p) := by
    unfold PrevSmall20 prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).farSmall
    · exact (actualNumbers20 (prev20 j) x p good).small.1
  have cl := cleared_holes20 j d raw s m (unsigned (start20 j) x p) g sg nums.odd nums.small.1 pre.cut inp hist scr
    (unsigned (prevTick20 j) x p) pg ps (prevCross20 j x p) prevOdd prevSm pre.facts
  have hmem : base (1028 + r) ∈ WideReference20.oldSites (start20 j) (prevLen20 j) := by
    have hpl : 15 ≤ prevLen20 j := by unfold prevLen20; split_ifs <;> decide
    simp only [WideReference20.oldSites, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨r, ⟨by rcases hr with rfl | rfl | rfl | rfl <;> omega, by rcases hr with rfl | rfl | rfl | rfl <;> omega⟩, Or.inr rfl⟩
  rw [WideReference20.endRaw_inside hs_le _ _ _ hmem, show start20 j + 20 - 1 = start20 j + 19 by omega]
  have hsig : ∀ k : Fin 9, ∀ δ ∈ [8, 6, 3, 1],
      OB5.sig (start20 k + 19) (base (1028 + (start20 k - δ))) =
      OB5.sig (start20 k) (base (1028 + (start20 k - δ))) := by decide +kernel
  have h4 : ∀ k : Fin 9, ∀ δ ∈ [8, 6, 3, 1], OB5.sig (start20 k) (base (1028 + (start20 k - δ))) ∈ fourHoles20 k := by
    decide +kernel
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hsig j 8 (by decide)]; exact cl _ (h4 j 8 (by decide))
  · rw [hsig j 6 (by decide)]; exact cl _ (h4 j 6 (by decide))
  · rw [hsig j 3 (by decide)]; exact cl _ (h4 j 3 (by decide))
  · rw [hsig j 1 (by decide)]; exact cl _ (h4 j 1 (by decide))

private theorem ordinary345_step (d : Bool) (x : Nat) (good : Bounds x p)
    (raw s : State) (g sg pg ps : Bool) (m : List Bool) (pre : At345 d x p raw s g sg pg ps) :
    Except (MixedGeo.cells10 335)
      (WideReference.endRaw 345 (rawPack325 d raw) (run (nextWindow345 d) m s))
      (run (groupProg d [57, 58]) [] (run (span 345 15) [] raw)) := by
  have nums := LeaveJ7.Admission.actualNumbers MixedWindow.j20 (by decide) (by decide) x p good
  have hist := WideReference.pulled_history MixedWindow.j20 rfl pre.domain
  have inp := readInput 345 x p raw g sg pre.input
  let T := Shadow.reduced (Shadow7.sbP 345) 15 (unsigned 345 x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd_shadow7 (Shadow7.sbP 345) (unsigned 345 x p) nums.farSmall nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ7.ready_pending_at MixedWindow.j20 raw s (unsigned 345 x p) g sg m nums.farSmall pre.cut inp hist
  have hp := pack345_hist_vals d x p good raw s m pre.domain _ _ _ pre.cut Z parity ready.2.1
  have hgp : groupProg d [57, 58] = Rolling1588.encodeAt base d 325 ++ Rolling1588.encodeAt base d 330 := by
    change groupProg d ([57] ++ [58]) = _
    rw [groupProg_append, groupProg_singleton, groupProg_singleton]
  have hrun : run (groupProg d [57, 58]) [] (run (span 345 15) [] raw) =
      run (Rolling1588.encodeAt base d 330) [] (run (span 345 15) [] (rawPack325 d raw)) := by
    rw [hgp, run_append, run_take, List.drop_nil, rawPack325_span_comm]; rfl
  rw [hrun]
  intro q hnot
  by_cases hold : q ∈ WideReference.oldSites 345
  · rw [WideReference.endRaw_inside_gen 345 (by decide) _ _ q hold]
    obtain ⟨r, r1, r2, er⟩ := WideReference.old_cell hold
    have hs345 : oldStart 345 = 330 ∧ oldCount 345 = 15 := by decide
    rw [hs345.1] at r1 r2; rw [hs345.2] at r2
    have hr_lt : r < 335 := by
      by_contra hge; apply hnot
      simp only [MixedGeo.cells10, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
      exact ⟨r, ⟨by omega, by omega⟩, by rcases er with e | e; exact Or.inl e; exact Or.inr (by simp only [base, Wire] at e ⊢; omega)⟩
    have hi : ∃ i : Fin 10, q = plain330 i := by
      rcases er with rfl | rfl
      · refine ⟨⟨2 * (r - 330), by omega⟩, ?_⟩
        simp only [plain330, History5.historyMap, History5.historyId, base, Wire, Fin.val_mk]; rw [if_pos (by omega)]; omega
      · refine ⟨⟨2 * (r - 330) + 1, by omega⟩, ?_⟩
        simp only [plain330, History5.historyMap, History5.historyId, base, Wire, Fin.val_mk]; rw [if_neg (by omega)]; omega
    obtain ⟨i, rfl⟩ := hi
    have hsig : OB5.sig 359 (plain330 i) = histB345 i := by
      have h : ∀ k : Fin 10, OB5.sig 359 (plain330 k) = histB345 k := by decide +kernel
      exact h i
    rw [show (345 : Nat) + 14 = 359 from rfl, hsig]
    exact hp.2 i
  · rw [WideReference.endRaw_outside_gen 345 (by decide) _ _ q hold]
    symm; apply run_preserves_outside
    intro used; apply hold
    obtain ⟨r, r1, r2, e⟩ := OrdinaryChainW.encode_cells d 330 q used
    have hs345 : oldStart 345 = 330 ∧ oldCount 345 = 15 := by decide
    simp only [WideReference.oldSites, hs345.1, hs345.2, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨r, ⟨by omega, by omega⟩, e⟩

private theorem holes345_step (d : Bool) (x : Nat) (good : Bounds x p)
    (raw s : State) (g sg pg ps : Bool) (m : List Bool) (pre : At345 d x p raw s g sg pg ps)
    (r : Nat) (hr : r = 337 ∨ r = 339 ∨ r = 342 ∨ r = 344) :
    (WideReference.endRaw 345 (rawPack325 d raw) (run (nextWindow345 d) m s)).basis (base (1028 + r)) = false := by
  have inp := readInput 345 x p raw g sg pre.input
  have cl := cleared_holes345 d x p good raw s m pre.domain g sg pre.cut inp pg ps _ pre.facts
  have hmem : base (1028 + r) ∈ WideReference.oldSites 345 := by
    have hs345 : oldStart 345 = 330 ∧ oldCount 345 = 15 := by decide
    simp only [WideReference.oldSites, hs345.1, hs345.2, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨r, ⟨by rcases hr with rfl | rfl | rfl | rfl <;> omega, by rcases hr with rfl | rfl | rfl | rfl <;> omega⟩, Or.inr rfl⟩
  rw [WideReference.endRaw_inside_gen 345 (by decide) _ _ _ hmem, show (345 : Nat) + 14 = 359 from rfl]
  have h4 : ∀ v ∈ [337, 339, 342, 344], OB5.sig 359 (base (1028 + v)) ∈ fourHoles345 := by decide +kernel
  exact cl _ (h4 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide))

/-! ### Section 3: End-to-End Mixed Ordinary Chain (`wiresMixed`) -/

attribute [local irreducible] WideReference.endRaw WideReference20.endRaw

private def Ord15 (j : Fin 26) (n : Nat) (gs : List Nat) (d : Bool) (x : Nat) (initial s : State) : Prop :=
  ∃ (raw : State) (g sg pg ps : Bool),
    AtJ j d x p raw s g sg pg ps ∧
    Except (bankMask n) raw (run (groupProg d gs) [] (run (span 45 (start j - 45)) [] initial)) ∧
    ∀ q ∈ bankHoles n, raw.basis q = false

private def Ord20 (j : Fin 9) (n : Nat) (gs : List Nat) (d : Bool) (x : Nat) (initial s : State) : Prop :=
  ∃ (raw : State) (g sg pg ps : Bool),
    At20 j d x p raw s g sg pg ps ∧
    Except (bankMask n) raw (run (groupProg d gs) [] (run (span 45 (start20 j - 45)) [] initial)) ∧
    ∀ q ∈ bankHoles n, raw.basis q = false

private def Ord345 (n : Nat) (gs : List Nat) (d : Bool) (x : Nat) (initial s : State) : Prop :=
  ∃ (raw : State) (g sg pg ps : Bool),
    At345 d x p raw s g sg pg ps ∧
    Except (bankMask n) raw (run (groupProg d gs) [] (run (span 45 300) [] initial)) ∧
    ∀ q ∈ bankHoles n, raw.basis q = false

private theorem ord_prefix (d : Bool) (x : Nat) (good : Bounds x p) (initial : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 45 initial.basis) :
    let ch1 := ([Shadow7.portalP 45, Shadow7.enterP MixedWindow.j0, Shadow7.routed MixedWindow.j0 0 1,
      MixedWindow.packW d 45 45, Shadow7.routed MixedWindow.j0 1 14, CRTBarrel.leave MixedWindow.j0]).flatten
    let ch2 := (MixedWindow.prefixPairs.flatMap fun p => MixedWindow.block15F d p.1 p.2).flatten
    Ord15 MixedWindow.j7 6 [0, 1, 4, 7, 10, 13, 16] d x initial
      (run (ch1 ++ ch2) m (pullState (OB5.sig 44) initial)) := by
  have beg := OrdinaryChainG.beginG WindowParams.first ⟨1, by decide⟩ (by decide) (by decide) rfl
    (OrdinaryChainG.first_ship StockWindowW7.leaves22.first)
    (OrdinaryChainG.firstOrdinary_ship OrdinaryChainG.firstOrdinary)
    d x good initial m stage
  let js : List (Fin 26) := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩]
  have hconsec : Consec WindowParams.first js := ⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩
  have ch := OrdinaryChainG.chainG WindowParams.first rfl 1 24 (by decide) (by decide) (by decide)
    StockWindowW7.leaves22.endpoint StockWindowW7.leaves22.scratch d x good initial
    WindowParams.first js hconsec (by intro k hk; simp only [js, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    ⟨1, by decide⟩ MixedWindow.j7 rfl rfl _ (m.drop (measurementCount ((Shadow7.portalP 45 ++ NativeFirstJ7.enteredWindow WindowParams.first d) ++ CRTBarrel.leave WindowParams.first))) beg
  have heq1 : ([Shadow7.portalP 45, Shadow7.enterP MixedWindow.j0, Shadow7.routed MixedWindow.j0 0 1,
      MixedWindow.packW d 45 45, Shadow7.routed MixedWindow.j0 1 14, CRTBarrel.leave MixedWindow.j0]).flatten =
      (Shadow7.portalP 45 ++ NativeFirstJ7.enteredWindow WindowParams.first d) ++ CRTBarrel.leave WindowParams.first := by
    have := OrdinaryChainG.first_eqF d WindowParams.first
    simpa only [firstF, CRTBarrel.params, Shadow7.params, ofParts, MixedWindow.packW,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] using this
  have heq2 : (MixedWindow.prefixPairs.flatMap fun p => MixedWindow.block15F d p.1 p.2).flatten =
      (chainF CRTBarrel.params d WindowParams.first js).flatten := by
    simp only [MixedWindow.prefixPairs, MixedWindow.block15F, MixedWindow.packW, js, chainF, nextF,
      WindowParams.first, CRTBarrel.params, Shadow7.params, ofParts, List.flatMap_cons, List.flatMap_nil,
      List.flatten_cons, List.flatten_nil, List.flatten_append, List.append_nil, List.append_assoc]
  dsimp only
  rw [run_append, run_take, heq1, heq2]
  obtain ⟨raw, g, sg, pg, ps, atJ, hist, zeros⟩ := ch
  have hm : OrdinaryChainW.mask 45 7 = bankMask 6 := by decide +kernel
  have hp : OrdinaryChainW.progW 45 d 7 = groupProg d [0, 1, 4, 7, 10, 13, 16] := by
    have := OrdinaryChainG.progW_plain 45 (by decide) d 6
    simpa only [groupProg, show StockWindowGeo.plain 6 = [0, 1, 4, 7, 10, 13, 16] by decide +kernel] using this
  have hh : StockWindowGeo.holes 45 6 = bankHoles 6 := by decide +kernel
  rw [show start WindowParams.first = 45 from rfl, show MixedWindow.j7.val - WindowParams.first.val = 7 from rfl,
    show 15 * 7 = start MixedWindow.j7 - 45 from rfl, hm, hp] at hist
  rw [show start WindowParams.first = 45 from rfl, show MixedWindow.j7.val - WindowParams.first.val - 1 = 6 from rfl, hh] at zeros
  exact ⟨raw, g, sg, pg, ps, atJ, hist, zeros⟩

private theorem ord_150To20 (d : Bool) (x : Nat) (good : Bounds x p) (initial s : State) (m : List Bool)
    (h : Ord15 MixedWindow.j7 6 [0, 1, 4, 7, 10, 13, 16] d x initial s) :
    let ch3 := ([Shadow7.enterP MixedWindow.j7, Shadow7.routed MixedWindow.j7 0 1, MixedWindow.packW d 150 140,
      Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, leave150To20Red]).flatten
    Ord20 ⟨0, by decide⟩ 7 [0, 1, 4, 7, 10, 13, 16, 19] d x initial (run ch3 m s) := by
  have hfl : ([Shadow7.enterP MixedWindow.j7, Shadow7.routed MixedWindow.j7 0 1, MixedWindow.packW d 150 140,
      Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, leave150To20Red]).flatten =
      NativeJ7.nextWindow MixedWindow.j7 d ++ leave150To20Red := by
    simp only [NativeJ7.nextWindow, NativeJ7.window, Shadow7.body, NativeJ7.withArchive, NativeJ7.program,
      MixedWindow.packW, show NativeJ7.prev MixedWindow.j7 = MixedWindow.j6 from rfl,
      show start MixedWindow.j7 = 150 from rfl, show (150 : Nat) - 10 = 140 from rfl,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  dsimp only
  rw [hfl, run_append, run_take]
  obtain ⟨raw, g, sg, pg, ps, pre, old, zeros⟩ := h
  have hs150 : start MixedWindow.j7 = 150 := rfl
  have hdom150 : Domain 150 x p raw := hs150 ▸ pre.domain
  have hinp150 : InputAt 150 (signedAt 150 x p g sg) raw := hs150 ▸ pre.input
  have hcut150 := pre.cut
  rw [hs150] at hcut150
  have nums := LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good
  have inp := readInput 150 x p raw g sg hinp150
  have scr := StockWindowW7.leaves22.scratch MixedWindow.j7 (by decide) (by decide) d x p good raw s g sg pg ps m pre
  have nat := NativeJ7.from_domain_matched MixedWindow.j7 (by decide) (by decide) d x p good raw s m pre.domain g sg pre.cut (hs150.symm ▸ inp) scr pg ps _ pre.facts
  have hnextSmall20 : Shadow7.SmallIfFar 163 20 (SkywalkNat.step^[15] (unsigned 150 x p)) := by
    have hs165 : start20 ⟨0, by decide⟩ = 165 := rfl
    have hsb163 : sbP20 (start20 ⟨0, by decide⟩) = 163 := rfl
    have h1 := (actualNumbers20 ⟨0, by decide⟩ x p good).small.1
    rw [hsb163, hs165] at h1
    have he165 : SkywalkNat.step^[15] (unsigned 150 x p) = unsigned 165 x p := by
      show SkywalkNat.step^[15] (SkywalkNat.step^[150] (SkywalkNat.init x p)) = SkywalkNat.step^[165] (SkywalkNat.init x p)
      rw [show (165 : Nat) = 150 + 15 by decide, Nat.add_comm, Function.iterate_add_apply]
    rw [he165]; exact h1
  have hred150 := leave150To20Red_pair (run (NativeJ7.nextWindow MixedWindow.j7 d) m s) (unsigned 150 x p) g sg nat.1 hnextSmall20
  rw [hred150.1]
  have ep := endpoint150To20 d x p good raw s m (m.drop (measurementCount (NativeJ7.nextWindow MixedWindow.j7 d)))
    hdom150 g sg hcut150 inp scr pg ps _ pre.facts
  have carried := stepInput_gen_shadow7 150 (Shadow7.sbP 150) x p (by decide) (by decide) good raw
    (run (NativeJ7.nextWindow MixedWindow.j7 d) m s) g sg hdom150 hinp150 (hs150 ▸ nums.farSmall)
  have canon := unique_input hinp150 (fixed_input 150 x p (by decide) good raw hdom150)
  have step := OrdinaryChainG.ordinaryG WindowParams.first rfl MixedWindow.j7 (by decide) (by decide) d x good raw s g sg pg ps m pre
  rw [hs150] at step
  have hbm : bankMask 7 = bankMask 6 ++ OrdinaryJ.newBank MixedWindow.j7 := by
    rw [bankMask_succ ⟨6, by decide⟩]
    have hnb : MixedGeo.cells10 (MixedGeo.endTick ⟨6, by decide⟩ - 10) = OrdinaryJ.newBank MixedWindow.j7 := by
      decide +kernel
    rw [hnb]
  have h165 : (150 : Nat) + 15 = start20 ⟨0, by decide⟩ := rfl
  have hpt0 : (150 : Nat) = prevTick20 ⟨0, by decide⟩ := rfl
  have hend6 : ∀ b : MixedGeo.Bank, b.val < 6 → MixedGeo.endTick b ≤ 135 := by decide +kernel
  refine ⟨WideReference.endRaw 150 raw (run (NativeJ7.nextWindow MixedWindow.j7 d) m s),
    (LeaveJ7.Admission.flags (unsigned 150 x p) g sg).1,
    (LeaveJ7.Admission.flags (unsigned 150 x p) g sg).2, g, sg,
    ⟨h165 ▸ carried.1, by rw [← h165, flags15_eq]; exact carried.2, by simpa only [← h165] using ep.1,
      by simpa only [PrevPast20, prevTick20, prevCross20, ↓reduceIte] using ep.2.1, hpt0 ▸ canon⟩, ?_, ?_⟩
  · rw [hbm, ← h165]
    rw [hs150] at old
    have h19 : [0, 1, 4, 7, 10, 13, 16, 19] = [0, 1, 4, 7, 10, 13, 16] ++ [19] := rfl
    rw [h19]
    refine extend_step d 150 15 (by decide) (by decide) (bankMask 6) (OrdinaryJ.newBank MixedWindow.j7)
      [0, 1, 4, 7, 10, 13, 16] [19] raw initial _ old
      (by rw [groupProg_singleton, show (40 : Nat) + 5 * 19 = 150 - 15 from rfl]; exact step) ?_ ?_ ?_
    · intro q hq
      obtain ⟨r, hr, e⟩ := bankMask_cells 6 135 hend6 q hq
      exact ⟨r, by omega, e⟩
    · intro q hq
      obtain ⟨r, hr, e⟩ := groupProg_cells d [0, 1, 4, 7, 10, 13, 16] 135 (by decide +kernel) q hq
      exact ⟨r, by omega, e⟩
    · intro q hq used
      rw [groupProg_singleton] at used
      obtain ⟨r, hr, e⟩ := bankMask_cells 6 135 hend6 q hq
      obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d 135 q used
      rcases e with rfl | rfl <;> rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
  · rw [bankHoles_succ ⟨6, by decide⟩]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · apply OrdinaryChainW.carry 150 (by decide) (bankHoles 6) ?_ ?_ raw _ zeros q hq
      · intro w hw hit
        obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells 6 135 hend6 w hw
        obtain ⟨r', r1, r2, e'⟩ := WideReference.old_cell hit
        have hs150 : oldStart 150 = 135 ∧ oldCount 150 = 15 := by decide
        rw [hs150.1] at r1 r2; rw [hs150.2] at r2
        rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
      · intro w hw
        obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells 6 135 hend6 w hw
        right; simp only [base, Wire]; omega
    · simp only [show MixedGeo.endTick ⟨6, by decide⟩ = 150 by decide +kernel, List.mem_cons, List.not_mem_nil, or_false] at hq
      have hG := fun r hr => hs150 ▸ OrdinaryChainG.holesG WindowParams.first rfl StockWindowW7.leaves22.scratch MixedWindow.j7 (by decide) (by decide) (by decide) d x good raw s g sg pg ps m pre r hr
      rcases hq with rfl | rfl | rfl | rfl
      · exact hG (150 - 8) (Or.inl rfl)
      · exact hG (150 - 6) (Or.inr (Or.inl rfl))
      · exact hG (150 - 3) (Or.inr (Or.inr (Or.inl rfl)))
      · exact hG (150 - 1) (Or.inr (Or.inr (Or.inr rfl)))

private theorem endTick20_prev_ord :
    ∀ (r : Fin 9) (b : MixedGeo.Bank), b.val < 7 + r.val → MixedGeo.endTick b ≤ start20 r - prevLen20 r := by
  decide +kernel

private theorem endTick20_cur_ord :
    ∀ r : Fin 9, MixedGeo.endTick ⟨7 + r.val, by have := r.isLt; omega⟩ = start20 r := by
  decide +kernel

private theorem endTick15_prev_ord :
    ∀ (r : Fin 26), 21 ≤ r.val → r.val ≤ 24 → ∀ b' : MixedGeo.Bank, b'.val < r.val - 4 → MixedGeo.endTick b' ≤ start r - 15 := by
  decide +kernel

private theorem endTick15_cur_ord :
    ∀ (r : Fin 26), 21 ≤ r.val → r.val ≤ 24 → MixedGeo.endTick ⟨r.val - 4, by have := r.isLt; omega⟩ = start r := by
  decide +kernel

private theorem ord_20_next (j k : Fin 9) (hk : k.val = j.val + 1) (gs : List Nat) (d : Bool) (x : Nat) (good : Bounds x p)
    (hgs : ∀ i ∈ gs, 40 + 5 * i + 5 ≤ start20 j - prevLen20 j)
    (initial s : State) (m : List Bool) (h : Ord20 j (7 + j.val) gs d x initial s) :
    Ord20 k (7 + k.val) (gs ++ groups20 j) d x initial (run (MixedWindow.block20F d j).flatten m s) := by
  have hj := j.isLt
  have hfl : (MixedWindow.block20F d j).flatten = nextWindow20 j d ++ leaveP20Red j := by
    unfold MixedWindow.block20F nextWindow20 window20 body20 withArchive20 packProg20 archLoad20 prev20
    by_cases h0 : j.val = 0 <;> simp only [h0, ↓reduceDIte, ↓reduceIte, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  rw [hfl, run_append, run_take]
  obtain ⟨raw, g, sg, pg, ps, pre, old, zeros⟩ := h
  have nums := actualNumbers20 j x p good
  have hist := WideReference20.pulled_history20 j pre.domain
  have inp := readInput (start20 j) x p raw g sg pre.input
  let T := Shadow.reduced (sbP20 (start20 j)) 20 (unsigned (start20 j) x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 (start20 j)) (unsigned (start20 j) x p) nums.small.1 nums.odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ20.ready_pending_at j raw s (unsigned (start20 j) x p) g sg m nums.small.1 pre.cut inp hist
  have scr := scratch_raw_clean20 j d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut
  have prevOdd : (unsigned (prevTick20 j) x p).v % 2 = 1 := by
    unfold prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).odd
    · exact (actualNumbers20 (prev20 j) x p good).odd
  have prevSm : PrevSmall20 j (unsigned (prevTick20 j) x p) := by
    unfold PrevSmall20 prevTick20; split_ifs with h0
    · exact (LeaveJ7.Admission.actualNumbers MixedWindow.j7 (by decide) (by decide) x p good).farSmall
    · exact (actualNumbers20 (prev20 j) x p good).small.1
  have adm := admitted20 j d x p good raw s m pre.domain g sg pre.cut inp scr
    (unsigned (prevTick20 j) x p) pg ps (prevCross20 j x p) prevOdd prevSm pre.facts
  have hred20 := leaveP20Red_pair j (run (nextWindow20 j d) m s) (unsigned (start20 j) x p) g sg adm.1
  rw [hred20.1]
  have ep := endpoint20_next j k hk d x p good raw s m (m.drop (measurementCount (nextWindow20 j d)))
    pre.domain g sg pre.cut inp scr (unsigned (prevTick20 j) x p) pg ps (prevCross20 j x p) prevOdd prevSm pre.facts
  have hprev_le : prevLen20 j ≤ start20 j := by unfold prevLen20 start20; split_ifs <;> omega
  have carried := WideReference20.stepInput20 (start20 j) (prevLen20 j) (sbP20 (start20 j)) x p hprev_le (by unfold start20; omega)
    good raw (run (nextWindow20 j d) m s) g sg pre.domain pre.input nums.small.1
  have canon := unique_input pre.input (fixed_input (start20 j) x p (by unfold start20; omega) good raw pre.domain)
  have hsk : start20 k = start20 j + 20 := by unfold start20; omega
  have hpk : prev20 k = j := Fin.ext (by simp only [prev20]; omega)
  have hend_prev : ∀ b : MixedGeo.Bank, b.val < 7 + j.val → MixedGeo.endTick b ≤ start20 j - prevLen20 j :=
    endTick20_prev_ord j
  have hend_cur : MixedGeo.endTick ⟨7 + j.val, by omega⟩ = start20 j := endTick20_cur_ord j
  refine ⟨WideReference20.endRaw (start20 j) (prevLen20 j) 20 raw (run (nextWindow20 j d) m s),
    (flags20 (unsigned (start20 j) x p) g sg).1, (flags20 (unsigned (start20 j) x p) g sg).2, g, sg,
    ⟨hsk ▸ carried.1, by rw [flags20_eq]; exact hsk ▸ carried.2, ep.1,
      by simp only [PrevPast20, prevTick20, prevCross20, if_neg (show k.val ≠ 0 by omega), hpk]; exact ep.2,
      by simp only [prevTick20, if_neg (show k.val ≠ 0 by omega), hpk]; exact canon⟩, ?_, ?_⟩
  · rw [hk, show 7 + (j.val + 1) = (7 + j.val) + 1 by omega, bankMask_succ ⟨7 + j.val, by omega⟩, hend_cur, hsk]
    refine extend_step d (start20 j) 20 (by unfold start20; omega) (by unfold start20; omega)
      (bankMask (7 + j.val)) (MixedGeo.cells10 (start20 j - 10)) gs (groups20 j) raw initial _ old
      (ordinary20_step j d x good raw s g sg pg ps m pre) ?_ ?_ ?_
    · intro q hq; obtain ⟨r, hr, e⟩ := bankMask_cells (7 + j.val) (start20 j - prevLen20 j) hend_prev q hq
      have : 15 ≤ prevLen20 j := by unfold prevLen20; split_ifs <;> decide
      exact ⟨r, by omega, e⟩
    · intro q hq; obtain ⟨r, hr, e⟩ := groupProg_cells d gs (start20 j - prevLen20 j) hgs q hq
      have : 15 ≤ prevLen20 j := by unfold prevLen20; split_ifs <;> decide
      exact ⟨r, by omega, e⟩
    · intro q hq used
      obtain ⟨r, hr, e⟩ := bankMask_cells (7 + j.val) (start20 j - prevLen20 j) hend_prev q hq
      have hge : ∃ r', start20 j - prevLen20 j ≤ r' ∧ r' < 512 ∧ (q = base r' ∨ q = base (1028 + r')) := by
        unfold groups20 at used; split_ifs at used with h0
        · rw [groupProg_singleton] at used; obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d 150 q used
          have : start20 j - prevLen20 j = 150 := by simp [start20, prevLen20, h0]
          exact ⟨r', by omega, by omega, e'⟩
        · change q ∈ wires (groupProg d ([(start20 j - 20 - 40) / 5] ++ [(start20 j - 15 - 40) / 5])) at used
          rw [groupProg_append, wires_append, Finset.mem_union, groupProg_singleton, groupProg_singleton] at used
          have : prevLen20 j = 20 := by simp [prevLen20, h0]
          rcases used with u | u
          · obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d _ q u
            exact ⟨r', by unfold start20 at *; omega, by unfold start20 at *; omega, e'⟩
          · obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d _ q u
            exact ⟨r', by unfold start20 at *; omega, by unfold start20 at *; omega, e'⟩
      obtain ⟨r', hr', hr2', e'⟩ := hge
      rcases e with rfl | rfl <;> rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
  · rw [hk, show 7 + (j.val + 1) = (7 + j.val) + 1 by omega, bankHoles_succ ⟨7 + j.val, by omega⟩, hend_cur]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact carry20_holes (start20 j) (prevLen20 j) (by unfold prevLen20; split_ifs <;> decide) hprev_le (by unfold start20; omega) (bankHoles (7 + j.val))
        (fun w hw => by obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells (7 + j.val) (start20 j - prevLen20 j) hend_prev w hw; exact ⟨r, by omega, rfl⟩)
        raw _ zeros q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact holes20_step j d x good raw s g sg pg ps m pre _ (Or.inl rfl)
      · exact holes20_step j d x good raw s g sg pg ps m pre _ (Or.inr (Or.inl rfl))
      · exact holes20_step j d x good raw s g sg pg ps m pre _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact holes20_step j d x good raw s g sg pg ps m pre _ (Or.inr (Or.inr (Or.inr rfl)))

private theorem ord_20_last (gs : List Nat) (d : Bool) (x : Nat) (good : Bounds x p)
    (hgs : ∀ i ∈ gs, 40 + 5 * i + 5 ≤ 305)
    (initial s : State) (m : List Bool) (h : Ord20 MixedWindow.k8 15 gs d x initial s) :
    Ord345 16 (gs ++ groups20 MixedWindow.k8) d x initial (run (MixedWindow.block20F d MixedWindow.k8).flatten m s) := by
  have hfl : (MixedWindow.block20F d MixedWindow.k8).flatten = nextWindow20 MixedWindow.k8 d ++ leaveP20Red MixedWindow.k8 := by
    unfold MixedWindow.block20F nextWindow20 window20 body20 withArchive20 packProg20 archLoad20 prev20
    simp only [show MixedWindow.k8.val ≠ 0 by decide, ↓reduceDIte, ↓reduceIte, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  rw [hfl, run_append, run_take]
  obtain ⟨raw, g, sg, pg, ps, pre, old, zeros⟩ := h
  have hs325 : start20 MixedWindow.k8 = 325 := rfl
  have hdom325 : Domain 325 x p raw := hs325 ▸ pre.domain
  have hinp325 : InputAt 325 (signedAt 325 x p g sg) raw := hs325 ▸ pre.input
  have hcut325 := pre.cut
  rw [hs325] at hcut325
  have nums := actualNumbers20 MixedWindow.k8 x p good
  have hnums_sm : Shadow7.SmallIfFar (sbP20 325) 20 (unsigned 325 x p) := hs325 ▸ nums.small.1
  have hnums_odd : (unsigned 325 x p).v % 2 = 1 := hs325 ▸ nums.odd
  have hist := WideReference20.pulled_history20 MixedWindow.k8 pre.domain
  have inp := readInput 325 x p raw g sg hinp325
  let T := Shadow.reduced (sbP20 325) 20 (unsigned 325 x p)
  let Z := encode g sg T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 325) (unsigned 325 x p) hnums_sm hnums_odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum g sg _ _ (by omega)
  have ready := EnterJ20.ready_pending_at MixedWindow.k8 raw s (unsigned (start20 MixedWindow.k8) x p) g sg m nums.small.1 pre.cut (hs325.symm ▸ inp) hist
  have scr := scratch_raw_clean20 MixedWindow.k8 d raw s m x p good pre.domain _ _ _ Z parity (by simpa only [hs325] using ready.2.1) pre.cut
  have hpt305 : prevTick20 MixedWindow.k8 = start20 (prev20 MixedWindow.k8) := rfl
  have prevOdd : (unsigned (prevTick20 MixedWindow.k8) x p).v % 2 = 1 :=
    hpt305.symm ▸ (actualNumbers20 (prev20 MixedWindow.k8) x p good).odd
  have prevSm : PrevSmall20 MixedWindow.k8 (unsigned (prevTick20 MixedWindow.k8) x p) :=
    hpt305.symm ▸ (actualNumbers20 (prev20 MixedWindow.k8) x p good).small.1
  have adm := admitted20 MixedWindow.k8 d x p good raw s m pre.domain g sg pre.cut (hs325.symm ▸ inp) scr
    (unsigned (prevTick20 MixedWindow.k8) x p) pg ps (prevCross20 MixedWindow.k8 x p) prevOdd prevSm pre.facts
  have hred20 := leaveP20Red_pair MixedWindow.k8 (run (nextWindow20 MixedWindow.k8 d) m s) (unsigned (start20 MixedWindow.k8) x p) g sg adm.1
  rw [hred20.1]
  have ep := endpoint20_reentry d x p good raw s m (m.drop (measurementCount (nextWindow20 MixedWindow.k8 d)))
    hdom325 g sg hcut325 inp scr (unsigned (prevTick20 MixedWindow.k8) x p) pg ps (prevCross20 MixedWindow.k8 x p) prevOdd prevSm pre.facts
  have carried := WideReference20.stepInput20 325 20 (sbP20 325) x p (by decide) (by decide)
    good raw (run (nextWindow20 MixedWindow.k8 d) m s) g sg hdom325 hinp325 hnums_sm
  have canon := unique_input hinp325 (fixed_input 325 x p (by decide) good raw hdom325)
  have hend_prev : ∀ b : MixedGeo.Bank, b.val < 15 → MixedGeo.endTick b ≤ 305 := by decide +kernel
  have h345 : (325 : Nat) + 20 = 345 := rfl
  refine ⟨WideReference20.endRaw 325 20 20 raw (run (nextWindow20 MixedWindow.k8 d) m s),
    (flags20 (unsigned 325 x p) g sg).1, (flags20 (unsigned 325 x p) g sg).2, g, sg,
    ⟨h345 ▸ carried.1, by rw [← h345, flags20_eq]; exact carried.2, ep.1, ep.2, canon⟩, ?_, ?_⟩
  · rw [bankMask_succ ⟨15, by decide⟩, show MixedGeo.endTick ⟨15, by decide⟩ = 325 by decide,
      show (300 : Nat) = 325 + 20 - 45 from rfl]
    rw [hs325] at old
    have hstep := ordinary20_step MixedWindow.k8 d x good raw s g sg pg ps m pre
    rw [hs325, show prevLen20 MixedWindow.k8 = 20 from rfl] at hstep
    refine extend_step d 325 20 (by decide) (by decide)
      (bankMask 15) (MixedGeo.cells10 (325 - 10)) gs (groups20 MixedWindow.k8) raw initial _ old
      hstep ?_ ?_ ?_
    · intro q hq; obtain ⟨r, hr, e⟩ := bankMask_cells 15 305 hend_prev q hq; exact ⟨r, by omega, e⟩
    · intro q hq; obtain ⟨r, hr, e⟩ := groupProg_cells d gs 305 hgs q hq; exact ⟨r, by omega, e⟩
    · intro q hq used
      obtain ⟨r, hr, e⟩ := bankMask_cells 15 305 hend_prev q hq
      have hge : ∃ r', 305 ≤ r' ∧ r' < 512 ∧ (q = base r' ∨ q = base (1028 + r')) := by
        rw [show groups20 MixedWindow.k8 = [53] ++ [54] by decide, groupProg_append, wires_append, Finset.mem_union,
          groupProg_singleton, groupProg_singleton] at used
        rcases used with u | u
        · obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d _ q u; exact ⟨r', by omega, by omega, e'⟩
        · obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d _ q u; exact ⟨r', by omega, by omega, e'⟩
      obtain ⟨r', hr', hr2', e'⟩ := hge
      rcases e with rfl | rfl <;> rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
  · rw [bankHoles_succ ⟨15, by decide⟩, show MixedGeo.endTick ⟨15, by decide⟩ = 325 by decide]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact carry20_holes 325 20 (by decide) (by decide) (by decide) (bankHoles 15)
        (fun w hw => by obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells 15 305 hend_prev w hw; exact ⟨r, by omega, rfl⟩)
        raw _ zeros q hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      have hH := fun r hr => by
        have hh := holes20_step MixedWindow.k8 d x good raw s g sg pg ps m pre r hr
        rw [hs325, show prevLen20 MixedWindow.k8 = 20 from rfl] at hh
        exact hh
      rcases hq with rfl | rfl | rfl | rfl
      · exact hH (325 - 8) (Or.inl rfl)
      · exact hH (325 - 6) (Or.inr (Or.inl rfl))
      · exact hH (325 - 3) (Or.inr (Or.inr (Or.inl rfl)))
      · exact hH (325 - 1) (Or.inr (Or.inr (Or.inr rfl)))

private theorem ord_345 (gs : List Nat) (d : Bool) (x : Nat) (good : Bounds x p)
    (hgs : ∀ i ∈ gs, 40 + 5 * i + 5 ≤ 325)
    (initial s : State) (m : List Bool) (h : Ord345 16 gs d x initial s) :
    let ch5 := ([Shadow7.enterP MixedWindow.j20, Shadow7.routed MixedWindow.j20 0 1,
      MixedWindow.packW d 345 330, MixedWindow.packW d 345 335, archiveLoadP20 MixedWindow.k8 d,
      Shadow7.routed MixedWindow.j20 1 14, CRTBarrel.leave MixedWindow.j20]).flatten
    Ord15 ⟨21, by decide⟩ 17 (gs ++ [57, 58]) d x initial (run ch5 m s) := by
  have hfl : ([Shadow7.enterP MixedWindow.j20, Shadow7.routed MixedWindow.j20 0 1,
      MixedWindow.packW d 345 330, MixedWindow.packW d 345 335, archiveLoadP20 MixedWindow.k8 d,
      Shadow7.routed MixedWindow.j20 1 14, CRTBarrel.leave MixedWindow.j20]).flatten =
      nextWindow345 d ++ CRTBarrel.leave MixedWindow.j20 := by
    simp only [nextWindow345, window345, Shadow7.body, withArchive345, packProg345,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  dsimp only
  rw [hfl, run_append, run_take]
  obtain ⟨raw, g, sg, pg, ps, pre, old, zeros⟩ := h
  have nums := LeaveJ7.Admission.actualNumbers MixedWindow.j20 (by decide) (by decide) x p good
  have inp := readInput 345 x p raw g sg pre.input
  have ep := endpoint345 d x p good raw s m (m.drop (measurementCount (nextWindow345 d)))
    pre.domain g sg pre.cut inp pg ps _ pre.facts
  have domP := rawPack325_domain d x p raw pre.domain
  have inpP := rawPack325_input d raw _ pre.input
  have carried := stepInput_gen_shadow7 345 (Shadow7.sbP 345) x p (by decide) (by decide) good (rawPack325 d raw)
    (run (nextWindow345 d) m s) g sg domP inpP nums.farSmall
  have canon := unique_input pre.input (fixed_input 345 x p (by decide) good raw pre.domain)
  have hend_prev : ∀ b : MixedGeo.Bank, b.val < 16 → MixedGeo.endTick b ≤ 325 := by decide +kernel
  refine ⟨WideReference.endRaw 345 (rawPack325 d raw) (run (nextWindow345 d) m s),
    (LeaveJ7.Admission.flags (unsigned 345 x p) g sg).1,
    (LeaveJ7.Admission.flags (unsigned 345 x p) g sg).2, g, sg,
    ⟨carried.1, by rw [flags15_eq]; exact carried.2, ep.2.1, ep.2.2.1, canon⟩, ?_, ?_⟩
  · rw [bankMask_succ ⟨16, by decide⟩, show MixedGeo.endTick ⟨16, by decide⟩ = 345 by decide,
      show start ⟨21, by decide⟩ = 345 + 15 from rfl]
    rw [show (300 : Nat) = 345 - 45 from rfl] at old
    refine extend_step d 345 15 (by decide) (by decide)
      (bankMask 16) (MixedGeo.cells10 (345 - 10)) gs [57, 58] raw initial _ old
      (ordinary345_step d x good raw s g sg pg ps m pre) ?_ ?_ ?_
    · intro q hq; obtain ⟨r, hr, e⟩ := bankMask_cells 16 325 hend_prev q hq; exact ⟨r, by omega, e⟩
    · intro q hq; obtain ⟨r, hr, e⟩ := groupProg_cells d gs 325 hgs q hq; exact ⟨r, by omega, e⟩
    · intro q hq used
      obtain ⟨r, hr, e⟩ := bankMask_cells 16 325 hend_prev q hq
      change q ∈ wires (groupProg d ([57] ++ [58])) at used
      rw [groupProg_append, wires_append, Finset.mem_union, groupProg_singleton, groupProg_singleton] at used
      rcases used with u | u
      · obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d _ q u
        rcases e with rfl | rfl <;> rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
      · obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d _ q u
        rcases e with rfl | rfl <;> rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
  · rw [bankHoles_succ ⟨16, by decide⟩, show MixedGeo.endTick ⟨16, by decide⟩ = 345 by decide]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · apply OrdinaryChainW.carry 345 (by decide) (bankHoles 16) ?_ ?_ (rawPack325 d raw) _ ?_ q hq
      · intro w hw hit
        obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells 16 325 hend_prev w hw
        obtain ⟨r', r1, r2, e'⟩ := WideReference.old_cell hit
        have hs345 : oldStart 345 = 330 ∧ oldCount 345 = 15 := by decide
        rw [hs345.1] at r1 r2; rw [hs345.2] at r2
        rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
      · intro w hw
        obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells 16 325 hend_prev w hw
        right; simp only [base, Wire]; omega
      · intro w hw
        obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells 16 325 hend_prev w hw
        have hout : (rawPack325 d raw).basis (base (1028 + r)) = raw.basis (base (1028 + r)) := by
          apply run_preserves_outside; intro used
          obtain ⟨r', r1, r2, e' | e'⟩ := OrdinaryChainW.encode_cells d 325 _ used <;> simp only [base, Wire] at e' <;> omega
        rw [hout]; exact zeros _ hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact holes345_step d x good raw s g sg pg ps m pre (345 - 8) (Or.inl rfl)
      · exact holes345_step d x good raw s g sg pg ps m pre (345 - 6) (Or.inr (Or.inl rfl))
      · exact holes345_step d x good raw s g sg pg ps m pre (345 - 3) (Or.inr (Or.inr (Or.inl rfl)))
      · exact holes345_step d x good raw s g sg pg ps m pre (345 - 1) (Or.inr (Or.inr (Or.inr rfl)))

private theorem ord_15_suffix_step (i k k1 : Fin 26) (hk : k.val = i.val + 1) (hk1 : k1.val = k.val + 1)
    (h21 : 21 ≤ k.val) (h24 : k.val ≤ 24) (n : Nat) (hn : n = k.val - 4) (gs : List Nat) (d : Bool)
    (x : Nat) (good : Bounds x p) (hgs : ∀ g ∈ gs, 40 + 5 * g + 5 ≤ start k - 15)
    (initial s : State) (m : List Bool) (h : Ord15 k n gs d x initial s) :
    Ord15 k1 (n + 1) (gs ++ [(start k - 15 - 40) / 5]) d x initial (run (MixedWindow.block15F d i k).flatten m s) := by
  have pk : NativeJ7.prev k = i := Fin.ext (by simp only [NativeJ7.prev]; omega)
  have hfl : (MixedWindow.block15F d i k).flatten = NativeJ7.nextWindow k d ++ CRTBarrel.leave k := by
    rw [← pk]
    simp only [MixedWindow.block15F, MixedWindow.packW, NativeJ7.nextWindow, NativeJ7.window,
      Shadow7.body, NativeJ7.withArchive, NativeJ7.program, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.append_assoc]
  rw [hfl, run_append, run_take]
  obtain ⟨raw, g, sg, pg, ps, pre, old, zeros⟩ := h
  have hwf : WindowParams.first.val = 0 := rfl
  have hfb : WideReference.firstBlock = 45 := rfl
  have hsk : start k = 45 + 15 * k.val := rfl
  rw [StockWindowW7.sameAt StockWindowW7.leaves22.scratch k (by omega) h24 d x p good raw s g sg pg ps m pre]
  obtain ⟨a, b, c, e, pre'⟩ := OrdinaryChainG.pinnedG 1 24 (by decide) (by decide) StockWindowW7.leaves22.endpoint
    StockWindowW7.leaves22.scratch k k1 hk1 (by omega) h24 d x good raw s g sg pg ps m pre
  have step := OrdinaryChainG.ordinaryG WindowParams.first rfl k (by omega) h24 d x good raw s g sg pg ps m pre
  have hsk1 : start k1 = start k + 15 := by simp only [start]; omega
  have hend_prev : ∀ b' : MixedGeo.Bank, b'.val < n → MixedGeo.endTick b' ≤ start k - 15 :=
    fun b' hb' => endTick15_prev_ord k h21 h24 b' (by omega)
  have hend_cur : MixedGeo.endTick ⟨n, by omega⟩ = start k := by
    have := endTick15_cur_ord k h21 h24; simpa only [hn] using this
  have hgp_eq : groupProg d [(start k - 15 - 40) / 5] = Rolling1588.encodeAt base d (start k - 15) := by
    rw [groupProg_singleton]; congr 1; simp only [start]; omega
  refine ⟨WideReference.endRaw (start k) raw (run (NativeJ7.nextWindow k d) m s), a, b, c, e, pre', ?_, ?_⟩
  · rw [bankMask_succ ⟨n, by omega⟩, hend_cur, hsk1]
    refine extend_step d (start k) 15 (by simp only [start]; omega) (by simp only [start]; omega)
      (bankMask n) (MixedGeo.cells10 (start k - 10)) gs [(start k - 15 - 40) / 5] raw initial _ old
      (by rw [hgp_eq]; exact step) ?_ ?_ ?_
    · intro q hq; obtain ⟨r, hr, e'⟩ := bankMask_cells n (start k - 15) hend_prev q hq; exact ⟨r, by omega, e'⟩
    · intro q hq; obtain ⟨r, hr, e'⟩ := groupProg_cells d gs (start k - 15) hgs q hq; exact ⟨r, by omega, e'⟩
    · intro q hq used
      rw [hgp_eq] at used
      obtain ⟨r, hr, e'⟩ := bankMask_cells n (start k - 15) hend_prev q hq
      obtain ⟨r', r1, r2, e''⟩ := OrdinaryChainW.encode_cells d (start k - 15) q used
      rcases e' with rfl | rfl <;> rcases e'' with e'' | e'' <;> simp only [base, Wire] at e'' <;> omega
  · rw [bankHoles_succ ⟨n, by omega⟩, hend_cur]
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · apply OrdinaryChainW.carry (start k) (by simp only [start]; omega) (bankHoles n) ?_ ?_ raw _ zeros q hq
      · intro w hw hit
        obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells n (start k - 15) hend_prev w hw
        obtain ⟨r', r1, r2, e'⟩ := WideReference.old_cell hit
        have hne : start k ≠ WideReference.firstBlock := by simp only [start, WideReference.firstBlock]; omega
        rw [oldStart_interior hne] at r1 r2; rw [oldCount_interior hne] at r2
        rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
      · intro w hw
        obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells n (start k - 15) hend_prev w hw
        right; simp only [base, Wire]; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact OrdinaryChainG.holesG WindowParams.first rfl StockWindowW7.leaves22.scratch k (by omega) (by omega) h24 d x good raw s g sg pg ps m pre _ (Or.inl rfl)
      · exact OrdinaryChainG.holesG WindowParams.first rfl StockWindowW7.leaves22.scratch k (by omega) (by omega) h24 d x good raw s g sg pg ps m pre _ (Or.inr (Or.inl rfl))
      · exact OrdinaryChainG.holesG WindowParams.first rfl StockWindowW7.leaves22.scratch k (by omega) (by omega) h24 d x good raw s g sg pg ps m pre _ (Or.inr (Or.inr (Or.inl rfl)))
      · exact OrdinaryChainG.holesG WindowParams.first rfl StockWindowW7.leaves22.scratch k (by omega) (by omega) h24 d x good raw s g sg pg ps m pre _ (Or.inr (Or.inr (Or.inr rfl)))

private theorem mixed_plain_eq :
    ((((((((((((([0, 1, 4, 7, 10, 13, 16, 19] ++ groups20 ⟨0, by decide⟩) ++
      groups20 ⟨1, by decide⟩) ++ groups20 ⟨2, by decide⟩) ++ groups20 ⟨3, by decide⟩) ++
      groups20 ⟨4, by decide⟩) ++ groups20 ⟨5, by decide⟩) ++ groups20 ⟨6, by decide⟩) ++
      groups20 ⟨7, by decide⟩) ++ groups20 ⟨8, by decide⟩) ++ [57, 58]) ++
      [(start ⟨21, by decide⟩ - 15 - 40) / 5]) ++ [(start ⟨22, by decide⟩ - 15 - 40) / 5]) ++
      [(start ⟨23, by decide⟩ - 15 - 40) / 5]) ++ [(start ⟨24, by decide⟩ - 15 - 40) / 5] ++ [73] =
      MixedGeo.plain := by
  decide +kernel

private theorem bankHoles_22_eq : bankHoles 22 = MixedGeo.holes := by decide +kernel

private theorem census_mixed (w : Wire) (hw : w ∈ bankMask 22) :
    w ∈ MixedGeo.holes ∨ OB5.sig 420 w ∈ MixedGeo.archives := by
  simp only [bankMask, List.take_of_length_le (by simp : (List.finRange 22).length ≤ 22),
    List.mem_flatMap, List.mem_finRange, true_and] at hw
  obtain ⟨b, hb⟩ := hw
  exact MixedGeo.cells_census b w hb

/-- End-to-end ordinary-chain agreement of `MixedWindow.forwardMixed d` with `common d raw` off `MixedGeo.archives`. -/
theorem wiresMixed (d : Bool) (x : Nat) (good : Bounds x p) (raw : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    ∀ q ∉ MixedGeo.archives,
      (run (MixedWindow.forwardMixed d) m (pullState (OB5.sig 44) raw)).basis q =
      (common d raw).basis q := by
  let ch1 := ([Shadow7.portalP 45, Shadow7.enterP MixedWindow.j0, Shadow7.routed MixedWindow.j0 0 1,
    MixedWindow.packW d 45 45, Shadow7.routed MixedWindow.j0 1 14, CRTBarrel.leave MixedWindow.j0]).flatten
  let ch2 := (MixedWindow.prefixPairs.flatMap fun p => MixedWindow.block15F d p.1 p.2).flatten
  let ch3 := ([Shadow7.enterP MixedWindow.j7, Shadow7.routed MixedWindow.j7 0 1, MixedWindow.packW d 150 140,
    Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, leave150To20Red]).flatten
  let ch5 := ([Shadow7.enterP MixedWindow.j20, Shadow7.routed MixedWindow.j20 0 1,
    MixedWindow.packW d 345 330, MixedWindow.packW d 345 335, archiveLoadP20 MixedWindow.k8 d,
    Shadow7.routed MixedWindow.j20 1 14, CRTBarrel.leave MixedWindow.j20]).flatten
  let ch7 := (exitF CRTBarrel.params d 420).flatten
  let p0 := ch1 ++ ch2
  let p1 := p0 ++ ch3
  let p2 := p1 ++ (MixedWindow.block20F d ⟨0, by decide⟩).flatten
  let p3 := p2 ++ (MixedWindow.block20F d ⟨1, by decide⟩).flatten
  let p4 := p3 ++ (MixedWindow.block20F d ⟨2, by decide⟩).flatten
  let p5 := p4 ++ (MixedWindow.block20F d ⟨3, by decide⟩).flatten
  let p6 := p5 ++ (MixedWindow.block20F d ⟨4, by decide⟩).flatten
  let p7 := p6 ++ (MixedWindow.block20F d ⟨5, by decide⟩).flatten
  let p8 := p7 ++ (MixedWindow.block20F d ⟨6, by decide⟩).flatten
  let p9 := p8 ++ (MixedWindow.block20F d ⟨7, by decide⟩).flatten
  let p10 := p9 ++ (MixedWindow.block20F d ⟨8, by decide⟩).flatten
  let p11 := p10 ++ ch5
  let p12 := p11 ++ (MixedWindow.block15F d ⟨20, by decide⟩ ⟨21, by decide⟩).flatten
  let p13 := p12 ++ (MixedWindow.block15F d ⟨21, by decide⟩ ⟨22, by decide⟩).flatten
  let p14 := p13 ++ (MixedWindow.block15F d ⟨22, by decide⟩ ⟨23, by decide⟩).flatten
  let p15 := p14 ++ (MixedWindow.block15F d ⟨23, by decide⟩ ⟨24, by decide⟩).flatten
  have hf : MixedWindow.forwardMixed d = p15 ++ ch7 := by
    have hfr : List.finRange 9 =
        [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
         ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩] := by decide
    simp only [MixedWindow.forwardMixed, MixedWindow.forwardL,
      p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, p0,
      ch1, ch2, ch3, ch5, ch7, hfr,
      MixedWindow.suffixPairs, exitF, CRTBarrel.params, Shadow7.params, ofParts, MixedWindow.tickW, MixedWindow.packW,
      List.flatMap_cons, List.flatMap_nil, List.flatten_cons, List.flatten_nil, List.flatten_append,
      List.append_nil, List.append_assoc]
  let init := pullState (OB5.sig 44) raw
  let g1 : List Nat := [0, 1, 4, 7, 10, 13, 16, 19]
  let g2 := g1 ++ groups20 ⟨0, by decide⟩
  let g3 := g2 ++ groups20 ⟨1, by decide⟩
  let g4 := g3 ++ groups20 ⟨2, by decide⟩
  let g5 := g4 ++ groups20 ⟨3, by decide⟩
  let g6 := g5 ++ groups20 ⟨4, by decide⟩
  let g7 := g6 ++ groups20 ⟨5, by decide⟩
  let g8 := g7 ++ groups20 ⟨6, by decide⟩
  let g9 := g8 ++ groups20 ⟨7, by decide⟩
  let g10 := g9 ++ groups20 ⟨8, by decide⟩
  let g11 := g10 ++ [57, 58]
  let g12 := g11 ++ [(start ⟨21, by decide⟩ - 15 - 40) / 5]
  let g13 := g12 ++ [(start ⟨22, by decide⟩ - 15 - 40) / 5]
  let g14 := g13 ++ [(start ⟨23, by decide⟩ - 15 - 40) / 5]
  let g15 := g14 ++ [(start ⟨24, by decide⟩ - 15 - 40) / 5]
  have o0 : Ord15 MixedWindow.j7 6 [0, 1, 4, 7, 10, 13, 16] d x raw (run p0 m init) :=
    ord_prefix d x good raw m stage
  have o1 : Ord20 ⟨0, by decide⟩ 7 g1 d x raw (run p1 m init) := by
    rw [show p1 = p0 ++ ch3 from rfl, run_append, run_take]; exact ord_150To20 d x good raw _ _ o0
  have o2 : Ord20 ⟨1, by decide⟩ 8 g2 d x raw (run p2 m init) := by
    rw [show p2 = p1 ++ (MixedWindow.block20F d ⟨0, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨0, by decide⟩ ⟨1, by decide⟩ rfl g1 d x good (by decide +kernel) raw _ _ o1
  have o3 : Ord20 ⟨2, by decide⟩ 9 g3 d x raw (run p3 m init) := by
    rw [show p3 = p2 ++ (MixedWindow.block20F d ⟨1, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨1, by decide⟩ ⟨2, by decide⟩ rfl g2 d x good (by decide +kernel) raw _ _ o2
  have o4 : Ord20 ⟨3, by decide⟩ 10 g4 d x raw (run p4 m init) := by
    rw [show p4 = p3 ++ (MixedWindow.block20F d ⟨2, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨2, by decide⟩ ⟨3, by decide⟩ rfl g3 d x good (by decide +kernel) raw _ _ o3
  have o5 : Ord20 ⟨4, by decide⟩ 11 g5 d x raw (run p5 m init) := by
    rw [show p5 = p4 ++ (MixedWindow.block20F d ⟨3, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨3, by decide⟩ ⟨4, by decide⟩ rfl g4 d x good (by decide +kernel) raw _ _ o4
  have o6 : Ord20 ⟨5, by decide⟩ 12 g6 d x raw (run p6 m init) := by
    rw [show p6 = p5 ++ (MixedWindow.block20F d ⟨4, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨4, by decide⟩ ⟨5, by decide⟩ rfl g5 d x good (by decide +kernel) raw _ _ o5
  have o7 : Ord20 ⟨6, by decide⟩ 13 g7 d x raw (run p7 m init) := by
    rw [show p7 = p6 ++ (MixedWindow.block20F d ⟨5, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨5, by decide⟩ ⟨6, by decide⟩ rfl g6 d x good (by decide +kernel) raw _ _ o6
  have o8 : Ord20 ⟨7, by decide⟩ 14 g8 d x raw (run p8 m init) := by
    rw [show p8 = p7 ++ (MixedWindow.block20F d ⟨6, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨6, by decide⟩ ⟨7, by decide⟩ rfl g7 d x good (by decide +kernel) raw _ _ o7
  have o9 : Ord20 ⟨8, by decide⟩ 15 g9 d x raw (run p9 m init) := by
    rw [show p9 = p8 ++ (MixedWindow.block20F d ⟨7, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_next ⟨7, by decide⟩ ⟨8, by decide⟩ rfl g8 d x good (by decide +kernel) raw _ _ o8
  have o10 : Ord345 16 g10 d x raw (run p10 m init) := by
    rw [show p10 = p9 ++ (MixedWindow.block20F d ⟨8, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_20_last g9 d x good (by decide +kernel) raw _ _ o9
  have o11 : Ord15 ⟨21, by decide⟩ 17 g11 d x raw (run p11 m init) := by
    rw [show p11 = p10 ++ ch5 from rfl, run_append, run_take]
    exact ord_345 g10 d x good (by decide +kernel) raw _ _ o10
  have o12 : Ord15 ⟨22, by decide⟩ 18 g12 d x raw (run p12 m init) := by
    rw [show p12 = p11 ++ (MixedWindow.block15F d ⟨20, by decide⟩ ⟨21, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_15_suffix_step ⟨20, by decide⟩ ⟨21, by decide⟩ ⟨22, by decide⟩ rfl rfl (by decide) (by decide) 17 rfl g11 d x good (by decide +kernel) raw _ _ o11
  have o13 : Ord15 ⟨23, by decide⟩ 19 g13 d x raw (run p13 m init) := by
    rw [show p13 = p12 ++ (MixedWindow.block15F d ⟨21, by decide⟩ ⟨22, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_15_suffix_step ⟨21, by decide⟩ ⟨22, by decide⟩ ⟨23, by decide⟩ rfl rfl (by decide) (by decide) 18 rfl g12 d x good (by decide +kernel) raw _ _ o12
  have o14 : Ord15 ⟨24, by decide⟩ 20 g14 d x raw (run p14 m init) := by
    rw [show p14 = p13 ++ (MixedWindow.block15F d ⟨22, by decide⟩ ⟨23, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_15_suffix_step ⟨22, by decide⟩ ⟨23, by decide⟩ ⟨24, by decide⟩ rfl rfl (by decide) (by decide) 19 rfl g13 d x good (by decide +kernel) raw _ _ o13
  have o15 : Ord15 ⟨25, by decide⟩ 21 g15 d x raw (run p15 m init) := by
    rw [show p15 = p14 ++ (MixedWindow.block15F d ⟨23, by decide⟩ ⟨24, by decide⟩).flatten from rfl, run_append, run_take]
    exact ord_15_suffix_step ⟨23, by decide⟩ ⟨24, by decide⟩ ⟨25, by decide⟩ rfl rfl (by decide) (by decide) 20 rfl g14 d x good (by decide +kernel) raw _ _ o14
  obtain ⟨rawF, gF, sgF, pgF, psF, preF, oldF, zerosF⟩ := o15
  let s15 := run p15 m init
  let m15 := m.drop (measurementCount p15)
  rw [hf, run_append, run_take]
  change ∀ q ∉ MixedGeo.archives, (run ch7 m15 s15).basis q = (common d raw).basis q
  obtain ⟨direct, lastHoles⟩ := OrdinaryChainG.exit420 d x good rawF s15 gF sgF pgF psF m15 preF
  have hend21 : ∀ b' : MixedGeo.Bank, b'.val < 21 → MixedGeo.endTick b' ≤ 405 := by decide +kernel
  have all : Except (bankMask 22) (pullState (OB5.sig 420) (run ch7 m15 s15))
      (run (ordinary d) [] (run (span 45 376) [] raw)) := by
    rw [bankMask_succ ⟨21, by decide⟩, show MixedGeo.endTick ⟨21, by decide⟩ = 420 by decide,
      ordinary, ← mixed_plain_eq, show (376 : Nat) = 420 + 1 - 45 from rfl]
    rw [show start ⟨25, by decide⟩ = 420 from rfl] at oldF
    refine extend_step d 420 1 (by decide) (by decide) (bankMask 21) (MixedGeo.cells10 (420 - 10)) _ [73]
      rawF raw _ oldF
      (by rw [groupProg_singleton, show (40 : Nat) + 5 * 73 = 420 - 15 from rfl]
          exact OrdinaryChainG.projectG 420 (by decide) rawF _ _ direct) ?_ ?_ ?_
    · intro q hq; obtain ⟨r, hr, e⟩ := bankMask_cells 21 405 hend21 q hq; exact ⟨r, by omega, e⟩
    · intro q hq; obtain ⟨r, hr, e⟩ := groupProg_cells d _ 405 (by decide +kernel) q hq; exact ⟨r, by omega, e⟩
    · intro q hq used
      rw [groupProg_singleton] at used
      obtain ⟨r, hr, e⟩ := bankMask_cells 21 405 hend21 q hq
      obtain ⟨r', r1, r2, e'⟩ := OrdinaryChainW.encode_cells d 405 q used
      rcases e with rfl | rfl <;> rcases e' with e' | e' <;> simp only [base, Wire] at e' <;> omega
  have zeroH : ∀ w ∈ MixedGeo.holes, (run ch7 m15 s15).basis (OB5.sig 420 w) = false := by
    rw [← bankHoles_22_eq, bankHoles_succ ⟨21, by decide⟩, show MixedGeo.endTick ⟨21, by decide⟩ = 420 by decide]
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨r, _, hr, rfl⟩ := bankHoles_cells 21 405 hend21 w h
      exact OrdinaryChainG.old_hole_G 420 (by decide) d rawF _ r (by omega) direct (zerosF _ h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact lastHoles (420 - 8) (Or.inl rfl)
      · exact lastHoles (420 - 6) (Or.inr (Or.inl rfl))
      · exact lastHoles (420 - 3) (Or.inr (Or.inr (Or.inl rfl)))
      · exact lastHoles (420 - 1) (Or.inr (Or.inr (Or.inr rfl)))
  intro q away
  have inv : OB5.sig 420 (OB5.sig 420 q) = q := OB5.sig_invol 420 (by decide) q
  generalize ey : OB5.sig 420 q = y at inv
  have goal : (common d raw).basis q =
      (eraseSites MixedGeo.holes (run (ordinary d) [] (run (span 45 376) [] raw))).basis y := by
    rw [← ey]; rfl
  rw [goal]
  by_cases hole : y ∈ MixedGeo.holes
  · simp only [eraseSites, if_pos hole]
    have z := zeroH y hole; rw [inv] at z; exact z
  · have free : y ∉ bankMask 22 := fun hit => by
      rcases census_mixed y hit with h | h
      · exact hole h
      · rw [inv] at h; exact away h
    have val := all y free
    change (run ch7 m15 s15).basis (OB5.sig 420 y) = _ at val
    rw [inv] at val
    simpa only [eraseSites, if_neg hole] using val

/-! ### Section 4: 22-Bank Stock Comparison API (`comparison`, `stored`, `Paired`, `binding`, `normalized`) -/

private theorem receipt_mixed (d : Bool) (x : Nat) (good : Bounds x p) (s : State) (dom : Domain 45 x p s)
    (i : Nat) (active : i ∈ MixedGeo.packed) (row : Nat) (lim : row < 63145)
    (truth : ArchiveStockRows.Chronology (MixedGeo.packet i) x p row) (j : Fin 10) :
    let raw := run (span 45 376) [] s
    (run (StockGroupsW.batch 45 d (StockGroupsW.all 25)) [] raw).basis (MixedGeo.slot i j) =
      (CodecBitSliceVerify.get (StairArchiveNativeRows.storage (StairArchiveNativeRows.native d (MixedGeo.high i))) j).testBit row := by
  have ⟨shape, lo', hi', _⟩ := MixedGeo.packed_chart active
  let raw := run (span 45 376) [] s
  have obs := StockArchiveTruthW.native_byte 45 376 x p (by decide) good s dom (MixedGeo.packet i) lo' (by omega)
    row lim truth d (MixedGeo.high i) []
  have bit := obs.2 j
  have hlt : i < 76 := MixedGeo.packed_lt active
  have hslot : MixedGeo.slot i j = StockWindowGeo.slot 45 i j := rfl
  dsimp only
  rw [hslot, StockGroupsW.isolated 45 (by decide) d (StockGroupsW.all 25) (StockGroupsW.allNodup 25)
    (StockGroupsW.small_all 45 25 (by decide) (by decide)) raw i (StockGroupsW.inAll hlt) _
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)]
  change (run (Rolling1588.codeEncodeAt d (History5.historyMap base (MixedGeo.gstart i))) [] raw).basis
    (History5.historyMap base (MixedGeo.gstart i) j) = _
  rw [shape]
  exact bit

theorem comparison (d : Bool) (x : Nat) (good : Bounds x p) (s a : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 45 s.basis)
    (results : mixedFinal StockWindowChainP.ExitPorts420 d x p a) :
    MixedArchiveSuffix.Same
      (run (Rolling1588TickGap.forward d 45 376) m (pullState (OB5.sig 44) s))
      (common d s) := by
  let raw := run (span 45 376) [] s
  have stock := StockDelayed.window d x good.nonzero good.small 45 376 (by decide) (by decide) s m stage
  change run (Rolling1588TickGap.forward d 45 376) m (pullState (OB5.sig 44) s) =
    pullState (OB5.sig 420) (run (StockDelayed.packs d 45 376) [] raw) at stock
  rw [stock, StockGroupsW.packs_bridge, StockGroupsW.stockEq d 45 25 (by decide) (by decide), common, ordinary]
  have hsmall_plain : ∀ i ∈ MixedGeo.plain, StockWindowGeo.gstart 45 i + 5 ≤ 512 := fun i hi => by
    have := MixedGeo.plain_lt hi; simp only [StockWindowGeo.gstart]; omega
  refine ⟨(StockBaselineW.phase_batch 45 d (StockGroupsW.all 25)
      (StockBaselineW.small512 45 25 (by decide) (by decide) _ (fun i hi => List.mem_range.mp hi)) raw).trans
      (StockBaselineW.phase_batch 45 d MixedGeo.plain hsmall_plain raw).symm, ?_⟩
  intro q safe
  let y := OB5.sig 420 q
  change (run (StockGroupsW.batch 45 d (StockGroupsW.all 25)) [] raw).basis y =
    (if y ∈ MixedGeo.holes then false else (run (StockGroupsW.batch 45 d MixedGeo.plain) [] raw).basis y)
  have away : OB5.sig 420 y ∉ MixedGeo.archives := by simpa only [y, OB5.sig_invol 420 (by decide)] using safe
  by_cases old : ∃ i ∈ MixedGeo.packed, y ∈ StockGroupsW.ports 45 i
  · obtain ⟨i, used, inside⟩ := old
    obtain ⟨j, _, atSite⟩ := Finset.mem_image.mp inside
    rcases MixedGeo.sparse i used j with ⟨blank, hit⟩ | covered
    · have hslot : StockWindowGeo.slot 45 i j = MixedGeo.slot i j := rfl
      rw [← atSite, hslot, if_pos hit]
      obtain ⟨_, _, _, b, hb⟩ := MixedGeo.packed_chart used
      have dom := WideReference.initial 45 x p (by decide) d s stage
      have bit := receipt_mixed d x good s dom i used (mixedRow x p b) (results b).1
        (by rw [hb]; exact mixedFinal_trace results b) j
      have cleared (k : Nat) (ok : k = 5 ∨ k = 9) :
          CodecBitSliceVerify.get (StairArchiveNativeRows.storage (StairArchiveNativeRows.native d (MixedGeo.high i))) k = 0 := by
        rcases ok with rfl | rfl <;> rfl
      exact bit.trans ((congrArg (fun n : Nat => n.testBit _) (cleared j (by rcases blank with rfl | rfl <;> decide))).trans
        (Nat.zero_testBit _))
    · exact (away (atSite ▸ covered)).elim
  · have nh : y ∉ MixedGeo.holes := fun h => by
      obtain ⟨i, used, j, e⟩ := MixedGeo.hole_slot y h
      exact old ⟨i, used, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, e.symm⟩⟩
    rw [if_neg nh]
    have hsp_plain : ∀ i ∈ MixedGeo.plain, StockWindowGeo.gstart 45 i + 5 ≤ 1028 := fun i hi => by
      have := MixedGeo.plain_lt hi; simp only [StockWindowGeo.gstart]; omega
    by_cases saved : ∃ i ∈ MixedGeo.plain, y ∈ StockGroupsW.ports 45 i
    · obtain ⟨i, mem, h⟩ := saved
      exact (StockGroupsW.isolated 45 (by decide) d (StockGroupsW.all 25) (StockGroupsW.allNodup 25)
          (StockGroupsW.small_all 45 25 (by decide) (by decide)) raw i (StockGroupsW.inAll (MixedGeo.plain_lt mem)) y h).trans
        (StockGroupsW.isolated 45 (by decide) d MixedGeo.plain MixedGeo.plain_nodup hsp_plain raw i mem y h).symm
    · have off (i : Nat) (hi : i < 76) : y ∉ StockGroupsW.ports 45 i := fun h => by
        rcases MixedGeo.split_all i hi with m' | m'
        · exact saved ⟨i, m', h⟩
        · exact old ⟨i, m', h⟩
      exact (StockGroupsW.outside 45 d (StockGroupsW.all 25) raw y (fun i hi => off i (List.mem_range.mp hi))).trans
        (StockGroupsW.outside 45 d MixedGeo.plain raw y (fun i hi => off i (MixedGeo.plain_lt hi))).symm

theorem stored (d : Bool) (x : Nat) (good : Bounds x p) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 45 s.basis) (b : MixedGeo.Bank) (row : Nat)
    (lim : row < 63145) (truth : ArchiveStockRows.Chronology (MixedGeo.bankTick b) x p row) :
    StockArchiveBanksW.nativeAt (MixedGeo.siteAt StockWindowChainP.ExitPorts420 b) d row
      (run (Rolling1588TickGap.forward d 45 376) m (pullState (OB5.sig 44) s)) := by
  let ports := MixedGeo.siteAt StockWindowChainP.ExitPorts420 b
  let z := run (StockGroupsW.batch 45 d (StockGroupsW.all 25)) [] (run (span 45 376) [] s)
  have stock :
      run (Rolling1588TickGap.forward d 45 376) m (pullState (OB5.sig 44) s) =
        pullState (OB5.sig 420) z :=
    StockArchiveBanksW.stock_state 45 25 (by decide) (by decide) (by decide) d x good s m stage
  have saved : StockArchiveBanksW.nativeAt ports d row (pullState (OB5.sig 420) z) := by
    intro j
    obtain ⟨addr, clock, used, hj⟩ := MixedGeo.chart b j
    let i := MixedGeo.groupOf b j
    let k := MixedGeo.index j
    have chronology : ArchiveStockRows.Chronology (MixedGeo.packet i) x p row :=
      (congrArg (fun t : Nat => ArchiveStockRows.Chronology t x p row) clock).mpr truth
    have dom := WideReference.initial 45 x p (by decide) d s stage
    have bit := receipt_mixed d x good s dom i used row lim chronology k
    have hbyte : CodecBitSliceVerify.get
        (StairArchiveNativeRows.storage (StairArchiveNativeRows.native d (MixedGeo.high i))) k =
          CodecBitSliceVerify.get (StairArchiveNativeCut.canonical d d) j :=
      (congrArg (fun h : Bool =>
        CodecBitSliceVerify.get (StairArchiveNativeRows.storage (StairArchiveNativeRows.native d h)) k) hj).trans
        (StockArchiveBanksW.byte d j)
    have haddr : ports j = OB5.sig 420 (MixedGeo.slot i k) :=
      (MixedGeo.site_eq StockWindowChainP.ExitPorts420 StockArchiveBanks.exitCells b j).trans addr
    exact (StockArchiveBanksW.readback 420 (by decide) z _ _ haddr).trans
      (bit.trans (congrArg (fun n : Nat => n.testBit row) hbyte))
  exact (congrArg (StockArchiveBanksW.nativeAt ports d row) stock).mpr saved

theorem common_phase (d : Bool) (x : Nat) (good : Bounds x p) (s : State)
    (stage : Rolling1588.Integer.Stage base d x p 45 s.basis) :
    (common d s).phase = s.phase := by
  have final := (MixedChain.strong d x good s [] stage).2.1
  have same := comparison d x good s _ [] stage final
  exact same.1.symm.trans (StockBaseline.forward_phase d x good 45 376 (by decide) (by decide) s [] stage)

theorem normalized (d : Bool) (x : Nat) (good : Bounds x p) (raw : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    MixedArchiveSuffix.Same
      (run (MixedWindow.forwardMixed d) m (pullState (OB5.sig 44) raw))
      (common d raw) :=
  ⟨(MixedChain.strong d x good raw m stage).1.trans (common_phase d x good raw stage).symm,
    wiresMixed d x good raw m stage⟩

end ECDSAAdd.Entrant.StairPacket.Shadow20.MixedOrd
end
-- ==== end Shadow7Wide20Ord ====

section
namespace ECDSAAdd.Entrant.StairPacket.StockStrongChain
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 StockCanonicalRow StockWindowW7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount key select WideReference.canonical

theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    let start0:=pullState (OB5.sig 44) raw
    let out:=run (Shadow20.MergeCut.forward d) m start0
    out.phase=raw.phase ∧ Shadow20.MixedChain.mixedFinal StockWindowChainP.ExitPorts420 d x p out ∧
      ∀n,run (Shadow20.MergeCut.reverse d) n out=start0 := by
  have h := Shadow20.MixedChain.strong d x good raw m stage
  rw [← (Shadow20.MergeCut.run_eq d).1, ← Shadow20.MergeCut.reverse_run_eq d] at h
  exact h

end ECDSAAdd.Entrant.StairPacket.StockStrongChain
end

section
namespace ECDSAAdd.Entrant.StairPacket.StockArchiveReference
open Arithmetic MappedCompressed WideReference
def common (d:Bool) (raw:State):State:=Shadow20.MixedOrd.common d raw
end ECDSAAdd.Entrant.StairPacket.StockArchiveReference

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanks
open Arithmetic MappedCompressed Secp256k1 WideReference ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run span
abbrev Bank := Shadow20.MixedGeo.Bank
def ports (b:Bank):Ports:=Shadow20.MixedGeo.bankPorts StockWindowChainP.ExitPorts420 b
def siteAt (b:Bank) (j:Fin 16):Wire:=ports b ⟨j.val,by omega⟩
def tick (b:Bank):Nat:=Shadow20.MixedGeo.bankTick b
def archives:List Wire:=Shadow20.MixedGeo.archives
def Same (a b:State):Prop:=Shadow20.MixedArchiveSuffix.Same a b
def nativeAt (d:Bool) (b:Bank) (r:Nat) (s:State):Prop:=StockArchiveBanksW.nativeAt (siteAt b) d r s

theorem site_eq (b:Bank) (j:Fin 16) : siteAt b j=Shadow20.MixedGeo.bankSite b j :=
  Shadow20.MixedGeo.site_eq StockWindowChainP.ExitPorts420 exitCells b j
theorem mem (b:Bank) (j:Fin 16) : siteAt b j∈archives := by
  rw [site_eq]; exact Shadow20.MixedGeo.bank_mem b j
theorem bank_rep (q:Wire) (h:q∈archives) : ∃(b:Bank)(j:Fin 16),siteAt b j=q :=
  Shadow20.MixedGeo.bank_rep StockWindowChainP.ExitPorts420 exitCells q h

structure Paired (d:Bool) (x:Nat) (a s:State) (rows:Bank→Nat):Prop where
  equality:Same a s
  labels:∀b,rows b<63145 ∧ ArchiveStockRows.Chronology (tick b) x p (rows b)
  custom:∀b,Kept (ports b) d (rows b) a
  stock:∀b,nativeAt d b (rows b) s

theorem Paired.through {d x a s rows} (pair:Paired d x a s rows) (P:Program)
    (off:∀q∈archives,q∉wires P) (m:List Bool):Paired d x (run P m a) (run P m s) rows:=by
  have h:=Shadow20.MixedArchiveSuffix.independent P off m a s pair.equality
  refine ⟨h.1,pair.labels,?_,?_⟩
  · intro b j
    exact (h.2 (siteAt b j) (mem b j)).trans (pair.custom b j)
  · intro b j
    exact (run_preserves_outside P m s (siteAt b j) (off _ (mem b j))).trans (pair.stock b j)

theorem safe (d:Bool) (i n:Nat) (lo:421 ≤ i) (hi:i+n ≤ 512) (q:Wire) (mem:q∈archives) :
    q∉wires (Rolling1588TickGap.forward d i n) ∧ q∉wires (Rolling1588.reverse d i n) :=
  Shadow20.MixedArchiveSuffix.safe d i n lo hi q mem
end ECDSAAdd.Entrant.StairPacket.StockArchiveBanks

namespace ECDSAAdd.Entrant.StairPacket.StockRowVector
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks
noncomputable def rows (x p:Nat) (b:Bank):Nat:=Shadow20.MixedChain.mixedRow x p b
theorem binding (d:Bool) (x:Nat) (good:Bounds x p) (raw a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis)
    (stored:Shadow20.MixedChain.mixedFinal StockWindowChainP.ExitPorts420 d x p a)
    (same:Same a (run (Rolling1588TickGap.forward d 45 376) m (pullState (OB5.sig 44) raw))) :
    Paired d x a (run (Rolling1588TickGap.forward d 45 376) m (pullState (OB5.sig 44) raw)) (rows x p) := by
  refine ⟨same, fun b => ⟨(stored b).1, Shadow20.MixedChain.mixedFinal_trace stored b⟩,
    fun b => (stored b).2.2, fun b => ?_⟩
  exact Shadow20.MixedOrd.stored d x good raw m stage b (rows x p b) (stored b).1 (Shadow20.MixedChain.mixedFinal_trace stored b)
end ECDSAAdd.Entrant.StairPacket.StockRowVector

namespace ECDSAAdd.Entrant.StairPacket.StockBaseline
open Arithmetic MappedCompressed WideReference Secp256k1 StockArchiveBanks
theorem comparison (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 s.basis)
    (results:Shadow20.MixedChain.mixedFinal StockWindowChainP.ExitPorts420 d x p a) :
    Same (run (Rolling1588TickGap.forward d 45 376) m (pullState (OB5.sig 44) s)) (StockArchiveReference.common d s) :=
  Shadow20.MixedOrd.comparison d x good s a m stage results
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

/-- Instantiate the three real windows from an odd-word cut endpoint `OCut`. -/
theorem ocaller (d : Bool) (x : Nat) (rows : Nat→Nat) (rb : ∀j∈bankIds,rows j<63145)
    (history : ∀j∈bankIds,ArchiveStockRows.Chronology (5*j-5) x ECDSAAdd.p (rows j))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (en : origin (base 2400)=true) (tr : TraceOK x origin)
    (actual ref : State) (m : List Bool)
    (initial : Fits rows (initialCode d) actual (pullIn ref))
    (start : OCut (if d then 1 else 85) origin (pullIn ref))
    (htag : TagReady (pullIn ref)) :
    Fits rows (finalCode d (plan d) (initialCode d)) (run (group84 d) m actual)
      (run (PacketSequence.program d (opk d) 1 84) (oreferenceTape1542 d m) (pullIn ref)) :=
  othree_run d x rows rb origin ctx en tr history m actual (pullIn ref) initial start htag
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
  · simp only [out, pullState]
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

def test (q : Wire) := fast (first q)==integerFirst (fast q) &&
  fast (rawX q)==duringX (fast q) && fast (rawOut q)==outer (fast q)

private def nearOutput (y : Nat) : Prop :=
  (4615 ≤ y ∧ y ≤ 4619) ∨ (4835 ≤ y ∧ y ≤ 4839) ∨ y = 4629

private def nearIndex (i : Nat) : Prop :=
  (500 ≤ i ∧ i ≤ 504) ∨ (720 ≤ i ∧ i ≤ 724) ∨ i = 514

private theorem outsideMeta (j : Nat) : ¬ nearOutput (metaN j) := by
  unfold nearOutput
  rcases Nat.lt_or_ge j 12 with hj | hj
  · have h : ∀ k : Fin 12, ¬ ((4615 ≤ metaN k.val ∧ metaN k.val ≤ 4619) ∨
        (4835 ≤ metaN k.val ∧ metaN k.val ≤ 4839) ∨ metaN k.val = 4629) := by decide +kernel
    exact h ⟨j, hj⟩
  · have h0 : metaN j = 0 := by
      simp only [metaN, show j ≠ 0 by omega, show j ≠ 1 by omega, show j ≠ 2 by omega,
        show j ≠ 3 by omega, show j ≠ 4 by omega, show j ≠ 5 by omega, show j ≠ 6 by omega,
        show j ≠ 7 by omega, show j ≠ 8 by omega, show j ≠ 9 by omega, show j ≠ 10 by omega,
        show j ≠ 11 by omega, ↓reduceIte]
    rw [h0]; omega

private theorem nearIndex_of_output (i : Nat) (h : nearOutput (pwN i)) : nearIndex i := by
  unfold pwN at h
  split_ifs at h <;> first
    | exact (outsideMeta _ h).elim
    | (unfold nearOutput at h; unfold nearIndex; omega)

private def testInputs : List Wire := [1558,1042,1557,739,740,516,517,518,519,520,530,737,738,736,785,1813]

private theorem outside_input (q : Nat) (outside : q ∉ testInputs) : ¬ nearOutput (fast q) := by
  intro hit
  rw [fast,pwB_eq] at hit
  have index := nearIndex_of_output _ hit
  simp only [testInputs,List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  obtain ⟨a,b,c,d,e,f,g,i,j,k,l,u,v,w,x,y⟩ := outside
  simp only [phaseHostB,swB_eq,sw,a,b,c,u,v,w,x,y,ite_false] at index
  unfold nearIndex at index
  omega

private theorem fixed_input (q : Wire) (h : q ∉ changeList) :
    first q=q ∧ rawX q=q ∧ rawOut q=q := by
  simp only [changeList,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  obtain ⟨a,b,c,d,e,f,g,i,j,k,l⟩ := h
  simp [rawX,rawOut,first,shared,chain,Equiv.swap_apply_def,a,b,c,d,e,f,g,i,j,k,l]

private theorem fixed_output (q : Wire) (h : ¬ nearOutput q) :
    integerFirst q=q ∧ duringX q=q ∧ outer q=q := by
  have off : q ∉ Stair44PointMap.changed := by
    intro used
    apply h
    simp only [Stair44PointMap.changed,List.mem_cons,List.not_mem_nil,or_false] at used
    unfold nearOutput
    rcases used with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [Stair44PointMap.changed,List.mem_cons,List.not_mem_nil,or_false,not_or] at off
  obtain ⟨a,b,c,d,e,f,g,i,j,k,l⟩ := off
  simp [integerFirst,duringX,outer,earlyPairs,chain,Equiv.swap_apply_def,a,b,c,d,e,f,g,i,j,k,l]

private theorem checkedInputs : ∀ q ∈ testInputs, test q = true := by decide +kernel

theorem maps (q : Wire) : phys (first q)=integerFirst (phys q) ∧
    phys (rawX q)=duringX (phys q) ∧ phys (rawOut q)=outer (phys q) := by
  simp only [phys_fast]
  by_cases h : q ∈ testInputs
  · simpa only [test,Bool.and_eq_true,beq_iff_eq,and_assoc] using checkedInputs q h
  · have subset : ∀ w ∈ changeList, w ∈ testInputs := by decide
    have a := fixed_input q (fun use => h (subset _ use))
    have b := fixed_output _ (outside_input q h)
    rw [a.1,a.2.1,a.2.2,b.1,b.2.1,b.2.2]
    exact ⟨rfl,rfl,rfl⟩

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
private theorem hook (j:Nat) (hj:j∈[10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (op:Stage):GoodP (fieldHook j op):=by
  have span:j∈List.range' 1 83:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;apply List.mem_range'_1.mpr;omega
  have chk:(fieldSites j).all (fun q=>decide (16 ≤ q ∧ q < 2330))=true:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  intro q hit
  rw [fieldHook,renameProgram_support] at hit
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hit
  have len:(fieldSites j).length=121:=by have hh:=(layout_frame j span).2;rwa [←field_layout,List.length_map] at hh
  have lt:w < (fieldSites j).length:=len ▸ (Finset.mem_range.mp (sub op hw))
  have pos:=of_decide_eq_true (List.all_eq_true.mp chk ((fieldSites j)[w]) (List.getElem_mem lt))
  have toCaller (v:Nat) (h:16≤v ∧ v<2330):v∈callerDomain:=by
    have baseEq:base (v-16)=v:=by simp only [base,Wire];omega
    rw [←baseEq]
    exact base_mem_caller _ (Or.inl (by omega))
  have yes:=toCaller _ pos
  simpa only [fieldPort,List.getElem?_eq_getElem lt,Option.getD_some] using yes
private theorem pair (d:Bool) (j:Nat) (hj:j∈[10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (hi:j≤83):GoodP (ten j (!d)):=by
  have here:=singleton d j (by omega)
  have next:=singleton d (j+1) (by omega)
  have a:GoodP (first j (!d)):=by cases d <;> first | exact here | exact next
  have b:GoodP (second j (!d)):=by cases d <;> first | exact here | exact next
  exact app (hook j hj _) (app a (app (hook j hj _) (app b (hook j hj _))))
-- oddten:begin GOOD
private theorem callerDomain_of_range {q : Wire} (hlo : 16 ≤ q) (hhi : q < 2330) : q ∈ callerDomain := by
  dsimp only [Wire] at hlo hhi
  rw [StairSemanticFinal.callerDomain, List.mem_toFinset, List.mem_map]
  refine ⟨q - 16, ?_, by unfold MappedCompressed.base; dsimp only [Wire]; omega⟩
  rw [StairSemanticFinal.callerIndices, List.mem_append, List.mem_range'_1]
  exact Or.inl ⟨by omega, by omega⟩

private theorem tagSites_range : tagSites.all (fun q => decide (16 ≤ q ∧ q < 2330)) = true := by
  decide +kernel

private theorem packTag_good : GoodP packTag := by
  intro q hq
  rw [packTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.packTagProg_wires_lt x hx
  have hmem : tagPort x ∈ tagSites := by
    simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  have hr := of_decide_eq_true (List.all_eq_true.mp tagSites_range _ hmem)
  exact callerDomain_of_range hr.1 hr.2

private theorem unpackTag_good : GoodP unpackTag := by
  intro q hq
  rw [unpackTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.unpackTagProg_wires_lt x hx
  have hmem : tagPort x ∈ tagSites := by
    simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  have hr := of_decide_eq_true (List.all_eq_true.mp tagSites_range _ hmem)
  exact callerDomain_of_range hr.1 hr.2

private theorem tagSwap_caller (q : Wire) (hq : q ∈ callerDomain) : tagSwap q ∈ callerDomain := by
  by_cases h1 : q = base 720
  · subst h1; rw [show tagSwap (base 720) = StairPhysicalLayout.sLetter 435 from Equiv.swap_apply_left _ _]
    have hr : 16 ≤ StairPhysicalLayout.sLetter 435 ∧ StairPhysicalLayout.sLetter 435 < 2330 := by decide +kernel
    exact callerDomain_of_range hr.1 hr.2
  · by_cases h2 : q = StairPhysicalLayout.sLetter 435
    · subst h2; rw [show tagSwap (StairPhysicalLayout.sLetter 435) = base 720 from Equiv.swap_apply_right _ _]
      exact callerDomain_of_range (by decide) (by decide)
    · rwa [tagSwap, Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem group84Body_good (d:Bool):GoodP (group84Body d):=by
  have ord {a b:Program} (x:GoodP a) (y:GoodP b):GoodP (ordered d a b):=by cases d <;> first | exact app x y | exact app y x
  have og (j n:Nat) (hi:j+n≤102):GoodP (rgroup d j n):= by
    intro q hq
    rcases Finset.mem_insert.mp (WindowFieldCosts.rgroup_sub d j n hq) with e|h
    · subst e; exact callerDomain_of_range (by decide) (by decide)
    · exact Finset.Subset.trans (WindowFieldCosts.ot_ogroup_sub d j n) (ordinary d j n hi) h
  have ot (j:Nat) (hj:j∈[10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (hi:j≤83):GoodP (oten j (!d)):=
    Finset.Subset.trans (WindowFieldCosts.ot_oten_sub j (!d)) (pair d j hj hi)
  have c43 := ord (ot 82 (by decide) (by decide)) (og 84 1 (by decide))
  have c42 := ord (og 81 1 (by decide)) c43
  have c41 := ord (ot 79 (by decide) (by decide)) c42
  have c40 := ord (og 78 1 (by decide)) c41
  have c39 := ord (ot 76 (by decide) (by decide)) c40
  have c38 := ord (og 75 1 (by decide)) c39
  have c37 := ord (ot 73 (by decide) (by decide)) c38
  have c36 := ord (og 72 1 (by decide)) c37
  have c35 := ord (ot 70 (by decide) (by decide)) c36
  have c34 := ord (og 69 1 (by decide)) c35
  have c33 := ord (ot 67 (by decide) (by decide)) c34
  have c32 := ord (og 65 2 (by decide)) c33
  have c31 := ord (ot 63 (by decide) (by decide)) c32
  have c30 := ord (og 61 2 (by decide)) c31
  have c29 := ord (ot 59 (by decide) (by decide)) c30
  have c28 := ord (og 57 2 (by decide)) c29
  have c27 := ord (ot 55 (by decide) (by decide)) c28
  have c26 := ord (og 53 2 (by decide)) c27
  have c25 := ord (ot 51 (by decide) (by decide)) c26
  have c24 := ord (og 49 2 (by decide)) c25
  have c23 := ord (ot 47 (by decide) (by decide)) c24
  have c22 := ord (og 45 2 (by decide)) c23
  have c21 := ord (ot 43 (by decide) (by decide)) c22
  have c20 := ord (og 41 2 (by decide)) c21
  have c19 := ord (ot 39 (by decide) (by decide)) c20
  have c18 := ord (og 37 2 (by decide)) c19
  have c17 := ord (ot 35 (by decide) (by decide)) c18
  have c16 := ord (og 33 2 (by decide)) c17
  have c15 := ord (ot 31 (by decide) (by decide)) c16
  have c14 := ord (og 30 1 (by decide)) c15
  have c13 := ord (ot 28 (by decide) (by decide)) c14
  have c12 := ord (og 27 1 (by decide)) c13
  have c11 := ord (ot 25 (by decide) (by decide)) c12
  have c10 := ord (og 24 1 (by decide)) c11
  have c9 := ord (ot 22 (by decide) (by decide)) c10
  have c8 := ord (og 21 1 (by decide)) c9
  have c7 := ord (ot 19 (by decide) (by decide)) c8
  have c6 := ord (og 18 1 (by decide)) c7
  have c5 := ord (ot 16 (by decide) (by decide)) c6
  have c4 := ord (og 15 1 (by decide)) c5
  have c3 := ord (ot 13 (by decide) (by decide)) c4
  have c2 := ord (og 12 1 (by decide)) c3
  exact ord (ot 10 (by decide) (by decide)) c2

theorem group84_good (d:Bool):GoodP (group84 d):=by
  have ord {a b:Program} (x:GoodP a) (y:GoodP b):GoodP (ordered d a b):=by cases d <;> first | exact app x y | exact app y x
  have og19 : GoodP (ogroup d 1 9) :=
    Finset.Subset.trans (WindowFieldCosts.ot_ogroup_sub d 1 9) (ordinary d 1 9 (by decide))
  have hbody : GoodP (renameProgram tagSwap (group84Body d)) := by
    intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    exact tagSwap_caller v (group84Body_good d hv)
  exact ord og19 (app (app packTag_good hbody) unpackTag_good)
-- oddten:end GOOD

theorem entryTailPrefix_ours :
    wires (WindowCallerCosts.entryTailPrefix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  have oddDom (d f c : Nat) (hd : d ≤ 44) (hfc : f + c ≤ 102) :
      wires (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true d f c) ⊆ callerDomain :=
    OddFullPass.P1LifeLoan.hostedGroup_wires_sub_1542 true d f c hd hfc
  unfold WindowCallerCosts.entryTailPrefix
  simp only [wires_append, Finset.union_subset_iff, and_assoc]
  exact ⟨group84_good true,
    fseg_caller 87 62 (by decide) (by decide) (by decide) (by decide),
    oddDom 14 85 5 (by decide) (by decide),
    fseg_caller 62 47 (by decide) (by decide) (by decide) (by decide),
    oddDom 23 90 3 (by decide) (by decide),
    fseg_caller 47 32 (by decide) (by decide) (by decide) (by decide),
    oddDom 31 93 3 (by decide) (by decide),
    fseg_caller 32 22 (by decide) (by decide) (by decide) (by decide),
    oddDom 37 96 2 (by decide) (by decide),
    fseg_caller 22 12 (by decide) (by decide) (by decide) (by decide),
    oddDom 42 98 2 (by decide) (by decide),
    forwardLastV3_caller⟩

theorem exitHeadSuffix_ours :
    wires (WindowCallerCosts.exitHeadSuffix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  have oddDom (d f c : Nat) (hd : d ≤ 44) (hfc : f + c ≤ 102) :
      wires (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false d f c) ⊆ callerDomain :=
    OddFullPass.P1LifeLoan.hostedGroup_wires_sub_1542 false d f c hd hfc
  have cutDom (B N s f d first c : Nat)
      (hw : wires (PackCutOddExit.cutRowOddPk B N s f d first c) ⊆
        wires (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false d first (c + 1)) ∪
        wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives B N s f))
      (h1 : wires (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false d first (c + 1)) ⊆ callerDomain)
      (h2 : wires (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives B N s f) ⊆ callerDomain) :
      wires (PackCutOddExit.cutRowOddPk B N s f d first c) ⊆ callerDomain :=
    hw.trans (Finset.union_subset h1 h2)
  unfold WindowCallerCosts.exitHeadSuffix
  simp only [wires_append, Finset.union_subset_iff, and_assoc]
  exact ⟨reverseLastV3_caller,
    cutDom 22 12 490 500 42 98 1 PackCutOddExit.cutRow4_wires (oddDom 42 98 2 (by decide) (by decide))
      (rseg_caller 22 12 (by decide) (by decide) (by decide) (by decide) (by decide)),
    cutDom 32 22 480 490 37 96 1 PackCutOddExit.cutRow3_wires (oddDom 37 96 2 (by decide) (by decide))
      (rseg_caller 32 22 (by decide) (by decide) (by decide) (by decide) (by decide)),
    cutDom 47 32 465 480 31 93 2 PackCutOddExit.cutRow2_wires (oddDom 31 93 3 (by decide) (by decide))
      (rseg_caller 47 32 (by decide) (by decide) (by decide) (by decide) (by decide)),
    cutDom 62 47 450 465 23 90 2 PackCutOddExit.cutRow1_wires (oddDom 23 90 3 (by decide) (by decide))
      (rseg_caller 62 47 (by decide) (by decide) (by decide) (by decide) (by decide)),
    cutDom 87 62 425 450 14 85 4 PackCutOddExit.cutRow0_wires (oddDom 14 85 5 (by decide) (by decide))
      (rseg_caller 87 62 (by decide) (by decide) (by decide) (by decide) (by decide)),
    group84_good false⟩

private theorem hostedFirstPacketOdd_caller (divide : Bool) :
    wires (StairLoan.rebindMany StairSchedule.exclusiveRoles
      (StairConcreteAssembly.hostPlan.firstPacket divide)
      (JointOdd1588.placedFirstPacketOdd WindowCallerCosts.oddFirstHalf divide)) ⊆ callerDomain := by
  refine rebindMany_caller _ _ _ exclusive_caller (hostPlan_firstPacket_caller divide) ?_
  intro q hq
  have hsup := StairWireCheck.allSites_sound StairWireCheck.fpSup _
    (JointOdd1588.placedFirstPacketOdd_passSup WindowCallerCosts.oddFirstHalf divide
      (WindowCallerCosts.oddFirstHalf_support divide)) q hq
  rcases WindowCallerCosts.fpSup_bounds q hsup with ⟨hlo, hhi⟩ | rfl
  · have heq : base (q - 16) = q := Nat.sub_add_cancel hlo
    rw [← heq]
    exact base_mem_caller _ (Or.inl (Nat.sub_lt_left_of_lt_add hlo hhi))
  · exact base_mem_caller 2409 (Or.inr (Or.inr (Or.inl rfl)))

theorem entryLowPrefix_ours :
    wires (WindowCallerCosts.entryLowPrefix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.entryLowPrefix
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (hostedFirstPacketOdd_caller true) glue_own.2.2.1)
    (borrow_caller _ entryTailPrefix_ours)) glue_own.2.2.2

theorem exitLowSuffix_ours :
    wires (WindowCallerCosts.exitLowSuffix StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  unfold WindowCallerCosts.exitLowSuffix
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _ glue_own.2.2.1
    (borrow_caller _ exitHeadSuffix_ours)) glue_own.2.2.2)
    (hostedFirstPacketOdd_caller false)

end ECDSAAdd.Entrant.StairPacket.ExteriorCaller

end


section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelPrograms
open Arithmetic MappedCompressed Baselines Stair44Placement Stair44PointMap Stair44WalkMap Stair44Kernel
open Stair44Outer Rolling1588Lifetime Secp256k1 StairConcreteAssembly StairSemanticFinal
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

def openWalk (d:Bool) (tail:Nat):Program:=Stair44Kernel.firstR++WindowWalkCosts.forward d tail
def divBefore:Program:=renameProgram phaseHost (openWalk true 4++checkpointPrimitives.firstPack)++WindowParityCaller.entryFieldHostedCut
def divAfter:Program:=Stair44Outer.reverseEnd++(WindowWalkCosts.backward false 85++renameProgram first (FrontierEntry1591NativeH.inverse base))
def division:Program:=divBefore++renameProgram phaseHost divAfter
def mulBefore:Program:=(renameProgram phaseHost (openWalk false 84++Stair44Outer.forwardEnd)++WindowParityCaller.exitFieldHosted checkpointPrimitives)++renameProgram phaseHost checkpointPrimitives.firstUnpack
def mulAfter (k:Nat):Program:=WindowWalkCosts.backward true 4++renameProgram rawX (ParityXExitInverse23Kernel.x1N k)
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
  enter:OddOuterBridge.EntryCorrectOdd division
  exit:∀k, k < p → OddOuterBridge.ExitMatchesOdd (renameProgram outMap.symm (multiplication k)) k
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

end ECDSAAdd.Entrant.Stair44PointSecond

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorCaller
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairSemanticFinal
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
attribute [local irreducible] wires renameProgram
private theorem localSite {q:Nat} (h:16 ≤ q ∧ q < 2330):q∈callerDomain:=by
  have e:base (q-16)=q:=by simp only [base,Wire];omega
  exact e ▸ base_mem_caller _ (Or.inl (by omega))
private theorem setup:GoodP WindowFieldParity.setup:=by
  apply wires_sub_of_parts _ _ glue_own.2.1
  -- one decide per bank region (a single decide over the 16-region `correction` overflows the stack)
  have app:∀ P Q:Program,StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330)) P=true →
      StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330)) Q=true →
      StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330)) (P++Q)=true:=by
    intro P Q a b
    simp only [StairWireCheck.allSites,List.all_append,Bool.and_eq_true] at a b ⊢
    exact ⟨a,b⟩
  have bk:∀ j∈[10, 13, 16, 19, 22, 25, 28, 31, 35, 39, 43, 47, 51, 55, 59, 63, 67, 70, 73, 76, 79, 82],StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330))
      (WindowFieldParity.bankCorrection j)=true:=by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  have table:StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330)) WindowFieldParity.correction=true:=by
    unfold WindowFieldParity.correction
    exact (app _ _ (bk 10 (by decide)) (app _ _ (bk 13 (by decide)) (app _ _ (bk 16 (by decide)) (app _ _ (bk 19 (by decide)) (app _ _ (bk 22 (by decide)) (app _ _ (bk 25 (by decide)) (app _ _ (bk 28 (by decide)) (app _ _ (bk 31 (by decide)) (app _ _ (bk 35 (by decide)) (app _ _ (bk 39 (by decide)) (app _ _ (bk 43 (by decide)) (app _ _ (bk 47 (by decide)) (app _ _ (bk 51 (by decide)) (app _ _ (bk 55 (by decide)) (app _ _ (bk 59 (by decide)) (app _ _ (bk 63 (by decide)) (app _ _ (bk 67 (by decide)) (app _ _ (bk 70 (by decide)) (app _ _ (bk 73 (by decide)) (app _ _ (bk 76 (by decide)) (app _ _ (bk 79 (by decide)) (bk 82 (by decide)))))))))))))))))))))))
  intro q h
  exact localSite (of_decide_eq_true (StairWireCheck.allSites_sound _ _ table q h))

theorem entryFieldHosted_corrected :
    wires (WindowParityCaller.entryFieldHosted StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  have hSuf : wires (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ⊆ callerDomain :=
    OddFullPass.P1LifeLoan.entryLowSuffixOdd_wires_sub
  unfold WindowParityCaller.entryFieldHosted
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
      (fieldRename_caller _ entryLowPrefix_ours) setup) glue_own.1)
    (fieldRename_caller _ hSuf)) glue_own.1) setup

theorem entryFieldHostedCut_corrected :
    wires WindowParityCaller.entryFieldHostedCut ⊆ callerDomain :=
  fun q hq => entryFieldHosted_corrected (PackCutSub.wires_sub WindowParityCaller.field_sublist q hq)

theorem exitFieldHosted_corrected :
    wires (WindowParityCaller.exitFieldHosted StairConcreteAssembly.checkpointPrimitives) ⊆ callerDomain := by
  have hPre : wires (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) ⊆ callerDomain :=
    OddFullPass.P1LifeLoan.exitLowPrefixOdd_wires_sub
  unfold WindowParityCaller.exitFieldHosted
  exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ (wires_sub_of_parts _ _
    (wires_sub_of_parts _ _ (wires_sub_of_parts _ _ setup glue_own.1)
      (fieldRename_caller _ hPre)) setup) glue_own.1)
    (fieldRename_caller _ exitLowSuffix_ours)

end ECDSAAdd.Entrant.StairPacket.ExteriorCaller

end


section

namespace ECDSAAdd.Entrant.StairPacket.StockNativeCompare
open Arithmetic MappedCompressed WideReference Secp256k1
attribute [local irreducible] run
theorem common_phase (d:Bool) (x:Nat) (good:Bounds x p) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 45 s.basis) :
    (StockArchiveReference.common d s).phase=s.phase :=
  Shadow20.MixedOrd.common_phase d x good s stage

theorem normalized (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) :
    StockArchiveBanks.Same (run (Shadow20.MergeCut.forward d) m (pullState (OB5.sig 44) raw))
      (StockArchiveReference.common d raw) := by
  rw [(Shadow20.MergeCut.run_eq d).1]
  exact Shadow20.MixedOrd.normalized d x good raw m stage
end ECDSAAdd.Entrant.StairPacket.StockNativeCompare

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkPrefix
set_option maxRecDepth 9500
set_option maxHeartbeats 3000000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount Shadow20.MergeCut.forward
def NewNormalized (d:Bool) (x:Nat):Prop:=∀(raw:State)(m:List Bool),Rolling1588.Integer.Stage base d x p 45 raw.basis →
    Same (run (Shadow20.MergeCut.forward d) m (pullState (OB5.sig 44) raw)) (StockArchiveReference.common d raw)

theorem steady (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:0 < i) (hi:i+n≤512) (s:State) (u v:List Bool) (stage:Rolling1588.Integer.Stage base d x p i s.basis):
    run (Rolling1588TickGap.forward d i n) u (pullState (OB5.sig (i-1)) s)=run (Rolling1588TickGap.forward d i n) v (pullState (OB5.sig (i-1)) s):=
  (StockDelayed.window d x good.nonzero good.small i n lo hi s u stage).trans
    (StockDelayed.window d x good.nonzero good.small i n lo hi s v stage).symm
theorem suffix_independent (d:Bool) (n x:Nat) (good:Bounds x p) (bound:421+n≤512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 45 s.basis) (u v y z:List Bool):
    let t:=pullState (OB5.sig 44) s
    let old:=Rolling1588TickGap.forward d 45 376
    let tail:=Rolling1588TickGap.forward d 421 n
    run tail u (run old v t)=run tail y (run old z t):=by
  let t:=pullState (OB5.sig 44) s
  let A:=Rolling1588TickGap.forward d 45 376
  let B:=Rolling1588TickGap.forward d 421 n
  let mix (v u:List Bool):=FlagEntry.pfx (measurementCount A) v++u
  have eq:=steady d x good 45 (376+n) (by decide) (by omega) s (mix v u) (mix z y) stage
  rw [StairRestSupport.forward_append d 376 45 n] at eq
  exact (Stair44PointSecond.joinRecords A B v u t).symm.trans (eq.trans (Stair44PointSecond.joinRecords A B z y t))

theorem window (d:Bool) (n x:Nat) (good:Bounds x p) (bound:421+n≤512) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) (m stockTape:List Bool) (norm:NewNormalized d x):
    let s:=pullState (OB5.sig 44) raw
    Paired d x (run (forwardEnd d n) m s) (run (Rolling1588TickGap.forward d 45 (376+n)) stockTape s) (StockRowVector.rows x p):=by
  let s:=pullState (OB5.sig 44) raw
  have result:=StockStrongChain.result d x good raw m stage
  have old:=StockBaseline.comparison d x good raw _ m stage result.2.1
  have new:=norm raw m stage
  have eq:Same _ _:=⟨new.1.trans old.1.symm,fun q off=>(new.2 q off).trans (old.2 q off).symm⟩
  have h:=StockRowVector.binding d x good raw _ m stage result.2.1 eq
  have onward:=h.through (Rolling1588TickGap.forward d 421 n) (fun q h=>(safe d 421 n (by decide) bound q h).1) (m.drop (measurementCount (Shadow20.MergeCut.forward d)))
  simp only [forwardEnd,StairRestSupport.forward_append d 376 45 n,run_append,run_take]
  rw [←suffix_independent d n x good bound raw stage (m.drop (measurementCount (Shadow20.MergeCut.forward d))) m (stockTape.drop (measurementCount (Rolling1588TickGap.forward d 45 376))) stockTape]
  exact onward
end ECDSAAdd.Entrant.StairPacket.StockWalkWindow

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockPlacedWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkPrefix StockWalkWindow
set_option maxRecDepth 12000
set_option maxHeartbeats 2500000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount Shadow20.MergeCut.forward
theorem fixed:∀(b:Bank)(j:Fin 16),Stair44WalkMap.rest (siteAt b j)=siteAt b j:=by
  intro b j; rw [site_eq]; exact Shadow20.MixedGeo.fixed_rest b j
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

theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.forward d (405+n)=
    first d++renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 45 (376+n)):=by
  have e:=StairRestSupport.forward_append d 29 16 (376+n)
  change Rolling1588TickGap.forward d 16 (29+(376+n))=Rolling1588TickGap.forward d 16 29++Rolling1588TickGap.forward d 45 (376+n) at e
  rw [show 405+n=29+(376+n) by omega]
  simp only [Stair44WalkRun.forward,first,e,renameProgram,List.map_append,List.append_assoc]

theorem forward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:421+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s) (norm:NewNormalized d x):
    Paired d x (run (WindowWalkCosts.forward d n) m a) (run (Stair44WalkRun.forward d (405+n)) m a) (StockRowVector.rows x p):=by
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
/-- Field bank of the ship's bank `b` (22 mixed 15/20-tick archive banks). -/
def groupId (b:Bank):Nat:=Shadow20.MixedGeo.groupId b
def parityPort (b:Bank) (i:Fin 16):Wire:=OB5.sig 511 (NewHistory5.payloadWire base (8*groupId b+i.val))
theorem native_ports:∀(b:Bank)(i:Fin 16),parityPort b i=siteAt b i:=by
  intro b i; rw [site_eq]; exact Shadow20.MixedGeo.parity_ports b i
theorem host_ports:∀(b:Bank)(i:Fin 16),Rolling1588Lifetime.phaseHost (siteAt b i)=siteAt b i:=by
  intro b i; rw [site_eq]; exact Shadow20.MixedGeo.fixed_phaseHost b i
theorem field_ports:∀(b:Bank)(i:Fin 16),fieldPort (groupId b) i.val=siteAt b i:=by
  intro b i; rw [site_eq]; exact Shadow20.MixedGeo.field_ports b i
theorem whole_iff (q:Wire):q∈allBanks ↔ q∈archives := by
  have hb : bankIds = Shadow20.MixedGeo.bankIds := rfl
  simp only [allBanks, archives, hb]
  exact Shadow20.MixedGeo.whole_iff q
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockInverseReplay
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkWindow StockPlacedWindow
set_option maxRecDepth 11000
set_option maxHeartbeats 3000000
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse
  Rolling1588.Integer.regularForward Rolling1588.Integer.regularReverse Shadow20.MergeCut.forward Shadow20.MergeCut.reverse
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
def fieldRows (r:Bank→Nat) (j:Nat):Nat:=Shadow20.MixedGeo.fieldRows r j
theorem rowsAt (r:Bank→Nat) (b:Bank):fieldRows r (groupId b)=r b:=
  Shadow20.MixedGeo.rowsAt r b
theorem idAt : ∀j∈bankIds,∃b:Bank,groupId b=j:=Shadow20.MixedGeo.idAt
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
  Rolling1588.Integer.regularForward Shadow20.MergeCut.forward Shadow20.MergeCut.reverse

def real (d:Bool) (raw:State):State:=run (Shadow20.MergeCut.forward d) [] (pullState (OB5.sig 44) raw)
def stock (d:Bool) (raw:State):State:=run (Rolling1588TickGap.forward d 45 376) [] (pullState (OB5.sig 44) raw)
theorem shadow (d:Bool) (x:Nat) (good:Bounds x p) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) (norm:NewNormalized d x):
    Paired d x (real d raw) (stock d raw) (StockRowVector.rows x p):=by
  have e:=norm raw [] stage
  have res:=StockStrongChain.result d x good raw [] stage
  have cmp:=StockBaseline.comparison d x good raw _ [] stage res.2.1
  exact StockRowVector.binding d x good raw _ [] stage res.2.1
    ⟨e.1.trans cmp.1.symm,fun q off=>(e.2 q off).trans (cmp.2 q off).symm⟩
theorem candidate_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis):
    run (Shadow20.MergeCut.reverse d) m (real d raw)=pullState (OB5.sig 44) raw:=
  (StockStrongChain.result d x good raw [] stage).2.2 m
theorem stock_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis):
    run (Rolling1588.reverse d 45 376) m (stock d raw)=pullState (OB5.sig 44) raw:=
  reverse_forward d x good 45 376 (by decide) (by decide) raw [] m stage
attribute [local irreducible] real stock poolEq
theorem inner (d:Bool) (x:Nat) (good:Bounds x p) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (stock d raw)):
    run (Shadow20.MergeCut.reverse d) m a=run (Rolling1588.reverse d 45 376) m ref:=by
  have ghost:=shadow d x good raw stage norm
  exact replay _ _ m a ref (real d raw) (stock d raw) _ (PartialSites.pool_partial d) (PartialSites.pool_old d 45 376 (by decide) (by decide))
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

def backwards (d:Bool) (n:Nat):Program:=Rolling1588.reverse d 421 n++Shadow20.MergeCut.reverse d

theorem result (d:Bool) (n x:Nat) (good:Bounds x p) (bound:421+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 45 (376+n)) [] (pullState (OB5.sig 44) raw))):
    run (backwards d n) m a=run (Rolling1588.reverse d 45 (376+n)) m ref:=by
  have h:=pair.through (Rolling1588.reverse d 421 n) (fun q hq=>(safe d 421 n (by decide) bound q hq).2) m
  have pools:=pool_run (PartialSites.pool_old d 421 n (by decide) bound) agree m
  simp only [StairRestSupport.forward_append d 376 45 n,run_append,run_take,List.drop_nil] at pools
  rw [tail_cancel d x 45 376 n good (by decide) bound raw stage m] at pools
  simp only [backwards,StairRestSupport.reverse_append d 376 45 n,run_append,run_take]
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
attribute [local irreducible] run measurementCount Rolling1588TickGap.forward Rolling1588.reverse Shadow20.MergeCut.reverse
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
def remaining (d:Bool):Program:=R (Rolling1588.reverse d 16 29)++renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)
theorem split (d:Bool) (n:Nat):WindowWalkCosts.backward d n=R (StockBackWindow.backwards d n)++remaining d:=by
  simp only [WindowWalkCosts.backward,StockBackWindow.backwards,R,remaining,renameProgram,List.map_append,List.append_assoc]
theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.backward d (405+n)=R (Rolling1588.reverse d 45 (376+n))++remaining d:=by
  have e:=StairRestSupport.reverse_append d 29 16 (376+n)
  change Rolling1588.reverse d 16 (29+(376+n))=Rolling1588.reverse d 45 (376+n)++Rolling1588.reverse d 16 29 at e
  rw [show 405+n=29+(376+n) by omega]
  simp only [remaining,Stair44WalkRun.backward,e,R,renameProgram,List.map_append,List.append_assoc]

theorem backward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:421+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 45 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 45 (376+n)) [] (pullState (OB5.sig 44) raw))):
    ∃old,run (WindowWalkCosts.backward d n) m a=run (Stair44WalkRun.backward d (405+n)) old ref:=by
  let A:=R (StockBackWindow.backwards d n)
  let B:=R (Rolling1588.reverse d 45 (376+n))
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
theorem opened (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (bound:421+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Paired d x (run (WindowWalkCosts.forward d n) m a) (run (Stair44WalkRun.forward d (405+n)) m a) (StockRowVector.rows x p):=
  StockPlacedWindow.forward d n x (bounds x nz lt) bound s a m stage input (StockNativeCompare.normalized d x (bounds x nz lt))

theorem rest_pool (q:Wire) (h:q∈pool):Stair44WalkMap.rest q∈pool:=by
  simp only [Stair44WalkMap.rest,Stair44WalkMap.shared,Equiv.trans_apply,Equiv.swap_apply_def]
  split_ifs <;> first | exact h | exact List.mem_toFinset.mpr (OB5.base_pool _ (by decide))
theorem fixed_old (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:421+n∈[425,505,506]) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (m:List Bool):
    let v:=run (Rolling1588TickGap.forward d 1 (420+n)) m s
    pullState Stair44WalkMap.rest v=v:=by
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have num:15+(405+n)=420+n:=by omega
  have cut:1+(15+(405+n))∈[425,505,506]:=by simpa only [show 1+(15+(405+n))=421+n by omega] using atCut
  have one:=Stair44WalkRun.forward_run d (405+n) x good.nonzero good.small s a m stage input
  have two:=Stair44WalkCuts.forward_done d (405+n) x cut good.nonzero good.small s a m stage input
  rw [two,num] at one
  exact one

theorem decompose (d:Bool) (x n:Nat) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:421+n≤512):
    let raw:=regular d s []
    run (Rolling1588TickGap.forward d 1 (420+n)) m s=
      run (Rolling1588TickGap.forward d 45 (376+n)) [] (pullState (OB5.sig 44) raw):=by
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  have same:=StockWalkWindow.steady d x good 1 (420+n) (by decide) (by omega) s m [] stage
  rw [show 1-1=0 from rfl,init] at same
  have cut:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 44 1 (by decide) (by decide) s [] stage
  rw [show 1-1=0 from rfl,init] at cut
  have shape:420+n=44+(376+n):=by omega
  rw [same,shape,StairRestSupport.forward_append d 44 1 (376+n),run_append,run_take,List.drop_nil,cut]
  rfl

theorem move {f:Wire→Wire} (a b c:State) (mem:∀q∈pool,f q∈pool) (eq:poolEq a b)
    (fixed:pullState f b=b) (next:b=c):poolEq (pullState f a) c:=by
  intro q hq
  exact (eq _ (mem q hq)).trans ((congrArg (fun s:State=>s.basis q) fixed).trans (congrArg (fun s:State=>s.basis q) next))
theorem endpoint_stage (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (stage:Rolling1588.Integer.Stage base d x p 1 s.basis):
    Rolling1588.Integer.Stage base d x p 45 (regular d s []).basis:=StockBackWindow.stageAt d x good 1 44 (by decide) s [] stage
theorem endpoint_pool (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:421+n∈[425,505,506]) (s ref:State) (enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:421+n≤512)
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (420+n)) enc s)):
    poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 45 (376+n)) [] (pullState (OB5.sig 44) (regular d s []))):=
  move _ _ _ rest_pool agree (fixed_old d n x good atCut s stage enc) (decompose d x n good s enc stage bound)
theorem closed (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:421+n∈[425,505,506]) (one a ref:State) (m enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (420+n)) enc one)):
    ∃old,run (WindowWalkCosts.backward d n) m a=run (Stair44WalkRun.backward d (405+n)) old ref:=by
  have good:=bounds x nz lt
  have bound:421+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
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
    (WindowWalkCosts.backward false 85++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [WindowKernelPrograms.division,divAfter,divHead,Six505.rename_append,List.append_assoc]
theorem old_div_head_split:Stair44Kernel.division=oldDivHead++renameProgram phaseHost
    (Stair44WalkRun.backward false 490++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [Stair44Kernel.division,oldDivHead,Stair44DivTerm.routedClose,Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,Six505.rename_append,List.append_assoc]
theorem mul_head_split (k:Nat):WindowKernelPrograms.multiplication k=mulHead++renameProgram phaseHost
    (WindowWalkCosts.backward true 4++renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)):=rfl
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
def original (d:Bool) (n:Nat):Program:=renameProgram phaseHost (openR d (405+n))

private theorem fixed (x y:Nat) (s:State) (h:SkywalkArithmeticInput base x y s.basis):
    pullState Stair44WalkMap.first s=s:=by
  let idx:List Nat:=[1026,514,1541,501,1542,500]
  have all:∀j∈idx,base j∈skywalkSharedWires base ∧ base j∉skywalkArithmeticDivisor base ∧ base j∉skywalkArithmeticNumerator base:=by decide +kernel
  have zero (j:Nat) (hj:j∈idx):s.basis (base j)=false:=h.2.2 _ (all j hj).1 (all j hj).2.1 (all j hj).2.2
  have a:=cleanWireRebind id s s _ _ rfl (zero 1026 (by decide)) (zero 514 (by decide))
  have b:=cleanWireRebind _ s s _ _ a (zero 1541 (by decide)) (zero 501 (by decide))
  exact cleanWireRebind _ s s _ _ b (zero 1542 (by decide)) (zero 500 (by decide))

theorem open_raw (d:Bool) (n x y:Nat) (nz:0 < x) (lt:x<p) (bound:421+n≤512)
    (hn:(skywalkSharedWires base).Nodup) (s:State) (input:SkywalkArithmeticInput base x y s.basis) (m:List Bool):
    Paired d x (run (openWalk d n) m s) (run (openR d (405+n)) m s) (StockRowVector.rows x p):=by
  let N:=FrontierEntry1591Native.forward base
  let t:=m.take (measurementCount firstR)
  have stage:=Rolling1588.Integer.stage_one base d x p _ (FrontierEntry1591Native.caller_first_stageW base hn x y nz lt s t input)
  have eq:=run_rename Stair44WalkMap.first Stair44WalkMap.first.injective N t s
  rw [fixed x y s input] at eq
  simp only [openWalk,openR,run_append]
  exact StockWalkEndpoints.opened d n x nz lt bound _ _ _ stage eq
theorem division {s:State} (F:EntryFrame s) (m:List Bool):
    Paired true F.x (pullState phaseHost (run (opening true 4) m s))
      (pullState phaseHost (run (original true 4) m s)) (StockRowVector.rows F.x p):=by
  rw [opening,original,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_entry F]
  exact open_raw true 4 F.x _ F.x_pos F.x_lt (by decide) F.sharedNodup s (StairField13V3Clean.entryInput F) m
theorem multiplication (k:Nat) {s:State} (F:ExitFrame k s) (m:List Bool):
    Paired false F.x (pullState phaseHost (run (opening false 84) m s))
      (pullState phaseHost (run (original false 84) m s)) (StockRowVector.rows F.x p):=by
  rw [opening,original,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_exit F]
  exact open_raw false 84 F.x _ F.x_pos F.x_lt (by decide) F.sharedNodup s F.input m
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

theorem ofEndpoint (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:421+n∈[425,505,506]) (ref:State)
    (h:Endpoint d x (420+n) ref):Native d x ref:=by
  obtain ⟨s,enc,stage,eq⟩:=h
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have bound:421+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
  have pair:=StockWalkEndpoints.opened d n x nz lt bound s a enc stage input
  have cut:1+(15+(405+n))∈[425,505,506]:=by simpa only [show 1+(15+(405+n))=421+n by omega] using atCut
  have same:=Stair44WalkCuts.forward_done d (405+n) x cut nz lt s a enc stage input
  rw [show 15+(405+n)=420+n by omega] at same
  refine ⟨pair.labels,?_⟩
  intro b j
  have loc:siteAt b j∈pool:=archives_pool _ (StockArchiveBanks.mem b j)
  exact (eq _ loc).trans ((congrArg (fun s:State=>s.basis (siteAt b j)) same.symm).trans (pair.stock b j))

theorem div_native {s:State} (F:StairConcreteAssembly.EntryFrame s) (m:List Bool):
    Native false F.x (pullState phaseHost (run oldDivHead m s)):=
  ofEndpoint false 85 F.x F.x_pos F.x_lt (by decide) _ (div_endpoint F m)
theorem mul_native (k:Nat) {s:State} (F:StairConcreteAssembly.ExitFrame k s) (m:List Bool):
    Native true F.x (pullState phaseHost (run oldMulHead m s)):=
  ofEndpoint true 4 F.x F.x_pos F.x_lt (by decide) _ (mul_endpoint k F m)

end ECDSAAdd.Entrant.StairPacket.WindowEndBytes

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowMiddlePieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime FlagEntry StockArchiveBanks
open WindowMiddleContract WindowStartStates
set_option maxRecDepth 14000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount renameProgram

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
    run (entryYAll layout (-cy) ++ entryXNew layout (pkW layout) (-cx)) m (put s (pkW layout) e) =
    run (E1QubitPlacement.tickF layout) [] (run (reference (-cx) (-cy)) [] s) := by
  intro e
  have a := (StairCallerEntry.head_pad_rest layout layout_widths layout_nodup cx cy X Y []
    s v.x v.y v.clean (by decide +kernel)).run_eq m
  have b := StairCallerEntry.stageAll_eq_ref layout layout_widths layout_nodup X Y (-cx) (-cy) []
    s (padE layout cy cx m) v.x v.y v.clean
  have c := E1QubitPlacement.entry1_eq layout layout_widths layout_nodup (-cx) (-cy) s X.val X.isLt Y G
    v.x v.y v.generic v.clean (padE layout cy cx m) []
  simp only [List.append_nil] at a b
  rw [a,b,c,run_append,List.take_nil,List.drop_nil,reference]

theorem prepClean (kx ky X Y : Fp) (G : Bool) (s : State)
    (v : PointDialogValues layout X Y G s.basis s.basis) :
    regValue layout.dialogPool (run (reference kx ky) [] s).basis=0 := by
  let P := fastConstAdd layout layout.point.x kx
  have u := fastStep_addX layout layout_widths layout_nodup X Y G s.basis kx s [] v
  have f := fusedY_correct layout layout_widths layout_nodup Y ky (run P [] s) [] u.2.y u.2.clean
  rw [reference,run_append,List.take_nil,List.drop_nil]
  exact (regValue_congr _ _ (run P [] s).basis (fun q hq => f.2.2 q
    (((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2))).trans u.2.clean

end ECDSAAdd.Entrant.Stair44PointDivision

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial
set_option maxRecDepth 20000
attribute [local irreducible] wires domain
theorem forward_domain (d : Bool) : ∀ q ∈ wires (Shadow20.MergeCut.forward d), domain q = true := by
  intro q h
  rw [domain_eq]
  exact (Shadow20.MergeCut.covered d).1 q h
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
theorem part (d:Bool):wires (Shadow20.MergeCut.forward d)⊆callerDomain ∧ wires (Shadow20.MergeCut.reverse d)⊆callerDomain:=
  ⟨fun q h=>range_ok q (forward_domain d _ h),fun q h=>range_ok q (reverse_domain d _ h)⟩

theorem forward (d:Bool) (n:Nat) (bound:420+n≤504):wires (WindowWalkCosts.forward d n)⊆callerDomain:=by
  have stock:=forward_own d (420+n) bound
  have shape:420+n=15+(29+(376+n)):=by omega
  rw [shape,tickGap_forward_split d 15 1 (29+(376+n)),tickGap_forward_split d 29 16 (376+n),tickGap_forward_split d 376 45 n] at stock
  simp only [wires_append,Finset.union_subset_iff] at stock
  apply wires_sub_of_parts _ _
  · exact rename_caller _ firstOK _ stock.1
  · apply rename_caller _ restOK
    exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ stock.2.1 (part d).1) stock.2.2.2

theorem backward (d:Bool) (n:Nat) (bound:420+n≤505):wires (WindowWalkCosts.backward d n)⊆callerDomain:=by
  have stock:=reverse_own d (420+n) bound
  have shape:420+n=15+(29+(376+n)):=by omega
  rw [shape,reverse_split d 15 1 (29+(376+n)),reverse_split d 29 16 (376+n),reverse_split d 376 45 n] at stock
  simp only [wires_append,Finset.union_subset_iff] at stock
  apply wires_sub_of_parts _ _
  · apply rename_caller _ restOK
    exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ stock.1.1.1 (part d).2) stock.1.2
  · exact rename_caller _ firstOK _ stock.2
end ECDSAAdd.Entrant.StairPacket.WindowIntegerSites

end

end

-- ==== begin OddTailPart1 ====
section

section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.OddFullPassBridge
open ECDSAAdd Arithmetic Challenge MappedCompressed Secp256k1 BalancedField BalancedCircuit
open OddFullPass.P1LifeLoan

private theorem run_zero_meas (P : Program) (h : measurementCount P = 0) (m n : List Bool) (s : State) :
    run P m s = run P n s := by
  induction P generalizing s m n with
  | nil => rfl
  | cons g gs ih =>
    cases g with
    | measureX _ _ _ => simp [measurementCount] at h
    | X _ | CX _ _ | CCX _ _ _ =>
      exact ih (by simpa [measurementCount] using h) m n _

private theorem meas_X (q : Wire) : measurementCount [.X q] = 0 := rfl

attribute [local irreducible] run wires measurementCount
  OddFullPass.P1LifeLoan.rawAddLoan OddFullPass.P1LifeLoan.foldLoan
  OddFullPass.P1LifeLoan.unfoldLoan OddFullPass.P1LifeLoan.compareBlockLoan
  OddFullPass.P1LifeLoan.rawSubLoan OddFullPass.P1LifeLoan.shortConstAddLoan
  OddFullPass.P1LifeLoan.forwardLoan OddFullPass.P1LifeLoan.inverseLoan
  OddFullPass.P1LifeLoan.half760OddLoan
  P1Life.rawAdd P1Life.fold P1Life.unfoldStep P1Life.compare P1Life.rawSub
  P1Life.shortConstAdd P1Life.forward P1Life.inverse P1Life.half

private abbrev L760 : BalancedCircuit.Layout := Q6EndpointCell.ports base (base 2409)

private theorem mem_wireBlock_iff (w : Nat → Wire) (s n q : Nat) :
    q ∈ wireBlock w s n ↔ ∃ i, i < n ∧ q = w (s + i) := by
  simp only [wireBlock, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, hkq⟩; exact ⟨k - s, by omega, by rw [← hkq]; congr 1; omega⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨s + i, ⟨by omega, by omega⟩, rfl⟩

private theorem base_eq_add (k : Nat) : (base k : Nat) = k + 16 := rfl

private theorem mem_L760_r_iff (q : Nat) : q ∈ L760.r ↔ 2072 ≤ q ∧ q < 2328 := by
  simp only [L760, BalancedCleanup.Layout.r, BalancedCleanup.Layout.low, Q6EndpointCell.ports,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, mem_wireBlock_iff]
  simp only [base_eq_add]
  constructor
  · rintro ((rfl | ⟨i, hi, rfl⟩) | rfl) <;> omega
  · rintro ⟨hlo, hhi⟩
    by_cases h0 : q = 2072
    · exact Or.inl (Or.inl h0)
    · by_cases h1 : q = 2327
      · exact Or.inr h1
      · exact Or.inl (Or.inr ⟨q - 2073, by omega, by omega⟩)

private theorem mem_L760_y_iff (q : Nat) : q ∈ L760.y ↔ 786 ≤ q ∧ q < 1042 := by
  simp only [L760, BalancedCleanup.Layout.y, Q6EndpointCell.ports,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, mem_wireBlock_iff]
  simp only [base_eq_add]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl) <;> omega
  · rintro ⟨hlo, hhi⟩
    by_cases h1 : q = 1041
    · exact Or.inr h1
    · exact Or.inl ⟨q - 786, by omega, by omega⟩

private theorem mem_L760_carry_iff (q : Nat) :
    q ∈ L760.carry ↔ (528 ≤ q ∧ q < 781) ∨ q = 1556 ∨ q = 1557 ∨ q = 1042 := by
  simp only [L760, Q6EndpointCell.ports, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, mem_wireBlock_iff]
  simp only [base_eq_add]
  constructor
  · rintro (⟨i, hi, rfl⟩ | h)
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr h
  · rintro (⟨h1, h2⟩ | h)
    · exact Or.inl ⟨q - 528, by omega, by omega⟩
    · exact Or.inr h

private theorem mem_L760_carry254_iff (q : Nat) :
    q ∈ L760.carry.take 254 ↔ (528 ≤ q ∧ q < 781) ∨ q = 1556 := by
  have htake : L760.carry.take 254 = wireBlock base 512 253 ++ [base 1540] := by
    have hlen : (wireBlock base 512 253).length = 253 := wireBlock_length base 512 253
    simp only [L760, Q6EndpointCell.ports, List.take_append, hlen]
    rfl
  rw [htake]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, mem_wireBlock_iff]
  simp only [base_eq_add]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl) <;> omega
  · rintro (⟨h1, h2⟩ | rfl)
    · exact Or.inl ⟨q - 528, by omega, by omega⟩
    · exact Or.inr rfl

private theorem L760_carry_away (q : Nat) (hq : q ∈ L760.carry) :
    q ≠ L760.lower ∧ q ∉ L760.r ∧ q ∉ L760.y := by
  rw [mem_L760_carry_iff] at hq
  rw [mem_L760_r_iff, mem_L760_y_iff]
  have hlo : (L760.lower : Nat) = 1813 := rfl
  rw [hlo]
  omega

private theorem mem_q6Carry255_drop1_iff (q : Nat) :
    q ∈ ((Q6Structural.q6Carry L760).take 255).drop 1 ↔
      (529 ≤ q ∧ q < 781) ∨ q = 1556 ∨ q = 1813 := by
  have hshape : ((Q6Structural.q6Carry L760).take 255).drop 1 =
      wireBlock base 513 252 ++ [base 1540, base 1797] := by
    have h1 : L760.carry.take 254 = wireBlock base 512 253 ++ [base 1540] := by
      have hlen : (wireBlock base 512 253).length = 253 := wireBlock_length base 512 253
      simp only [L760, Q6EndpointCell.ports, List.take_append, hlen]; rfl
    have hlen254 : (L760.carry.take 254).length = 254 := by rw [h1]; simp [wireBlock_length]
    have h2 : (Q6Structural.q6Carry L760).take 255 = L760.carry.take 254 ++ [L760.lower] := by
      rw [Q6Structural.q6Carry, List.append_assoc, List.take_append, hlen254]
      rw [List.take_of_length_le (by rw [hlen254]; omega)]
      rfl
    rw [h2, h1]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    change (base 512 :: (wireBlock base 513 252 ++ [base 1540, base 1797])).drop 1 = _
    rfl
  rw [hshape]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, mem_wireBlock_iff]
  simp only [base_eq_add]
  constructor
  · rintro (⟨i, hi, rfl⟩ | h)
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inr h
  · rintro (⟨h1, h2⟩ | h)
    · exact Or.inl ⟨q - 529, by omega, by omega⟩
    · exact Or.inr h

private theorem not_mem_L760_r_of_eq {q : Wire} (n : Nat) (heq : n = q)
    (hn : ¬(2072 ≤ n ∧ n < 2328)) : q ∉ L760.r := by
  rw [← heq, mem_L760_r_iff]; exact hn

private theorem not_mem_L760_y_of_eq {q : Wire} (n : Nat) (heq : n = q)
    (hn : ¬(786 ≤ n ∧ n < 1042)) : q ∉ L760.y := by
  rw [← heq, mem_L760_y_iff]; exact hn

private theorem not_mem_L760_carry254_of_eq {q : Wire} (n : Nat) (heq : n = q)
    (hn : ¬((528 ≤ n ∧ n < 781) ∨ n = 1556)) : q ∉ L760.carry.take 254 := by
  rw [← heq, mem_L760_carry254_iff]; exact hn

private theorem p1Seed_eq : p1Seed L760 = P1Life.p1Seed L760 := rfl
private theorem prepareCompare_eq : prepareCompare L760 = P1Life.prepareCompare L760 := rfl
private theorem exposure_eq : exposure L760 = P1Life.exposure L760 := rfl
private theorem orMajor_eq (a b c : Wire) : orMajor a b c = P1Life.orMajor a b c := rfl
private theorem orErase_eq (a b c : Wire) : orErase a b c = P1Life.orErase a b c := rfl
private theorem oddEncoding_norm (x : Int) :
    DirectPass.oddEncoding.normalized x = encodeWord 255 (P1Life.oddNormalized x) := rfl
private theorem regValue_singleton_false (w : Wire) (b : BasisState) (h : b w = false) :
    regValue [w] b = 0 := by
  simp [regValue, h]
private theorem L760_sign_ne_parity : L760.sign ≠ L760.parity := by decide +kernel
private theorem L760_sign_ne_lower : L760.sign ≠ L760.lower := by decide +kernel
private theorem L760_sign_ne_one : L760.sign ≠ L760.one := by decide +kernel
private theorem L760_one_ne_lower : L760.one ≠ L760.lower := by decide +kernel
private theorem L760_parity_ne_lower : L760.parity ≠ L760.lower := by decide +kernel

private theorem mem_mappedWires_read (ws : List Wire) (q : Wire)
    (hq : q ∈ mappedWires (mappedRead ws false)) : q ∈ ws := by
  induction ws with
  | nil => simp [mappedWires, mappedRead] at hq
  | cons w ws ih =>
    simp only [mappedRead, mappedWires, List.map_cons, List.flatMap_cons, List.mem_append,
      Option.toList_some, List.mem_singleton] at hq
    rcases hq with rfl | hrest
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih hrest)

private theorem hw760 : L760.Widths := Q6EndpointCell.ports_widths base (base 2409)
private theorem hn760 : L760.wires.Nodup := Rolling1588Lifetime.half_ports_nodup760
private theorem mem760 : base 760 ∈ (L760.carry.take 254).drop 1 := R2Life760.member760

private theorem pull_swap_invol (a b : Wire) (s : State) :
    pullState (Equiv.swap a b) (pullState (Equiv.swap a b) s) = s := by
  apply State.extensionality
  · rfl
  · funext q; simp [pullState]

private theorem move_run_eq (a b : Wire) (P Q : Program) (s : State) (m n : List Bool)
    (h : run P m (pullState (Equiv.swap a b) s) = run Q n (pullState (Equiv.swap a b) s)) :
    run (Q6LifetimeResearch.move a b P) m s = run (Q6LifetimeResearch.move a b Q) n s := by
  have hp := run_rename (Equiv.swap a b) (Equiv.swap a b).injective P m s
  have hq := run_rename (Equiv.swap a b) (Equiv.swap a b).injective Q n s
  have heq : pullState (Equiv.swap a b) (run (Q6LifetimeResearch.move a b P) m s) =
      pullState (Equiv.swap a b) (run (Q6LifetimeResearch.move a b Q) n s) :=
    hp.trans (h.trans hq.symm)
  simpa only [pull_swap_invol] using congrArg (pullState (Equiv.swap a b)) heq

private theorem replace_mid (A P Q B : Program) (s : State) (m : List Bool)
    (h : ∀ x, ∃ y, run P x (run A (m.take (measurementCount A)) s) =
      run Q y (run A (m.take (measurementCount A)) s)) :
    ∃ n, run (A ++ (P ++ B)) m s = run (A ++ (Q ++ B)) n s := by
  let t1 := m.take (measurementCount A)
  let rest := m.drop (measurementCount A)
  let t2 := rest.take (measurementCount P)
  let t3 := rest.drop (measurementCount P)
  obtain ⟨y, hy⟩ := h t2
  refine ⟨StairPacket.WindowFieldJourney.joinTapes A t1
      (StairPacket.WindowFieldJourney.joinTapes Q y t3), ?_⟩
  rw [run_append A (P ++ B), run_append P B,
      StairPacket.WindowFieldJourney.joined, StairPacket.WindowFieldJourney.joined]
  exact congrArg (run B t3) hy

private theorem replace_last (A P Q : Program) (s : State) (m : List Bool)
    (h : ∀ x, ∃ y, run P x (run A (m.take (measurementCount A)) s) =
      run Q y (run A (m.take (measurementCount A)) s)) :
    ∃ n, run (A ++ P) m s = run (A ++ Q) n s := by
  simpa only [List.append_nil] using replace_mid A P Q [] s m h

private theorem carry_all_zero_of_outside (origin : BasisState)
    (horig : ∀ q ∈ L760.carry, origin q = false)
    (b : BasisState)
    (hclean : DirectPass.CleanExcept (L760.carry.take 254) (base 760) b)
    (hframe : DirectPass.HalfOutside L760 origin b)
    (h760 : b (base 760) = false) :
    ∀ q ∈ L760.carry, b q = false := by
  intro q hq
  by_cases htake : q ∈ L760.carry.take 254
  · by_cases hq760 : q = base 760
    · exact hq760 ▸ h760
    · exact hclean q htake hq760
  · have hq2 : q = base 1541 ∨ q = base 1026 := by
      rcases (mem_L760_carry_iff q).mp hq with h1 | h2 | h3 | h4
      · exact absurd ((mem_L760_carry254_iff q).mpr (Or.inl h1)) htake
      · exact absurd ((mem_L760_carry254_iff q).mpr (Or.inr h2)) htake
      · exact Or.inl h3
      · exact Or.inr h4
    rcases hq2 with rfl | rfl
    · exact (hframe _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (horig _ hq)
    · exact (hframe _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans (horig _ hq)

private theorem rawAddLoan_760_run_eq (d : Nat) (hd : d ≤ 44) (s : State) (m : List Bool)
    (hready : P1Life.OddRawReady L760 s.basis)
    (hlow : s.basis L760.lower = false)
    (hcar : ∀ q ∈ L760.carry, s.basis q = false) :
    ∃ n, run (rawAddLoan d L760) m s = run (P1Life.rawAdd (base 760) L760) n s := by
  let a := L760.ylow.getD 0 0
  let b := L760.low.getD 0 0
  let cs := (Q6Structural.q6Carry L760).take 255
  let c := cs.getD 0 0
  let clear : Program := [.CX L760.parity b, .CX a b, .X b]
  let Pre := signComplement L760.sign L760.y ++ orMajor a b c ++ clear
  let Post := clear.reverse ++ orErase a b c ++ [.CX a b, .X b] ++ signComplement L760.sign L760.y
  let MidP := Q6LifetimeResearch.move (base 760) b
    (StairLoan.addPrefixLoan d StairLoan.retiredRoles (L760.ylow.drop 1) (L760.low.drop 1)
      (cs.drop 1) L760.ymsb L760.rmsb L760.one c)
  let MidQ := Q6LifetimeResearch.move (base 760) b
    (StairLoan.addPrefixLoan 0 StairLoan.retiredRoles (L760.ylow.drop 1) (L760.low.drop 1)
      (cs.drop 1) L760.ymsb L760.rmsb L760.one c)
  have hshapeP : rawAddLoan d L760 = Pre ++ (MidP ++ Post) := by
    delta rawAddLoan; simp only [Pre, MidP, Post, a, b, cs, c, clear, List.append_assoc]
  have hshapeQ : P1Life.rawAdd (base 760) L760 = Pre ++ (MidQ ++ Post) := by
    delta P1Life.rawAdd; dsimp only
    rw [show CoherentTail.addPrefix (L760.ylow.drop 1) (L760.low.drop 1) (cs.drop 1)
        L760.ymsb L760.rmsb L760.one c =
        StairLoan.addPrefixLoan 0 StairLoan.retiredRoles (L760.ylow.drop 1) (L760.low.drop 1)
          (cs.drop 1) L760.ymsb L760.rmsb L760.one c from (StairLoan.addPrefixLoan_zero _ _ _ _ _ _ _ _).symm]
    simp only [Pre, MidQ, Post, a, b, cs, c, clear, orMajor, orErase, P1Life.orMajor, P1Life.orErase, List.append_assoc]
  rw [hshapeP, hshapeQ]
  apply replace_mid Pre MidP MidQ Post s m
  intro x
  refine ⟨[], ?_⟩
  let u := run Pre (m.take (measurementCount Pre)) s
  have hPreM : measurementCount Pre = 0 := by
    have hsc : measurementCount (signComplement L760.sign L760.y) = 0 := (signComplement_counts _ _).2
    have hom : measurementCount (orMajor a b c) = 0 := by decide +kernel
    have hcl : measurementCount clear = 0 := by decide +kernel
    simp only [Pre, measurementCount_append, hsc, hom, hcl]
  have huEq : u = run clear [] (run (orMajor a b c) [] (run (signComplement L760.sign L760.y) [] s)) := by
    dsimp only [u]
    rw [run_zero_meas Pre hPreM _ [], show Pre = signComplement L760.sign L760.y ++ orMajor a b c ++ clear from rfl,
        run_append, run_append]
    simp [List.take_nil, List.drop_nil]
  have hyND : L760.y.Nodup := PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hsignY : L760.sign ∉ L760.y := by decide +kernel
  let s1 := run (signComplement L760.sign L760.y) [] s
  have hs1 (q : Wire) : s1.basis q = if q ∈ L760.y then s.basis q ^^ s.basis L760.sign else s.basis q :=
    GuardCompression.complement_bit L760.sign L760.y hyND hsignY s [] q
  have hnotY : ∀ (q : Nat), q ∈ [L760.one, L760.rmsb, L760.parity, L760.lower, b] ++ L760.carry → s1.basis q = s.basis q := by
    intro q hq
    have hny : q ∉ L760.y := by
      rw [mem_L760_y_iff]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, mem_L760_carry_iff] at hq
      rcases hq with (rfl | rfl | rfl | rfl | rfl) | hc
      · decide
      · decide
      · decide
      · decide
      · decide
      · omega
    rw [hs1, if_neg hny]
  have haY : a ∈ L760.y := by decide +kernel
  have hs1a : s1.basis a = (s.basis a ^^ s.basis L760.sign) := by rw [hs1, if_pos haY]
  have habc_away : ∀ q, q ≠ c → (run (orMajor a b c) [] s1).basis q = s1.basis q := by
    intro q hqc
    have hab : a ≠ b := by decide +kernel
    have hac : a ≠ c := by decide +kernel
    have hbc : b ≠ c := by decide +kernel
    by_cases hqa : q = a
    · subst hqa; simp [orMajor, run, writeBit, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
    · by_cases hqb : q = b
      · subst hqb; simp [orMajor, run, writeBit, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
      · simp [orMajor, run, writeBit, hqa, hqb, hqc]
  have hclear_away : ∀ q, q ≠ b → (run clear [] (run (orMajor a b c) [] s1)).basis q = (run (orMajor a b c) [] s1).basis q := by
    intro q hqb
    simp [clear, run, writeBit, hqb]
  have hu_b : u.basis b = false := by
    rw [huEq]
    have hpb : L760.parity ≠ b := by decide +kernel
    have hab : a ≠ b := by decide +kernel
    have hpc : L760.parity ≠ c := by decide +kernel
    have hac : a ≠ c := by decide +kernel
    have hbc : b ≠ c := by decide +kernel
    have h1 : (run clear [] (run (orMajor a b c) [] s1)).basis b =
        !(((run (orMajor a b c) [] s1).basis b ^^ (run (orMajor a b c) [] s1).basis L760.parity) ^^
          (run (orMajor a b c) [] s1).basis a) := by
      simp [clear, run, writeBit, hpb, hab]
    rw [h1, habc_away b hbc, habc_away L760.parity hpc, habc_away a hac,
        hnotY b (by simp), hnotY L760.parity (by simp), hs1a]
    have hpar : s.basis L760.parity = (s.basis b ^^ s.basis a ^^ (s.basis L760.sign ^^ true)) := hready.2
    rw [hpar]
    cases s.basis b <;> cases s.basis a <;> cases s.basis L760.sign <;> rfl
  have hu_keep : ∀ q ∈ [L760.one, L760.rmsb, L760.lower] ++ L760.carry.drop 1, u.basis q = s.basis q := by
    have hchk : ([L760.one, L760.rmsb, L760.lower] ++ L760.carry.drop 1).all
        (fun q => decide (q ≠ b ∧ q ≠ c)) = true := by decide +kernel
    intro q hq
    have hne := of_decide_eq_true (List.all_eq_true.mp hchk q hq)
    rw [huEq, hclear_away q hne.1, habc_away q hne.2]
    apply hnotY q
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with (rfl | rfl | rfl) | hc'
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (List.mem_of_mem_drop hc')
  apply move_run_eq (base 760) b _ _ u x []
  apply addPrefixLoan_760_run_eq d (by omega) (pullState (Equiv.swap (base 760) b) u) x []
  · simp only [pullState,
      Equiv.swap_apply_of_ne_of_ne (by decide : L760.one ≠ base 760) (by decide : L760.one ≠ b),
      Equiv.swap_apply_of_ne_of_ne (by decide : L760.rmsb ≠ base 760) (by decide : L760.rmsb ≠ b)]
    rw [hu_keep L760.one (by simp), hu_keep L760.rmsb (by simp)]
    exact hready.1
  · intro q hq
    by_cases hq760 : q = base 760
    · subst hq760; simp only [pullState, Equiv.swap_apply_left]; exact hu_b
    · have hqb : q ≠ b := by
        have hchk : (cs.drop 1 ++ [L760.carry.getD 255 0]).all (fun z => decide (z ≠ b)) = true := by decide +kernel
        exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
      simp only [pullState, Equiv.swap_apply_of_ne_of_ne hq760 hqb]
      have hmem : q = L760.lower ∨ q ∈ L760.carry.drop 1 := by
        have hchk : (cs.drop 1 ++ [L760.carry.getD 255 0]).all
            (fun z => decide (z = L760.lower ∨ z ∈ L760.carry.drop 1)) = true := by decide +kernel
        exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
      rcases hmem with rfl | hcd
      · rw [hu_keep L760.lower (by simp)]; exact hlow
      · rw [hu_keep q (List.mem_append_right _ hcd)]; exact hcar q (List.mem_of_mem_drop hcd)

private theorem foldLoan_760_run_eq (d : Nat) (hd : d ≤ 44) (s : State) (m : List Bool)
    (hlow : s.basis L760.lower = s.basis L760.rmsb)
    (hcar : ∀ q ∈ L760.carry, s.basis q = false) :
    ∃ n, run (foldLoan d L760) m s = run (P1Life.fold (base 760) L760) n s := by
  let Pre : Program := [.CCX L760.parity L760.lower L760.one, .CX L760.lower L760.rmsb]
  let Post : Program := [.CX L760.lower L760.rmsb, .CX L760.parity L760.rmsb, .X L760.rmsb,
    .CX L760.parity L760.lower, .CX L760.rmsb L760.lower, .X L760.lower,
    .measureX L760.one [] [.CZ L760.parity L760.rmsb]]
  let MidP := Q6LifetimeResearch.move (base 760) L760.rmsb
    (FoldLoanTop.choose d L760 false)
  let MidQ := Q6LifetimeResearch.move (base 760) L760.rmsb
    (StairLoan.mappedAddLoan 0 StairLoan.retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one)
  have hP : foldLoan d L760 = Pre ++ (MidP ++ Post) := by
    delta foldLoan; simp only [Pre, MidP, Post, List.append_assoc]
  have hQ : P1Life.fold (base 760) L760 = Pre ++ (MidQ ++ Post) := by
    delta P1Life.fold
    rw [show mappedAdd (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one =
        StairLoan.mappedAddLoan 0 StairLoan.retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one from
        (StairLoan.mappedAddLoan_zero _ _ _ _ _).symm]
    simp only [Pre, MidQ, Post, List.append_assoc]
  rw [hP, hQ]
  apply replace_mid Pre MidP MidQ Post s m
  intro x
  refine ⟨[], ?_⟩
  let u := run Pre (m.take (measurementCount Pre)) s
  have huEq : u = run Pre [] s := run_zero_meas Pre (by decide +kernel) _ [] s
  have hurmsb : u.basis L760.rmsb = false := by
    rw [huEq]
    have h1 : L760.lower ≠ L760.one := by decide +kernel
    have h2 : L760.rmsb ≠ L760.one := by decide +kernel
    simp [Pre, run, writeBit, h1, h2, hlow]
  apply move_run_eq (base 760) L760.rmsb _ _ u x []
  have clean : ∀ q ∈ L760.carry.take 254, (pullState (Equiv.swap (base 760) L760.rmsb) u).basis q = false := by
    intro q hq
    by_cases hq760 : q = base 760
    · subst hq760; simp only [pullState, Equiv.swap_apply_left]; exact hurmsb
    · have hqAway : q ≠ L760.rmsb ∧ q ≠ L760.one := by
        have hchk : (L760.carry.take 254).all (fun z => decide (z ≠ L760.rmsb ∧ z ≠ L760.one)) = true := by decide +kernel
        exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
      simp only [pullState, Equiv.swap_apply_of_ne_of_ne hq760 hqAway.1]
      rw [huEq]
      simp only [Pre, run, writeBit, Function.update_of_ne hqAway.1, Function.update_of_ne hqAway.2]
      exact hcar q (List.mem_of_mem_take hq)
  exact FoldLoanTop.choose_run d false _ x [] clean (mappedAddLoan_760_run_eq d (by omega) _ x [] clean)

private theorem unfoldLoan_760_run_eq (d : Nat) (hd : d ≤ 44) (s : State) (m : List Bool)
    (hlow : s.basis L760.lower = false)
    (hcar : ∀ q ∈ L760.carry, s.basis q = false) :
    ∃ n, run (unfoldLoan d L760) m s = run (P1Life.unfoldStep (base 760) L760) n s := by
  let Pre : Program := [.CX L760.parity L760.lower, .CX L760.rmsb L760.lower, .X L760.lower,
    .CCX L760.parity L760.lower L760.one, .CX L760.lower L760.rmsb,
    .CX L760.parity L760.rmsb, .X L760.rmsb]
  let Post : Program := [.CX L760.lower L760.rmsb, .CX L760.rmsb L760.lower,
    .measureX L760.one [] [.CZ L760.parity L760.rmsb]]
  let MidP := Q6LifetimeResearch.move (base 760) L760.rmsb
    (FoldLoanTop.choose d L760 true)
  let MidQ := Q6LifetimeResearch.move (base 760) L760.rmsb
    (StairLoan.mappedSubLoan 0 StairLoan.retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one)
  have hP : unfoldLoan d L760 = Pre ++ (MidP ++ Post) := by
    delta unfoldLoan; simp only [Pre, MidP, Post, List.append_assoc]
  have hQ : P1Life.unfoldStep (base 760) L760 = Pre ++ (MidQ ++ Post) := by
    delta P1Life.unfoldStep
    rw [show mappedSub (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one =
        StairLoan.mappedSubLoan 0 StairLoan.retiredRoles (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one from
        (StairLoan.mappedSubLoan_zero _ _ _ _ _).symm]
    simp only [Pre, MidQ, Post, List.append_assoc]
  rw [hP, hQ]
  apply replace_mid Pre MidP MidQ Post s m
  intro x
  refine ⟨[], ?_⟩
  let u := run Pre (m.take (measurementCount Pre)) s
  have huEq : u = run Pre [] s := run_zero_meas Pre (by decide +kernel) _ [] s
  have hurmsb : u.basis L760.rmsb = false := by
    rw [huEq]
    have h1 : L760.parity ≠ L760.lower := by decide +kernel
    have h2 : L760.parity ≠ L760.one := by decide +kernel
    have h3 : L760.parity ≠ L760.rmsb := by decide +kernel
    have h4 : L760.rmsb ≠ L760.lower := by decide +kernel
    have h5 : L760.rmsb ≠ L760.one := by decide +kernel
    have h6 : L760.lower ≠ L760.one := by decide +kernel
    simp only [Pre, run, writeBit, Function.update_self,
      Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
      Function.update_of_ne h1.symm, Function.update_of_ne h2.symm, Function.update_of_ne h3.symm,
      Function.update_of_ne h4.symm, Function.update_of_ne h5.symm, Function.update_of_ne h6.symm, hlow]
    cases s.basis L760.parity <;> cases s.basis L760.rmsb <;> rfl
  apply move_run_eq (base 760) L760.rmsb _ _ u x []
  have clean : ∀ q ∈ L760.carry.take 254, (pullState (Equiv.swap (base 760) L760.rmsb) u).basis q = false := by
    intro q hq
    by_cases hq760 : q = base 760
    · subst hq760; simp only [pullState, Equiv.swap_apply_left]; exact hurmsb
    · have hqAway : q ≠ L760.rmsb ∧ q ≠ L760.one ∧ q ≠ L760.lower := by
        have hchk : (L760.carry.take 254).all (fun z => decide (z ≠ L760.rmsb ∧ z ≠ L760.one ∧ z ≠ L760.lower)) = true := by decide +kernel
        exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
      simp only [pullState, Equiv.swap_apply_of_ne_of_ne hq760 hqAway.1]
      rw [huEq]
      simp only [Pre, run, writeBit, Function.update_of_ne hqAway.1, Function.update_of_ne hqAway.2.1,
        Function.update_of_ne hqAway.2.2]
      exact hcar q (List.mem_of_mem_take hq)
  exact FoldLoanTop.choose_run d true _ x [] clean (mappedSubLoan_760_run_eq d (by omega) _ x [] clean)

private theorem shortConstAddLoan_760_move_run_eq (d : Nat) (hd : d ≤ 44)
    (k : Nat) (hk : k / 8 < 2 ^ 252) (s : State) (m : List Bool)
    (hrmsb : s.basis L760.rmsb = false) (hone : s.basis L760.one = false)
    (hpar : s.basis L760.parity = false) (hcar : ∀ q ∈ L760.carry, s.basis q = false) :
    ∃ n, run (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 k)) m s =
      run (Q6LifetimeResearch.move (base 760) L760.rmsb (P1Life.shortConstAdd L760 k)) n s := by
  refine ⟨[], ?_⟩
  have h0 : P1Life.shortConstAdd L760 k = shortConstAddLoan 0 L760 k := by
    rw [short_zero]
    delta P1Life.shortConstAdd previousShort
    simp [StairLoan.literalConstAddLoan]
  rw [h0]
  apply move_run_eq (base 760) L760.rmsb _ _ s m []
  apply shortConstAddLoan_run_eq d hd k hk (pullState (Equiv.swap (base 760) L760.rmsb) s) m []
  · intro q hq
    by_cases hq760 : q = base 760
    · subst hq760; simp only [pullState, Equiv.swap_apply_left]; exact hrmsb
    · have hqne : q ≠ L760.rmsb := by
        have hchk : L760.carry.all (fun z => decide (z ≠ L760.rmsb)) = true := by decide +kernel
        exact of_decide_eq_true (List.all_eq_true.mp hchk q hq)
      simp only [pullState, Equiv.swap_apply_of_ne_of_ne hq760 hqne]
      exact hcar q hq
  · simp only [pullState, Equiv.swap_apply_of_ne_of_ne (by decide : L760.one ≠ base 760) (by decide : L760.one ≠ L760.rmsb)]; exact hone
  · simp only [pullState, Equiv.swap_apply_of_ne_of_ne (by decide : L760.parity ≠ base 760) (by decide : L760.parity ≠ L760.rmsb)]; exact hpar

private theorem compareBlockLoan_760_eq_p1 (d : Nat) (hd : d ≤ 44) (fwd : Bool)
    (s : State) (m : List Bool)
    (oneZero : s.basis L760.one = false)
    (carryZero : ∀ q ∈ L760.carry, s.basis q = false)
    (lowerZero : s.basis L760.lower = false)
    (flag : fwd = true → s.basis L760.parity = decide (regValue L760.r s.basis < regValue L760.y s.basis)) :
    ∃ n, run (compareBlockLoan d fwd L760) m s = run (P1Life.compare (base 760) fwd L760) n s := by
  refine ⟨[], ?_⟩
  have h0 : P1Life.compare (base 760) fwd L760 = compareBlockLoan 0 fwd L760 := by
    delta P1Life.compare compareBlockLoan; dsimp only
    rw [StairLoan.compareLoan_zero]
  rw [h0]
  exact compareBlockLoan_760_run_eq d (by omega) fwd s m [] oneZero carryZero lowerZero flag

private theorem rawSubLoan_760_run_eq (d : Nat) (hd : d ≤ 44)
    (origin : BasisState) (B : Bool) (R Y : Int)
    (hr : P1Life.OddDomain R) (hy : P1Life.OddDomain Y) (hsign : origin L760.sign = B)
    (s : State) (m : List Bool)
    (hraw : DirectPass.AfterRaw DirectPass.standardEncoding L760 (base 760) origin (P1Life.oddSum B R Y) Y s.basis)
    (hcar : ∀ q ∈ L760.carry, s.basis q = false) :
    ∃ n, run (rawSubLoan d L760) m s = run (P1Life.rawSub (base 760) L760) n s := by
  let xs := GuardCompression.source L760
  let ys := BalancedCircuit.rawTarget L760
  let cs := (Q6Structural.q6Carry L760).take 255
  let a := xs.getD 0 0
  let b := ys.getD 0 0
  let c := cs.getD 0 0
  let Pre := signComplement L760.sign L760.y ++ notRegister ys ++ orMajor a b c ++ [.X b, .CX L760.parity b]
  let Post := [.CX L760.parity b, .X b] ++ orErase a b c ++ [.CX a b, .X b] ++
    notRegister ys ++ signComplement L760.sign L760.y ++
    [.CX b L760.parity, .CX (L760.ylow.getD 0 0) L760.parity, .CX L760.sign L760.parity,
     .X L760.parity, .CX L760.rmsb L760.one]
  let MidP := Q6LifetimeResearch.move (base 760) b
    (StairLoan.addTopLoan d StairLoan.retiredRoles (xs.drop 1) (ys.drop 1) (cs.drop 1) c)
  let MidQ := Q6LifetimeResearch.move (base 760) b
    (StairLoan.addTopLoan 0 StairLoan.retiredRoles (xs.drop 1) (ys.drop 1) (cs.drop 1) c)
  have hP : rawSubLoan d L760 = Pre ++ (MidP ++ Post) := by
    delta rawSubLoan; simp only [Pre, MidP, Post, xs, ys, cs, a, b, c, List.append_assoc]
  have hQ : P1Life.rawSub (base 760) L760 = Pre ++ (MidQ ++ Post) := by
    delta P1Life.rawSub; dsimp only
    rw [show Q6LifetimeResearch.addTop (xs.drop 1) (ys.drop 1) (cs.drop 1) c =
        StairLoan.addTopLoan 0 StairLoan.retiredRoles (xs.drop 1) (ys.drop 1) (cs.drop 1) c from
        (StairLoan.addTopLoan_zero _ _ _ _ _).symm]
    simp only [Pre, MidQ, Post, xs, ys, cs, a, b, c, orMajor, orErase, P1Life.orMajor, P1Life.orErase, List.append_assoc]
  rw [hP, hQ]
  apply replace_mid Pre MidP MidQ Post s m
  intro x
  refine ⟨[], ?_⟩
  let u := run Pre (m.take (measurementCount Pre)) s
  have hPreM : measurementCount Pre = 0 := by
    have h1 := (signComplement_counts L760.sign L760.y).2
    have h2 := (notRegister_counts ys).2
    have h3 : measurementCount (orMajor a b c) = 0 := by decide +kernel
    have h4 : measurementCount [.X b, .CX L760.parity b] = 0 := by decide +kernel
    simp only [Pre, measurementCount_append, h1, h2, h3, h4]
  have huEq : u = run [.X b, .CX L760.parity b] []
      (run (orMajor a b c) [] (run (notRegister ys) [] (run (signComplement L760.sign L760.y) [] s))) := by
    dsimp only [u]
    rw [run_zero_meas Pre hPreM _ [],
        show Pre = signComplement L760.sign L760.y ++ notRegister ys ++ orMajor a b c ++ [.X b, .CX L760.parity b] from rfl,
        run_append, run_append, run_append]
    simp [List.take_nil, List.drop_nil]
  have hyND : L760.y.Nodup := PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hysND : ys.Nodup := PeakNodup.nodup_of_mask _ (by decide +kernel)
  have hsignY : L760.sign ∉ L760.y := by decide +kernel
  let st1 := run (signComplement L760.sign L760.y) [] s
  let st2 := run (notRegister ys) [] st1
  let st3 := run (orMajor a b c) [] st2
  have hst1 (q : Wire) : st1.basis q = if q ∈ L760.y then s.basis q ^^ s.basis L760.sign else s.basis q :=
    GuardCompression.complement_bit L760.sign L760.y hyND hsignY s [] q
  have hst2 (q : Wire) : st2.basis q = if q ∈ ys then !st1.basis q else st1.basis q :=
    congrFun (congrArg State.basis (notRegister_correct ys hysND st1 [])) q
  have hst3_away (q : Wire) (hqc : q ≠ c) : st3.basis q = st2.basis q := by
    have hab : a ≠ b := by decide +kernel
    have hac : a ≠ c := by decide +kernel
    have hbc : b ≠ c := by decide +kernel
    by_cases hqa : q = a
    · subst hqa; simp [st3, orMajor, run, writeBit, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
    · by_cases hqb : q = b
      · subst hqb; simp [st3, orMajor, run, writeBit, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
      · simp [st3, orMajor, run, writeBit, hqa, hqb, hqc]
  have hu_away (q : Wire) (hqb : q ≠ b) : u.basis q = st3.basis q := by
    rw [huEq]; simp [st3, st2, st1, run, writeBit, hqb]
  have hpar_eq_b : s.basis L760.parity = s.basis b := by
    have tlen : ys.length = 257 := by decide +kernel
    have htd : signedRegValue ys s.basis = P1Life.oddSum B R Y := by
      unfold signedRegValue; rw [tlen, hraw.1]
      have ht := P1Life.oddSum_signed B R Y hr hy
      exact decode_encodeWord 257 (by decide) _ ht
    have hbit : s.basis L760.r0 = originalParity (P1Life.oddSum B R Y) := by
      apply word_parity L760.r0 (L760.rtail ++ [L760.rmsb, L760.one]) s.basis _
      simpa only [ys, BalancedCircuit.rawTarget, BalancedCleanup.Layout.r, BalancedCleanup.Layout.low,
        List.cons_append, List.append_assoc, List.singleton_append] using htd
    exact hraw.2.2.1.trans hbit.symm
  have hu_b : u.basis b = false := by
    rw [huEq]
    have hpb : L760.parity ≠ b := by decide +kernel
    have hpc : L760.parity ≠ c := by decide +kernel
    have hbc : b ≠ c := by decide +kernel
    have hbYs : b ∈ ys := by decide +kernel
    have hpYs : L760.parity ∉ ys := by decide +kernel
    have hbY : b ∉ L760.y := by decide +kernel
    have hpY : L760.parity ∉ L760.y := by decide +kernel
    change (run [.X b, .CX L760.parity b] [] st3).basis b = false
    simp only [run, writeBit, Function.update_self, Function.update_of_ne hpb]
    rw [hst3_away b hbc, hst3_away L760.parity hpc, hst2 b, hst2 L760.parity,
        if_pos hbYs, if_neg hpYs, hst1 b, hst1 L760.parity, if_neg hbY, if_neg hpY, hpar_eq_b]
    cases s.basis b <;> rfl
  have hclean_u : ∀ (q : Nat), q ∈ cs.drop 1 ++ [L760.carry.getD 255 0] →
      (pullState (Equiv.swap (base 760) b) u).basis q = false := by
    intro q hq
    have hlast : (L760.carry.getD 255 0 : Nat) = 1042 := by decide +kernel
    have hq_rng : (529 ≤ q ∧ q < 781) ∨ q = 1556 ∨ q = 1813 ∨ q = 1042 := by
      simp only [List.mem_append, List.mem_singleton, hlast] at hq
      rcases hq with h1 | rfl
      · have h1' := (mem_q6Carry255_drop1_iff q).mp h1
        rcases h1' with a | b | c'
        · exact Or.inl a
        · exact Or.inr (Or.inl b)
        · exact Or.inr (Or.inr (Or.inl c'))
      · exact Or.inr (Or.inr (Or.inr rfl))
    by_cases hq760 : q = base 760
    · subst hq760; simp only [pullState, Equiv.swap_apply_left]; exact hu_b
    · have hb_val : (b : Nat) = 2072 := rfl
      have hc_val : (c : Nat) = 528 := by decide +kernel
      have hqb : q ≠ b := by rw [hb_val]; omega
      have hqc : q ≠ c := by rw [hc_val]; omega
      have hqy : q ∉ L760.y := by rw [mem_L760_y_iff]; omega
      have hqys : q ∉ ys := by
        simp only [ys, BalancedCircuit.rawTarget, List.mem_append, List.mem_singleton, mem_L760_r_iff]
        have ho_val : (L760.one : Nat) = 1043 := rfl
        rw [ho_val]; omega
      simp only [pullState, Equiv.swap_apply_of_ne_of_ne hq760 hqb]
      rw [hu_away q hqb, hst3_away q hqc, hst2 q, if_neg hqys, hst1 q, if_neg hqy]
      by_cases hlo : q = L760.lower
      · rw [hlo]; exact hraw.2.2.2.1
      · have hlo_val : (L760.lower : Nat) = 1813 := rfl
        rw [hlo_val] at hlo
        exact hcar q ((mem_L760_carry_iff q).mpr (by omega))
  apply move_run_eq (base 760) b _ _ u x []
  apply addTopLoan_760_run_eq d (by omega) (pullState (Equiv.swap (base 760) b) u) x [] hclean_u
  -- Post-condition: after `addInPlace` on `v0 = pullState (swap (base 760) b) u`, `L760.one = L760.rmsb`.
  let v0 := pullState (Equiv.swap (base 760) b) u
  have hmv : ∀ (ws : List Wire) (bs : BasisState), mappedValue (mappedRead ws false) bs = regValue ws bs := by
    intro ws bs; induction ws with
    | nil => rfl
    | cons w ws ih =>
      have hstep : mappedValue (mappedRead (w :: ws) false) bs =
          (bs w).toNat + 2 * mappedValue (mappedRead ws false) bs := by
        simp [mappedRead, mappedValue, MappedBit.value]
      have hreg : regValue (w :: ws) bs = (if bs w = true then 1 else 0) + 2 * regValue ws bs := rfl
      rw [hstep, hreg, ih]; cases bs w <;> simp
  have hadd_eq : ∀ (bs as cs : List Wire) (cin : Wire),
      as.length = bs.length → cs.length + 1 = bs.length →
      addInPlace as bs cs cin = mappedAdd (mappedRead as false) bs cs cin := by
    intro bs
    induction bs with
    | nil =>
      intro as cs cin _ hc; simp at hc
    | cons b bs ih =>
      intro as cs cin ha hc
      cases as with
      | nil => simp at ha
      | cons a as =>
        cases bs with
        | nil =>
          cases as with
          | cons _ _ => simp at ha
          | nil =>
            cases cs with
            | cons _ _ => simp at hc
            | nil => rfl
        | cons b2 bs2 =>
          cases as with
          | nil => simp at ha
          | cons a2 as2 =>
            cases cs with
            | nil => simp at hc
            | cons c cs =>
              simp only [addInPlace, mappedAdd, mappedRead, List.map_cons,
                mappedMajority, mappedEraseCarry, mappedSum]
              rw [ih (a2 :: as2) cs c (by simpa using ha) (by simpa using hc)]
              rfl
  have hnd_add : (c :: ((L760.low.drop 1 ++ [L760.rmsb, L760.one]) ++
      (cs.drop 1 ++ [L760.carry.getD 255 0]))).Nodup :=
    PeakNodup.nodup_of_mask _ (by decide +kernel)
  have haway_add : ∀ (q : Nat), q ∈ mappedWires (mappedRead (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) false) →
      q ∉ c :: ((L760.low.drop 1 ++ [L760.rmsb, L760.one]) ++ (cs.drop 1 ++ [L760.carry.getD 255 0])) := by
    intro q hq
    have hw := mem_mappedWires_read _ q hq
    have hqy_rng : 786 ≤ q ∧ q < 1042 := by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hdrop | rfl | rfl
      · exact (mem_L760_y_iff q).mp (List.mem_append_left _ (List.mem_of_mem_drop hdrop))
      · have hy_val : (L760.ymsb : Nat) = 1041 := rfl; rw [hy_val]; omega
      · have hy_val : (L760.ymsb : Nat) = 1041 := rfl; rw [hy_val]; omega
    have hlast : (L760.carry.getD 255 0 : Nat) = 1042 := by decide +kernel
    have hc_val : (c : Nat) = 528 := by decide +kernel
    have hrm_val : (L760.rmsb : Nat) = 2327 := rfl
    have ho_val : (L760.one : Nat) = 1043 := rfl
    rw [hlast]
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    rintro (rfl | ((hlow | rfl | rfl) | (hcar | rfl)))
    · rw [hc_val] at hqy_rng; omega
    · have hrr := (mem_L760_r_iff q).mp (List.mem_append_left _ (List.mem_of_mem_drop hlow)); omega
    · rw [hrm_val] at hqy_rng; omega
    · rw [ho_val] at hqy_rng; omega
    · have hcar' := (mem_q6Carry255_drop1_iff q).mp hcar; omega
    · omega
  have hmc := mappedAdd_correct (mappedRead (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) false)
    (L760.low.drop 1 ++ [L760.rmsb, L760.one]) (cs.drop 1 ++ [L760.carry.getD 255 0]) c
    hnd_add haway_add (by decide +kernel) (by decide +kernel) v0 [] hclean_u
  rw [hadd_eq _ _ _ _ (by decide +kernel) (by decide +kernel)]
  have hrv : regValue (L760.low.drop 1 ++ [L760.rmsb, L760.one])
      (run (mappedAdd (mappedRead (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) false)
        (L760.low.drop 1 ++ [L760.rmsb, L760.one]) (cs.drop 1 ++ [L760.carry.getD 255 0]) c) [] v0).basis =
      (regValue (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) v0.basis +
       regValue (L760.low.drop 1 ++ [L760.rmsb, L760.one]) v0.basis + (v0.basis c).toNat) % 2 ^ 256 := by
    rw [hmc.2.2, hmv]; rfl
  apply DirectPass.extended_bits (L760.low.drop 1) L760.rmsb L760.one _
  rw [show (L760.low.drop 1).length = 254 by decide +kernel, hrv]
  -- Relate v0 on xs.drop 1, ys.drop 1, c back to st2
  have hv0_xs : regValue (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) v0.basis =
      regValue (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) st2.basis := by
    apply regValue_congr; intro q hq
    have hchk : (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]).all
        (fun z => decide (z ≠ base 760 ∧ z ≠ b ∧ z ≠ c)) = true := by decide +kernel
    have hf := of_decide_eq_true (List.all_eq_true.mp hchk q hq)
    simp only [v0, pullState, Equiv.swap_apply_of_ne_of_ne hf.1 hf.2.1]
    rw [hu_away q hf.2.1, hst3_away q hf.2.2]
  have hv0_ys : regValue (L760.low.drop 1 ++ [L760.rmsb, L760.one]) v0.basis =
      regValue (L760.low.drop 1 ++ [L760.rmsb, L760.one]) st2.basis := by
    apply regValue_congr; intro q hq
    have hchk : (L760.low.drop 1 ++ [L760.rmsb, L760.one]).all
        (fun z => decide (z ≠ base 760 ∧ z ≠ b ∧ z ≠ c)) = true := by decide +kernel
    have hf := of_decide_eq_true (List.all_eq_true.mp hchk q hq)
    simp only [v0, pullState, Equiv.swap_apply_of_ne_of_ne hf.1 hf.2.1]
    rw [hu_away q hf.2.1, hst3_away q hf.2.2]
  have hv0_c : v0.basis c = carryBit (st2.basis a) (st2.basis b) true := by
    have hcb : c ≠ b := by decide +kernel
    have hc760 : c ≠ base 760 := by decide +kernel
    have hcYs : c ∉ ys := by decide +kernel
    have hcY : c ∉ L760.y := by decide +kernel
    have hc0 : st2.basis c = false := by
      rw [hst2 c, if_neg hcYs, hst1 c, if_neg hcY]
      exact hcar c (by decide +kernel)
    simp only [v0, pullState, Equiv.swap_apply_of_ne_of_ne hc760 hcb]
    rw [hu_away c hcb]
    have hab : a ≠ b := by decide +kernel
    have hac : a ≠ c := by decide +kernel
    have hbc : b ≠ c := by decide +kernel
    change (run (orMajor a b c) [] st2).basis c = _
    have hc_run : (run (orMajor a b c) [] st2).basis c =
        !((st2.basis c) ^^ ((!st2.basis a) && (!st2.basis b))) := by
      simp [orMajor, run, writeBit, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
    rw [hc_run, hc0]
    cases st2.basis a <;> cases st2.basis b <;> rfl
  rw [hv0_xs, hv0_ys, hv0_c]
  have hxs_split : xs = a :: (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) := by decide +kernel
  have hys_split : ys = b :: (L760.low.drop 1 ++ [L760.rmsb, L760.one]) := by decide +kernel
  have hsum_st2 : (regValue xs st2.basis + regValue ys st2.basis + 1) % 2 ^ 257 =
      2 ^ 257 - 1 - encodeWord 257 R := by
    have hsign_s : s.basis L760.sign = B := by
      have haway : L760.sign ∉ ys ∧ L760.sign ≠ L760.parity ∧ L760.sign ≠ L760.lower ∧ L760.sign ≠ L760.one := by
        decide +kernel
      have hnr : L760.sign ∉ L760.r := by decide +kernel
      exact (hraw.2.2.2.2.2 L760.sign hnr haway.2.1 haway.2.2.1 haway.2.2.2).trans hsign
    have hgen : ∀ (ws : List Wire) (b1 b2 : BasisState),
        (∀ q ∈ ws, b1 q = !b2 q) → regValue ws b1 = 2 ^ ws.length - 1 - regValue ws b2 := by
      intro ws b1 b2 hf
      induction ws with
      | nil => simp [regValue]
      | cons w ws ih =>
        have hlt := regValue_lt ws b2
        have ih' := ih (fun q hq => hf q (List.mem_cons_of_mem w hq))
        have hw0 := hf w (List.mem_cons_self ..)
        change (if b1 w = true then 1 else 0) + 2 * regValue ws b1 =
          2 ^ (ws.length + 1) - 1 - ((if b2 w = true then 1 else 0) + 2 * regValue ws b2)
        rw [ih', hw0, Nat.pow_succ]
        cases b2 w <;> simp <;> omega
    have hst2_ys : regValue ys st2.basis = 2 ^ 257 - 1 - encodeWord 257 (P1Life.oddSum B R Y) := by
      have hst1_ys : regValue ys st1.basis = regValue ys s.basis := by
        apply regValue_congr; intro (q : Nat) hq
        have hny : q ∉ L760.y := by
          simp only [ys, BalancedCircuit.rawTarget, List.mem_append, List.mem_singleton, mem_L760_r_iff] at hq
          rw [mem_L760_y_iff]
          rcases hq with hr | rfl
          · omega
          · have ho_val : (L760.one : Nat) = 1043 := rfl; rw [ho_val]; omega
        rw [hst1 q, if_neg hny]
      have hflip := hgen ys st2.basis st1.basis (fun q hq => by rw [hst2 q, if_pos hq])
      have hlen_ys : ys.length = 257 := by decide +kernel
      rw [hflip, hlen_ys, hst1_ys, hraw.1]; rfl
    have hst2_xs : regValue xs st2.basis =
        if B then 2 ^ 257 - 1 - encodeWord 257 Y else encodeWord 257 Y := by
      have hxs_in_y : ∀ (q : Nat), q ∈ xs → q ∈ L760.y := by
        intro q hq
        have hxs_def : xs = L760.y ++ [L760.ymsb] := rfl
        rw [hxs_def, List.mem_append, List.mem_singleton] at hq
        rcases hq with hqy | hlast
        · exact hqy
        · rw [hlast, mem_L760_y_iff]; have hy_val : (L760.ymsb : Nat) = 1041 := rfl; rw [hy_val]; omega
      have hst2_eq_st1 : regValue xs st2.basis = regValue xs st1.basis := by
        apply regValue_congr; intro (q : Nat) hq
        have hnys : q ∉ ys := by
          have hy := (mem_L760_y_iff q).mp (hxs_in_y q hq)
          simp only [ys, BalancedCircuit.rawTarget, List.mem_append, List.mem_singleton, mem_L760_r_iff]
          rintro (hr | rfl)
          · omega
          · have ho_val : (L760.one : Nat) = 1043 := rfl; rw [ho_val] at hy; omega
        rw [hst2 q, if_neg hnys]
      rw [hst2_eq_st1]
      have hsrc_s : regValue xs s.basis = encodeWord 257 Y := by
        have widths := BalancedCleanup.widths L760.toLayout hw760
        have yd : signedRegValue L760.y s.basis = Y := by
          unfold signedRegValue; rw [widths.2.2.1, hraw.2.1]
          exact decode_encodeWord 256 (by decide) Y (P1Life.oddDomain_signed Y hy)
        have sd : signedRegValue xs s.basis = Y :=
          (signed_extension L760.ylow L760.ymsb L760.ymsb s.basis rfl).trans yd
        exact word_encoding xs 257 (by decide +kernel) s.basis Y sd
      cases hB : B
      · rw [if_neg Bool.false_ne_true, ← hsrc_s]
        apply regValue_congr; intro q hq
        rw [hst1 q, hsign_s, hB]; split_ifs <;> simp
      · rw [if_pos rfl, ← hsrc_s]
        have hcomp : ∀ q ∈ xs, st1.basis q = !s.basis q := by
          intro q hq
          rw [hst1 q, if_pos (hxs_in_y q hq), hsign_s, hB]
          simp
        simpa only [show xs.length = 257 by decide +kernel] using hgen xs st1.basis s.basis hcomp
    have hadd := P1Life.oddSum_encoded 257 B R Y
    have hltR : encodeWord 257 R < 2 ^ 257 := encodeWord_bound 257 R
    have hltT : encodeWord 257 (P1Life.oddSum B R Y) < 2 ^ 257 := encodeWord_bound 257 _
    have hltY : encodeWord 257 Y < 2 ^ 257 := encodeWord_bound 257 Y
    rw [hst2_xs, hst2_ys]
    cases B <;> simp only [Bool.false_eq_true, if_false, if_true] at hadd ⊢ <;> omega
  have hext_comp : DirectPass.Extended 255 (2 ^ 257 - 1 - encodeWord 257 R) := by
    have heR := DirectPass.encoded_extended 255 R (P1Life.oddDomain_signed R hr)
    have hltR := encodeWord_bound 257 R
    rw [show (255 : Nat) + 2 = 257 from rfl] at heR
    unfold DirectPass.Extended at heR ⊢
    omega
  apply DirectPass.extended_tail (st2.basis a) (st2.basis b) true
    (regValue (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) st2.basis)
    (regValue (L760.low.drop 1 ++ [L760.rmsb, L760.one]) st2.basis) 254
  have hcons : ∀ (bs : BasisState) (w : Wire) (ws : List Wire),
      regValue (w :: ws) bs = (bs w).toNat + 2 * regValue ws bs := by
    intro bs w ws; simp [regValue, Bool.toNat]
  have hxs_val : regValue xs st2.basis =
      (st2.basis a).toNat + 2 * regValue (L760.ylow.drop 1 ++ [L760.ymsb, L760.ymsb]) st2.basis := by
    rw [hxs_split]; exact hcons _ _ _
  have hys_val : regValue ys st2.basis =
      (st2.basis b).toNat + 2 * regValue (L760.low.drop 1 ++ [L760.rmsb, L760.one]) st2.basis := by
    rw [hys_split]; exact hcons _ _ _
  simpa only [← hxs_val, ← hys_val, Bool.toNat_true, hsum_st2] using hext_comp

private theorem carry_all_zero_of_afterHalf (origin : BasisState)
    (horig : ∀ q ∈ L760.carry, origin q = false) (b : BasisState)
    (hclean : DirectPass.CleanExcept (L760.carry.take 254) (base 760) b)
    (hframe : DirectPass.HalfOutside L760 origin b) :
    ∀ q ∈ L760.carry, b q = false :=
  carry_all_zero_of_outside origin horig b hclean hframe
    ((hframe (base 760) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      (horig (base 760) (by decide +kernel)))

private theorem compare_after_prepare_run_eq (d : Nat) (hd : d ≤ 44) (fwd : Bool)
    (U Y : Int) (B Neg : Bool)
    (hu_b : -((2 ^ 254 : Nat) : Int) ≤ U ∧ U < ((2 ^ 254 : Nat) : Int))
    (hy_b : -((2 ^ 255 : Nat) : Int) ≤ Y ∧ Y < ((2 ^ 255 : Nat) : Int))
    (u0 : State) (m x : List Bool)
    (hrv : regValue L760.r u0.basis = encodeWord 255 U)
    (hyu : regValue L760.y u0.basis = encodeWord 256 Y)
    (hsign : u0.basis L760.sign = B)
    (hlower : u0.basis L760.lower = Neg)
    (hone : u0.basis L760.one = false)
    (hcar0 : ∀ q ∈ L760.carry, u0.basis q = false)
    (hpar : fwd = true → u0.basis L760.parity =
      DirectPass.comparisonPredicate true B Neg U Y) :
    ∃ y, run (compareBlockLoan d fwd L760) x
        (run (P1Life.prepareCompare L760 ++ P1Life.exposure L760) m u0) =
      run (P1Life.compare (base 760) fwd L760) y
        (run (P1Life.prepareCompare L760 ++ P1Life.exposure L760) m u0) := by
  let n0 : L760.toLayout.wires.Nodup := (List.nodup_append'.mp hn760).2.1
  have hpc_eq : P1Life.prepareCompare L760 = DirectPass.comparePrepareMode true L760.toLayout := rfl
  have hex_eq : P1Life.exposure L760 = DirectPass.compareExposeMode true L760 := rfl
  have hp0 : measurementCount (P1Life.prepareCompare L760) = 0 :=
    properProgram_measurementCount _ (DirectPass.prepare_compare_proper_mode true L760.toLayout n0)
  have he0 : measurementCount (P1Life.exposure L760) = 0 := by decide +kernel
  rw [run_append, run_zero_meas (P1Life.prepareCompare L760) hp0 _ [],
      run_zero_meas (P1Life.exposure L760) he0 _ []]
  have hvals := DirectPass.prepare_compare_value_mode true L760.toLayout hw760 n0
    U Y B Neg hu_b hy_b u0 [] hrv hyu hsign hlower
  have hrel := DirectPass.prepare_compare_low_mode true L760.toLayout hw760 n0
    U Y B Neg hu_b hy_b u0 [] hrv hyu hsign hlower
  rw [← hpc_eq] at hvals hrel
  generalize hu1_def : run (P1Life.prepareCompare L760) [] u0 = u1
  rw [hu1_def] at hvals hrel
  have hu1_sign : u1.basis L760.sign = B :=
    (hvals.2.2 L760.sign (not_mem_L760_r_of_eq 2425 rfl (by omega))
      (not_mem_L760_y_of_eq 2425 rfl (by omega))).trans hsign
  have hu1_low : u1.basis L760.lower = Neg :=
    (hvals.2.2 L760.lower (not_mem_L760_r_of_eq 1813 rfl (by omega))
      (not_mem_L760_y_of_eq 1813 rfl (by omega))).trans hlower
  have hexp := DirectPass.expose_correct_mode true L760 (by decide +kernel) (by decide +kernel)
    u1 [] B Neg hu1_sign hu1_low hrel
  rw [← hex_eq] at hexp
  generalize hu2_def : run (P1Life.exposure L760) [] u1 = u2
  rw [hu2_def] at hexp
  have hu2_one : u2.basis L760.one = false :=
    (hexp.2.2 L760.one L760_one_ne_lower).trans
      ((hvals.2.2 L760.one (not_mem_L760_r_of_eq 1043 rfl (by omega))
        (not_mem_L760_y_of_eq 1043 rfl (by omega))).trans hone)
  have hu2_car : ∀ q ∈ L760.carry, u2.basis q = false := by
    intro q hq
    have hf := L760_carry_away q hq
    exact (hexp.2.2 q hf.1).trans ((hvals.2.2 q hf.2.1 hf.2.2).trans (hcar0 q hq))
  refine compareBlockLoan_760_eq_p1 d hd fwd u2 x hu2_one hu2_car hexp.2.1 ?_
  intro hfwd
  have hp_keep : u2.basis L760.parity = DirectPass.comparisonPredicate true B Neg U Y :=
    (hexp.2.2 L760.parity L760_parity_ne_lower).trans
      ((hvals.2.2 L760.parity (not_mem_L760_r_of_eq 784 rfl (by omega))
        (not_mem_L760_y_of_eq 784 rfl (by omega))).trans (hpar hfwd))
  have hvr : (regValue L760.r u2.basis : Int) =
      DirectPass.compareLeftValue true B Neg U + ((2 ^ 255 : Nat) : Int) := by
    rw [regValue_congr L760.r u2.basis u1.basis (fun q hq =>
      hexp.2.2 q (fun heq => by
        have h := (mem_L760_r_iff q).mp hq
        have hl : (L760.lower : Nat) = 1813 := rfl
        rw [heq, hl] at h; omega))]
    exact hvals.1
  have hvy : (regValue L760.y u2.basis : Int) =
      DirectPass.compareViewedValue B Neg Y + ((2 ^ 255 : Nat) : Int) := by
    rw [regValue_congr L760.y u2.basis u1.basis (fun q hq =>
      hexp.2.2 q (fun heq => by
        have h := (mem_L760_y_iff q).mp hq
        have hl : (L760.lower : Nat) = 1813 := rfl
        rw [heq, hl] at h; omega))]
    exact hvals.2.1
  have hiff : regValue L760.r u2.basis < regValue L760.y u2.basis ↔
      DirectPass.compareLeftValue true B Neg U < DirectPass.compareViewedValue B Neg Y := by
    rw [← Int.ofNat_lt, hvr, hvy]
    exact Int.add_lt_add_iff_right _
  rw [hp_keep]
  simp only [DirectPass.comparisonPredicate, if_true]
  exact (decide_eq_decide.mpr hiff).symm

theorem forwardLoan_760_run_eq (d : Nat) (hd : d ≤ 44)
    (origin : BasisState) (horig : ∀ q ∈ L760.carry, origin q = false)
    (R Y : Int) (hr : P1Life.OddDomain R) (hy : P1Life.OddDomain Y)
    (s : State) (m : List Bool)
    (hs : DirectPass.AfterHalf L760 (base 760) origin R Y s.basis) :
    ∃ n, run (forwardLoan d L760) m s = run (P1Life.forward (base 760) L760) n s := by
  let T := P1Life.oddSum (origin L760.sign) R Y
  have ht := P1Life.oddSum_bounds (origin L760.sign) R Y hr hy
  have hf := P1Life.oddFold_bounds T ht
  have mt : base 760 ∈ L760.carry.take 254 := List.mem_of_mem_drop mem760
  have hshapeP : forwardLoan d L760 =
      P1Life.p1Seed L760 ++ (rawAddLoan d L760 ++
        (OneReuse.newPrepare L760 ++ rotateRight (BalancedCircuit.rawTarget L760) ++
          (foldLoan d L760 ++
            (BalancedCleanup.prepareSign L760.toLayout ++ BiasedCircuit.flipBias L760 ++
              P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
              (compareBlockLoan d true L760 ++
                ((P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
                  (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 h.toNat) ++
                    (BalancedCleanup.prepareSign L760.toLayout).reverse))))))) := by
    delta forwardLoan; simp only [p1Seed_eq, prepareCompare_eq, exposure_eq, List.append_assoc]
  rw [hshapeP]
  -- Step 1: replace `rawAddLoan d L760` with `P1Life.rawAdd (base 760) L760`
  have h1 : ∃ n1, run (P1Life.p1Seed L760 ++ (rawAddLoan d L760 ++
        (OneReuse.newPrepare L760 ++ rotateRight (BalancedCircuit.rawTarget L760) ++
          (foldLoan d L760 ++
            (BalancedCleanup.prepareSign L760.toLayout ++ BiasedCircuit.flipBias L760 ++
              P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
              (compareBlockLoan d true L760 ++
                ((P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
                  (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 h.toNat) ++
                    (BalancedCleanup.prepareSign L760.toLayout).reverse)))))))) m s =
      run (P1Life.p1Seed L760 ++ (P1Life.rawAdd (base 760) L760 ++
        (OneReuse.newPrepare L760 ++ rotateRight (BalancedCircuit.rawTarget L760) ++
          (foldLoan d L760 ++
            (BalancedCleanup.prepareSign L760.toLayout ++ BiasedCircuit.flipBias L760 ++
              P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
              (compareBlockLoan d true L760 ++
                ((P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
                  (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 h.toNat) ++
                    (BalancedCleanup.prepareSign L760.toLayout).reverse)))))))) n1 s := by
    apply replace_mid
    intro x
    have hsp := DirectPass.seed_prepare true (base 760) L760 hw760 hn760 mem760 origin R Y
      (P1Life.oddDomain_signed R hr) (P1Life.oddDomain_signed Y hy) s
      (m.take (measurementCount (P1Life.p1Seed L760))) hs
    rcases hsp with ⟨_, htop, hpv, _, _, _, _, hcleanQ, hframe⟩
    have hlow : (run (P1Life.p1Seed L760) (m.take (measurementCount (P1Life.p1Seed L760))) s).basis L760.lower = false :=
      hcleanQ L760.lower (by decide +kernel) (by decide +kernel)
    have hclean254 : DirectPass.CleanExcept (L760.carry.take 254) (base 760)
        (run (P1Life.p1Seed L760) (m.take (measurementCount (P1Life.p1Seed L760))) s).basis := by
      intro q hq hne
      exact hcleanQ q (by rw [DirectPass.active_carry_shape L760 hw760]; exact List.mem_append_left _ hq) hne
    have hcar := carry_all_zero_of_afterHalf origin horig _ hclean254 hframe
    exact rawAddLoan_760_run_eq d hd _ x ⟨htop, hpv⟩ hlow hcar
  obtain ⟨n1, hn1⟩ := h1; rw [hn1]
  -- Step 2: replace `foldLoan d L760` with `P1Life.fold (base 760) L760`
  let A2 := (P1Life.p1Seed L760 ++ P1Life.rawAdd (base 760) L760) ++
    (OneReuse.newPrepare L760 ++ rotateRight (BalancedCircuit.rawTarget L760))
  let B2 := BalancedCleanup.prepareSign L760.toLayout ++ BiasedCircuit.flipBias L760 ++
    P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
    (compareBlockLoan d true L760 ++
      ((P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
        (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 h.toNat) ++
          (BalancedCleanup.prepareSign L760.toLayout).reverse)))
  have h2re : P1Life.p1Seed L760 ++ (P1Life.rawAdd (base 760) L760 ++
        (OneReuse.newPrepare L760 ++ rotateRight (BalancedCircuit.rawTarget L760) ++
          (foldLoan d L760 ++ B2))) = A2 ++ (foldLoan d L760 ++ B2) := by
    simp only [A2, List.append_assoc]
  rw [h2re]
  have htr2 : Triple (DirectPass.AfterHalf L760 (base 760) origin R Y) A2
      (DirectPass.AfterShift L760 (base 760) origin T Y) := by
    have hrng : -((2 ^ 256 : Nat) : Int) ≤ T ∧ T < ((2 ^ 256 : Nat) : Int) := by
      have hp_lt : (p : Int) < ((2 ^ 256 : Nat) : Int) := by decide
      omega
    exact Triple.seq (P1Life.seed_to_raw (base 760) L760 hw760 hn760 mem760 origin R Y hr hy)
      (DirectPass.shift_boundary_full (base 760) L760 hw760 hn760 origin T Y hrng)
  have h2 : ∃ n2, run (A2 ++ (foldLoan d L760 ++ B2)) n1 s =
      run (A2 ++ (P1Life.fold (base 760) L760 ++ B2)) n2 s := by
    apply replace_mid
    intro x
    have hsh := (htr2 s (n1.take (measurementCount A2)) hs).2
    rcases hsh with ⟨_, _, ⟨_, hlow, _⟩, hrmsb, hclean, hframe⟩
    exact foldLoan_760_run_eq d hd _ x (hlow.trans hrmsb.symm)
      (carry_all_zero_of_afterHalf origin horig _ hclean hframe)
  obtain ⟨n2, hn2⟩ := h2; rw [hn2]
  -- Step 3: replace `compareBlockLoan d true L760` with `P1Life.compare (base 760) true L760`
  let A3f := (P1Life.p1Seed L760 ++ P1Life.rawAdd (base 760) L760) ++
    (OneReuse.newPrepare L760 ++ rotateRight (BalancedCircuit.rawTarget L760) ++ P1Life.fold (base 760) L760) ++
    (BalancedCleanup.prepareSign L760.toLayout ++ BiasedCircuit.flipBias L760)
  let Front3 := P1Life.prepareCompare L760 ++ P1Life.exposure L760
  let A3 := A3f ++ Front3
  let B3 := (P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
    (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 h.toNat) ++
      (BalancedCleanup.prepareSign L760.toLayout).reverse)
  have h3re : A2 ++ (P1Life.fold (base 760) L760 ++ B2) = A3 ++ (compareBlockLoan d true L760 ++ B3) := by
    simp only [A2, B2, A3, A3f, Front3, B3, List.append_assoc]
  rw [h3re]
  have htr3f : Triple (DirectPass.AfterHalf L760 (base 760) origin R Y) A3f
      (DirectPass.InverseComparison DirectPass.oddEncoding L760 (base 760) origin T (P1Life.oddFold T) Y) :=
    Triple.seq (Triple.seq (P1Life.seed_to_raw (base 760) L760 hw760 hn760 mem760 origin R Y hr hy)
      (P1Life.raw_to_fold (base 760) L760 hw760 hn760 mt origin T Y ht))
      (P1Life.fold_view (base 760) L760 hw760 hn760 origin T (P1Life.oddFold T) Y hf)
  have h3 : ∃ n3, run (A3 ++ (compareBlockLoan d true L760 ++ B3)) n2 s =
      run (A3 ++ (P1Life.compare (base 760) true L760 ++ B3)) n3 s := by
    apply replace_mid
    intro x
    rw [show A3 = A3f ++ (P1Life.prepareCompare L760 ++ P1Life.exposure L760) from rfl, run_append]
    have hinv := (htr3f s ((n2.take (measurementCount A3)).take (measurementCount A3f)) hs).2
    generalize hu0_def : run A3f ((n2.take (measurementCount A3)).take (measurementCount A3f)) s = u0
    rw [hu0_def] at hinv
    rcases hinv with ⟨hlow, hrmsb, hyu, ⟨hpar, hlower, hone⟩, hclean, hframe⟩
    have hrv : regValue L760.r u0.basis = encodeWord 255 (P1Life.oddNormalized (P1Life.oddFold T)) := by
      change regValue (L760.low ++ [L760.rmsb]) u0.basis = _
      rw [regValue_append, hlow, oddEncoding_norm, regValue_singleton_false _ _ hrmsb, Nat.mul_zero, Nat.add_zero]
    have hsign : u0.basis L760.sign = origin L760.sign :=
      hframe L760.sign (not_mem_L760_r_of_eq 2425 rfl (by omega))
        L760_sign_ne_parity L760_sign_ne_lower L760_sign_ne_one
    have hu_b : -((2 ^ 254 : Nat) : Int) ≤ P1Life.oddNormalized (P1Life.oddFold T) ∧
        P1Life.oddNormalized (P1Life.oddFold T) < ((2 ^ 254 : Nat) : Int) := by
      have hb := P1Life.oddNormalized_bounds (P1Life.oddFold T) hf
      have hc := constants; omega
    have hpar_eq : true = true → u0.basis L760.parity =
        DirectPass.comparisonPredicate true (origin L760.sign) (negative (P1Life.oddFold T))
          (P1Life.oddNormalized (P1Life.oddFold T)) Y := fun _ => by
      rw [hpar, P1Life.odd_comparison_predicate]
      exact P1Life.oddComparison_parity (origin L760.sign) R Y hr hy
    exact compare_after_prepare_run_eq d hd true (P1Life.oddNormalized (P1Life.oddFold T)) Y
      (origin L760.sign) (negative (P1Life.oddFold T)) hu_b (P1Life.oddDomain_signed Y hy)
      u0 _ x hrv hyu hsign hlower hone (carry_all_zero_of_afterHalf origin horig u0.basis hclean hframe) hpar_eq
  obtain ⟨n3, hn3⟩ := h3; rw [hn3]
  -- Step 4: replace `shortConstAddLoan d L760 h.toNat` with `P1Life.shortConstAdd L760 h.toNat`
  let A4 := (P1Life.p1Seed L760 ++ P1Life.rawAdd (base 760) L760) ++
    (OneReuse.newPrepare L760 ++ rotateRight (BalancedCircuit.rawTarget L760) ++ P1Life.fold (base 760) L760) ++
    (BalancedCleanup.prepareSign L760.toLayout ++ BiasedCircuit.flipBias L760 ++
      P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++ P1Life.compare (base 760) true L760 ++
      (P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse)
  let B4 := (BalancedCleanup.prepareSign L760.toLayout).reverse
  have h4re : A3 ++ (P1Life.compare (base 760) true L760 ++ B3) =
      A4 ++ (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 h.toNat) ++ B4) := by
    simp only [A3, A3f, Front3, B3, A4, B4, List.append_assoc]
  rw [h4re]
  have htr4 : Triple (DirectPass.AfterHalf L760 (base 760) origin R Y) A4
      (DirectPass.AfterComparison DirectPass.oddEncoding L760 (base 760) origin (P1Life.oddFold T) Y) :=
    Triple.seq (Triple.seq (P1Life.seed_to_raw (base 760) L760 hw760 hn760 mem760 origin R Y hr hy)
      (P1Life.raw_to_fold (base 760) L760 hw760 hn760 mt origin T Y ht))
      (P1Life.fold_to_comparison (base 760) L760 hw760 hn760 mem760 origin R Y hr hy)
  have h4 : ∃ n4, run (A4 ++ (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 h.toNat) ++ B4)) n3 s =
      run (A4 ++ (Q6LifetimeResearch.move (base 760) L760.rmsb (P1Life.shortConstAdd L760 h.toNat) ++ B4)) n4 s := by
    apply replace_mid
    intro x
    have hc := (htr4 s (n3.take (measurementCount A4)) hs).2
    rcases hc with ⟨_, hrmsb, _, ⟨hpar, _, hone⟩, hclean, hframe⟩
    exact shortConstAddLoan_760_move_run_eq d hd h.toNat (by decide +kernel) _ x hrmsb hone hpar
      (carry_all_zero_of_afterHalf origin horig _ hclean hframe)
  obtain ⟨n4, hn4⟩ := h4
  refine ⟨n4, hn4.trans ?_⟩
  have hQ : A4 ++ (Q6LifetimeResearch.move (base 760) L760.rmsb (P1Life.shortConstAdd L760 h.toNat) ++ B4) =
      P1Life.forward (base 760) L760 := by
    rw [P1Life.forward_chunks]; simp only [A4, B4, List.append_assoc]
  rw [hQ]

theorem inverseLoan_760_run_eq (d : Nat) (hd : d ≤ 44)
    (origin : BasisState) (horig : ∀ q ∈ L760.carry, origin q = false)
    (F Y : Int) (hf : P1Life.OddDomain F) (hy : P1Life.OddDomain Y)
    (s : State) (m : List Bool)
    (hs : DirectPass.AfterHalf L760 (base 760) origin F Y s.basis) :
    ∃ n, run (inverseLoan d L760) m s = run (P1Life.inverse (base 760) L760) n s := by
  let B := origin L760.sign
  let R := P1Life.oddInverse B F Y
  let T := P1Life.oddSum B R Y
  have hr : P1Life.OddDomain R := P1Life.oddRep_bounds _
  have ht := P1Life.oddSum_bounds B R Y hr hy
  have hres : P1Life.oddFold T = F := P1Life.oddForward_inverse B F Y hf hy
  have hival : originalParity T = decide (P1Life.oddComparisonLeft F < P1Life.oddComparisonY B F Y) := by
    have h0 := P1Life.oddComparison_parity B R Y hr hy
    rwa [hres] at h0
  have mt : base 760 ∈ L760.carry.take 254 := List.mem_of_mem_drop mem760
  have hshapeP : inverseLoan d L760 =
      BalancedCleanup.prepareSign L760.toLayout ++
        (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 (encodeWord 255 (-h))) ++
          (P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
            (compareBlockLoan d false L760 ++
              ((P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
                BiasedInverse.unbiasView L760 ++
                (unfoldLoan d L760 ++
                  (rotateLeft (BalancedCircuit.rawTarget L760) ++ [.CX L760.parity L760.r0] ++
                    rawSubLoan d L760)))))) := by
    delta inverseLoan; simp only [prepareCompare_eq, exposure_eq, List.append_assoc]
  rw [hshapeP]
  -- Step 1: shortConstAddLoan
  have h1 : ∃ n1, run (BalancedCleanup.prepareSign L760.toLayout ++
        (Q6LifetimeResearch.move (base 760) L760.rmsb (shortConstAddLoan d L760 (encodeWord 255 (-h))) ++
          (P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
            (compareBlockLoan d false L760 ++
              ((P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
                BiasedInverse.unbiasView L760 ++
                (unfoldLoan d L760 ++
                  (rotateLeft (BalancedCircuit.rawTarget L760) ++ [.CX L760.parity L760.r0] ++
                    rawSubLoan d L760))))))) m s =
      run (BalancedCleanup.prepareSign L760.toLayout ++
        (Q6LifetimeResearch.move (base 760) L760.rmsb (P1Life.shortConstAdd L760 (encodeWord 255 (-h))) ++
          (P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
            (compareBlockLoan d false L760 ++
              ((P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
                BiasedInverse.unbiasView L760 ++
                (unfoldLoan d L760 ++
                  (rotateLeft (BalancedCircuit.rawTarget L760) ++ [.CX L760.parity L760.r0] ++
                    rawSubLoan d L760))))))) n1 s := by
    apply replace_mid
    intro x
    have hu := (P1Life.prepare_sign_odd (base 760) L760 hw760 hn760 origin F Y hf s
      (m.take (measurementCount (BalancedCleanup.prepareSign L760.toLayout))) hs).2
    rcases hu with ⟨_, hrmsb, _, ⟨hpar, _, hone⟩, hclean, hframe⟩
    exact shortConstAddLoan_760_move_run_eq d hd (encodeWord 255 (-h)) (by decide +kernel) _ x hrmsb hone hpar
      (carry_all_zero_of_afterHalf origin horig _ hclean hframe)
  obtain ⟨n1, hn1⟩ := h1; rw [hn1]
  -- Step 2: compareBlockLoan d false L760
  let A2f := BalancedCleanup.prepareSign L760.toLayout ++
    Q6LifetimeResearch.move (base 760) L760.rmsb (P1Life.shortConstAdd L760 (encodeWord 255 (-h)))
  let A2 := A2f ++ (P1Life.prepareCompare L760 ++ P1Life.exposure L760)
  let B2 := (P1Life.exposure L760).reverse ++ (P1Life.prepareCompare L760).reverse ++
    BiasedInverse.unbiasView L760 ++
    (unfoldLoan d L760 ++
      (rotateLeft (BalancedCircuit.rawTarget L760) ++ [.CX L760.parity L760.r0] ++ rawSubLoan d L760))
  have h2re : BalancedCleanup.prepareSign L760.toLayout ++
        (Q6LifetimeResearch.move (base 760) L760.rmsb (P1Life.shortConstAdd L760 (encodeWord 255 (-h))) ++
          (P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++ (compareBlockLoan d false L760 ++ B2))) =
      A2 ++ (compareBlockLoan d false L760 ++ B2) := by
    simp only [A2, A2f, List.append_assoc]
  rw [h2re]
  have htr2f : Triple (DirectPass.AfterHalf L760 (base 760) origin F Y) A2f
      (DirectPass.AfterComparison DirectPass.oddEncoding L760 (base 760) origin F Y) :=
    Triple.seq (P1Life.prepare_sign_odd (base 760) L760 hw760 hn760 origin F Y hf)
      (P1Life.normalize_boundary (base 760) L760 hw760 hn760 mem760 origin F Y)
  have h2 : ∃ n2, run (A2 ++ (compareBlockLoan d false L760 ++ B2)) n1 s =
      run (A2 ++ (P1Life.compare (base 760) false L760 ++ B2)) n2 s := by
    apply replace_mid
    intro x
    rw [show A2 = A2f ++ (P1Life.prepareCompare L760 ++ P1Life.exposure L760) from rfl, run_append]
    have hcomp := (htr2f s ((n1.take (measurementCount A2)).take (measurementCount A2f)) hs).2
    generalize hu0_def : run A2f ((n1.take (measurementCount A2)).take (measurementCount A2f)) s = u0
    rw [hu0_def] at hcomp
    rcases hcomp with ⟨hlow, hrmsb, hyu, ⟨_, hlower, hone⟩, hclean, hframe⟩
    have hrv : regValue L760.r u0.basis = encodeWord 255 (P1Life.oddNormalized F) := by
      change regValue (L760.low ++ [L760.rmsb]) u0.basis = _
      rw [regValue_append, hlow, oddEncoding_norm, regValue_singleton_false _ _ hrmsb, Nat.mul_zero, Nat.add_zero]
    have hsign : u0.basis L760.sign = B :=
      hframe L760.sign (not_mem_L760_r_of_eq 2425 rfl (by omega))
        L760_sign_ne_parity L760_sign_ne_lower L760_sign_ne_one
    have hu_b : -((2 ^ 254 : Nat) : Int) ≤ P1Life.oddNormalized F ∧ P1Life.oddNormalized F < ((2 ^ 254 : Nat) : Int) := by
      have hb := P1Life.oddNormalized_bounds F hf; have hc := constants; omega
    exact compare_after_prepare_run_eq d hd false (P1Life.oddNormalized F) Y B (negative F)
      hu_b (P1Life.oddDomain_signed Y hy) u0 _ x hrv hyu hsign hlower hone
      (carry_all_zero_of_afterHalf origin horig u0.basis hclean hframe)
      (fun e => absurd e Bool.false_ne_true)
  obtain ⟨n2, hn2⟩ := h2; rw [hn2]
  -- Step 3: unfoldLoan
  let A3 := A2f ++ (P1Life.prepareCompare L760 ++ P1Life.exposure L760 ++
    P1Life.compare (base 760) false L760 ++ (P1Life.exposure L760).reverse ++
    (P1Life.prepareCompare L760).reverse ++ BiasedInverse.unbiasView L760)
  let B3 := rotateLeft (BalancedCircuit.rawTarget L760) ++ [.CX L760.parity L760.r0] ++ rawSubLoan d L760
  have h3re : A2 ++ (P1Life.compare (base 760) false L760 ++ B2) = A3 ++ (unfoldLoan d L760 ++ B3) := by
    simp only [A2, B2, A3, B3, List.append_assoc]
  rw [h3re]
  have htr3 : Triple (DirectPass.AfterHalf L760 (base 760) origin F Y) A3
      (DirectPass.AfterFold DirectPass.oddEncoding L760 (base 760) origin T F Y) :=
    Triple.seq htr2f (P1Life.comparison_to_fold (base 760) L760 hw760 hn760 mem760 origin T F Y hf hy hival)
  have h3 : ∃ n3, run (A3 ++ (unfoldLoan d L760 ++ B3)) n2 s =
      run (A3 ++ (P1Life.unfoldStep (base 760) L760 ++ B3)) n3 s := by
    apply replace_mid
    intro x
    have haf := (htr3 s (n2.take (measurementCount A3)) hs).2
    rcases haf with ⟨_, _, ⟨_, hlow, _⟩, hclean, hframe⟩
    exact unfoldLoan_760_run_eq d hd _ x hlow (carry_all_zero_of_afterHalf origin horig _ hclean hframe)
  obtain ⟨n3, hn3⟩ := h3; rw [hn3]
  -- Step 4: rawSubLoan
  let A4 := A3 ++ (P1Life.unfoldStep (base 760) L760 ++ rotateLeft (BalancedCircuit.rawTarget L760) ++ [.CX L760.parity L760.r0])
  have h4re : A3 ++ (P1Life.unfoldStep (base 760) L760 ++ B3) = A4 ++ rawSubLoan d L760 := by
    simp only [A4, B3, List.append_assoc]
  rw [h4re]
  have htr4 : Triple (DirectPass.AfterHalf L760 (base 760) origin F Y) A4
      (DirectPass.AfterRaw DirectPass.standardEncoding L760 (base 760) origin T Y) := by
    have hfr := P1Life.fold_to_raw (base 760) L760 hw760 hn760 mt origin T Y ht
    rw [hres] at hfr
    exact Triple.seq htr3 hfr
  have h4 : ∃ n4, run (A4 ++ rawSubLoan d L760) n3 s =
      run (A4 ++ P1Life.rawSub (base 760) L760) n4 s := by
    apply replace_last
    intro x
    have hraw := (htr4 s (n3.take (measurementCount A4)) hs).2
    have hcar := carry_all_zero_of_afterHalf origin horig _ hraw.2.2.2.2.1 hraw.2.2.2.2.2
    exact rawSubLoan_760_run_eq d hd origin B R Y hr hy rfl _ x hraw hcar
  obtain ⟨n4, hn4⟩ := h4
  refine ⟨n4, hn4.trans ?_⟩
  have hQ : A4 ++ P1Life.rawSub (base 760) L760 = P1Life.inverse (base 760) L760 := by
    rw [P1Life.inverse_chunks]; simp only [A4, A3, A2f, List.append_assoc]
  rw [hQ]

theorem half760OddLoan_law (d : Nat) (divide : Bool) (hd : d ≤ 44) :
    RouteA.Rolling1588.HalfLaw (half760OddLoan d divide) divide P1Life.oddWord P1Life.oddWord := by
  intro origin clean X Y s m input
  let bodyP := if divide then forwardLoan d L760 else inverseLoan d L760
  let bodyQ := if divide then P1Life.forward (base 760) L760 else P1Life.inverse (base 760) L760
  have hP : half760OddLoan d divide = [.X (base 2409)] ++ (bodyP ++ [.X (base 2409)]) := by
    delta half760OddLoan; cases divide <;> simp [bodyP, L760, List.append_assoc]
  have hQ : P1Life.half (base 760) divide base (base 2409) = [.X (base 2409)] ++ (bodyQ ++ [.X (base 2409)]) := by
    delta P1Life.half; cases divide <;> simp [bodyQ, L760, List.append_assoc]
  have horig : ∀ q ∈ L760.carry, origin q = false := by
    intro q hq
    exact Q6EndpointCell.clean_work base (base 2409) origin clean q (by simp [BalancedCircuit.work, hq])
  have hstep : ∃ n, run (half760OddLoan d divide) m s =
      run (P1Life.half (base 760) divide base (base 2409)) n s := by
    rw [hP, hQ]
    apply replace_mid
    intro x
    let u := run [.X (base 2409)] (m.take (measurementCount [.X (base 2409)])) s
    have hcl := Q6EndpointCell.clean_work base (base 2409) origin clean
    have hsr : base 2409 ∉ L760.r := by decide +kernel
    have hsy : base 2409 ∉ L760.y := by decide +kernel
    have hu_eq : u = run [.X (base 2409)] [] s := run_zero_meas [.X (base 2409)] (meas_X (base 2409)) _ [] s
    have huf : ∀ q, q ≠ base 2409 → u.basis q = s.basis q := fun q hq => by simp [hu_eq, run, writeBit, hq]
    have huc : ∀ q ∈ BalancedCircuit.work L760, u.basis q = false := by
      intro q hq
      have ha := DirectPass.work_outside L760 hn760 q hq
      exact (huf q ha.2.2).trans ((input.2.2 q ha.1 ha.2.1).trans (hcl q hq))
    have hah : DirectPass.AfterHalf L760 (base 760) u.basis (P1Life.oddRep X) (P1Life.oddRep Y) u.basis := by
      refine ⟨?_, ?_, ⟨huc _ (by simp [BalancedCircuit.work]), huc _ (by simp [BalancedCircuit.work]),
        huc _ (by simp [BalancedCircuit.work])⟩, ?_, fun _ _ _ _ _ => rfl⟩
      · exact (regValue_congr _ _ _ (fun q hq => huf q (fun e => hsr (e ▸ hq)))).trans input.1
      · exact (regValue_congr _ _ _ (fun q hq => huf q (fun e => hsy (e ▸ hq)))).trans input.2.1
      · intro q hq _; exact huc q (by simp [BalancedCircuit.work, List.mem_of_mem_take hq])
    have hu_car : ∀ q ∈ L760.carry, u.basis q = false := fun q hq => huc q (by simp [BalancedCircuit.work, hq])
    cases divide
    · exact inverseLoan_760_run_eq d hd u.basis hu_car (P1Life.oddRep X) (P1Life.oddRep Y)
        (P1Life.oddRep_bounds X) (P1Life.oddRep_bounds Y) u x hah
    · exact forwardLoan_760_run_eq d hd u.basis hu_car (P1Life.oddRep X) (P1Life.oddRep Y)
        (P1Life.oddRep_bounds X) (P1Life.oddRep_bounds Y) u x hah
  obtain ⟨n, hn⟩ := hstep
  rw [hn]
  exact P1Life.half_frame (base 760) divide base (base 2409) hn760 mem760 origin clean X Y s n input

private theorem mem_jp760_iff (q : Nat) :
    q ∈ P1Life.junctionFootprint L760 ↔
      q = 2425 ∨ q = 784 ∨ q = 1813 ∨ q = 1043 ∨
      (2072 ≤ q ∧ q < 2328) ∨ (786 ≤ q ∧ q < 1042) ∨ (528 ≤ q ∧ q < 781) ∨ q = 1556 := by
  unfold P1Life.junctionFootprint
  rw [List.mem_toFinset]
  simp only [List.mem_cons, List.mem_append, mem_L760_r_iff, mem_L760_y_iff, mem_L760_carry254_iff]
  have hs : (L760.sign : Nat) = 2425 := rfl
  have hp : (L760.parity : Nat) = 784 := rfl
  have hl : (L760.lower : Nat) = 1813 := rfl
  have ho : (L760.one : Nat) = 1043 := rfl
  rw [hs, hp, hl, ho]
  tauto

private theorem retiredRoles_in_jp (q : Nat) (hq : q ∈ StairLoan.retiredRoles) :
    q ∈ P1Life.junctionFootprint L760 := by
  have hchk : StairLoan.retiredRoleIndices.all (fun i => decide (512 ≤ i ∧ i < 765)) = true := by decide +kernel
  simp only [StairLoan.retiredRoles, List.mem_map, base_eq_add] at hq
  rcases hq with ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true (List.all_eq_true.mp hchk i hi)
  rw [mem_jp760_iff]; omega

private theorem shortFreeHosts_in_jp (d : Nat) (q : Nat) (hq : q ∈ OddFullPass.P1LifeLoan.shortFreeHosts d) :
    q ∈ P1Life.junctionFootprint L760 := by
  rw [mem_jp760_iff]
  unfold OddFullPass.P1LifeLoan.shortFreeHosts at hq
  split_ifs at hq <;>
    (simp only [List.mem_cons, List.not_mem_nil, or_false, base_eq_add] at hq; omega)

private theorem mem_jp760_of_eq {q : Wire} (n : Nat) (heq : n = q)
    (hn : n = 2425 ∨ n = 784 ∨ n = 1813 ∨ n = 1043 ∨
      (2072 ≤ n ∧ n < 2328) ∨ (786 ≤ n ∧ n < 1042) ∨ (528 ≤ n ∧ n < 781) ∨ n = 1556) :
    q ∈ P1Life.junctionFootprint L760 := by
  rw [← heq, mem_jp760_iff]; exact hn

private theorem mem_jp760_of_r (q : Nat) (hq : q ∈ L760.r) : q ∈ P1Life.junctionFootprint L760 := by
  rw [mem_jp760_iff]; have hr := (mem_L760_r_iff q).mp hq; omega

private theorem jp_swap760 {host q : Wire}
    (hh : host ∈ P1Life.junctionFootprint L760) (hq : q ∈ P1Life.junctionFootprint L760) :
    Equiv.swap (base 760) host q ∈ P1Life.junctionFootprint L760 := by
  have h760 : base 760 ∈ P1Life.junctionFootprint L760 := mem_jp760_of_eq 776 rfl (by omega)
  by_cases h1 : q = base 760
  · rw [h1, Equiv.swap_apply_left]; exact hh
  · by_cases h2 : q = host
    · rw [h2, Equiv.swap_apply_right]; exact h760
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hq

private theorem move_in_jp {host : Wire} {P : Program}
    (hh : host ∈ P1Life.junctionFootprint L760) (hP : wires P ⊆ P1Life.junctionFootprint L760) :
    wires (Q6LifetimeResearch.move (base 760) host P) ⊆ P1Life.junctionFootprint L760 := by
  intro q hq
  rw [Q6LifetimeResearch.move, renameProgram_support, Finset.mem_image] at hq
  rcases hq with ⟨v, hv, rfl⟩
  exact jp_swap760 hh (hP hv)

private theorem layerHosts_take_in_jp {ls : List StairLoan.CarryLayer} {d : Nat}
    (hls : ∀ l ∈ ls, l.host ∈ P1Life.junctionFootprint L760) :
    (StairLoan.layerHosts (ls.take d)).toFinset ⊆ P1Life.junctionFootprint L760 := by
  intro q hq
  rw [List.mem_toFinset] at hq
  simp only [StairLoan.layerHosts, List.mem_map] at hq
  rcases hq with ⟨l, hl, rfl⟩
  exact hls l (List.mem_of_mem_take hl)

private theorem mappedLayers_hosts (bits : List MappedBit) (ys cs : List Wire) (cin : Wire)
    (hcs : ∀ q ∈ cs, q ∈ P1Life.junctionFootprint L760) :
    ∀ l ∈ StairLoan.mappedLayers bits ys cs cin, l.host ∈ P1Life.junctionFootprint L760 := by
  induction bits generalizing ys cs cin with
  | nil => intro l hl; simp [StairLoan.mappedLayers] at hl
  | cons b bs ih =>
    cases bs with
    | nil => intro l hl; simp [StairLoan.mappedLayers] at hl
    | cons b2 bs2 =>
      cases ys with
      | nil => intro l hl; simp [StairLoan.mappedLayers] at hl
      | cons y ys =>
        cases ys with
        | nil => intro l hl; simp [StairLoan.mappedLayers] at hl
        | cons y2 ys2 =>
          cases cs with
          | nil => intro l hl; simp [StairLoan.mappedLayers] at hl
          | cons c cs =>
            intro l hl
            simp only [StairLoan.mappedLayers, List.mem_cons] at hl
            rcases hl with rfl | hrest
            · exact hcs c (List.mem_cons_self ..)
            · exact ih (y2 :: ys2) cs c (fun q hq => hcs q (List.mem_cons_of_mem _ hq)) l hrest

private theorem compareLayers_hosts (fwd : Bool) (as bs cs : List Wire) (cin tgt : Wire)
    (hcs : ∀ q ∈ cs, q ∈ P1Life.junctionFootprint L760) :
    ∀ l ∈ StairLoan.compareLayers fwd as bs cs cin tgt, l.host ∈ P1Life.junctionFootprint L760 := by
  induction as generalizing bs cs cin with
  | nil => intro l hl; simp [StairLoan.compareLayers] at hl
  | cons a as ih =>
    cases bs with
    | nil => intro l hl; simp [StairLoan.compareLayers] at hl
    | cons b bs =>
      cases as with
      | nil => intro l hl; simp [StairLoan.compareLayers] at hl
      | cons a2 as2 =>
        cases bs with
        | nil => intro l hl; simp [StairLoan.compareLayers] at hl
        | cons b2 bs2 =>
          cases cs with
          | nil => intro l hl; simp [StairLoan.compareLayers] at hl
          | cons c cs =>
            intro l hl
            simp only [StairLoan.compareLayers, List.mem_cons] at hl
            rcases hl with rfl | hrest
            · exact hcs c (List.mem_cons_self ..)
            · exact ih (b2 :: bs2) cs c (fun q hq => hcs q (List.mem_cons_of_mem _ hq)) l hrest

private theorem prefixLayers_hosts (xs ys cs : List Wire) (a t z cin : Wire)
    (hcs : ∀ q ∈ cs, q ∈ P1Life.junctionFootprint L760) :
    ∀ l ∈ StairLoan.prefixLayers xs ys cs a t z cin, l.host ∈ P1Life.junctionFootprint L760 := by
  induction xs generalizing ys cs cin with
  | nil => intro l hl; simp [StairLoan.prefixLayers] at hl
  | cons x xs ih =>
    cases ys with
    | nil => intro l hl; simp [StairLoan.prefixLayers] at hl
    | cons y ys =>
      cases cs with
      | nil => intro l hl; simp [StairLoan.prefixLayers] at hl
      | cons c cs =>
        intro l hl
        simp only [StairLoan.prefixLayers, List.mem_cons] at hl
        rcases hl with rfl | hrest
        · exact hcs c (List.mem_cons_self ..)
        · exact ih ys cs c (fun q hq => hcs q (List.mem_cons_of_mem _ hq)) l hrest

private theorem addTopLayers_hosts (as bs cs : List Wire) (cin : Wire)
    (hcs : ∀ q ∈ cs, q ∈ P1Life.junctionFootprint L760) :
    ∀ l ∈ StairLoan.addTopLayers as bs cs cin, l.host ∈ P1Life.junctionFootprint L760 := by
  match as, bs, cs with
  | [_, _], [_, _], _ => intro l hl; simp [StairLoan.addTopLayers] at hl
  | a :: a' :: as', b :: b' :: bs', c :: cs' =>
    cases as' with
    | nil =>
      cases bs' with
      | nil => intro l hl; simp [StairLoan.addTopLayers] at hl
      | cons b2 bs2 =>
        intro l hl
        have hstep : StairLoan.addTopLayers [a, a'] (b :: b' :: b2 :: bs2) (c :: cs') cin =
            { host := c, up := majority a b cin c, erase := eraseCarry a b cin c,
              finish := [.CX a b, .CX cin b] } :: StairLoan.addTopLayers [a'] (b' :: b2 :: bs2) cs' c := rfl
        rw [hstep, List.mem_cons] at hl
        rcases hl with rfl | hrest
        · exact hcs c (List.mem_cons_self ..)
        · exact addTopLayers_hosts [a'] (b' :: b2 :: bs2) cs' c
            (fun q hq => hcs q (List.mem_cons_of_mem _ hq)) l hrest
    | cons a2 as2 =>
      intro l hl
      have hstep : StairLoan.addTopLayers (a :: a' :: a2 :: as2) (b :: b' :: bs') (c :: cs') cin =
          { host := c, up := majority a b cin c, erase := eraseCarry a b cin c,
            finish := [.CX a b, .CX cin b] } :: StairLoan.addTopLayers (a' :: a2 :: as2) (b' :: bs') cs' c := rfl
      rw [hstep, List.mem_cons] at hl
      rcases hl with rfl | hrest
      · exact hcs c (List.mem_cons_self ..)
      · exact addTopLayers_hosts (a' :: a2 :: as2) (b' :: bs') cs' c
          (fun q hq => hcs q (List.mem_cons_of_mem _ hq)) l hrest
  | [], _, _ => intro l hl; simp [StairLoan.addTopLayers] at hl
  | [_], _, _ => intro l hl; simp [StairLoan.addTopLayers] at hl
  | _, [], _ => intro l hl; simp [StairLoan.addTopLayers] at hl
  | _, [_], _ => intro l hl; simp [StairLoan.addTopLayers] at hl
  | a', b', [] =>
    intro l hl
    rcases a' with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rcases b' with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
      simp [StairLoan.addTopLayers] at hl

private theorem wires_append_sub {A B : Program} {S : Finset Wire}
    (hA : wires A ⊆ S) (hB : wires B ⊆ S) : wires (A ++ B) ⊆ S := by
  rw [wires_append]; exact Finset.union_subset hA hB

private theorem wires_append_un {A B : Program} {S : Finset Wire}
    (h : wires (A ++ B) ⊆ S) : wires A ⊆ S ∧ wires B ⊆ S := by
  rw [wires_append] at h; exact Finset.union_subset_iff.mp h

private theorem wires_X_sub {a : Wire} {S : Finset Wire} (ha : a ∈ S) :
    wires ([Instr.X a] : Program) ⊆ S := by
  intro q hq
  have hqa : q = a := by simp [wires, Instr.wires] at hq; exact hq
  exact hqa ▸ ha

private theorem emitLoan_in_jp (d : Nat) (ls : List StairLoan.CarryLayer) (top : Program)
    (hsw : wires (StairLoan.emitSweep ls top) ⊆ P1Life.junctionFootprint L760)
    (hls : ∀ l ∈ ls, l.host ∈ P1Life.junctionFootprint L760) :
    wires (StairLoan.emitLoan d StairLoan.retiredRoles ls top) ⊆ P1Life.junctionFootprint L760 := by
  have h1 := StairLoanSupport.emitLoan_support_envelope d StairLoan.retiredRoles ls top
  refine h1.trans (Finset.union_subset (Finset.union_subset hsw ?_) (layerHosts_take_in_jp hls))
  intro q hq
  exact retiredRoles_in_jp q (List.mem_of_mem_take (List.mem_toFinset.mp hq))

private theorem q6Tail_in_jp : ∀ q ∈ ((Q6Structural.q6Carry L760).take 255).drop 1,
    q ∈ P1Life.junctionFootprint L760 := by
  intro q hq; rw [mem_q6Carry255_drop1_iff] at hq; rw [mem_jp760_iff]; omega

private theorem carry254_in_jp : ∀ q ∈ L760.carry.take 254,
    q ∈ P1Life.junctionFootprint L760 := by
  intro q hq; rw [mem_L760_carry254_iff] at hq; rw [mem_jp760_iff]; omega

private theorem carry251_in_jp : ∀ q ∈ L760.carry.take 251, q ∈ P1Life.junctionFootprint L760 := by
  intro q hq
  have h254 : q ∈ L760.carry.take 254 := by
    have ht : L760.carry.take 251 = (L760.carry.take 254).take 251 := by rw [List.take_take]; rfl
    rw [ht] at hq; exact List.mem_of_mem_take hq
  rw [mem_L760_carry254_iff] at h254; rw [mem_jp760_iff]; omega

private theorem jp_of_p1half (divide : Bool) :
    wires (P1Life.half (base 760) divide base (base 2409)) ⊆ P1Life.junctionFootprint L760 :=
  (RouteA.Rolling1588.half_support divide).trans (Finset.erase_subset _ _)

private theorem previousShort_in_jp (d k : Nat)
    (h0 : wires (P1Life.shortConstAdd L760 k) ⊆ P1Life.junctionFootprint L760) :
    wires (previousShort d L760 k) ⊆ P1Life.junctionFootprint L760 := by
  have hx2 : L760.low.getD 2 0 ∈ P1Life.junctionFootprint L760 := mem_jp760_of_eq 2074 rfl (by omega)
  have hlit : ∀ d', wires (StairLoan.literalConstAddLoan d' StairLoan.retiredRoles
      (L760.low.drop 3) (L760.carry.take 251) (L760.low.getD 2 0) L760.one (k / 8)) ⊆
      P1Life.junctionFootprint L760 := by
    intro d'
    have h0lit : wires (literalConstAdd (L760.low.drop 3) (L760.carry.take 251)
        (L760.low.getD 2 0) L760.one (k / 8)) ⊆ P1Life.junctionFootprint L760 := by
      delta P1Life.shortConstAdd at h0
      exact (wires_append_un h0).1
    cases d' with
    | zero => simpa [StairLoan.literalConstAddLoan] using h0lit
    | succ d' =>
      simp only [StairLoan.literalConstAddLoan, Nat.succ_ne_zero, if_false, StairLoan.mappedAddLoan]
      apply emitLoan_in_jp
      · rw [← StairLoan.mappedAdd_as_sweep]
        intro q hq
        have maw := mappedAdd_wires_subset _ _ _ _ hq
        simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at maw
        rcases maw with ((h1 | h2) | h3) | rfl
        · exact absurd (mappedConstant_wires none _ _ q h1) (by simp)
        · exact mem_jp760_of_r q (List.mem_append_left _ (List.mem_of_mem_drop h2))
        · exact carry251_in_jp q h3
        · exact hx2
      · exact mappedLayers_hosts _ _ _ _ carry251_in_jp
  unfold previousShort
  split_ifs
  · exact wires_append_sub (hlit d) (wires_X_sub hx2)
  · refine wires_append_sub ?_ (wires_X_sub hx2)
    refine (OddFullPass.rebindMany_wires_sub _ _ _).trans (Finset.union_subset (Finset.union_subset (hlit _) ?_) ?_)
    · intro q hq
      exact retiredRoles_in_jp q (List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_toFinset.mp hq)))
    · intro q hq
      exact shortFreeHosts_in_jp d q (List.mem_toFinset.mp hq)

private theorem shortConstAddLoan_in_jp (d k : Nat)
    (h0 : wires (P1Life.shortConstAdd L760 k) ⊆ P1Life.junctionFootprint L760) :
    wires (shortConstAddLoan d L760 k) ⊆ P1Life.junctionFootprint L760 := by
  apply short_cases d L760 k (fun p => wires p ⊆ P1Life.junctionFootprint L760) (previousShort_in_jp d k h0)
  intro dir _ lo hi q hit
  rcases LiteralTop.support d lo hi dir q hit with hl | ho | hp | hc
  · exact mem_jp760_of_r q (List.mem_append_left _ hl)
  · rw [ho]; exact mem_jp760_of_eq 1043 rfl (by omega)
  · rw [hp]; exact mem_jp760_of_eq 784 rfl (by omega)
  · exact carry254_in_jp q hc.1

private theorem half760OddLoan_in_jp (d : Nat) (divide : Bool) :
    wires (half760OddLoan d divide) ⊆ P1Life.junctionFootprint L760 := by
  have hp1 := jp_of_p1half divide
  have h2409 : base 2409 ∈ P1Life.junctionFootprint L760 := mem_jp760_of_eq 2425 rfl (by omega)
  have hrmsb : L760.rmsb ∈ P1Life.junctionFootprint L760 := mem_jp760_of_eq 2327 rfl (by omega)
  have hr0 : L760.r0 ∈ P1Life.junctionFootprint L760 := mem_jp760_of_eq 2072 rfl (by omega)
  have hone : L760.one ∈ P1Life.junctionFootprint L760 := mem_jp760_of_eq 1043 rfl (by omega)
  have hmove_in_jp : ∀ {host : Wire} {P : Program} (Q : Program),
      host ∈ P1Life.junctionFootprint L760 →
      wires (Q6LifetimeResearch.move (base 760) host Q) ⊆ P1Life.junctionFootprint L760 →
      (∀ q ∈ wires P, q ∈ wires Q ∨ q ∈ P1Life.junctionFootprint L760) →
      wires (Q6LifetimeResearch.move (base 760) host P) ⊆ P1Life.junctionFootprint L760 := by
    intro host P Q hh hQ hPQ q hq
    rw [Q6LifetimeResearch.move, renameProgram_support, Finset.mem_image] at hq
    rcases hq with ⟨v, hv, rfl⟩
    rcases hPQ v hv with hvQ | hvJ
    · exact hQ (by rw [Q6LifetimeResearch.move, renameProgram_support]; exact Finset.mem_image.mpr ⟨v, hvQ, rfl⟩)
    · exact jp_swap760 hh hvJ
  have hmove_un : ∀ {host : Wire} {P : Program},
      host ∈ P1Life.junctionFootprint L760 →
      wires (Q6LifetimeResearch.move (base 760) host P) ⊆ P1Life.junctionFootprint L760 →
      wires P ⊆ P1Life.junctionFootprint L760 := by
    intro host P hh hM w hw
    have hm := hM (by rw [Q6LifetimeResearch.move, renameProgram_support]; exact Finset.mem_image.mpr ⟨w, hw, rfl⟩)
    simpa [Equiv.swap_apply_self] using jp_swap760 hh hm
  have hcomp_in : ∀ (fwd : Bool),
      wires (P1Life.compare (base 760) fwd L760) ⊆ P1Life.junctionFootprint L760 →
      wires (compareBlockLoan d fwd L760) ⊆ P1Life.junctionFootprint L760 := by
    intro fwd hP1
    delta compareBlockLoan; delta P1Life.compare at hP1
    dsimp only at hP1 ⊢
    rcases wires_append_un hP1 with ⟨hP1, h7⟩
    rcases wires_append_un hP1 with ⟨hP1, h6⟩
    rcases wires_append_un hP1 with ⟨hP1, h5⟩
    rcases wires_append_un hP1 with ⟨hP1, h4⟩
    rcases wires_append_un hP1 with ⟨hP1, h3⟩
    rcases wires_append_un hP1 with ⟨h1, h2⟩
    refine wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
      (wires_append_sub (wires_append_sub h1 h2) h3) ?_) h5) h6) h7
    refine hmove_in_jp (Q6LifetimeResearch.compareChain fwd (L760.r.drop 1) (L760.y.drop 1)
        (((Q6Structural.q6Carry L760).take 255).drop 1)
        (((Q6Structural.q6Carry L760).take 255).getD 0 0) L760.parity) hone h4 ?_
    intro w hw
    have he := StairLoanSupport.emitLoan_support_envelope d StairLoan.retiredRoles
      (StairLoan.compareLayers fwd (L760.r.drop 1) (L760.y.drop 1) (((Q6Structural.q6Carry L760).take 255).drop 1)
        (((Q6Structural.q6Carry L760).take 255).getD 0 0) L760.parity)
      (StairLoan.compareTop fwd (L760.r.drop 1) (L760.y.drop 1) (((Q6Structural.q6Carry L760).take 255).drop 1)
        (((Q6Structural.q6Carry L760).take 255).getD 0 0) L760.parity) hw
    rw [← StairLoan.compareChain_as_sweep] at he
    simp only [Finset.mem_union] at he
    rcases he with (hsw | hret) | hlay
    · exact Or.inl hsw
    · exact Or.inr (retiredRoles_in_jp w (List.mem_of_mem_take (List.mem_toFinset.mp hret)))
    · exact Or.inr (layerHosts_take_in_jp (compareLayers_hosts _ _ _ _ _ _ q6Tail_in_jp) hlay)
  cases divide
  · -- inverse (divide = false)
    have hp1' : wires (P1Life.inverse (base 760) L760) ⊆ P1Life.junctionFootprint L760 := by
      delta P1Life.half at hp1; dsimp only at hp1; simp only [Bool.false_eq_true, if_false] at hp1
      exact (wires_append_un (wires_append_un hp1).1).2
    delta half760OddLoan; dsimp only; simp only [Bool.false_eq_true, if_false]
    refine wires_append_sub (wires_append_sub (wires_X_sub h2409) ?_) (wires_X_sub h2409)
    delta inverseLoan; delta P1Life.inverse at hp1'
    rw [prepareCompare_eq, exposure_eq]
    rcases wires_append_un hp1' with ⟨hp1', h12⟩
    rcases wires_append_un hp1' with ⟨hp1', h11⟩
    rcases wires_append_un hp1' with ⟨hp1', h10⟩
    rcases wires_append_un hp1' with ⟨hp1', h9⟩
    rcases wires_append_un hp1' with ⟨hp1', h8⟩
    rcases wires_append_un hp1' with ⟨hp1', h7⟩
    rcases wires_append_un hp1' with ⟨hp1', h6⟩
    rcases wires_append_un hp1' with ⟨hp1', h5⟩
    rcases wires_append_un hp1' with ⟨hp1', h4⟩
    rcases wires_append_un hp1' with ⟨hp1', h3⟩
    rcases wires_append_un hp1' with ⟨h1, h2⟩
    refine wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
      (wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
      (wires_append_sub (wires_append_sub (wires_append_sub
        h1 (move_in_jp hrmsb (shortConstAddLoan_in_jp d _ (hmove_un hrmsb h2))))
        h3) h4) (hcomp_in false h5)) h6) h7) h8) ?_) h10) h11) ?_
    · -- unfoldLoan
      delta unfoldLoan; delta P1Life.unfoldStep at h9
      rcases wires_append_un h9 with ⟨h9, hu3⟩
      rcases wires_append_un h9 with ⟨hu1, hu2⟩
      refine wires_append_sub (wires_append_sub hu1 ?_) hu3
      refine hmove_in_jp (mappedSub (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one)
        hrmsb hu2 ?_
      intro w fresh
      have hw := FoldLoanTop.choose_sites d true fresh
      simp only [FoldLoanTop.stock,Bool.false_eq_true,if_false,if_true] at hw
      simp only [StairLoan.mappedSubLoan, wires_append, Finset.mem_union] at hw
      rcases hw with (hn | hm) | hn
      · exact Or.inl (by simp only [mappedSub, wires_append, Finset.mem_union, hn, true_or, or_true])
      · have he := StairLoanSupport.emitLoan_support_envelope d StairLoan.retiredRoles
          (StairLoan.mappedLayers (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one)
          (StairLoan.mappedTop (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one) hm
        rw [← StairLoan.mappedAdd_as_sweep] at he
        simp only [Finset.mem_union] at he
        rcases he with (hsw | hret) | hlay
        · exact Or.inl (by simp only [mappedSub, wires_append, Finset.mem_union, hsw, true_or, or_true])
        · exact Or.inr (retiredRoles_in_jp w (List.mem_of_mem_take (List.mem_toFinset.mp hret)))
        · exact Or.inr (layerHosts_take_in_jp (mappedLayers_hosts _ _ _ _ carry254_in_jp) hlay)
      · exact Or.inl (by simp only [mappedSub, wires_append, Finset.mem_union, hn, true_or, or_true])
    · -- rawSubLoan
      delta rawSubLoan; delta P1Life.rawSub at h12
      dsimp only at h12 ⊢
      rw [orMajor_eq, orErase_eq]
      rcases wires_append_un h12 with ⟨h12, r11⟩
      rcases wires_append_un h12 with ⟨h12, r10⟩
      rcases wires_append_un h12 with ⟨h12, r9⟩
      rcases wires_append_un h12 with ⟨h12, r8⟩
      rcases wires_append_un h12 with ⟨h12, r7⟩
      rcases wires_append_un h12 with ⟨h12, r6⟩
      rcases wires_append_un h12 with ⟨h12, r5⟩
      rcases wires_append_un h12 with ⟨h12, r4⟩
      rcases wires_append_un h12 with ⟨h12, r3⟩
      rcases wires_append_un h12 with ⟨r1, r2⟩
      refine wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
        (wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
        (wires_append_sub (wires_append_sub r1 r2) r3) r4) ?_) r6) r7) r8) r9) r10) r11
      refine hmove_in_jp (Q6LifetimeResearch.addTop ((GuardCompression.source L760).drop 1)
          ((BalancedCircuit.rawTarget L760).drop 1)
          (((Q6Structural.q6Carry L760).take 255).drop 1)
          (((Q6Structural.q6Carry L760).take 255).getD 0 0)) hr0 r5 ?_
      intro w hw
      have he := StairLoanSupport.emitLoan_support_envelope d StairLoan.retiredRoles
        (StairLoan.addTopLayers ((GuardCompression.source L760).drop 1) ((BalancedCircuit.rawTarget L760).drop 1)
          (((Q6Structural.q6Carry L760).take 255).drop 1) (((Q6Structural.q6Carry L760).take 255).getD 0 0))
        (StairLoan.addTopTop ((GuardCompression.source L760).drop 1) ((BalancedCircuit.rawTarget L760).drop 1)
          (((Q6Structural.q6Carry L760).take 255).drop 1) (((Q6Structural.q6Carry L760).take 255).getD 0 0)) hw
      rw [← StairLoan.addTop_as_sweep] at he
      simp only [Finset.mem_union] at he
      rcases he with (hsw | hret) | hlay
      · exact Or.inl hsw
      · exact Or.inr (retiredRoles_in_jp w (List.mem_of_mem_take (List.mem_toFinset.mp hret)))
      · exact Or.inr (layerHosts_take_in_jp (addTopLayers_hosts _ _ _ _ q6Tail_in_jp) hlay)
  · -- forward (divide = true)
    have hp1' : wires (P1Life.forward (base 760) L760) ⊆ P1Life.junctionFootprint L760 := by
      delta P1Life.half at hp1; dsimp only at hp1; simp only [if_true] at hp1
      exact (wires_append_un (wires_append_un hp1).1).2
    delta half760OddLoan; dsimp only; simp only [if_true]
    refine wires_append_sub (wires_append_sub (wires_X_sub h2409) ?_) (wires_X_sub h2409)
    delta forwardLoan; delta P1Life.forward at hp1'
    rw [p1Seed_eq, prepareCompare_eq, exposure_eq]
    rcases wires_append_un hp1' with ⟨hp1', h14⟩
    rcases wires_append_un hp1' with ⟨hp1', h13⟩
    rcases wires_append_un hp1' with ⟨hp1', h12⟩
    rcases wires_append_un hp1' with ⟨hp1', h11⟩
    rcases wires_append_un hp1' with ⟨hp1', h10⟩
    rcases wires_append_un hp1' with ⟨hp1', h9⟩
    rcases wires_append_un hp1' with ⟨hp1', h8⟩
    rcases wires_append_un hp1' with ⟨hp1', h7⟩
    rcases wires_append_un hp1' with ⟨hp1', h6⟩
    rcases wires_append_un hp1' with ⟨hp1', h5⟩
    rcases wires_append_un hp1' with ⟨hp1', h4⟩
    rcases wires_append_un hp1' with ⟨hp1', h3⟩
    rcases wires_append_un hp1' with ⟨h1, h2⟩
    refine wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
      (wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
      (wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
        h1 ?_) h3) h4) ?_) h6) h7) h8) h9) (hcomp_in true h10)) h11) h12)
        (move_in_jp hrmsb (shortConstAddLoan_in_jp d _ (hmove_un hrmsb h13)))) h14
    · -- rawAddLoan
      delta rawAddLoan; delta P1Life.rawAdd at h2
      dsimp only at h2 ⊢
      rw [orMajor_eq, orErase_eq]
      rcases wires_append_un h2 with ⟨h2, r8⟩
      rcases wires_append_un h2 with ⟨h2, r7⟩
      rcases wires_append_un h2 with ⟨h2, r6⟩
      rcases wires_append_un h2 with ⟨h2, r5⟩
      rcases wires_append_un h2 with ⟨h2, r4⟩
      rcases wires_append_un h2 with ⟨h2, r3⟩
      rcases wires_append_un h2 with ⟨r1, r2⟩
      refine wires_append_sub (wires_append_sub (wires_append_sub (wires_append_sub
        (wires_append_sub (wires_append_sub (wires_append_sub r1 r2) r3) ?_) r5) r6) r7) r8
      refine hmove_in_jp (CoherentTail.addPrefix (L760.ylow.drop 1) (L760.low.drop 1)
          (((Q6Structural.q6Carry L760).take 255).drop 1)
          L760.ymsb L760.rmsb L760.one (((Q6Structural.q6Carry L760).take 255).getD 0 0)) hr0 r4 ?_
      intro w hw
      have he := StairLoanSupport.emitLoan_support_envelope d StairLoan.retiredRoles
        (StairLoan.prefixLayers (L760.ylow.drop 1) (L760.low.drop 1) (((Q6Structural.q6Carry L760).take 255).drop 1)
          L760.ymsb L760.rmsb L760.one (((Q6Structural.q6Carry L760).take 255).getD 0 0))
        (StairLoan.prefixTop (L760.ylow.drop 1) (L760.low.drop 1) (((Q6Structural.q6Carry L760).take 255).drop 1)
          L760.ymsb L760.rmsb L760.one (((Q6Structural.q6Carry L760).take 255).getD 0 0)) hw
      rw [← StairLoan.addPrefix_as_sweep] at he
      simp only [Finset.mem_union] at he
      rcases he with (hsw | hret) | hlay
      · exact Or.inl hsw
      · exact Or.inr (retiredRoles_in_jp w (List.mem_of_mem_take (List.mem_toFinset.mp hret)))
      · exact Or.inr (layerHosts_take_in_jp (prefixLayers_hosts _ _ _ _ _ _ _ q6Tail_in_jp) hlay)
    · -- foldLoan
      delta foldLoan; delta P1Life.fold at h5
      rcases wires_append_un h5 with ⟨h5, f3⟩
      rcases wires_append_un h5 with ⟨f1, f2⟩
      refine wires_append_sub (wires_append_sub f1 ?_) f3
      refine hmove_in_jp (mappedAdd (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one)
        hrmsb f2 ?_
      intro w fresh
      have hw := FoldLoanTop.choose_sites d false fresh
      simp only [FoldLoanTop.stock,Bool.false_eq_true,if_false,if_true] at hw
      have he := StairLoanSupport.emitLoan_support_envelope d StairLoan.retiredRoles
        (StairLoan.mappedLayers (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one)
        (StairLoan.mappedTop (ShortBiasedFold.lowBits L760) L760.low (L760.carry.take 254) L760.one) hw
      rw [← StairLoan.mappedAdd_as_sweep] at he
      simp only [Finset.mem_union] at he
      rcases he with (hsw | hret) | hlay
      · exact Or.inl hsw
      · exact Or.inr (retiredRoles_in_jp w (List.mem_of_mem_take (List.mem_toFinset.mp hret)))
      · exact Or.inr (layerHosts_take_in_jp (mappedLayers_hosts _ _ _ _ carry254_in_jp) hlay)

theorem half760OddLoan_support (d : Nat) (divide : Bool) (hd : d ≤ 44) :
    RouteA.Rolling1588.HalfSupport (half760OddLoan d divide) := by
  have h1 := OddFullPass.P1LifeLoan.half760OddLoan_wires_sub d divide hd
  have h2 := StairLoanSupport.half760Loan_support760 d divide (by omega)
  have hnot760 : base 760 ∉ wires (half760OddLoan d divide) := by
    intro hmem
    have hs := (Finset.sdiff_subset (h2 (h1 hmem)))
    rw [StairLoan.half760Loan_zero] at hs
    exact R2Life760.half760_free divide hs
  intro q hq
  exact Finset.mem_erase.mpr ⟨fun e => hnot760 (e ▸ hq), half760OddLoan_in_jp d divide hq⟩

private def basePacketWith (divide : Bool) (P : Program) (j : Nat) : Program :=
  ECDSAAdd.Entrant.Rolling1588.onPacket j (ECDSAAdd.Entrant.Rolling1588.dp ++ ParityCodec5New.untwist) ++
    (if divide then
      RouteA.Rolling1588.cellWith true P j 3 2 ++ RouteA.Rolling1588.cellWith true P j 4 2 ++
      ECDSAAdd.Entrant.Rolling1588.onPacket j ECDSAAdd.Entrant.Rolling1588.bridge7 ++
      RouteA.Rolling1588.cellWith true P j 4 2 ++ RouteA.Rolling1588.cellWith true P j 3 2 ++
      ECDSAAdd.Entrant.Rolling1588.onPacket j ECDSAAdd.Entrant.Rolling1588.bridge5 ++
      RouteA.Rolling1588.cellWith true P j 4 2
    else
      RouteA.Rolling1588.cellWith false P j 4 2 ++
      ECDSAAdd.Entrant.Rolling1588.onPacket j ECDSAAdd.Entrant.Rolling1588.bridge5 ++
      RouteA.Rolling1588.cellWith false P j 3 2 ++ RouteA.Rolling1588.cellWith false P j 4 2 ++
      ECDSAAdd.Entrant.Rolling1588.onPacket j ECDSAAdd.Entrant.Rolling1588.bridge7inv ++
      RouteA.Rolling1588.cellWith false P j 4 2 ++ RouteA.Rolling1588.cellWith false P j 3 2) ++
    ECDSAAdd.Entrant.Rolling1588.onPacket j (ParityCodec5New.twist ++ ECDSAAdd.Entrant.Rolling1588.ep)

private theorem cell_eq_cellWith (divide : Bool) (d j active hole : Nat) :
    OddFullPass.P1LifeLoan.cell divide d j active hole =
      RouteA.Rolling1588.cellWith divide (half760OddLoan d divide) j active hole := by
  unfold OddFullPass.P1LifeLoan.cell OddFullPass.P1LifeLoan.halfWindow
    RouteA.Rolling1588.cellWith RouteA.Rolling1588.halfWindowWith
  cases divide <;> rfl

private theorem basePacket_eq_with (divide : Bool) (d k : Nat) :
    OddFullPass.P1LifeLoan.basePacket divide d k = basePacketWith divide (half760OddLoan d divide) k := by
  unfold OddFullPass.P1LifeLoan.basePacket basePacketWith
  cases divide <;> simp only [if_true, if_false, Bool.false_eq_true, cell_eq_cellWith]

private theorem packet_with_cut_frame (P : Program) (divide : Bool)
    (hlaw : RouteA.Rolling1588.HalfLaw P divide P1Life.oddWord P1Life.oddWord)
    (hsup : RouteA.Rolling1588.HalfSupport P)
    (k : Nat) (lo : 1 ≤ k) (hi : k < 102)
    (hsub : wires (basePacketWith divide P k) ⊆ wires (ECDSAAdd.Entrant.Rolling1588.basePacket divide k))
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if divide then k else k + 1) origin X Y)
      (renameProgram (shifted (Placement5.pi k)) (basePacketWith divide P k))
      (fun state => let V := CompressedFieldSupport.directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X, Y)
        RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if divide then k + 1 else k) origin V.1 V.2 state) := by
  intro state records input
  have hk0 : k ≠ 0 := by omega
  have hkk : k ≤ k := le_rfl
  have hk1 : ¬ (k + 1 ≤ k) := by omega
  let Vout := CompressedFieldSupport.directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X, Y)
  have raw := RouteA.Rolling1588.cut_window_frame P1Life.oddWord P1Life.oddWord P1Life.oddWord P1Life.oddWord
    (if divide then k else k + 1) (if divide then k + 1 else k) k hi origin X Y Vout.1 Vout.2
    (basePacketWith divide P k)
    (by cases divide
        · exact (ECDSAAdd.Entrant.Rolling1588.otherEncodeCut_step base k 102).symm
        · exact ECDSAAdd.Entrant.Rolling1588.otherEncodeCut_step base k 102)
    (ECDSAAdd.Entrant.Rolling1588.otherEncodeCut_body_disjoint (if divide then k else k + 1) k hi origin ctx _
      (hsub.trans (ECDSAAdd.Entrant.Rolling1588.basePacket_read_support divide k hi)))
    (fun current tape frame => by
      have normalized : RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
          (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt divide (History5.historyMap base (5 * k))) origin X Y current := by
        cases divide <;> simpa only [ECDSAAdd.Entrant.Rolling1588.encodeGroup,
          ECDSAAdd.Entrant.Rolling1588.encodeAt, hk0, hkk, hk1, Bool.false_eq_true,
          if_true, if_false, decide_true, decide_false] using frame
      let Frame (sIdx : Nat) (V : Fp × Fp) :=
        RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
          (ECDSAAdd.Entrant.Rolling1588.stageCodeAt divide sIdx (History5.historyMap base (5 * k))) origin V.1 V.2
      have opening (V : Fp × Fp) : ECDSAAdd.Entrant.Rolling1588.StateTriple
          (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
            (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt divide (History5.historyMap base (5 * k))) origin V.1 V.2)
          (ECDSAAdd.Entrant.Rolling1588.onPacket k ECDSAAdd.Entrant.Rolling1588.stageOpen) (Frame 0 V) :=
        fun s r h => RouteA.Rolling1588.regular_open_frame P1Life.oddWord P1Life.oddWord divide k hi origin ctx V.1 V.2 s r h
      have step (sIdx lIdx pIdx : Nat) (hs : sIdx < 3)
          (hl : (lIdx, pIdx) ∈ ECDSAAdd.Entrant.Rolling1588.activeSlots divide sIdx) (V : Fp × Fp) :
          ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame sIdx V)
            (RouteA.Rolling1588.cellWith divide P k pIdx 2)
            (Frame sIdx (ECDSAAdd.Entrant.Rolling1588.regularStep divide k origin lIdx V)) :=
        fun s r h => RouteA.Rolling1588.regular_cellWith_frame P divide P1Life.oddWord P1Life.oddWord
          hlaw hsup k sIdx lIdx pIdx hi hs hl origin ctx enabled V.1 V.2 s r h
      have transfer (sIdx : Nat) (hs : sIdx < 2) (V : Fp × Fp) :
          ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame sIdx V)
            (ECDSAAdd.Entrant.Rolling1588.onPacket k (ECDSAAdd.Entrant.Rolling1588.stageTransition divide sIdx)) (Frame (sIdx + 1) V) :=
        fun s r h => RouteA.Rolling1588.regular_transition_frame P1Life.oddWord P1Life.oddWord divide k sIdx hi hs origin ctx V.1 V.2 s r h
      have closing (V : Fp × Fp) : ECDSAAdd.Entrant.Rolling1588.StateTriple (Frame 2 V)
          (ECDSAAdd.Entrant.Rolling1588.onPacket k ECDSAAdd.Entrant.Rolling1588.stageClose)
          (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
            (ECDSAAdd.Entrant.Rolling1588.codeEncodeAt (!divide) (History5.historyMap base (5 * k))) origin V.1 V.2) :=
        fun s r h => RouteA.Rolling1588.regular_close_frame P1Life.oddWord P1Life.oddWord divide k hi origin ctx V.1 V.2 s r h
      have h10 : (1 : Nat) ≠ 0 := by decide
      cases divide
      · let V1 := ECDSAAdd.Entrant.Rolling1588.regularStep false k origin 4 (X, Y)
        let V2 := ECDSAAdd.Entrant.Rolling1588.regularStep false k origin 3 V1
        let V3 := ECDSAAdd.Entrant.Rolling1588.regularStep false k origin 2 V2
        let V4 := ECDSAAdd.Entrant.Rolling1588.regularStep false k origin 1 V3
        let V5 := ECDSAAdd.Entrant.Rolling1588.regularStep false k origin 0 V4
        have hres := (opening (X, Y)).seq
          ((step 0 4 4 (by decide) (by decide) (X, Y)).seq
          ((transfer 0 (by decide) V1).seq
          ((step 1 3 3 (by decide) (by decide) V1).seq
          ((step 1 2 4 (by decide) (by decide) V2).seq
          ((transfer 1 (by decide) V3).seq
          ((step 2 1 4 (by decide) (by decide) V3).seq
          ((step 2 0 3 (by decide) (by decide) V4).seq (closing V5))))))))
        have hstep := hres current tape normalized
        rw [show V5 = ECDSAAdd.Entrant.Rolling1588.regularPayload false k origin (X, Y) from by
              simp only [V5, V4, V3, V2, V1, ECDSAAdd.Entrant.Rolling1588.regularPayload, Bool.false_eq_true, if_false],
            ECDSAAdd.Entrant.Rolling1588.regularPayload_eq false k hi origin enabled] at hstep
        simpa only [basePacketWith, Vout, ECDSAAdd.Entrant.Rolling1588.stageOpen,
          ECDSAAdd.Entrant.Rolling1588.stageClose, ECDSAAdd.Entrant.Rolling1588.stageTransition,
          ECDSAAdd.Entrant.Rolling1588.encodeGroup, ECDSAAdd.Entrant.Rolling1588.encodeAt,
          hk0, hkk, hk1, h10, Bool.false_eq_true, Bool.not_false, if_true, if_false,
          decide_true, decide_false, List.append_assoc] using hstep
      · let V1 := ECDSAAdd.Entrant.Rolling1588.regularStep true k origin 0 (X, Y)
        let V2 := ECDSAAdd.Entrant.Rolling1588.regularStep true k origin 1 V1
        let V3 := ECDSAAdd.Entrant.Rolling1588.regularStep true k origin 2 V2
        let V4 := ECDSAAdd.Entrant.Rolling1588.regularStep true k origin 3 V3
        let V5 := ECDSAAdd.Entrant.Rolling1588.regularStep true k origin 4 V4
        have hres := (opening (X, Y)).seq
          ((step 0 0 3 (by decide) (by decide) (X, Y)).seq
          ((step 0 1 4 (by decide) (by decide) V1).seq
          ((transfer 0 (by decide) V2).seq
          ((step 1 2 4 (by decide) (by decide) V2).seq
          ((step 1 3 3 (by decide) (by decide) V3).seq
          ((transfer 1 (by decide) V4).seq
          ((step 2 4 4 (by decide) (by decide) V4).seq (closing V5))))))))
        have hstep := hres current tape normalized
        rw [show V5 = ECDSAAdd.Entrant.Rolling1588.regularPayload true k origin (X, Y) from by
              simp only [V5, V4, V3, V2, V1, ECDSAAdd.Entrant.Rolling1588.regularPayload, if_true],
            ECDSAAdd.Entrant.Rolling1588.regularPayload_eq true k hi origin enabled] at hstep
        simpa only [basePacketWith, Vout, ECDSAAdd.Entrant.Rolling1588.stageOpen,
          ECDSAAdd.Entrant.Rolling1588.stageClose, ECDSAAdd.Entrant.Rolling1588.stageTransition,
          ECDSAAdd.Entrant.Rolling1588.encodeGroup, ECDSAAdd.Entrant.Rolling1588.encodeAt,
          hk0, hkk, hk1, h10, Bool.false_eq_true, Bool.not_true, if_true, if_false,
          decide_true, decide_false, List.append_assoc] using hstep)
    state records input
  have same := Replay5.placed_eq (Placement5.pi k) (basePacketWith divide P k)
    (fun q hq => Placement5.pi_outside k q hi hq) state records
    (RouteA.Rolling1588.cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx X Y state input)
    (RouteA.Rolling1588.cutFrame_zero_region P1Life.oddWord P1Life.oddWord _ origin ctx _ _ _ raw.2)
  rw [same]; exact raw

theorem packet_oddLoan_cut_frame (d : Nat) (divide : Bool) (hd : d ≤ 44)
    (k : Nat) (lo : 1 ≤ k) (hi : k < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if divide then k else k + 1) origin X Y)
      (OddFullPass.P1LifeLoan.packet divide d k)
      (fun state => let V := CompressedFieldSupport.directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) (X, Y)
        RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if divide then k + 1 else k) origin V.1 V.2 state) := by
  have hsub : wires (OddFullPass.P1LifeLoan.basePacket divide d k) ⊆
      wires (ECDSAAdd.Entrant.Rolling1588.basePacket divide k) := by
    have hp := OddFullPass.P1LifeLoan.packet_wires_sub divide d k hd
    have hps := StairLoanGroupSupport.packet_sub divide d k (by omega)
    have hcomb := hp.trans hps
    rw [OddFullPass.P1LifeLoan.packet, StairGroups.packet_zero, ECDSAAdd.Entrant.Rolling1588.packet,
        renameProgram_support, renameProgram_support] at hcomb
    intro q hq
    obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp (hcomb (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
    exact (Equiv.injective _ eq) ▸ hv
  have hpeq : OddFullPass.P1LifeLoan.packet divide d k =
      renameProgram (shifted (Placement5.pi k)) (basePacketWith divide (half760OddLoan d divide) k) := by
    rw [OddFullPass.P1LifeLoan.packet, basePacket_eq_with]
  rw [hpeq]
  exact packet_with_cut_frame (half760OddLoan d divide) divide
    (half760OddLoan_law d divide hd) (half760OddLoan_support d divide hd)
    k lo hi (basePacket_eq_with divide d k ▸ hsub) origin ctx enabled X Y

theorem groups_oddLoan_cut_frame (d : Nat) (divide : Bool) (hd : d ≤ 44)
    (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp) :
    ECDSAAdd.Entrant.Rolling1588.StateTriple
      (RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if divide then j else j + n) origin X Y)
      (OddFullPass.P1LifeLoan.groups divide d j n)
      (fun state => let V := Replay5.groupsPayload divide origin j n (X, Y)
        RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (if divide then j + n else j) origin V.1 V.2 state) :=
  RouteA.Rolling1588.route_cut_sequence_frame divide (OddFullPass.P1LifeLoan.packet divide d)
    (fun k V => CompressedFieldSupport.directionalPayload (!divide) (mixedTranscriptControls origin (base 2400) (Replay5.letters k)) V)
    (fun k (V : Fp × Fp) => RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord k origin V.1 V.2) 102
    (fun k hk kb V => packet_oddLoan_cut_frame d divide hd k hk kb origin ctx enabled V.1 V.2)
    j n lo hi (X, Y)

theorem oddFirstHalf_law (divide : Bool) :
    JointOdd1588.OddHalfLaw (StairPacket.WindowCallerCosts.oddFirstHalf divide) divide :=
  fun origin clean X Y =>
    P1Life.half_frame (base 760) divide base (base 2409) hn760 mem760 origin clean X Y

end ECDSAAdd.Entrant.OddFullPassBridge
end

end
-- ==== end OddTailPart1 ====

-- ==== begin OddLockstepBase ====
section

/-!
# Odd-word stock lockstep bridge (Division + Multiplication)

Couples the stock odd-word kernel heads (`stockOddDivHead`, `stockOddMulHead`,
using `WindowFieldCosts.ogroup`, `OddFullPass.P1LifeLoan.hostedGroup`,
`JointOdd1588.hostedFirstPacketOdd`, `OddFullPass.CompareDecoderOdd`,
`OddFullPass.InverseTailCOdd`, and `OddFullPass.HalfConvertOdd`) directly
against the existing stock heads (`oldDivHead`, `oldMulHead`) step by step
along `StairField13V3Clean`'s 25-piece decomposition.

Produces the four clean deliverables consumed by the window replay tail:
1. `stockOddDiv_cut3`: cut-3 `OCut 1` + `Loan` + `AgreeRY` against `ExteriorEntryCut.stockPrefix`.
2. `stockOddDivHead_eq_oldDivHead`: exact state equality `run stockOddDivHead m tOdd = run oldDivHead n tStd`.
3. `stockOddMul_cut21`: cut-21 `OCut 85` + `Loan` + `AgreeRY` against `WindowExitFrame.stockPrefix k`.
4. `stockOddMulHead_agree_oldMulHead`: `AgreeOutsideR` + `regValue fieldR = oddWord (Y * x / 2)`
   against `oldMulHead`, plus `mulRawTail_disjoint_fieldR` and `outMap_fix_fieldR`.
-/

set_option autoImplicit false

section

namespace ECDSAAdd.Entrant.OddStockLockstep

open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout
open StairLoanExitReachX StairPacket

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] run measurementCount wires renameProgram

/-! ## Section 1: Wire regions, `AgreeRY`, `AgreeOutsideR`, `OddRel`, fixed-point lemmas -/

abbrev fieldR : List Wire := wireBlock base 2056 256
abbrev fieldY : List Wire := wireBlock base 770 256
abbrev ryWires : List Wire := fieldR ++ fieldY

theorem ryWires_eq : ryWires = fieldR ++ fieldY := rfl

theorem mem_ryWires_iff (q : Wire) : q ∈ ryWires ↔ q ∈ fieldR ∨ q ∈ fieldY := by
  rw [ryWires_eq, List.mem_append]

private theorem mem_fieldR_iff (q : Wire) : q ∈ fieldR ↔ 2072 ≤ q ∧ q < 2328 := by
  simp only [fieldR, wireBlock, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; change 2072 ≤ i + 16 ∧ i + 16 < 2328; omega
  · rintro ⟨h1, h2⟩
    have h16 : 16 ≤ q := Nat.le_trans (by decide) h1
    exact ⟨q - 16, ⟨Nat.le_sub_of_add_le h1, Nat.sub_lt_left_of_lt_add h16 h2⟩,
      Nat.sub_add_cancel h16⟩

private theorem mem_fieldY_iff (q : Wire) : q ∈ fieldY ↔ 786 ≤ q ∧ q < 1042 := by
  simp only [fieldY, wireBlock, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; change 786 ≤ i + 16 ∧ i + 16 < 1042; omega
  · rintro ⟨h1, h2⟩
    have h16 : 16 ≤ q := Nat.le_trans (by decide) h1
    exact ⟨q - 16, ⟨Nat.le_sub_of_add_le h1, Nat.sub_lt_left_of_lt_add h16 h2⟩,
      Nat.sub_add_cancel h16⟩

def notFieldR (q : Wire) : Bool := !(decide (2072 ≤ q ∧ q < 2328))
def notRY (q : Wire) : Bool := notFieldR q && !(decide (786 ≤ q ∧ q < 1042))

theorem notFieldR_iff (q : Wire) : notFieldR q = true ↔ q ∉ fieldR := by
  simp only [notFieldR, Bool.not_eq_true', decide_eq_false_iff_not, mem_fieldR_iff]

theorem notRY_iff (q : Wire) : notRY q = true ↔ q ∉ ryWires := by
  simp only [notRY, Bool.and_eq_true, notFieldR_iff, Bool.not_eq_true',
    decide_eq_false_iff_not, mem_ryWires_iff, mem_fieldY_iff, not_or]

/-- Two states agree on phase and on every wire outside `ryWires = fieldR ++ fieldY`. -/
def AgreeRY (a b : State) : Prop :=
  a.phase = b.phase ∧ ∀ q, q ∉ ryWires → a.basis q = b.basis q

/-- Two states agree on phase and on every wire outside `fieldR`. -/
def AgreeOutsideR (a b : State) : Prop :=
  a.phase = b.phase ∧ ∀ q, q ∉ fieldR → a.basis q = b.basis q

/-- Binary state relation carrying the odd-word vs center-word register correspondence
without threading explicit `(X, Y)` parameters across disjoint segments. -/
def OddRel (wR wY : Fp → Nat) (a b : State) : Prop :=
  AgreeRY a b ∧
  (∀ X : Fp, regValue fieldR b.basis = centerWord X → regValue fieldR a.basis = wR X) ∧
  (∀ Y : Fp, regValue fieldY b.basis = centerWord Y → regValue fieldY a.basis = wY Y)

theorem agreeRY_refl (a : State) : AgreeRY a a := ⟨rfl, fun _ _ => rfl⟩

theorem agreeRY_symm {a b : State} (h : AgreeRY a b) : AgreeRY b a :=
  ⟨h.1.symm, fun q hq => (h.2 q hq).symm⟩

theorem agreeRY_trans {a b c : State} (h1 : AgreeRY a b) (h2 : AgreeRY b c) : AgreeRY a c :=
  ⟨h1.1.trans h2.1, fun q hq => (h1.2 q hq).trans (h2.2 q hq)⟩

theorem agreeOutsideR_refl (a : State) : AgreeOutsideR a a := ⟨rfl, fun _ _ => rfl⟩

theorem agreeOutsideR_symm {a b : State} (h : AgreeOutsideR a b) : AgreeOutsideR b a :=
  ⟨h.1.symm, fun q hq => (h.2 q hq).symm⟩

theorem agreeOutsideR_trans {a b c : State} (h1 : AgreeOutsideR a b) (h2 : AgreeOutsideR b c) :
    AgreeOutsideR a c :=
  ⟨h1.1.trans h2.1, fun q hq => (h1.2 q hq).trans (h2.2 q hq)⟩

theorem agreeRY_of_agreeOutsideR {a b : State} (h : AgreeOutsideR a b) : AgreeRY a b :=
  ⟨h.1, fun q hq => h.2 q (fun hr => hq ((mem_ryWires_iff q).mpr (Or.inl hr)))⟩

theorem agreeOutsideR_of_agreeRY {a b : State} (h : AgreeRY a b)
    (hy : ∀ q ∈ fieldY, a.basis q = b.basis q) : AgreeOutsideR a b := by
  refine ⟨h.1, fun q hq => ?_⟩
  by_cases hfy : q ∈ fieldY
  · exact hy q hfy
  · exact h.2 q (fun hry => ((mem_ryWires_iff q).mp hry).elim hq hfy)

theorem basis_eq_of_regValue_eq (r : List Wire) (a b : BasisState)
    (h : regValue r a = regValue r b) : ∀ q ∈ r, a q = b q := by
  intro q hq
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
  have hb : (a (r.getD i 0)).toNat = (b (r.getD i 0)).toNat := by
    rw [Arithmetic.regValue_bit r i 0 a hi, Arithmetic.regValue_bit r i 0 b hi, h]
  rw [List.getD_eq_getElem _ _ hi] at hb
  cases h1 : a r[i] <;> cases h2 : b r[i] <;> simp_all

theorem state_eq_of_agreeOutsideR {a b : State} (h : AgreeOutsideR a b)
    (hr : regValue fieldR a.basis = regValue fieldR b.basis) : a = b := by
  apply State.extensionality _ _ h.1
  funext q
  by_cases hfr : q ∈ fieldR
  · exact basis_eq_of_regValue_eq fieldR a.basis b.basis hr q hfr
  · exact h.2 q hfr

theorem centerWord_injective {x y : Fp} (h : centerWord x = centerWord y) : x = y := by
  have hd : centerFp x = centerFp y := by
    rw [← BalancedField.centerWord_decode x, ← BalancedField.centerWord_decode y, h]
  have hx := BalancedField.centerFp_cast x
  have hy := BalancedField.centerFp_cast y
  rw [← hx, ← hy, hd]

theorem oddRel_of_agreeRY_values {wR wY : Fp → Nat} {a b : State} (X Y : Fp)
    (hag : AgreeRY a b)
    (hRb : regValue fieldR b.basis = centerWord X)
    (hYb : regValue fieldY b.basis = centerWord Y)
    (hRa : regValue fieldR a.basis = wR X)
    (hYa : regValue fieldY a.basis = wY Y) :
    OddRel wR wY a b := by
  refine ⟨hag, ?_, ?_⟩
  · intro X' hX'
    have eq := centerWord_injective (hRb.symm.trans hX')
    subst eq; exact hRa
  · intro Y' hY'
    have eq := centerWord_injective (hYb.symm.trans hY')
    subst eq; exact hYa

theorem agreeRY_disjoint (P : Program) (hP : ∀ q ∈ wires P, q ∉ ryWires)
    {a b : State} (h : AgreeRY a b) (m : List Bool) :
    AgreeRY (run P m a) (run P m b) := by
  have inc := Arithmetic.run_local_increment P a b m (fun q hq => h.2 q (hP q hq))
  have hp : (run P m a).phase = (run P m b).phase := by
    have h1 := inc.1; rw [h.1] at h1
    revert h1
    generalize (run P m a).phase = x
    generalize (run P m b).phase = y
    generalize b.phase = z
    cases x <;> cases y <;> cases z <;> decide
  refine ⟨hp, fun q hq => ?_⟩
  by_cases hp' : q ∈ wires P
  · exact inc.2 q hp'
  · rw [run_preserves_outside P m a q hp', run_preserves_outside P m b q hp']
    exact h.2 q hq

theorem oddRel_disjoint {wR wY : Fp → Nat} (P : Program) (hP : ∀ q ∈ wires P, q ∉ ryWires)
    {a b : State} (h : OddRel wR wY a b) (m : List Bool) :
    OddRel wR wY (run P m a) (run P m b) := by
  have keepR (s : State) : regValue fieldR (run P m s).basis = regValue fieldR s.basis :=
    regValue_congr _ _ _ (fun q hq => run_preserves_outside P m s q
      (fun hw => hP q hw ((mem_ryWires_iff q).mpr (Or.inl hq))))
  have keepY (s : State) : regValue fieldY (run P m s).basis = regValue fieldY s.basis :=
    regValue_congr _ _ _ (fun q hq => run_preserves_outside P m s q
      (fun hw => hP q hw ((mem_ryWires_iff q).mpr (Or.inr hq))))
  refine ⟨agreeRY_disjoint P hP h.1 m, ?_, ?_⟩
  · intro X hX; rw [keepR a]; exact h.2.1 X (by rwa [keepR b] at hX)
  · intro Y hY; rw [keepY a]; exact h.2.2 Y (by rwa [keepY b] at hY)

theorem agreeOutsideR_disjoint (P : Program) (hP : ∀ q ∈ wires P, q ∉ fieldR)
    {a b : State} (h : AgreeOutsideR a b) (m : List Bool) :
    AgreeOutsideR (run P m a) (run P m b) := by
  have inc := Arithmetic.run_local_increment P a b m (fun q hq => h.2 q (hP q hq))
  have hp : (run P m a).phase = (run P m b).phase := by
    have h1 := inc.1; rw [h.1] at h1
    revert h1
    generalize (run P m a).phase = x
    generalize (run P m b).phase = y
    generalize b.phase = z
    cases x <;> cases y <;> cases z <;> decide
  refine ⟨hp, fun q hq => ?_⟩
  by_cases hp' : q ∈ wires P
  · exact inc.2 q hp'
  · rw [run_preserves_outside P m a q hp', run_preserves_outside P m b q hp']
    exact h.2 q hq

theorem regValue_fieldR_disjoint (P : Program) (hP : ∀ q ∈ wires P, q ∉ fieldR)
    (a : State) (m : List Bool) :
    regValue fieldR (run P m a).basis = regValue fieldR a.basis :=
  regValue_congr _ _ _ (fun q hq => run_preserves_outside P m a q (fun hw => hP q hw hq))

/-! ### Fixed-point & disjointness checks (`decide +kernel`) -/

theorem fieldPlace_fix_ryWires : ∀ q ∈ ryWires, fieldPlace q = q := by
  have h : ryWires.all (fun q => decide (fieldPlace q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem fieldPlaceInv_fix_ryWires : ∀ q ∈ ryWires, fieldPlaceInv q = q := by
  intro q hq
  have h := congrArg fieldPlaceInv (fieldPlace_fix_ryWires q hq)
  rw [inv_fieldPlace] at h
  exact h.symm

theorem fieldMap_fix_ryWires : ∀ q ∈ ryWires, fieldMap q = q := by
  have h : ryWires.all (fun q => decide (fieldMap q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem lowMap_fix_ryWires : ∀ q ∈ ryWires, lowMap q = q := by
  have h : ryWires.all (fun q => decide (lowMap q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem sig511_fix_ryWires : ∀ q ∈ ryWires, OB5.sig 511 q = q := by
  have h : ryWires.all (fun q => decide (OB5.sig 511 q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem borrow_fix_ryWires : ∀ q ∈ ryWires, Prefix1590.borrow q = q := by
  have h : ryWires.all (fun q => decide (Prefix1590.borrow q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem phaseHost_fix_fieldR : ∀ q ∈ fieldR, Rolling1588Lifetime.phaseHost q = q := by
  have h : fieldR.all (fun q => decide (Rolling1588Lifetime.phaseHost q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem outMap_fix_fieldR : ∀ q ∈ fieldR, Stair44Kernel.outMap q = q := by
  have h : fieldR.all (fun q => decide (Stair44Kernel.outMap q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem fieldR_disjoint_pool : ∀ q ∈ skywalkPoolWires base, q ∉ fieldR := by
  have h : (skywalkPoolWires base).all notFieldR = true := by decide +kernel
  intro q hq; exact (notFieldR_iff q).mp (List.all_eq_true.mp h q hq)

theorem ryWires_off : ∀ q ∈ ryWires, Off q := by
  have h : ryWires.all (fun q => decide (q ∉ EP)) = true := by decide +kernel
  intro q hq
  exact off_of_not_EP q (of_decide_eq_true (List.all_eq_true.mp h q hq))

theorem futurePayload_not_ryWires : ∀ B ∈ budgets, ∀ q ∈ futurePayload B, q ∉ ryWires := by
  have h : budgets.all (fun B => (futurePayload B).all notRY) = true := by decide +kernel
  intro B hB q hq
  exact (notRY_iff q).mp (List.all_eq_true.mp (List.all_eq_true.mp h B hB) q hq)

theorem exclusiveRoles_not_ryWires : ∀ q ∈ StairSchedule.exclusiveRoles, q ∉ ryWires := by
  have h : StairSchedule.exclusiveRoles.all notRY = true := by decide +kernel
  intro q hq; exact (notRY_iff q).mp (List.all_eq_true.mp h q hq)

theorem hosts_not_ryWires : ∀ B ∈ budgets, ∀ q ∈ hosts B, q ∉ ryWires := by
  have h : budgets.all (fun B => (hosts B).all notRY) = true := by decide +kernel
  intro B hB q hq
  exact (notRY_iff q).mp (List.all_eq_true.mp (List.all_eq_true.mp h B hB) q hq)

theorem poolHosts_not_ryWires : ∀ q ∈ StairV3Primitives.poolHosts, q ∉ ryWires := by
  have h : StairV3Primitives.poolHosts.all notRY = true := by decide +kernel
  intro q hq; exact (notRY_iff q).mp (List.all_eq_true.mp h q hq)

theorem archives_not_fieldR : ∀ (b : StockArchiveBanks.Bank) (i : Fin 16),
    StockArchiveBanks.siteAt b i ∉ fieldR := by
  have h : ∀ (b : StockArchiveBanks.Bank) (i : Fin 16),
      notFieldR (StockArchiveBanks.siteAt b i) = true := by decide +kernel
  intro b i; exact (notFieldR_iff _).mp (h b i)

theorem fieldR_disjoint_fieldY : ∀ q ∈ fieldR, q ∉ fieldY := by
  intro q hq hy
  have h1 := (mem_fieldR_iff q).mp hq
  have h2 := (mem_fieldY_iff q).mp hy
  simp only [Wire] at *; omega

theorem pullIn_agreeRY {a b : State} (h : AgreeRY a b) :
    AgreeRY (pullIn a) (pullIn b) := by
  refine ⟨h.1, fun q hq => ?_⟩
  change a.basis (fieldPlace q) = b.basis (fieldPlace q)
  apply h.2
  intro hmem
  have eq := fieldPlaceInv_fix_ryWires _ hmem
  rw [inv_fieldPlace] at eq
  exact hq (eq ▸ hmem)

theorem pullOut_agreeRY {a b : State} (h : AgreeRY a b) :
    AgreeRY (pullOut a) (pullOut b) := by
  refine ⟨h.1, fun q hq => ?_⟩
  change a.basis (fieldPlaceInv q) = b.basis (fieldPlaceInv q)
  apply h.2
  intro hmem
  have eq := fieldPlace_fix_ryWires _ hmem
  rw [fieldPlace_inv] at eq
  exact hq (eq ▸ hmem)

theorem pullIn_regValue_R (a : State) : regValue fieldR (pullIn a).basis = regValue fieldR a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    change a.basis (fieldPlace q) = a.basis q
    rw [fieldPlace_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inl hq))])

theorem pullIn_regValue_Y (a : State) : regValue fieldY (pullIn a).basis = regValue fieldY a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    change a.basis (fieldPlace q) = a.basis q
    rw [fieldPlace_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inr hq))])

theorem pullIn_oddRel {wR wY : Fp → Nat} {a b : State} (h : OddRel wR wY a b) :
    OddRel wR wY (pullIn a) (pullIn b) := by
  refine ⟨pullIn_agreeRY h.1, ?_, ?_⟩
  · intro X hX; rw [pullIn_regValue_R]; exact h.2.1 X (by rwa [pullIn_regValue_R] at hX)
  · intro Y hY; rw [pullIn_regValue_Y]; exact h.2.2 Y (by rwa [pullIn_regValue_Y] at hY)

theorem pullOut_oddRel {wR wY : Fp → Nat} {a b : State} (h : OddRel wR wY a b) :
    OddRel wR wY (pullOut a) (pullOut b) := by
  have rEq (s : State) : regValue fieldR (pullOut s).basis = regValue fieldR s.basis :=
    regValue_congr _ _ _ (fun q hq => by
      change s.basis (fieldPlaceInv q) = s.basis q
      rw [fieldPlaceInv_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inl hq))])
  have yEq (s : State) : regValue fieldY (pullOut s).basis = regValue fieldY s.basis :=
    regValue_congr _ _ _ (fun q hq => by
      change s.basis (fieldPlaceInv q) = s.basis q
      rw [fieldPlaceInv_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inr hq))])
  refine ⟨pullOut_agreeRY h.1, ?_, ?_⟩
  · intro X hX; rw [rEq]; exact h.2.1 X (by rwa [rEq] at hX)
  · intro Y hY; rw [yEq]; exact h.2.2 Y (by rwa [yEq] at hY)

theorem pullState_sig511_agreeRY {a b : State} (h : AgreeRY a b) :
    AgreeRY (pullState (OB5.sig 511) a) (pullState (OB5.sig 511) b) := by
  refine ⟨h.1, fun q hq => ?_⟩
  change a.basis (OB5.sig 511 q) = b.basis (OB5.sig 511 q)
  apply h.2
  intro hmem
  have eq := sig511_fix_ryWires _ hmem
  rw [OB5.sig_invol 511 (by decide)] at eq
  exact hq (eq ▸ hmem)

theorem pullState_sig511_regValue_R (a : State) :
    regValue fieldR (pullState (OB5.sig 511) a).basis = regValue fieldR a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    change a.basis (OB5.sig 511 q) = a.basis q
    rw [sig511_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inl hq))])

theorem pullState_sig511_regValue_Y (a : State) :
    regValue fieldY (pullState (OB5.sig 511) a).basis = regValue fieldY a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    change a.basis (OB5.sig 511 q) = a.basis q
    rw [sig511_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inr hq))])

theorem pullState_fieldMap_agreeRY {a b : State} (h : AgreeRY a b) :
    AgreeRY (pullState fieldMap a) (pullState fieldMap b) := by
  refine ⟨h.1, fun q hq => ?_⟩
  change a.basis (fieldMap q) = b.basis (fieldMap q)
  apply h.2
  intro hmem
  have eq := fieldMap_fix_ryWires _ hmem
  have qeq : fieldMap q = fieldMap (fieldMap q) := eq.symm
  exact hq ((fieldMap_injective qeq).symm ▸ hmem)

theorem pullState_fieldMap_regValue_R (a : State) :
    regValue fieldR (pullState fieldMap a).basis = regValue fieldR a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    change a.basis (fieldMap q) = a.basis q
    rw [fieldMap_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inl hq))])

theorem pullState_fieldMap_regValue_Y (a : State) :
    regValue fieldY (pullState fieldMap a).basis = regValue fieldY a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    change a.basis (fieldMap q) = a.basis q
    rw [fieldMap_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inr hq))])

/-! ### `ryWires`-disjointness of all shared / segment / glue programs -/

theorem disjoint_ryWires_of_allSites {P : Program} (h : StairWireCheck.allSites notRY P = true) :
    ∀ q ∈ wires P, q ∉ ryWires :=
  fun q hq => (notRY_iff q).mp (StairWireCheck.allSites_sound notRY P h q hq)

theorem disjoint_ryWires_append {A B : Program}
    (hA : ∀ q ∈ wires A, q ∉ ryWires) (hB : ∀ q ∈ wires B, q ∉ ryWires) :
    ∀ q ∈ wires (A ++ B), q ∉ ryWires := by
  intro q hq
  rw [wires_append, Finset.mem_union] at hq
  exact hq.elim (hA q) (hB q)

theorem disjoint_ryWires_rename {f : Wire → Wire} (inj : Function.Injective f)
    (fix : ∀ q ∈ ryWires, f q = q) {P : Program} (hP : ∀ q ∈ wires P, q ∉ ryWires) :
    ∀ q ∈ wires (renameProgram f P), q ∉ ryWires := by
  intro q hq hmem
  rw [renameProgram_support] at hq
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  have eq : f (f r) = f r := fix (f r) hmem
  exact hP r hr ((inj eq) ▸ hmem)

theorem disjoint_ryWires_liftF {P : Program} (hP : ∀ q ∈ wires P, q ∉ ryWires) :
    ∀ q ∈ wires (liftF P), q ∉ ryWires := by
  rw [show liftF P = renameProgram ExteriorPorts.fieldEquiv P from ExteriorPorts.placedShape P]
  exact disjoint_ryWires_rename ExteriorPorts.fieldEquiv.injective fieldPlace_fix_ryWires hP

theorem disjoint_ryWires_fieldRename {P : Program} (hP : ∀ q ∈ wires P, q ∉ ryWires) :
    ∀ q ∈ wires (StairSchedule.fieldRename P), q ∉ ryWires := by
  rw [fieldRename_eq]
  exact disjoint_ryWires_rename fieldMap_injective fieldMap_fix_ryWires hP

private theorem rowSitesL_notRY (B : Nat) (hB : B ∈ budgets) :
    ∀ q ∈ StairPhysicalPrimitives.rowSitesL B, q ∉ ryWires := by
  have ok : budgets.all (fun B => (StairPhysicalPrimitives.rowSitesL B).all notRY) = true := by
    decide +kernel
  intro q hq
  exact (notRY_iff q).mp (List.all_eq_true.mp (List.all_eq_true.mp ok B hB) q hq)

private theorem of_rowSitesL {B : Nat} (hB : B ∈ budgets) {P : Program}
    (sub : ∀ q ∈ wires P, q ∈ StairPhysicalPrimitives.rowSitesL B) :
    ∀ q ∈ wires P, q ∉ ryWires :=
  fun q hq => rowSitesL_notRY B hB q (sub q hq)

theorem clearProgram_notRY : ∀ q ∈ wires FourScratchWindow.clearProgram, q ∉ ryWires :=
  disjoint_ryWires_of_allSites (by decide +kernel)

theorem unprefix_notRY : ∀ q ∈ wires FourScratchWindow.unprefix, q ∉ ryWires :=
  disjoint_ryWires_of_allSites (by decide +kernel)

theorem paritySetup_notRY : ∀ q ∈ wires StairSchedule.paritySetup, q ∉ ryWires :=
  disjoint_ryWires_of_allSites (by decide +kernel)

theorem hostedX_notRY : ∀ q ∈ wires StairSchedule.hostedX, q ∉ ryWires :=
  disjoint_ryWires_of_allSites (by decide +kernel)

private theorem forwardSites_notRY : ∀ q ∈ StairTerminalV3.forwardSites, q ∉ ryWires := by
  have h : StairTerminalV3.forwardSites.all notRY = true := by decide +kernel
  intro q hq; exact (notRY_iff q).mp (List.all_eq_true.mp h q hq)

private theorem reverseSites_notRY : ∀ q ∈ StairTerminalV3.reverseSites, q ∉ ryWires := by
  have h : StairTerminalV3.reverseSites.all notRY = true := by decide +kernel
  intro q hq; exact (notRY_iff q).mp (List.all_eq_true.mp h q hq)

theorem forwardSeg_notRY (B B' a b : Nat) (hB : B ∈ budgets) (hB' : B' ∈ budgets)
    (ha : a = startFor B) (hb : b = endFor B)
    (ho : ∀ q ∈ wires (checkpointPrimitives.orient b), q ∉ ryWires)
    (hp : ∀ q ∈ wires (renameProgram (OB5.sig b) (Rolling1588.Integer.packFirst base true b)), q ∉ ryWires) :
    ∀ q ∈ wires (StairSchedule.forwardSegment checkpointPrimitives B B' a b), q ∉ ryWires := by
  subst ha; subst hb
  exact disjoint_ryWires_append
    (disjoint_ryWires_append
      (disjoint_ryWires_append
        (disjoint_ryWires_append
          (disjoint_ryWires_append
            (of_rowSitesL hB (StairPhysicalPrimitives.unpack_rows B hB))
            (of_rowSitesL hB (StairPhysicalPrimitives.tickForward_rows B hB)))
          (of_rowSitesL hB (StairPhysicalPrimitives.middleForward_rows B hB)))
        ho)
      hp)
    (of_rowSitesL hB' (StairPhysicalPrimitives.pack_rows B' hB'))

theorem reverseSeg_notRY (B B' a b : Nat) (hB : B ∈ budgets) (hB' : B' ∈ budgets)
    (ha : a = startFor B) (hb : b = endFor B)
    (hrev : StairPhysicalPrimitivesFix505.reverseEnd B = b)
    (ho : ∀ q ∈ wires (checkpointPrimitives.orientR b), q ∉ ryWires)
    (hu : ∀ q ∈ wires (renameProgram (OB5.sig b) (Rolling1588.unpackAtTick true b)), q ∉ ryWires) :
    ∀ q ∈ wires (StairSchedule.reverseSegment checkpointPrimitives B B' a b), q ∉ ryWires := by
  subst ha; subst hb
  exact disjoint_ryWires_append
    (disjoint_ryWires_append
      (disjoint_ryWires_append
        (disjoint_ryWires_append
          (disjoint_ryWires_append
            (of_rowSitesL hB' (StairPhysicalPrimitives.unpack_rows B' hB'))
            hu)
          ho)
        (of_rowSitesL hB (hrev ▸ StairPhysicalPrimitivesFix505.middleReverseFix_rows B hB)))
      (of_rowSitesL hB (StairPhysicalPrimitives.tickReverse_rows B hB)))
    (of_rowSitesL hB (StairPhysicalPrimitives.pack_rows B hB))

theorem forward425_notRY : ∀ q ∈ wires (StairSchedule.forwardSegment cp 87 62 425 450), q ∉ ryWires :=
  forwardSeg_notRY 87 62 425 450 (by decide) (by decide) rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem forward450_notRY : ∀ q ∈ wires (StairSchedule.forwardSegment cp 62 47 450 465), q ∉ ryWires :=
  forwardSeg_notRY 62 47 450 465 (by decide) (by decide) rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem forward465_notRY : ∀ q ∈ wires (StairSchedule.forwardSegment cp 47 32 465 480), q ∉ ryWires :=
  forwardSeg_notRY 47 32 465 480 (by decide) (by decide) rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem forward480_notRY : ∀ q ∈ wires (StairSchedule.forwardSegment cp 32 22 480 490), q ∉ ryWires :=
  forwardSeg_notRY 32 22 480 490 (by decide) (by decide) rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem forward490_notRY : ∀ q ∈ wires (StairSchedule.forwardSegment cp 22 12 490 500), q ∉ ryWires :=
  forwardSeg_notRY 22 12 490 500 (by decide) (by decide) rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem reverse425_notRY : ∀ q ∈ wires (StairSchedule.reverseSegment cp 87 62 425 450), q ∉ ryWires :=
  reverseSeg_notRY 87 62 425 450 (by decide) (by decide) rfl rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem reverse450_notRY : ∀ q ∈ wires (StairSchedule.reverseSegment cp 62 47 450 465), q ∉ ryWires :=
  reverseSeg_notRY 62 47 450 465 (by decide) (by decide) rfl rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem reverse465_notRY : ∀ q ∈ wires (StairSchedule.reverseSegment cp 47 32 465 480), q ∉ ryWires :=
  reverseSeg_notRY 47 32 465 480 (by decide) (by decide) rfl rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem reverse480_notRY : ∀ q ∈ wires (StairSchedule.reverseSegment cp 32 22 480 490), q ∉ ryWires :=
  reverseSeg_notRY 32 22 480 490 (by decide) (by decide) rfl rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem reverse490_notRY : ∀ q ∈ wires (StairSchedule.reverseSegment cp 22 12 490 500), q ∉ ryWires :=
  reverseSeg_notRY 22 12 490 500 (by decide) (by decide) rfl rfl rfl
    (disjoint_ryWires_of_allSites (by decide +kernel)) (disjoint_ryWires_of_allSites (by decide +kernel))

theorem forwardLast_notRY : ∀ q ∈ wires (StairSchedule.forwardLast cp), q ∉ ryWires := by
  have term : ∀ q ∈ wires cp.forwardTerminal, q ∉ ryWires := fun q hq =>
    forwardSites_notRY q (List.mem_toFinset.mp (StairTerminalV3.forwardTerminalV3_wires hq))
  exact disjoint_ryWires_append
    (disjoint_ryWires_append
      (disjoint_ryWires_append
        (of_rowSitesL (B := 12) (by decide) (StairPhysicalPrimitives.unpack_rows 12 (by decide)))
        (of_rowSitesL (B := 12) (by decide) (StairPhysicalPrimitives.tickForward_rows 12 (by decide))))
      (of_rowSitesL (B := 12) (by decide) (StairPhysicalPrimitives.middleForward_rows 12 (by decide))))
    term

theorem reverseLast_notRY : ∀ q ∈ wires (StairSchedule.reverseLast cp), q ∉ ryWires := by
  have term : ∀ q ∈ wires cp.reverseTerminal, q ∉ ryWires := fun q hq =>
    reverseSites_notRY q (List.mem_toFinset.mp (StairTerminalV3.reverseTerminalV3_wires hq))
  exact disjoint_ryWires_append
    (disjoint_ryWires_append
      (disjoint_ryWires_append
        term
        (of_rowSitesL (B := 12) (by decide) (StairPhysicalPrimitivesFix505.middleReverseFix_rows 12 (by decide))))
      (of_rowSitesL (B := 12) (by decide) (StairPhysicalPrimitives.tickReverse_rows 12 (by decide))))
    (of_rowSitesL (B := 12) (by decide) (StairPhysicalPrimitives.pack_rows 12 (by decide)))

theorem firstUnpack_notFieldR :
    ∀ q ∈ wires (renameProgram Rolling1588Lifetime.phaseHost cp.firstUnpack), q ∉ fieldR := by
  have raw : ∀ q ∈ wires cp.firstUnpack, q ∉ fieldR := by
    have h4 : (StairPhysicalPrimitives.rowSitesL 87).all (fun q => notFieldR (phaseRelabel q)) = true := by decide +kernel
    have hrows : ∀ q ∈ wires (renameProgram phaseRelabel (StairPhysicalPrimitives.unpack 87)), q ∉ fieldR := by
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
      exact (notFieldR_iff _).mp (List.all_eq_true.mp h4 w (StairPhysicalPrimitives.unpack_rows 87 (by decide) w hw))
    have hrest : ∀ q ∈ wires StairPhysicalPhase.phaseBReturn, q ∉ fieldR := by
      have h : StairWireCheck.allSites notFieldR StairPhysicalPhase.phaseBReturn = true := by decide +kernel
      exact fun q hq => (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h q hq)
    have hunp : ∀ q ∈ wires (renameProgram (OB5.sig 425) (Rolling1588.unpackAtTick true 425)), q ∉ fieldR := by
      have h : StairWireCheck.allSites notFieldR (renameProgram (OB5.sig 425) (Rolling1588.unpackAtTick true 425)) = true := by decide +kernel
      exact fun q hq => (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h q hq)
    have hori : ∀ q ∈ wires (renameProgram StairV3Primitives.xRelabel (StairV3Primitives.orient 425)), q ∉ fieldR := by
      have h : StairWireCheck.allSites notFieldR (renameProgram StairV3Primitives.xRelabel (StairV3Primitives.orient 425)) = true := by decide +kernel
      exact fun q hq => (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h q hq)
    intro q hq
    simp only [cp, checkpointPrimitives, StairV3Primitives.primitives, StairV3Primitives.firstUnpack,
      wires_append, Finset.mem_union] at hq
    rcases hq with ((h | h) | h) | h
    · exact hrows q h
    · exact hrest q h
    · exact hunp q h
    · exact hori q h
  intro q hq hfr
  rw [renameProgram_support] at hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  have eq : Rolling1588Lifetime.phaseHost (Rolling1588Lifetime.phaseHost w) =
      Rolling1588Lifetime.phaseHost w := phaseHost_fix_fieldR _ hfr
  exact raw w hw ((Rolling1588Lifetime.phaseHost.injective eq) ▸ hfr)

theorem reverse_notFieldR (d : Bool) (n i : Nat) (lo : 1 ≤ i) (hi : i + n ≤ 506)
    (q : Wire) (hq : q ∈ wires (Rolling1588.reverse d i n)) : q ∉ fieldR :=
  fieldR_disjoint_pool q (List.mem_toFinset.mp (StairPacket.PartialSites.pool_old d i n lo (by omega) hq))

theorem mulRawTail_notFieldR (k : Nat) :
    ∀ q ∈ wires (renameProgram Rolling1588Lifetime.phaseHost (Stair44Kernel.mulRawTail k)), q ∉ fieldR := by
  have first_fix : ∀ q ∈ fieldR, Stair44WalkMap.first q = q := by
    have h : fieldR.all (fun q => decide (Stair44WalkMap.first q = q)) = true := by decide +kernel
    intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)
  have rest_fix : ∀ q ∈ fieldR, Stair44WalkMap.rest q = q := by
    have h : fieldR.all (fun q => decide (Stair44WalkMap.rest q = q)) = true := by decide +kernel
    intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)
  have rawX_x1N : ∀ q ∈ wires (renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)), q ∉ fieldR := by
    have pi_fix : ∀ q ∈ fieldR, ParityXExitInverse23Kernel.pi q = q := fun q hq =>
      ParityXExitInverse23Kernel.pi_out q (fun hp => fieldR_disjoint_pool q hp hq)
    have rawX_fix : ∀ q ∈ fieldR, Stair44Kernel.rawX q = q := by
      have h : fieldR.all (fun q => decide (Stair44Kernel.rawX q = q)) = true := by decide +kernel
      intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)
    have tSites_notR : ∀ w ∈ StairSiteEasy.tSites base (base 2400), w ∉ fieldR := by
      have h : (StairSiteEasy.tSites base (base 2400)).all notFieldR = true := by decide +kernel
      intro w hw; exact (notFieldR_iff w).mp (List.all_eq_true.mp h w hw)
    intro q hq hfr
    rw [renameProgram_support] at hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    have hv_fr : v ∈ fieldR := (Stair44Kernel.rawX.injective (rawX_fix _ hfr)) ▸ hfr
    have hv1 := ParityXExitInverse23Kernel.x1N_sub k hv
    rw [ParityXExitInverse23Kernel.x1, renameProgram_support] at hv1
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv1
    have hw_fr : w ∈ fieldR := (ParityXExitInverse23Kernel.pi.injective (pi_fix _ hv_fr)) ▸ hv_fr
    have hw1 := StairSiteEasy.exitMerge_tight base (base 2400) k (ParityXExit.programAll_wires base (base 2400) k hw)
    exact tSites_notR w (List.mem_toFinset.mp hw1) hw_fr
  have bwd : ∀ q ∈ wires (Stair44WalkRun.backward true 409), q ∉ fieldR := by
    intro q hq hfr
    unfold Stair44WalkRun.backward at hq
    rw [wires_append, Finset.mem_union] at hq
    rcases hq with h1 | h2
    · rw [renameProgram_support] at h1
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h1
      have eq := rest_fix _ hfr
      exact reverse_notFieldR true 409 16 (by decide) (by decide) w hw
        ((Stair44WalkMap.rest.injective eq) ▸ hfr)
    · rw [renameProgram_support] at h2
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h2
      have eq := first_fix _ hfr
      exact reverse_notFieldR true 15 1 (by decide) (by decide) w hw
        ((Stair44WalkMap.first.injective eq) ▸ hfr)
  intro q hq hfr
  rw [renameProgram_support] at hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  have hw_fr : w ∈ fieldR := (Rolling1588Lifetime.phaseHost.injective (phaseHost_fix_fieldR _ hfr)) ▸ hfr
  unfold Stair44Kernel.mulRawTail at hw
  rw [wires_append, Finset.mem_union] at hw
  exact hw.elim (fun h => bwd w h hw_fr) (fun h => rawX_x1N w h hw_fr)

/-! ## Section 2: `spliceRY`, `CutFrame`, `EncodedFieldFrame`, and boundary helpers -/

/-- Replace `s`'s bits on `ryWires = fieldR ++ fieldY` with `a`'s bits (keeping `s`'s phase and outside bits). -/
def spliceRY (a s : State) : State :=
  ⟨s.phase, fun q => if q ∈ ryWires then a.basis q else s.basis q⟩

theorem spliceRY_agreeRY (a s : State) (hph : a.phase = s.phase) : AgreeRY (spliceRY a s) s :=
  ⟨rfl, fun q hq => by simp only [spliceRY, hq, if_false]⟩

theorem spliceRY_regValue_R (a s : State) :
    regValue fieldR (spliceRY a s).basis = regValue fieldR a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    simp only [spliceRY, (mem_ryWires_iff q).mpr (Or.inl hq), if_true])

theorem spliceRY_regValue_Y (a s : State) :
    regValue fieldY (spliceRY a s).basis = regValue fieldY a.basis :=
  regValue_congr _ _ _ (fun q hq => by
    simp only [spliceRY, (mem_ryWires_iff q).mpr (Or.inr hq), if_true])

theorem pullState_sig511_spliceRY (a s : State) :
    pullState (OB5.sig 511) (spliceRY a s) = spliceRY (pullState (OB5.sig 511) a) (pullState (OB5.sig 511) s) := by
  apply State.extensionality
  · rfl
  funext q
  change (if OB5.sig 511 q ∈ ryWires then a.basis (OB5.sig 511 q) else s.basis (OB5.sig 511 q)) =
    (if q ∈ ryWires then a.basis (OB5.sig 511 q) else s.basis (OB5.sig 511 q))
  by_cases hq : q ∈ ryWires
  · rw [if_pos hq, sig511_fix_ryWires q hq, if_pos hq]
  · have hq' : OB5.sig 511 q ∉ ryWires := fun hm => by
      have eq := sig511_fix_ryWires _ hm
      rw [OB5.sig_invol 511 (by decide)] at eq
      exact hq (eq ▸ hm)
    rw [if_neg hq, if_neg hq']

theorem allEncode_notRY (isA : Bool) :
    ∀ q ∈ wires (Rolling1588.allEncode base isA 102), q ∉ ryWires := by
  have h : (wireBlock base 0 512 ++ wireBlock base 1028 512).all notRY = true := by decide +kernel
  intro q hq
  have hm := List.mem_toFinset.mp (Rolling1588.allEncode_history_support base isA 102 (by decide) hq)
  exact (notRY_iff q).mp (List.all_eq_true.mp h q hm)

theorem allEncodeCut_notRY (c : Nat) :
    ∀ q ∈ wires (Rolling1588.allEncodeCut base c 102), q ∉ ryWires := by
  intro q hq
  rw [Rolling1588.allEncodeCut_support_eq, ← Rolling1588.allEncode_support_eq base true 102] at hq
  exact allEncode_notRY true q hq

theorem run_disjoint_spliceRY (P : Program) (hP : ∀ q ∈ wires P, q ∉ ryWires)
    (a s : State) (m : List Bool) :
    run P m (spliceRY a s) = spliceRY a (run P m s) := by
  have inc := Arithmetic.run_local_increment P (spliceRY a s) s m
    (fun q hq => by simp only [spliceRY, hP q hq, if_false])
  have hph : (run P m (spliceRY a s)).phase = (spliceRY a (run P m s)).phase := by
    have h1 := inc.1
    change ((run P m (spliceRY a s)).phase ^^ s.phase) = ((run P m s).phase ^^ s.phase) at h1
    change (run P m (spliceRY a s)).phase = (run P m s).phase
    revert h1
    generalize (run P m (spliceRY a s)).phase = x
    generalize (run P m s).phase = y
    generalize s.phase = z
    cases x <;> cases y <;> cases z <;> decide
  apply State.extensionality _ _ hph
  funext q
  by_cases hmem : q ∈ ryWires
  · have hnot : q ∉ wires P := fun hw => hP q hw hmem
    rw [run_preserves_outside P m (spliceRY a s) q hnot]
    simp only [spliceRY, hmem, if_true]
  · change (run P m (spliceRY a s)).basis q = (if q ∈ ryWires then a.basis q else (run P m s).basis q)
    rw [if_neg hmem]
    by_cases hp : q ∈ wires P
    · exact inc.2 q hp
    · rw [run_preserves_outside P m (spliceRY a s) q hp, run_preserves_outside P m s q hp]
      simp only [spliceRY, hmem, if_false]

theorem cutFrame_spliceRY (wR wY : Fp → Nat) (c : Nat) (origin : BasisState) (X Y : Fp)
    (a s : State) (hcut : Rolling1588.CutFrame c origin X Y (pullState (OB5.sig 511) s))
    (hRa : regValue fieldR a.basis = wR X) (hYa : regValue fieldY a.basis = wY Y) :
    RouteA.Rolling1588.CutFrame wR wY c origin X Y (pullState (OB5.sig 511) (spliceRY a s)) := by
  obtain ⟨raw, hph, hpair, henc⟩ := hcut
  refine ⟨spliceRY (pullState (OB5.sig 511) a) raw, hph, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · change regValue fieldR (spliceRY (pullState (OB5.sig 511) a) raw).basis = wR X
      rw [spliceRY_regValue_R, pullState_sig511_regValue_R]; exact hRa
    · change regValue fieldY (spliceRY (pullState (OB5.sig 511) a) raw).basis = wY Y
      rw [spliceRY_regValue_Y, pullState_sig511_regValue_Y]; exact hYa
    · intro q hnr hny
      have hnot : q ∉ ryWires := fun hm => ((mem_ryWires_iff q).mp hm).elim hnr hny
      simp only [spliceRY, hnot, if_false]
      exact hpair.2.2 q hnr hny
  · rw [pullState_sig511_spliceRY, henc, run_disjoint_spliceRY _ (allEncodeCut_notRY c)]

theorem cutFrame_values (wR wY : Fp → Nat) (c : Nat) (origin : BasisState) (X Y : Fp) (t : State)
    (hcut : RouteA.Rolling1588.CutFrame wR wY c origin X Y t) :
    regValue fieldR t.basis = wR X ∧ regValue fieldY t.basis = wY Y := by
  obtain ⟨raw, _, hpair, henc⟩ := hcut
  rw [henc]
  constructor
  · exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ [] raw q
      (fun hw => allEncodeCut_notRY c q hw ((mem_ryWires_iff q).mpr (Or.inl hq))))).trans hpair.1
  · exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ [] raw q
      (fun hw => allEncodeCut_notRY c q hw ((mem_ryWires_iff q).mpr (Or.inr hq))))).trans hpair.2.1

theorem cutFrame_std_values (c : Nat) (origin : BasisState) (X Y : Fp) (t : State)
    (hcut : Rolling1588.CutFrame c origin X Y t) :
    regValue fieldR t.basis = centerWord X ∧ regValue fieldY t.basis = centerWord Y :=
  cutFrame_values centerWord centerWord c origin X Y t hcut

theorem cutFrame_agreeRY (wR wY : Fp → Nat) (c : Nat) (origin : BasisState) (X1 Y1 X2 Y2 : Fp)
    (t1 t2 : State) (hph : t1.phase = t2.phase)
    (h1 : RouteA.Rolling1588.CutFrame wR wY c origin X1 Y1 t1)
    (h2 : Rolling1588.CutFrame c origin X2 Y2 t2) :
    AgreeRY t1 t2 := by
  obtain ⟨raw1, hp1, hf1, he1⟩ := h1
  obtain ⟨raw2, hp2, hf2, he2⟩ := h2
  have hraw : AgreeRY raw1 raw2 := by
    refine ⟨hp1.trans (hph.trans hp2.symm), fun q hq => ?_⟩
    have hnr : q ∉ fieldR := fun h => hq ((mem_ryWires_iff q).mpr (Or.inl h))
    have hny : q ∉ fieldY := fun h => hq ((mem_ryWires_iff q).mpr (Or.inr h))
    exact (hf1.2.2 q hnr hny).trans (hf2.2.2 q hnr hny).symm
  rw [he1, he2]
  exact agreeRY_disjoint _ (allEncodeCut_notRY c) hraw []

theorem encodedFieldFrame_spliceRY (wR wY : Fp → Nat) (isA : Bool) (origin : BasisState)
    (X Y : Fp) (a s : State)
    (hin : Rolling1588Frame.EncodedFieldFrame isA origin X Y s)
    (hRa : regValue fieldR a.basis = wR X) (hYa : regValue fieldY a.basis = wY Y) :
    JointOdd1588.EncodedFieldFrameOdd wR wY isA origin X Y (spliceRY a s) := by
  obtain ⟨raw, hph, hpair, henc⟩ := hin
  refine ⟨spliceRY (pullState (OB5.sig 511) a) raw, hph, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · change regValue fieldR (spliceRY (pullState (OB5.sig 511) a) raw).basis = wR X
      rw [spliceRY_regValue_R, pullState_sig511_regValue_R]; exact hRa
    · change regValue fieldY (spliceRY (pullState (OB5.sig 511) a) raw).basis = wY Y
      rw [spliceRY_regValue_Y, pullState_sig511_regValue_Y]; exact hYa
    · intro q hnr hny
      have hnot : q ∉ ryWires := fun hm => ((mem_ryWires_iff q).mp hm).elim hnr hny
      simp only [spliceRY, hnot, if_false]
      exact hpair.2.2 q hnr hny
  · rw [pullState_sig511_spliceRY, henc, run_disjoint_spliceRY _ (allEncode_notRY isA)]

theorem encodedFieldFrameOdd_values (wR wY : Fp → Nat) (isA : Bool) (origin : BasisState)
    (X Y : Fp) (s : State) (h : JointOdd1588.EncodedFieldFrameOdd wR wY isA origin X Y s) :
    regValue fieldR s.basis = wR X ∧ regValue fieldY s.basis = wY Y := by
  obtain ⟨raw, _, hpair, henc⟩ := h
  constructor
  · rw [← pullState_sig511_regValue_R, henc]
    exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ [] raw q
      (fun hw => allEncode_notRY isA q hw ((mem_ryWires_iff q).mpr (Or.inl hq))))).trans hpair.1
  · rw [← pullState_sig511_regValue_Y, henc]
    exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ [] raw q
      (fun hw => allEncode_notRY isA q hw ((mem_ryWires_iff q).mpr (Or.inr hq))))).trans hpair.2.1

theorem encodedFieldFrame_values (isA : Bool) (origin : BasisState)
    (X Y : Fp) (s : State) (h : Rolling1588Frame.EncodedFieldFrame isA origin X Y s) :
    regValue fieldR s.basis = centerWord X ∧ regValue fieldY s.basis = centerWord Y :=
  encodedFieldFrameOdd_values centerWord centerWord isA origin X Y s h

theorem encodedFieldFrame_agreeRY (wR wY : Fp → Nat) (isA : Bool) (origin : BasisState)
    (X1 Y1 X2 Y2 : Fp) (s1 s2 : State) (hph : s1.phase = s2.phase)
    (h1 : JointOdd1588.EncodedFieldFrameOdd wR wY isA origin X1 Y1 s1)
    (h2 : Rolling1588Frame.EncodedFieldFrame isA origin X2 Y2 s2) :
    AgreeRY s1 s2 := by
  obtain ⟨raw1, hp1, hf1, he1⟩ := h1
  obtain ⟨raw2, hp2, hf2, he2⟩ := h2
  have hraw : AgreeRY raw1 raw2 := by
    refine ⟨hp1.trans (hph.trans hp2.symm), fun q hq => ?_⟩
    have hnr : q ∉ fieldR := fun h => hq ((mem_ryWires_iff q).mpr (Or.inl h))
    have hny : q ∉ fieldY := fun h => hq ((mem_ryWires_iff q).mpr (Or.inr h))
    exact (hf1.2.2 q hnr hny).trans (hf2.2.2 q hnr hny).symm
  have hp : AgreeRY (pullState (OB5.sig 511) s1) (pullState (OB5.sig 511) s2) := by
    rw [he1, he2]
    exact agreeRY_disjoint _ (allEncode_notRY isA) hraw []
  have hu := pullState_sig511_agreeRY hp
  rwa [StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide)),
       StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide))] at hu


end ECDSAAdd.Entrant.OddStockLockstep

end

end
-- ==== end OddLockstepBase ====

-- ==== begin OddLockstepSteps ====
section

set_option autoImplicit false

section

namespace ECDSAAdd.Entrant.OddStockLockstep

open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout
open StairLoanExitReachX StairPacket

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] run measurementCount wires renameProgram

private theorem phase_eq_of_xor {a b c d e f : Bool}
    (h1 : (a ^^ c) = (e ^^ f)) (h2 : (b ^^ d) = (e ^^ f)) (h3 : c = d) : a = b := by
  subst h3
  cases a <;> cases b <;> cases c <;> cases e <;> cases f <;> simp_all

private theorem phase_eq_of_xor2 {a b c d e1 e2 f1 f2 : Bool}
    (h1 : (a ^^ c) = (e1 ^^ f1)) (h2 : (b ^^ d) = (e2 ^^ f2))
    (he : e1 = f1) (hf : e2 = f2) (hcd : c = d) : a = b := by
  subst he; subst hf; subst hcd
  cases a <;> cases b <;> cases c <;> cases e1 <;> cases e2 <;> simp_all

private theorem base_not_ryWires_of_zeroRegion (q : Nat) (hq : Placement5.zeroRegion q) :
    base q ∉ ryWires := by
  apply (notRY_iff _).mp
  simp only [notRY, notFieldR, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  change ¬ (2072 ≤ q + 16 ∧ q + 16 < 2328) ∧ ¬ (786 ≤ q + 16 ∧ q + 16 < 1042)
  rcases hq with ⟨h1, h2⟩ | ⟨h1, h2, _⟩ <;> omega

/-! ## Section 3: Uniform hosted group step & `from_record_odd` -/

theorem from_record_odd (c : Nat) (hc1 : 1 ≤ c) (hc2 : c ≤ 85) (origin : BasisState) (X Y : Fp)
    (r s : State)
    (cut : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord c origin X Y (pullState (OB5.sig 511) s))
    (tag : r.basis (base 720) = false)
    (hosted : ∀ q, r.basis (StairArchiveInactive.host q) = r.basis q)
    (agrees : ∀ q, Off q → q ∉ futurePayload 87 → r.basis q = s.basis q) :
    WindowFieldView.OCut c origin r := by
  let b := pullState StairArchiveInactive.host.symm s
  have back : pullState WindowFieldView.wire b = pullState (OB5.sig 511) s := by
    have hgen : ∀ (e : Equiv.Perm Wire) (f : Wire → Wire),
        pullState (fun q => e (f q)) (pullState e.symm s) = pullState f s := fun e f => by
      apply State.extensionality
      · rfl
      · funext q; change s.basis (e.symm (e (f q))) = s.basis (f q); rw [e.symm_apply_apply]
    exact hgen StairArchiveInactive.host (OB5.sig 511)
  refine ⟨tag, X, Y, b, ?_, ?_⟩
  · rw [WindowFieldView.oddCutWord_odd hc1 hc2, back]; exact cut
  · intro q hq ntag
    have ready := WindowFieldView.reliable hq ntag
    have fixed := hosted (StairArchiveInactive.host.symm q)
    rw [Equiv.apply_symm_apply] at fixed
    exact fixed.trans (agrees _ ready.1 ready.2)

/-- Uniform lockstep across ANY hosted group `(d, def_, start, len)` on `OddFullPass.P1LifeLoan.hostedGroup`
versus the logical stock group `liftF (renameProgram (OB5.sig 511) (StairGroups.groups d def_ start len))`. -/
theorem odd_hostedGroup_step (d : Bool) (dOdd def_ start len B x : Nat)
    (hpOdd : StairHostsSchedule.HostPlan := OddFullPass.P1LifeLoan.hostPlan1542)
    (hdefOdd : dOdd ≤ 44) (hdef : def_ ≤ 43) (hlo : 1 ≤ start) (hhi : start + len ≤ 102)
    (hB_mem : B = 0 ∨ B ∈ budgets)
    (havoid_payload : B ≠ 0 → ∀ q ∈ futurePayload B,
      q ∉ wires (renameProgram (OB5.sig 511) (Rolling1588.groups d start len)))
    (a b record : State) (m : List Bool)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hframe : FrameAt x (if d then start else start + len) record)
    (hagree : if B = 0 then b = record else AgreeOutside (Δv B) b record)
    (hcleanIn : ∀ q ∈ (StairSchedule.exclusiveRoles.drop dOdd ++ hpOdd.group d dOdd start len).map lowMap,
      b.basis q = false)
    (hcleanOut : ∀ q ∈ (StairSchedule.exclusiveRoles.drop dOdd).map lowMap,
      (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups d def_ start len))) m b).basis q = false)
    (hhosts_notRY : ∀ q ∈ hpOdd.group d dOdd start len, q ∉ ryWires)
    (hfresh : ∀ q ∈ hpOdd.group d dOdd start len,
      q ∉ wires (renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups d dOdd start len))) :
    OddRel P1Life.oddWord P1Life.oddWord
      (run (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup hpOdd d dOdd start len)) m a)
      (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups d def_ start len))) m b) := by
  let P_odd := renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups d dOdd start len)
  let P_std := renameProgram (OB5.sig 511) (StairGroups.groups d def_ start len)
  let P_rec := renameProgram (OB5.sig 511) (Rolling1588.groups d start len)
  have hsub_odd : wires P_odd ⊆ wires P_rec := by
    have h1 : wires (OddFullPass.P1LifeLoan.groups d dOdd start len) ⊆ wires (StairGroups.groups d dOdd start len) :=
      StairLoanGroupSupport.sequence_sub _ _ _ (fun k => OddFullPass.P1LifeLoan.packet_wires_sub d dOdd k hdefOdd) _ _
    have h2 := StairLoanGroupSupport.groups_sub d dOdd (by omega) start len
    rw [show P_odd = renameProgram (OB5.sig 511) _ from rfl,
        show P_rec = renameProgram (OB5.sig 511) _ from rfl,
        renameProgram_support, renameProgram_support]
    exact Finset.image_subset_image (h1.trans h2)
  have hsub_std : wires P_std ⊆ wires P_rec := by
    rw [show P_std = renameProgram (OB5.sig 511) _ from rfl,
        show P_rec = renameProgram (OB5.sig 511) _ from rfl,
        renameProgram_support, renameProgram_support]
    exact Finset.image_subset_image (StairLoanGroupSupport.groups_sub d def_ (by omega) start len)
  have hrec_off : ∀ q ∈ wires P_rec, Off q := by
    cases d
    · exact StairField2V3ExitRec.groupsF_off start len hlo hhi
    · exact groups_off start len hlo hhi
  obtain ⟨origin, X, Y, s_rec, ctx, en, tr, cut_rec, agree_rec⟩ := hframe
  -- Agreement between `pullIn b` and `s_rec` on `Off` outside `futurePayload B`
  have hpb_rec : ∀ q, Off q → (B ≠ 0 → q ∉ futurePayload B) → (pullIn b).basis q = s_rec.basis q := by
    intro q hq hnp
    have hbr : (pullIn b).basis q = (pullIn record).basis q := by
      by_cases hB0 : B = 0
      · simp only [hB0, if_true] at hagree; rw [hagree]
      · simp only [hB0, if_false] at hagree
        change b.basis (fieldPlace q) = record.basis (fieldPlace q)
        apply hagree.2
        intro hmem
        simp only [Δv, List.mem_toFinset, List.mem_map] at hmem
        obtain ⟨r, hr, heq⟩ := hmem
        have qr : r = q := by
          have := congrArg fieldPlaceInv heq
          rwa [inv_fieldPlace, inv_fieldPlace] at this
        exact hnp hB0 (qr ▸ hr)
    exact hbr.trans (agree_rec q hq)
  -- Extract `(centerWord X, centerWord Y)` on `b`
  have hb_vals : regValue fieldR b.basis = centerWord X ∧ regValue fieldY b.basis = centerWord Y := by
    have hrec_vals := cutFrame_std_values _ origin X Y _ cut_rec
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hrec_vals
    have hEq_ry : ∀ q ∈ ryWires, (pullIn b).basis q = s_rec.basis q := by
      intro q hq
      apply hpb_rec q (ryWires_off q hq)
      intro hB0 hfp
      rcases hB_mem with rfl | hBm
      · exact hB0 rfl
      · exact futurePayload_not_ryWires B hBm q hfp hq
    constructor
    · rw [← pullIn_regValue_R]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hrec_vals.1
    · rw [← pullIn_regValue_Y]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hrec_vals.2
  have ha_vals : regValue fieldR a.basis = P1Life.oddWord X ∧ regValue fieldY a.basis = P1Life.oddWord Y :=
    ⟨hrel.2.1 X hb_vals.1, hrel.2.2 Y hb_vals.2⟩
  -- Splice `pullIn a` onto `s_rec`
  let s_odd : State := spliceRY (pullIn a) s_rec
  have hcut_odd : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord
      (if d then start else start + len) origin X Y (pullState (OB5.sig 511) s_odd) :=
    cutFrame_spliceRY P1Life.oddWord P1Life.oddWord _ origin X Y (pullIn a) s_rec cut_rec
      (by rw [pullIn_regValue_R]; exact ha_vals.1) (by rw [pullIn_regValue_Y]; exact ha_vals.2)
  -- Run `groups_oddLoan_cut_frame` on `s_odd` and `StairLoanReplay.groups_cut_frame` on `s_rec`
  have hrun_odd := OddFullPassBridge.groups_oddLoan_cut_frame dOdd d hdefOdd start len hlo hhi
    origin ctx en X Y (pullState (OB5.sig 511) s_odd) m hcut_odd
  have hrun_std := StairLoanReplay.groups_cut_frame StairOpenWiring.half760 d def_ start len (by omega)
    hlo hhi origin ctx en X Y (pullState (OB5.sig 511) s_rec) m cut_rec
  have hconj (P : Program) (u : State) :
      pullState (OB5.sig 511) (run (renameProgram (OB5.sig 511) P) m u) =
        run P m (pullState (OB5.sig 511) u) := by
    rw [run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))]
  -- Transfer `run P_odd m (pullIn a)` to `run P_odd m s_odd` via `run_local_increment`
  have hpa_sodd : ∀ q ∈ wires P_odd, (pullIn a).basis q = s_odd.basis q := by
    intro q hq
    by_cases hry : q ∈ ryWires
    · simp only [s_odd, spliceRY, hry, if_true]
    · simp only [s_odd, spliceRY, hry, if_false]
      have h1 := (pullIn_agreeRY hrel.1).2 q hry
      have h2 := hpb_rec q (hrec_off q (hsub_odd hq)) (fun hB0 hfp => havoid_payload hB0 q hfp (hsub_odd hq))
      exact h1.trans h2
  have hpb_srec : ∀ q ∈ wires P_std, (pullIn b).basis q = s_rec.basis q := fun q hq =>
    hpb_rec q (hrec_off q (hsub_std hq)) (fun hB0 hfp => havoid_payload hB0 q hfp (hsub_std hq))
  have hinc_odd := Arithmetic.run_local_increment P_odd (pullIn a) s_odd m hpa_sodd
  have hinc_std := Arithmetic.run_local_increment P_std (pullIn b) s_rec m hpb_srec
  -- Outputs of `P_odd` on `s_odd` and `P_std` on `s_rec` satisfy `AgreeRY` and have oddWord / centerWord of `V`
  have hout_s_ag : AgreeRY (run P_odd m s_odd) (run P_std m s_rec) := by
    have hph : (pullState (OB5.sig 511) (run P_odd m s_odd)).phase =
        (pullState (OB5.sig 511) (run P_std m s_rec)).phase := by
      rw [hconj, hconj, hrun_odd.1, hrun_std.1]; rfl
    have h1 := cutFrame_agreeRY P1Life.oddWord P1Life.oddWord _ origin _ _ _ _ _ _ hph
      (by rw [hconj]; exact hrun_odd.2) (by rw [hconj]; exact hrun_std.2)
    have h2 := pullState_sig511_agreeRY h1
    rwa [StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide)),
         StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide))] at h2
  -- Hence `run P_odd m (pullIn a)` and `run P_std m (pullIn b)` satisfy `AgreeRY`!
  have hout_ag : AgreeRY (run P_odd m (pullIn a)) (run P_std m (pullIn b)) := by
    have hph : (run P_odd m (pullIn a)).phase = (run P_std m (pullIn b)).phase := by
      have hp1 : (run P_odd m s_odd).phase = s_odd.phase := by
        have := hrun_odd.1; rw [← hconj] at this; exact this
      have hp2 : (run P_std m s_rec).phase = s_rec.phase := by
        have := hrun_std.1; rw [← hconj] at this; exact this
      exact phase_eq_of_xor2 hinc_odd.1 hinc_std.1 hp1 hp2 hrel.1.1
    refine ⟨hph, fun q hq => ?_⟩
    by_cases h1 : q ∈ wires P_odd
    · by_cases h2 : q ∈ wires P_std
      · rw [hinc_odd.2 q h1, hinc_std.2 q h2]; exact hout_s_ag.2 q hq
      · rw [hinc_odd.2 q h1, run_preserves_outside P_std m (pullIn b) q h2]
        have h3 := hout_s_ag.2 q hq
        rw [run_preserves_outside P_std m s_rec q h2] at h3
        exact h3.trans (hpb_rec q (hrec_off q (hsub_odd h1))
          (fun hB0 hfp => havoid_payload hB0 q hfp (hsub_odd h1))).symm
    · rw [run_preserves_outside P_odd m (pullIn a) q h1]
      by_cases h2 : q ∈ wires P_std
      · rw [hinc_std.2 q h2]
        have h3 := hout_s_ag.2 q hq
        rw [run_preserves_outside P_odd m s_odd q h1] at h3
        have h4 : (pullIn a).basis q = s_odd.basis q := by
          simp only [s_odd, spliceRY, hq, if_false]
          exact ((pullIn_agreeRY hrel.1).2 q hq).trans
            (hpb_rec q (hrec_off q (hsub_std h2)) (fun hB0 hfp => havoid_payload hB0 q hfp (hsub_std h2)))
        exact h4.trans h3
      · rw [run_preserves_outside P_std m (pullIn b) q h2]
        exact (pullIn_agreeRY hrel.1).2 q hq
  -- Drop `rebindMany` on `pullIn a`!
  have hclean_a_in : ∀ q ∈ StairSchedule.exclusiveRoles.drop dOdd ++ hpOdd.group d dOdd start len,
      (pullIn a).basis q = false := by
    intro q hq
    have hnot : q ∉ ryWires := by
      rcases List.mem_append.mp hq with hr | hh
      · exact exclusiveRoles_not_ryWires q (List.mem_of_mem_drop hr)
      · exact hhosts_notRY q hh
    have h1 := (pullIn_agreeRY hrel.1).2 q hnot
    have h2 : (pullIn b).basis q = false := hcleanIn (lowMap q) (List.mem_map.mpr ⟨q, hq, rfl⟩)
    exact h1.trans h2
  have hclean_a_out : ∀ q ∈ StairSchedule.exclusiveRoles.drop dOdd ++ hpOdd.group d dOdd start len,
      (run P_odd m (pullIn a)).basis q = false := by
    intro q hq
    rcases List.mem_append.mp hq with hr | hh
    · have hnot : q ∉ ryWires := exclusiveRoles_not_ryWires q (List.mem_of_mem_drop hr)
      have h1 := hout_ag.2 q hnot
      have h2 := hcleanOut (lowMap q) (List.mem_map.mpr ⟨q, hr, rfl⟩)
      have h3 : (pullIn (run (liftF P_std) m b)).basis q = false := h2
      rw [pullIn_liftF] at h3
      exact h1.trans h3
    · rw [run_preserves_outside P_odd m (pullIn a) q (hfresh q hh)]
      exact hclean_a_in q (List.mem_append_right _ hh)
  have hrebind : run (OddFullPass.P1LifeLoan.hostedGroup hpOdd d dOdd start len) m (pullIn a) =
      run P_odd m (pullIn a) :=
    StairLoan.rebindMany_run _ _ P_odd (pullIn a) m hclean_a_in hclean_a_out
  -- Values of `V = Replay5.groupsPayload d origin start len (X, Y)` on outputs
  let V := Replay5.groupsPayload d origin start len (X, Y)
  have hv_odd : regValue fieldR (run P_odd m (pullIn a)).basis = P1Life.oddWord V.1 ∧
      regValue fieldY (run P_odd m (pullIn a)).basis = P1Life.oddWord V.2 := by
    have hvs := cutFrame_values P1Life.oddWord P1Life.oddWord _ origin V.1 V.2 (pullState (OB5.sig 511) (run P_odd m s_odd)) (by rw [hconj]; exact hrun_odd.2)
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hvs
    have hEq (q : Wire) (hq : q ∈ ryWires) : (run P_odd m (pullIn a)).basis q = (run P_odd m s_odd).basis q := by
      by_cases hw : q ∈ wires P_odd
      · exact hinc_odd.2 q hw
      · rw [run_preserves_outside P_odd m (pullIn a) q hw, run_preserves_outside P_odd m s_odd q hw]
        simp only [s_odd, spliceRY, hq, if_true]
    exact ⟨(regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hvs.1,
           (regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvs.2⟩
  have hv_std : regValue fieldR (run P_std m (pullIn b)).basis = centerWord V.1 ∧
      regValue fieldY (run P_std m (pullIn b)).basis = centerWord V.2 := by
    have hvs := cutFrame_std_values _ origin V.1 V.2 (pullState (OB5.sig 511) (run P_std m s_rec)) (by rw [hconj]; exact hrun_std.2)
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hvs
    have hEq (q : Wire) (hq : q ∈ ryWires) : (run P_std m (pullIn b)).basis q = (run P_std m s_rec).basis q := by
      by_cases hw : q ∈ wires P_std
      · exact hinc_std.2 q hw
      · rw [run_preserves_outside P_std m (pullIn b) q hw, run_preserves_outside P_std m s_rec q hw]
        apply hpb_rec q (ryWires_off q hq)
        intro hB0 hfp
        rcases hB_mem with rfl | hBm
        · exact hB0 rfl
        · exact futurePayload_not_ryWires B hBm q hfp hq
    exact ⟨(regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hvs.1,
           (regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvs.2⟩
  have hout_rel : OddRel P1Life.oddWord P1Life.oddWord (run P_odd m (pullIn a)) (run P_std m (pullIn b)) :=
    oddRel_of_agreeRY_values V.1 V.2 hout_ag hv_std.1 hv_std.2 hv_odd.1 hv_odd.2
  rw [show renameProgram ExteriorPorts.fieldEquiv _ = liftF _ from (ExteriorPorts.placedShape _).symm, StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run, hrebind]
  exact pullOut_oddRel hout_rel

theorem rebindMany_append (roles hosts : List Wire) (A B : Program) :
    StairLoan.rebindMany roles hosts (A ++ B) =
      StairLoan.rebindMany roles hosts A ++ StairLoan.rebindMany roles hosts B := by
  induction roles generalizing hosts with
  | nil => rfl
  | cons r rs ih =>
    cases hosts with
    | nil => rfl
    | cons h hs =>
      simp only [StairLoan.rebindMany, ih hs, Six505.rename_append]

theorem ogroup_eq_rebindMany (d : Bool) : ∀ n j,
    WindowFieldCosts.ogroup d j n =
      StairLoan.rebindMany StairSchedule.exclusiveRoles (hosts 87)
        (renameProgram (OB5.sig 511) (PacketSequence.program d (WindowFieldCosts.oddPk d) j n))
  | 0, j => by
    have hnil (rs hs : List Wire) : StairLoan.rebindMany rs hs [] = [] := by
      induction rs generalizing hs with
      | nil => rfl
      | cons _ rs ih => cases hs <;> simp [StairLoan.rebindMany, ih, renameProgram]
    simp [WindowFieldCosts.ogroup, PacketSequence.program, renameProgram, hnil]
  | n + 1, j => by
    have ih := ogroup_eq_rebindMany d n (j + 1)
    cases d <;> simp only [WindowFieldCosts.ogroup, WindowFieldCosts.opk, PacketSequence.program,
      Bool.false_eq_true, if_true, if_false, Six505.rename_append, rebindMany_append] at ih ⊢ <;>
      rw [ih]

/-- `oddPk d` wires are contained in `Rolling1588.packet d` for `1 ≤ k ≤ 84`. -/
theorem oddPk_wires_sub (d : Bool) (k : Nat) (_h1 : 1 ≤ k) (_h2 : k ≤ 84) :
    wires (WindowFieldCosts.oddPk d k) ⊆ wires (Rolling1588.packet d k) :=
  WindowFieldCosts.oddPk_sub d k

theorem oddPk_seq_wires_sub (d : Bool) : ∀ n j, 1 ≤ j → j + n ≤ 85 →
    wires (PacketSequence.program d (WindowFieldCosts.oddPk d) j n) ⊆
      wires (Rolling1588.groups d j n)
  | 0, j, _, _ => by simp [PacketSequence.program, Rolling1588.groups, wires]
  | n + 1, j, h1, h2 => by
    have hp := oddPk_wires_sub d j h1 (by omega)
    have hr := oddPk_seq_wires_sub d n (j + 1) (by omega) (by omega)
    cases d <;> simp only [Rolling1588.groups, PacketSequence.program, Bool.false_eq_true,
      if_true, if_false, wires_append] <;> exact Finset.union_subset_union (by assumption) (by assumption)

/-- Lockstep across the 84-packet odd group (`WindowFieldCosts.ogroup d 1 84`) vs stock
`liftF (renameProgram (OB5.sig 511) (StairGroups.groups d 0 1 84))`. -/
theorem odd_ogroup84_step (d : Bool) (x : Nat) (a b record : State) (m : List Bool)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hframe : FrameAt x (if d then 1 else 85) record)
    (hagree : AgreeOutside (Δv 87) b record)
    (hcleanIn : ∀ q ∈ (StairSchedule.exclusiveRoles ++ hostPlan.group d 0 1 84).map lowMap,
      b.basis q = false)
    (hcleanOut : ∀ q ∈ StairSchedule.exclusiveRoles.map lowMap,
      (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups d 0 1 84))) m b).basis q = false) :
    OddRel P1Life.oddWord P1Life.oddWord
      (run (renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup d 1 84)) m a)
      (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups d 0 1 84))) m b) := by
  let P_odd := renameProgram (OB5.sig 511) (PacketSequence.program d (WindowFieldCosts.oddPk d) 1 84)
  let P_std := renameProgram (OB5.sig 511) (StairGroups.groups d 0 1 84)
  let P_rec := renameProgram (OB5.sig 511) (Rolling1588.groups d 1 84)
  have hsub_odd : wires P_odd ⊆ wires P_rec := by
    rw [show P_odd = renameProgram (OB5.sig 511) _ from rfl,
        show P_rec = renameProgram (OB5.sig 511) _ from rfl,
        renameProgram_support, renameProgram_support]
    exact Finset.image_subset_image (oddPk_seq_wires_sub d 84 1 (by decide) (by decide))
  have hsub_std : wires P_std ⊆ wires P_rec := by
    rw [show P_std = renameProgram (OB5.sig 511) _ from rfl,
        show P_rec = renameProgram (OB5.sig 511) _ from rfl,
        renameProgram_support, renameProgram_support]
    exact Finset.image_subset_image (StairLoanGroupSupport.groups_sub d 0 (by decide) 1 84)
  have hrec_off : ∀ q ∈ wires P_rec, Off q := by
    cases d
    · exact StairField2V3ExitRec.groupsF_off 1 84 (by decide) (by decide)
    · exact groups_off 1 84 (by decide) (by decide)
  have havoid : ∀ q ∈ futurePayload 87, q ∉ wires P_rec :=
    StairField2V3Groups.groups_avoid_payload d 87 (by decide) 84 1 (by decide)
  obtain ⟨origin, X, Y, s_rec, ctx, en, tr, cut_rec, agree_rec⟩ := hframe
  have hpb_rec : ∀ q, Off q → q ∉ futurePayload 87 → (pullIn b).basis q = s_rec.basis q := by
    intro q hq hnp
    have hbr : (pullIn b).basis q = (pullIn record).basis q := by
      change b.basis (fieldPlace q) = record.basis (fieldPlace q)
      apply hagree.2
      intro hmem
      simp only [Δv, List.mem_toFinset, List.mem_map] at hmem
      obtain ⟨r, hr, heq⟩ := hmem
      have qr : r = q := by
        have := congrArg fieldPlaceInv heq
        rwa [inv_fieldPlace, inv_fieldPlace] at this
      exact hnp (qr ▸ hr)
    exact hbr.trans (agree_rec q hq)
  have hb_vals : regValue fieldR b.basis = centerWord X ∧ regValue fieldY b.basis = centerWord Y := by
    have hrec_vals := cutFrame_std_values _ origin X Y _ cut_rec
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hrec_vals
    have hEq_ry : ∀ q ∈ ryWires, (pullIn b).basis q = s_rec.basis q := fun q hq =>
      hpb_rec q (ryWires_off q hq) (futurePayload_not_ryWires 87 (by decide) q · hq)
    constructor
    · rw [← pullIn_regValue_R]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hrec_vals.1
    · rw [← pullIn_regValue_Y]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hrec_vals.2
  have ha_vals : regValue fieldR a.basis = P1Life.oddWord X ∧ regValue fieldY a.basis = P1Life.oddWord Y :=
    ⟨hrel.2.1 X hb_vals.1, hrel.2.2 Y hb_vals.2⟩
  let s_odd : State := spliceRY (pullIn a) s_rec
  have hcut_odd : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord
      (if d then 1 else 85) origin X Y (pullState (OB5.sig 511) s_odd) :=
    cutFrame_spliceRY P1Life.oddWord P1Life.oddWord _ origin X Y (pullIn a) s_rec cut_rec
      (by rw [pullIn_regValue_R]; exact ha_vals.1) (by rw [pullIn_regValue_Y]; exact ha_vals.2)
  have hrun_odd := WindowFieldView.ofield_cut_frame_odd d origin ctx en X Y
    (pullState (OB5.sig 511) s_odd) m hcut_odd
  have hrun_std := StairLoanReplay.groups_cut_frame StairOpenWiring.half760 d 0 1 84 (by decide)
    (by decide) (by decide) origin ctx en X Y (pullState (OB5.sig 511) s_rec) m cut_rec
  have hconj (P : Program) (u : State) :
      pullState (OB5.sig 511) (run (renameProgram (OB5.sig 511) P) m u) =
        run P m (pullState (OB5.sig 511) u) := by
    rw [run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))]
  have hpa_sodd : ∀ q ∈ wires P_odd, (pullIn a).basis q = s_odd.basis q := by
    intro q hq
    by_cases hry : q ∈ ryWires
    · simp only [s_odd, spliceRY, hry, if_true]
    · simp only [s_odd, spliceRY, hry, if_false]
      exact ((pullIn_agreeRY hrel.1).2 q hry).trans
        (hpb_rec q (hrec_off q (hsub_odd hq)) (fun hfp => havoid q hfp (hsub_odd hq)))
  have hpb_srec : ∀ q ∈ wires P_std, (pullIn b).basis q = s_rec.basis q := fun q hq =>
    hpb_rec q (hrec_off q (hsub_std hq)) (fun hfp => havoid q hfp (hsub_std hq))
  have hinc_odd := Arithmetic.run_local_increment P_odd (pullIn a) s_odd m hpa_sodd
  have hinc_std := Arithmetic.run_local_increment P_std (pullIn b) s_rec m hpb_srec
  have hout_s_ag : AgreeRY (run P_odd m s_odd) (run P_std m s_rec) := by
    have hph : (pullState (OB5.sig 511) (run P_odd m s_odd)).phase =
        (pullState (OB5.sig 511) (run P_std m s_rec)).phase := by
      rw [hconj, hconj, hrun_odd.1, hrun_std.1]; rfl
    have h1 := cutFrame_agreeRY P1Life.oddWord P1Life.oddWord _ origin _ _ _ _ _ _ hph
      (by rw [hconj]; exact hrun_odd.2) (by rw [hconj]; exact hrun_std.2)
    have h2 := pullState_sig511_agreeRY h1
    rwa [StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide)),
         StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide))] at h2
  have hout_ag : AgreeRY (run P_odd m (pullIn a)) (run P_std m (pullIn b)) := by
    have hph : (run P_odd m (pullIn a)).phase = (run P_std m (pullIn b)).phase := by
      have hp1 : (run P_odd m s_odd).phase = s_odd.phase := by
        have := hrun_odd.1; rw [← hconj] at this; exact this
      have hp2 : (run P_std m s_rec).phase = s_rec.phase := by
        have := hrun_std.1; rw [← hconj] at this; exact this
      exact phase_eq_of_xor2 hinc_odd.1 hinc_std.1 hp1 hp2 hrel.1.1
    refine ⟨hph, fun q hq => ?_⟩
    by_cases h1 : q ∈ wires P_odd
    · by_cases h2 : q ∈ wires P_std
      · rw [hinc_odd.2 q h1, hinc_std.2 q h2]; exact hout_s_ag.2 q hq
      · rw [hinc_odd.2 q h1, run_preserves_outside P_std m (pullIn b) q h2]
        have h3 := hout_s_ag.2 q hq
        rw [run_preserves_outside P_std m s_rec q h2] at h3
        exact h3.trans (hpb_rec q (hrec_off q (hsub_odd h1)) (fun hfp => havoid q hfp (hsub_odd h1))).symm
    · rw [run_preserves_outside P_odd m (pullIn a) q h1]
      by_cases h2 : q ∈ wires P_std
      · rw [hinc_std.2 q h2]
        have h3 := hout_s_ag.2 q hq
        rw [run_preserves_outside P_odd m s_odd q h1] at h3
        have h4 : (pullIn a).basis q = s_odd.basis q := by
          simp only [s_odd, spliceRY, hq, if_false]
          exact ((pullIn_agreeRY hrel.1).2 q hq).trans
            (hpb_rec q (hrec_off q (hsub_std h2)) (fun hfp => havoid q hfp (hsub_std h2)))
        exact h4.trans h3
      · rw [run_preserves_outside P_std m (pullIn b) q h2]
        exact (pullIn_agreeRY hrel.1).2 q hq
  have hhost_eq : hostPlan.group d 0 1 84 = hosts 87 := hp_group d 0 1 84 (by decide)
  have hfresh : ∀ q ∈ hosts 87, q ∉ wires P_odd := by
    intro q hq hw
    have hfr := StairField13V3Fresh.hostPlan_group_fresh d 0 1 84 (by simp) q (hhost_eq.symm ▸ hq)
    have hst : StairSchedule.placedGroups StairConcrete.bestLoans d 0 1 84 = P_rec := by
      simp only [StairSchedule.placedGroups, StairConcrete.bestLoans, StairGroups.groups_zero, P_rec]
    rw [hst] at hfr
    exact hfr (hsub_odd hw)
  have hclean_a_in : ∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (pullIn a).basis q = false := by
    intro q hq
    have hnot : q ∉ ryWires := by
      rcases List.mem_append.mp hq with hr | hh
      · exact exclusiveRoles_not_ryWires q hr
      · exact hosts_not_ryWires 87 (by decide) q hh
    have h1 := (pullIn_agreeRY hrel.1).2 q hnot
    have h2 : (pullIn b).basis q = false :=
      hcleanIn (lowMap q) (List.mem_map.mpr ⟨q, by rw [hhost_eq]; exact hq, rfl⟩)
    exact h1.trans h2
  have hclean_a_out : ∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87,
      (run P_odd m (pullIn a)).basis q = false := by
    intro q hq
    rcases List.mem_append.mp hq with hr | hh
    · have hnot : q ∉ ryWires := exclusiveRoles_not_ryWires q hr
      have h1 := hout_ag.2 q hnot
      have h2 := hcleanOut (lowMap q) (List.mem_map.mpr ⟨q, hr, rfl⟩)
      have h3 : (pullIn (run (liftF P_std) m b)).basis q = false := h2
      rw [pullIn_liftF] at h3
      exact h1.trans h3
    · rw [run_preserves_outside P_odd m (pullIn a) q (hfresh q hh)]
      exact hclean_a_in q (List.mem_append_right _ hh)
  have hrebind : run (WindowFieldCosts.ogroup d 1 84) m (pullIn a) = run P_odd m (pullIn a) := by
    rw [ogroup_eq_rebindMany]
    exact StairLoan.rebindMany_run _ _ P_odd (pullIn a) m hclean_a_in hclean_a_out
  let V := Replay5.groupsPayload d origin 1 84 (X, Y)
  have hv_odd : regValue fieldR (run P_odd m (pullIn a)).basis = P1Life.oddWord V.1 ∧
      regValue fieldY (run P_odd m (pullIn a)).basis = P1Life.oddWord V.2 := by
    have hvs := cutFrame_values P1Life.oddWord P1Life.oddWord _ origin V.1 V.2 (pullState (OB5.sig 511) (run P_odd m s_odd)) (by rw [hconj]; exact hrun_odd.2)
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hvs
    have hEq (q : Wire) (hq : q ∈ ryWires) : (run P_odd m (pullIn a)).basis q = (run P_odd m s_odd).basis q := by
      by_cases hw : q ∈ wires P_odd
      · exact hinc_odd.2 q hw
      · rw [run_preserves_outside P_odd m (pullIn a) q hw, run_preserves_outside P_odd m s_odd q hw]
        simp only [s_odd, spliceRY, hq, if_true]
    exact ⟨(regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hvs.1,
           (regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvs.2⟩
  have hv_std : regValue fieldR (run P_std m (pullIn b)).basis = centerWord V.1 ∧
      regValue fieldY (run P_std m (pullIn b)).basis = centerWord V.2 := by
    have hvs := cutFrame_std_values _ origin V.1 V.2 (pullState (OB5.sig 511) (run P_std m s_rec)) (by rw [hconj]; exact hrun_std.2)
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hvs
    have hEq (q : Wire) (hq : q ∈ ryWires) : (run P_std m (pullIn b)).basis q = (run P_std m s_rec).basis q := by
      by_cases hw : q ∈ wires P_std
      · exact hinc_std.2 q hw
      · rw [run_preserves_outside P_std m (pullIn b) q hw, run_preserves_outside P_std m s_rec q hw]
        exact hpb_rec q (ryWires_off q hq) (futurePayload_not_ryWires 87 (by decide) q · hq)
    exact ⟨(regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hvs.1,
           (regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvs.2⟩
  have hout_rel := oddRel_of_agreeRY_values V.1 V.2 hout_ag hv_std.1 hv_std.2 hv_odd.1 hv_odd.2
  rw [show renameProgram ExteriorPorts.fieldEquiv _ = liftF _ from (ExteriorPorts.placedShape _).symm, StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run, hrebind]
  exact pullOut_oddRel hout_rel

/-- Extract `OCut c origin (pullIn a)` from `OddRel` + `FrameAt x c record` + `AgreeOutside (Δv 87)` + `Loan`. -/
theorem odd_cut_ocut (c : Nat) (hc1 : 1 ≤ c) (hc2 : c ≤ 85) (x : Nat)
    (a b record : State)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hframe : FrameAt x c record) (hagree : AgreeOutside (Δv 87) b record)
    (hloan : ∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, b.basis (fieldPlace q) = false) :
    ∃ (origin : BasisState), FrontierReplay1591.Context origin ∧ origin (base 2400) = true ∧
      TraceOK x origin ∧ WindowFieldView.OCut c origin (pullIn a) := by
  obtain ⟨origin, X, Y, s_rec, ctx, en, tr, cut_rec, agree_rec⟩ := hframe
  have hpb_rec : ∀ q, Off q → q ∉ futurePayload 87 → (pullIn b).basis q = s_rec.basis q := by
    intro q hq hnp
    have hbr : (pullIn b).basis q = (pullIn record).basis q := by
      change b.basis (fieldPlace q) = record.basis (fieldPlace q)
      apply hagree.2
      intro hmem
      simp only [Δv, List.mem_toFinset, List.mem_map] at hmem
      obtain ⟨r, hr, heq⟩ := hmem
      have qr : r = q := by
        have := congrArg fieldPlaceInv heq
        rwa [inv_fieldPlace, inv_fieldPlace] at this
      exact hnp (qr ▸ hr)
    exact hbr.trans (agree_rec q hq)
  have hb_vals : regValue fieldR b.basis = centerWord X ∧ regValue fieldY b.basis = centerWord Y := by
    have hrec_vals := cutFrame_std_values _ origin X Y _ cut_rec
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hrec_vals
    have hEq_ry : ∀ q ∈ ryWires, (pullIn b).basis q = s_rec.basis q := fun q hq =>
      hpb_rec q (ryWires_off q hq) (futurePayload_not_ryWires 87 (by decide) q · hq)
    constructor
    · rw [← pullIn_regValue_R]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hrec_vals.1
    · rw [← pullIn_regValue_Y]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hrec_vals.2
  let s_odd : State := spliceRY (pullIn a) s_rec
  have hcut_odd := cutFrame_spliceRY P1Life.oddWord P1Life.oddWord c origin X Y (pullIn a) s_rec cut_rec
    (by rw [pullIn_regValue_R]; exact hrel.2.1 X hb_vals.1)
    (by rw [pullIn_regValue_Y]; exact hrel.2.2 Y hb_vals.2)
  have hloan_a : ∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (pullIn a).basis q = false := by
    intro q hq
    have hnot : q ∉ ryWires := by
      rcases List.mem_append.mp hq with hr | hh
      · exact exclusiveRoles_not_ryWires q hr
      · exact hosts_not_ryWires 87 (by decide) q hh
    exact ((pullIn_agreeRY hrel.1).2 q hnot).trans (hloan q hq)
  refine ⟨origin, ctx, en, tr, from_record_odd c hc1 hc2 origin X Y (pullIn a) s_odd hcut_odd
    (hloan_a (base 720) (by decide +kernel)) (WindowFieldView.host_fixed (pullIn a) hloan_a) ?_⟩
  intro q hq hnp
  by_cases hry : q ∈ ryWires
  · simp only [s_odd, spliceRY, hry, if_true]
  · simp only [s_odd, spliceRY, hry, if_false]
    exact ((pullIn_agreeRY hrel.1).2 q hry).trans (hpb_rec q hq hnp)

/-! ### Boundary helpers: `Q6EndpointCell.Clean`, `convWork`, `copyN`, `firstPacketOdd`, `divEndTail`, `mulHeadCore` -/

private theorem q6Clean_of_encoded5 {isA : Bool} (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X Y : Fp) (s : State)
    (hin : Rolling1588.EncodedFieldFrame5 base (base 2409) isA origin X Y s) :
    Q6EndpointCell.Clean base s.basis := by
  obtain ⟨raw, _, hpair, henc⟩ := hin
  have hclean := Q6EndpointCell.clean_of_env base origin ctx.env ctx.parity
  have hnot_ry : (Q6EndpointCell.workIds.map base).all notRY = true := by decide +kernel
  have hnot_hist : (Q6EndpointCell.workIds.map base).all
      (fun q => !(decide (16 ≤ q ∧ q < 528)) && !(decide (1044 ≤ q ∧ q < 1556))) = true := by
    decide +kernel
  intro q hq
  have hnr : q ∉ ryWires := (notRY_iff q).mp (List.all_eq_true.mp hnot_ry q hq)
  have hnh : q ∉ wireBlock base 0 512 ++ wireBlock base 1028 512 := by
    have hb := List.all_eq_true.mp hnot_hist q hq
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h1
      simp only [List.mem_range'_1] at hi
      exact hb.1 ⟨by change 16 ≤ i + 16; omega, by change i + 16 < 528; omega⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h2
      simp only [List.mem_range'_1] at hi
      exact hb.2 ⟨by change 1044 ≤ i + 16; omega, by change i + 16 < 1556; omega⟩
  have hne : q ∉ wires (Rolling1588.allEncode base isA 102) := fun hw =>
    hnh (List.mem_toFinset.mp (Rolling1588.allEncode_history_support base isA 102 (by decide) hw))
  rw [henc, run_preserves_outside _ [] raw q hne]
  exact (hpair.2.2 q (fun h => hnr ((mem_ryWires_iff q).mpr (Or.inl h)))
    (fun h => hnr ((mem_ryWires_iff q).mpr (Or.inr h)))).trans (hclean q hq)

private theorem q6Clean_of_agreeRY {a b : State} (h : AgreeRY a b)
    (hb : Q6EndpointCell.Clean base b.basis) : Q6EndpointCell.Clean base a.basis := by
  have hnot_ry : (Q6EndpointCell.workIds.map base).all notRY = true := by decide +kernel
  intro q hq
  exact (h.2 q ((notRY_iff q).mp (List.all_eq_true.mp hnot_ry q hq))).trans (hb q hq)

private theorem convWork_not_fieldR :
    ∀ q ∈ OddFullPass.HalfConvertOdd.convWork StairBoundaryLoan.converterLayout760, q ∉ fieldR := by
  have h : (OddFullPass.HalfConvertOdd.convWork StairBoundaryLoan.converterLayout760).all notFieldR = true := by
    decide +kernel
  intro q hq; exact (notFieldR_iff q).mp (List.all_eq_true.mp h q hq)

private theorem yHosts44_sub_fieldY :
    ∀ q ∈ OddFullPass.HalfConvertOdd.yHosts44, q ∈ fieldY := by
  have h : OddFullPass.HalfConvertOdd.yHosts44.all (fun q => decide (q ∈ fieldY)) = true := by
    decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

private theorem bcWork_extra_pulled :
    ([StairBoundaryLoan.converterLayout760.flag,
      StairBoundaryLoan.converterLayout760.cin,
      StairBoundaryLoan.converterLayout760.one] ++
      StairBoundaryLoan.converterLayout760.carry.drop 254).all
      (fun q => decide (StairBoundaryLoan.PulledClass (OB5.sig 511 q))) = true := by
  decide +kernel

private theorem bcWork_clean_of_encodedField {isA : Bool} (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X : Fp) (s : State)
    (hin : Rolling1588Frame.EncodedFieldFrame isA origin X 0 s) :
    ∀ q ∈ BalancedConvert.work StairBoundaryLoan.converterLayout760, s.basis q = false := by
  have hcar := StairBoundaryLoan.canon_ladder_clean origin ctx X s hin
  intro q hq
  simp only [BalancedConvert.work, BalancedConvert.scratch, List.mem_cons, List.mem_append] at hq
  have hpull (hm : q ∈ [StairBoundaryLoan.converterLayout760.flag,
      StairBoundaryLoan.converterLayout760.cin,
      StairBoundaryLoan.converterLayout760.one] ++
      StairBoundaryLoan.converterLayout760.carry.drop 254) : s.basis q = false := by
    have hpc := of_decide_eq_true (List.all_eq_true.mp bcWork_extra_pulled q hm)
    have h := StairBoundaryLoan.field_pulled_zero origin ctx X (pullState (OB5.sig 511) s) hin _ hpc
    change s.basis (OB5.sig 511 (OB5.sig 511 q)) = false at h; rwa [StairBoundaryLoan.sig511_invol] at h
  rcases hq with rfl | (rfl | rfl | _) | hc
  · exact hpull (by simp)
  · exact hpull (by simp)
  · exact hpull (by simp)
  · simp at *
  · rw [← List.take_append_drop 254 StairBoundaryLoan.converterLayout760.carry, List.mem_append] at hc
    rcases hc with h1 | h2
    · exact hcar q h1
    · exact hpull (List.mem_append_right _ h2)

private theorem convWork_clean_of_encodedField {isA : Bool} (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin) (X : Fp) (s : State)
    (hin : Rolling1588Frame.EncodedFieldFrame isA origin X 0 s) :
    ∀ q ∈ OddFullPass.HalfConvertOdd.convWork StairBoundaryLoan.converterLayout760, s.basis q = false := by
  intro q hq
  apply bcWork_clean_of_encodedField origin ctx X s hin q
  simp only [OddFullPass.HalfConvertOdd.convWork, BalancedConvert.work, BalancedConvert.scratch,
    List.mem_cons, List.mem_append] at hq ⊢
  rcases hq with rfl | rfl | hc
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (Or.inl rfl))
  · exact Or.inr (Or.inr (List.mem_of_mem_take hc))

private theorem allEncode_510_free (isA : Bool) :
    base 510 ∉ wires (Rolling1588.allEncode base isA 102) := by
  have hgen : ∀ n, 5 * n ≤ 510 → base 510 ∉ wires (Rolling1588.allEncode base isA n) := by
    intro n
    induction n with
    | zero => intro _; simp [Rolling1588.allEncode, wires]
    | succ n ih =>
      intro hn hw
      rw [Rolling1588.allEncode, wires_append, Finset.mem_union] at hw
      rcases hw with h1 | h2
      · exact ih (by omega) h1
      · rw [Rolling1588.encodeGroup_support_eq, NewHistory5.encode_support_eq] at h2
        obtain ⟨j, hj⟩ := History5.history_gate_mem base (5 * n) _ (Or.inl rfl) (base 510) h2
        have eq : 510 = History5.historyId (5 * n) j := by
          have := congrArg (· - 16) hj
          simpa [base] using this
        unfold History5.historyId at eq
        have jlt := j.isLt
        split_ifs at eq <;> omega
  exact hgen 102 (by decide)

private theorem bcWork_clean_of_encodedCanonical {isA : Bool} (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin = 0) (X : Fp) (s : State)
    (hin : Rolling1588Frame.EncodedCanonicalFrame isA origin X 0 s) :
    ∀ q ∈ BalancedConvert.work StairBoundaryLoan.converterLayout760, s.basis q = false := by
  have hcar := StairBoundaryLoan.center_ladder_clean origin ctx ha X s hin
  intro q hq
  simp only [BalancedConvert.work, BalancedConvert.scratch, List.mem_cons, List.mem_append] at hq
  have hpull (hm : q ∈ [StairBoundaryLoan.converterLayout760.flag,
      StairBoundaryLoan.converterLayout760.cin,
      StairBoundaryLoan.converterLayout760.one] ++
      StairBoundaryLoan.converterLayout760.carry.drop 254) : s.basis q = false := by
    have hpc := of_decide_eq_true (List.all_eq_true.mp bcWork_extra_pulled q hm)
    have h := StairBoundaryLoan.canonical_pulled_zero origin ctx ha X (pullState (OB5.sig 511) s) hin _ hpc
    change s.basis (OB5.sig 511 (OB5.sig 511 q)) = false at h; rwa [StairBoundaryLoan.sig511_invol] at h
  rcases hq with rfl | (rfl | rfl | _) | hc
  · exact hpull (by simp)
  · exact hpull (by simp)
  · exact hpull (by simp)
  · simp at *
  · rw [← List.take_append_drop 254 StairBoundaryLoan.converterLayout760.carry, List.mem_append] at hc
    rcases hc with h1 | h2
    · exact hcar q h1
    · exact hpull (List.mem_append_right _ h2)

private theorem convWork_clean_of_encodedCanonical {isA : Bool} (origin : BasisState)
    (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin = 0) (X : Fp) (s : State)
    (hin : Rolling1588Frame.EncodedCanonicalFrame isA origin X 0 s) :
    ∀ q ∈ OddFullPass.HalfConvertOdd.convWork StairBoundaryLoan.converterLayout760, s.basis q = false := by
  intro q hq
  apply bcWork_clean_of_encodedCanonical origin ctx ha X s hin q
  simp only [OddFullPass.HalfConvertOdd.convWork, BalancedConvert.work, BalancedConvert.scratch,
    List.mem_cons, List.mem_append] at hq ⊢
  rcases hq with rfl | rfl | hc
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (Or.inl rfl))
  · exact Or.inr (Or.inr (List.mem_of_mem_take hc))

/-- `HalfFieldOB5.copyN` preserves phase and everything outside `fieldY`, and XORs `fieldR` into `fieldY`. -/
theorem copyN_step (hn : (skywalkSharedWires base).Nodup) (s : State) (m : List Bool) :
    (run HalfFieldOB5.copyN m s).phase = s.phase ∧
    (∀ q, q ∉ fieldY → (run HalfFieldOB5.copyN m s).basis q = s.basis q) ∧
    regValue fieldY (run HalfFieldOB5.copyN m s).basis =
      regValue fieldY s.basis ^^^ regValue fieldR s.basis := by
  have len : (balancedSharedPorts base (base 2409)).r.length =
      (balancedSharedPorts base (base 2409)).y.length := by
    rw [balancedSharedPorts_r, balancedSharedPorts_y]; simp [wireBlock_length]
  obtain ⟨hph, hkeep, hval⟩ := copyRegister_correct none
    (balancedSharedPorts base (base 2409)).r (balancedSharedPorts base (base 2409)).y len
    (balancedSharedLayout_pairND base (base 2409) hn) (by simp) s m
  refine ⟨hph, ?_, ?_⟩
  · intro q hq
    exact hkeep q (by rw [balancedSharedPorts_y]; exact hq)
  · simpa only [copyValue, balancedSharedPorts_r, balancedSharedPorts_y] using hval

/-- Lockstep for `firstPacketOdd` (both `divide = true` at cut 1 and `divide = false` at cut 23). -/
theorem firstPacketOdd_step (divide isA : Bool)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (en : origin (base 2400) = true) (x : Nat) (hx : x < p)
    (trace : skywalkTapeControls origin (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int)))
    (X Y : Fp) (hz : FirstZero.FirstHyp divide origin X Y)
    (a b s_rec : State) (m : List Bool)
    (hag : AgreeRY a b)
    (hrec : Rolling1588Frame.EncodedFieldFrame isA origin X Y s_rec)
    (hpb_fp : ∀ q, StairWireCheck.fpSup q = true → (pullState fieldMap b).basis q = s_rec.basis q)
    (hpb_ry : ∀ q ∈ ryWires, (pullState fieldMap b).basis q = s_rec.basis q)
    (hRa : regValue fieldR a.basis = P1Life.oddWord X)
    (hYa : regValue fieldY a.basis = JointOdd1588.firstYIn divide Y)
    (hcleanIn : ∀ q ∈ (StairSchedule.exclusiveRoles ++ hostPlan.firstPacket divide).map fieldMap,
      b.basis q = false)
    (hcleanOut : ∀ q ∈ StairSchedule.exclusiveRoles.map fieldMap,
      (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket divide)) m b).basis q = false) :
    let V := Replay5.firstPayload divide origin (X, Y)
    let a' := run (StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf divide)) m a
    let b' := run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket divide)) m b
    AgreeRY a' b' ∧
    regValue fieldR a'.basis = P1Life.oddWord V.1 ∧
    regValue fieldY a'.basis = JointOdd1588.firstYOut divide V.2 ∧
    regValue fieldR b'.basis = centerWord V.1 ∧
    regValue fieldY b'.basis = centerWord V.2 := by
  let P_odd := JointOdd1588.placedFirstPacketOdd WindowCallerCosts.oddFirstHalf divide
  let P_std := Rolling1588.placedFirstPacket divide
  have hfp_odd : ∀ q ∈ wires P_odd, StairWireCheck.fpSup q = true :=
    StairWireCheck.allSites_sound StairWireCheck.fpSup P_odd
      (JointOdd1588.placedFirstPacketOdd_passSup WindowCallerCosts.oddFirstHalf divide
        (WindowCallerCosts.oddFirstHalf_support divide))
  have hfp_std : ∀ q ∈ wires P_std, StairWireCheck.fpSup q = true :=
    StairWireCheck.allSites_sound StairWireCheck.fpSup P_std
      (by cases divide; exact StairFirstPacketKernel.passSup_false; exact StairFirstPacketKernel.passSup_true)
  let s_odd : State := spliceRY (pullState fieldMap a) s_rec
  have hframe_odd : JointOdd1588.EncodedFieldFrameOdd P1Life.oddWord (JointOdd1588.firstYIn divide) isA origin X Y s_odd :=
    encodedFieldFrame_spliceRY P1Life.oddWord (JointOdd1588.firstYIn divide) isA origin X Y
      (pullState fieldMap a) s_rec hrec
      (by rw [pullState_fieldMap_regValue_R]; exact hRa)
      (by rw [pullState_fieldMap_regValue_Y]; exact hYa)
  have hrun_odd := JointOdd1588.placedFirstPacketOdd_frame WindowCallerCosts.oddFirstHalf divide isA
    (OddFullPassBridge.oddFirstHalf_law divide) (WindowCallerCosts.oddFirstHalf_support divide)
    origin ctx en x hx trace X Y hz s_odd m hframe_odd
  have hrun_std := Rolling1588.placedFirstPacket_frame divide isA origin ctx en x hx trace X Y hz s_rec m hrec
  have hpa_sodd : ∀ q ∈ wires P_odd, (pullState fieldMap a).basis q = s_odd.basis q := by
    intro q hq
    by_cases hry : q ∈ ryWires
    · simp only [s_odd, spliceRY, hry, if_true]
    · simp only [s_odd, spliceRY, hry, if_false]
      exact ((pullState_fieldMap_agreeRY hag).2 q hry).trans (hpb_fp q (hfp_odd q hq))
  have hpb_srec : ∀ q ∈ wires P_std, (pullState fieldMap b).basis q = s_rec.basis q := fun q hq =>
    hpb_fp q (hfp_std q hq)
  have hinc_odd := Arithmetic.run_local_increment P_odd (pullState fieldMap a) s_odd m hpa_sodd
  have hinc_std := Arithmetic.run_local_increment P_std (pullState fieldMap b) s_rec m hpb_srec
  have hout_s_ag : AgreeRY (run P_odd m s_odd) (run P_std m s_rec) :=
    encodedFieldFrame_agreeRY P1Life.oddWord (JointOdd1588.firstYOut divide) isA origin _ _ _ _ _ _
      (by rw [hrun_odd.1, hrun_std.1]; rfl) hrun_odd.2 hrun_std.2
  have hout_ag : AgreeRY (run P_odd m (pullState fieldMap a)) (run P_std m (pullState fieldMap b)) := by
    have hph : (run P_odd m (pullState fieldMap a)).phase = (run P_std m (pullState fieldMap b)).phase :=
      phase_eq_of_xor2 hinc_odd.1 hinc_std.1 hrun_odd.1 hrun_std.1 hag.1
    refine ⟨hph, fun q hq => ?_⟩
    by_cases h1 : q ∈ wires P_odd
    · by_cases h2 : q ∈ wires P_std
      · rw [hinc_odd.2 q h1, hinc_std.2 q h2]; exact hout_s_ag.2 q hq
      · rw [hinc_odd.2 q h1, run_preserves_outside P_std m (pullState fieldMap b) q h2]
        have h3 := hout_s_ag.2 q hq
        rw [run_preserves_outside P_std m s_rec q h2] at h3
        exact h3.trans (hpb_fp q (hfp_odd q h1)).symm
    · rw [run_preserves_outside P_odd m (pullState fieldMap a) q h1]
      by_cases h2 : q ∈ wires P_std
      · rw [hinc_std.2 q h2]
        have h3 := hout_s_ag.2 q hq
        rw [run_preserves_outside P_odd m s_odd q h1] at h3
        have h4 : (pullState fieldMap a).basis q = s_odd.basis q := by
          simp only [s_odd, spliceRY, hq, if_false]
          exact ((pullState_fieldMap_agreeRY hag).2 q hq).trans (hpb_fp q (hfp_std q h2))
        exact h4.trans h3
      · rw [run_preserves_outside P_std m (pullState fieldMap b) q h2]
        exact (pullState_fieldMap_agreeRY hag).2 q hq
  -- Drop `rebindMany` on `pullState fieldMap a`
  have hroles_in : ∀ q ∈ StairSchedule.exclusiveRoles, (pullState fieldMap a).basis q = false := by
    intro q hq
    exact ((pullState_fieldMap_agreeRY hag).2 q (exclusiveRoles_not_ryWires q hq)).trans
      (hcleanIn (fieldMap q) (List.mem_map.mpr ⟨q, List.mem_append_left _ hq, rfl⟩))
  have hhosts_in : ∀ q ∈ hostPlan.firstPacket divide, (pullState fieldMap a).basis q = false := by
    intro q hq
    have hnot : q ∉ ryWires := hosts_not_ryWires 87 (by decide) q (by simpa [StairV3Primitives.hostPlan] using hq)
    exact ((pullState_fieldMap_agreeRY hag).2 q hnot).trans
      (hcleanIn (fieldMap q) (List.mem_map.mpr ⟨q, List.mem_append_right _ hq, rfl⟩))
  have hroles_out : ∀ q ∈ StairSchedule.exclusiveRoles,
      (run P_odd m (pullState fieldMap a)).basis q = false := by
    intro q hq
    have h1 := hout_ag.2 q (exclusiveRoles_not_ryWires q hq)
    have h2 := hcleanOut (fieldMap q) (List.mem_map.mpr ⟨q, hq, rfl⟩)
    rw [fieldRename_eq] at h2
    have h3 : (pullState fieldMap (run (renameProgram fieldMap P_std) m b)).basis q = false := h2
    rw [run_rename fieldMap fieldMap_injective] at h3
    exact h1.trans h3
  have hrebind := JointOdd1588.hostedFirstPacketOdd_run_eq WindowCallerCosts.oddFirstHalf divide
    (WindowCallerCosts.oddFirstHalf_support divide) m (pullState fieldMap a) hroles_in hhosts_in hroles_out
  -- Values of `V` on `run P_odd m (pullState fieldMap a)` and `run P_std m (pullState fieldMap b)`
  let V := Replay5.firstPayload divide origin (X, Y)
  have hvo := encodedFieldFrameOdd_values P1Life.oddWord (JointOdd1588.firstYOut divide) isA origin V.1 V.2 _ hrun_odd.2
  have hvs := encodedFieldFrame_values isA origin V.1 V.2 _ hrun_std.2
  have hEq_odd (q : Wire) (hq : q ∈ ryWires) :
      (run P_odd m (pullState fieldMap a)).basis q = (run P_odd m s_odd).basis q := by
    by_cases hw : q ∈ wires P_odd
    · exact hinc_odd.2 q hw
    · rw [run_preserves_outside P_odd m (pullState fieldMap a) q hw, run_preserves_outside P_odd m s_odd q hw]
      simp only [s_odd, spliceRY, hq, if_true]
  have hEq_std (q : Wire) (hq : q ∈ ryWires) :
      (run P_std m (pullState fieldMap b)).basis q = (run P_std m s_rec).basis q := by
    by_cases hw : q ∈ wires P_std
    · exact hinc_std.2 q hw
    · rw [run_preserves_outside P_std m (pullState fieldMap b) q hw, run_preserves_outside P_std m s_rec q hw]
      exact hpb_ry q hq
  -- Lift back through `fieldRename = renameProgram fieldMap` using `fieldMapEquiv`
  let fmInv : Wire → Wire := fun q => HostOB5.hostSwap (Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host q)
  let fmEq : Equiv.Perm Wire := ⟨fieldMap, fmInv,
    fun q => by simp only [fieldMap, fmInv, Equiv.swap_apply_self, HostOB5.hostSwap_invol],
    fun q => by simp only [fieldMap, fmInv, HostOB5.hostSwap_invol, Equiv.swap_apply_self]⟩
  have hfmInv_fix : ∀ q ∈ ryWires, fmInv q = q := fun q hq => by
    have h1 := fieldMap_fix_ryWires q hq
    have h2 := congrArg fmInv h1
    exact (fmEq.left_inv q).symm.trans h2 |>.symm
  have hconj_fm (P : Program) (u : State) :
      run (StairSchedule.fieldRename P) m u = pullState fmInv (run P m (pullState fieldMap u)) := by
    rw [fieldRename_eq]
    have hr := run_rename fieldMap fieldMap_injective P m u
    apply State.extensionality
    · change (pullState fieldMap (run (renameProgram fieldMap P) m u)).phase =
        (run P m (pullState fieldMap u)).phase
      exact congrArg State.phase hr
    · funext q
      have h1 := congrFun (congrArg State.basis hr) (fmInv q)
      change (run (renameProgram fieldMap P) m u).basis (fieldMap (fmInv q)) = _ at h1
      have hfr : fieldMap (fmInv q) = q := by
        simp only [fieldMap, fmInv, HostOB5.hostSwap_invol, Equiv.swap_apply_self]
      rw [hfr] at h1
      exact h1
  have hpullInv_ag : ∀ {u v : State}, AgreeRY u v → AgreeRY (pullState fmInv u) (pullState fmInv v) := by
    intro u v huv
    refine ⟨huv.1, fun q hq => ?_⟩
    change u.basis (fmInv q) = v.basis (fmInv q)
    apply huv.2
    intro hm
    have h1 := fieldMap_fix_ryWires (fmInv q) hm
    have h2 : fieldMap (fmInv q) = q := by
      simp only [fieldMap, fmInv, HostOB5.hostSwap_invol, Equiv.swap_apply_self]
    rw [h2] at h1
    exact hq (h1 ▸ hm)
  have hpullInv_R (u : State) : regValue fieldR (pullState fmInv u).basis = regValue fieldR u.basis :=
    regValue_congr _ _ _ (fun q hq => by
      change u.basis (fmInv q) = u.basis q
      rw [hfmInv_fix q ((mem_ryWires_iff q).mpr (Or.inl hq))])
  have hpullInv_Y (u : State) : regValue fieldY (pullState fmInv u).basis = regValue fieldY u.basis :=
    regValue_congr _ _ _ (fun q hq => by
      change u.basis (fmInv q) = u.basis q
      rw [hfmInv_fix q ((mem_ryWires_iff q).mpr (Or.inr hq))])
  dsimp only
  rw [hconj_fm, hconj_fm, hrebind]
  refine ⟨hpullInv_ag hout_ag, ?_, ?_, ?_, ?_⟩
  · rw [hpullInv_R]
    exact (regValue_congr _ _ _ (fun q hq => hEq_odd q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hvo.1
  · rw [hpullInv_Y]
    exact (regValue_congr _ _ _ (fun q hq => hEq_odd q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvo.2
  · rw [hpullInv_R]
    exact (regValue_congr _ _ _ (fun q hq => hEq_std q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hvs.1
  · rw [hpullInv_Y]
    exact (regValue_congr _ _ _ (fun q hq => hEq_std q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvs.2

private theorem skywalkSharedField_z_eq_fieldR : (skywalkSharedField base).z = fieldR ++ [base 2312] := by decide +kernel
private theorem skywalkSharedField_a_eq_fieldY : (skywalkSharedField base).a = fieldY ++ [base 1026] := by decide +kernel

private theorem pullState_phase (f : Wire → Wire) (s : State) :
    (pullState f s).phase = s.phase := rfl

private theorem fixedLayout_r_eq : DecoderBiasReuse.fixedLayout.r = fieldR := by decide +kernel
private theorem fixedLayout_y_eq : DecoderBiasReuse.fixedLayout.y = fieldY := by decide +kernel
private theorem endpointL_r_eq : (Q6EndpointCell.ports base (base 2409)).r = fieldR := by decide +kernel
private theorem endpointL_y_eq : (Q6EndpointCell.ports base (base 2409)).y = fieldY := by decide +kernel

private theorem converterLayout760_word_eq_fieldR :
    StairBoundaryLoan.converterLayout760.word = fieldR := by
  decide +kernel

private theorem converterLayout760_wires_nodup :
    StairBoundaryLoan.converterLayout760.wires.Nodup := by
  have heq : StairBoundaryLoan.converterLayout760.wires =
      HalfField.tgt.wires.map StairBoundaryLoan.converterRename := by
    simp only [BalancedConvert.Layout.wires, StairBoundaryLoan.converterLayout760,
      BalancedConvert.Layout.word, List.map_append, List.map_cons, List.map_nil]
  rw [heq]
  exact List.Nodup.map StairBoundaryLoan.converterRename_injective_k4a
    (PeakNodup.nodup_of_mask _ (by decide +kernel))

/-- Pieces 4–6 of Multiplication (`center760OddLoan ++ copyN ++ endPacket760OddLoan44` vs
`center ++ copyN ++ placedEndPacket bestLoans false 68`) starting from identical `b` (`pullIn b`
agrees on `Off` with `s_rec` which carries `EncodedCanonicalFrame false origin Y 0`). -/
theorem mulHeadCore_step (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin = 0)
    (en : origin (base 2400) = true) (Y : Fp)
    (b s_rec : State) (m : List Bool)
    (hrec : Rolling1588Frame.EncodedCanonicalFrame false origin Y 0 s_rec)
    (hpb_rec : ∀ q, Off q → (pullIn b).basis q = s_rec.basis q) :
    OddRel P1Life.oddWord P1Life.oddWord
      (run (liftF (OddFullPass.HalfConvertOdd.center760OddLoan ++ HalfFieldOB5.copyN ++
          renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44)) m b)
      (run (liftF (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
          StairSchedule.placedEndPacket StairConcrete.bestLoans false 68)) m b) := by
  let P_odd := OddFullPass.HalfConvertOdd.center760OddLoan ++ HalfFieldOB5.copyN ++
    renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44
  let P_std := StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
    StairSchedule.placedEndPacket StairConcrete.bestLoans false 68
  have hstd_off : ∀ q ∈ wires P_std, Off q := by
    have hsub_hc : wires P_std ⊆ wires headCore := by
      have h1 := StairLoanConverterSupport.center760Loan_sub
      have h2 : wires (StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) ⊆
          wires (renameProgram (OB5.sig 511) (R2SqEp760.endPacket760 false)) := by
        have he : StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false := by
          simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true, if_false, if_true]
        rw [StairSchedule.placedEndPacket, he, renameProgram_support, renameProgram_support]
        exact Finset.image_subset_image StairEndpointLoan44.endPacket760Loan44_support
      simp only [P_std, headCore, wires_append]
      exact Finset.union_subset_union (Finset.union_subset_union h1 (Finset.Subset.refl _)) h2
    exact fun q hq => headCore_off q (hsub_hc hq)
  have hodd_sub_std : wires P_odd ⊆ wires P_std := by
    have h1 := OddFullPass.HalfConvertOdd.center760OddLoan_wires_sub
    have h2 : wires (renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44) ⊆
        wires (StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) := by
      have he : StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false := by
        simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true, if_false, if_true]
      rw [StairSchedule.placedEndPacket, he, renameProgram_support, renameProgram_support]
      exact Finset.image_subset_image OddFullPass.InverseTailCOdd.endPacket760OddLoan44_wires_sub
    intro q hq
    simp only [P_odd, P_std, wires_append, Finset.mem_union] at hq ⊢
    rcases hq with (ha | hb) | hc
    · rcases Finset.mem_union.mp (h1 ha) with hca | hcb
      · exact Or.inl (Or.inl hca)
      · exact Or.inl (Or.inr hcb)
    · exact Or.inl (Or.inr hb)
    · exact Or.inr (h2 hc)
  have hodd_off : ∀ q ∈ wires P_odd, Off q := fun q hq => hstd_off q (hodd_sub_std hq)
  -- Run `P_odd` vs `P_std` on `s_rec` first, then transfer to `pullIn b` via `run_local_increment`!
  let m12o := m.take (measurementCount (OddFullPass.HalfConvertOdd.center760OddLoan ++ HalfFieldOB5.copyN))
  let m1o := m12o.take (measurementCount OddFullPass.HalfConvertOdd.center760OddLoan)
  let m2o := m12o.drop (measurementCount OddFullPass.HalfConvertOdd.center760OddLoan)
  let m3o := m.drop (measurementCount (OddFullPass.HalfConvertOdd.center760OddLoan ++ HalfFieldOB5.copyN))
  let m12s := m.take (measurementCount (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN))
  let m1s := m12s.take (measurementCount StairConcrete.bestLoans.center)
  let m2s := m12s.drop (measurementCount StairConcrete.bestLoans.center)
  let m3s := m.drop (measurementCount (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN))
  -- Step 1: center760OddLoan vs center760Loan on `s_rec`
  have hs_vals : regValue fieldR s_rec.basis = Y.val ∧ regValue fieldY s_rec.basis = 0 := by
    obtain ⟨raw, _, hpair, henc⟩ := hrec
    have hpR : regValue fieldR raw.basis = Y.val := by
      have h1 := hpair.1
      rw [skywalkSharedField_z_eq_fieldR, Arithmetic.regValue_append] at h1
      have hlen : fieldR.length = 256 := by simp [fieldR, wireBlock_length]
      have hlt : Y.val < 2 ^ 256 := lt_trans Y.val_lt (by decide)
      rw [hlen] at h1
      have hbit0 : regValue [base 2312] raw.basis = 0 := by
        by_contra hne
        have hge : 2 ^ 256 ≤ 2 ^ 256 * regValue [base 2312] raw.basis :=
          Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
        omega
      rw [hbit0, Nat.mul_zero, Nat.add_zero] at h1
      exact h1
    have hpY : regValue fieldY raw.basis = 0 := by
      have h1 := hpair.2.1
      rw [skywalkSharedField_a_eq_fieldY, Arithmetic.regValue_append, ZMod.val_zero] at h1
      omega
    constructor
    · rw [← pullState_sig511_regValue_R, henc]
      exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ [] raw q
        (fun hw => allEncode_notRY false q hw ((mem_ryWires_iff q).mpr (Or.inl hq))))).trans hpR
    · rw [← pullState_sig511_regValue_Y, henc]
      exact (regValue_congr _ _ _ (fun q hq => run_preserves_outside _ [] raw q
        (fun hw => allEncode_notRY false q hw ((mem_ryWires_iff q).mpr (Or.inr hq))))).trans hpY
  have hcw_s := convWork_clean_of_encodedCanonical origin ctx ha Y s_rec hrec
  have hy43_s : ∀ q ∈ OddFullPass.HalfConvertOdd.yHosts44, s_rec.basis q = false := fun q hq =>
    (regValue_zero fieldY s_rec.basis).mp hs_vals.2 q (yHosts44_sub_fieldY q hq)
  let a1 := run OddFullPass.HalfConvertOdd.center760OddLoan m1o s_rec
  let b1 := run StairConcrete.bestLoans.center m1s s_rec
  have ha1_eq := OddFullPass.HalfConvertOdd.center760OddLoan_run_eq_centerOdd Y s_rec m1o (by rw [converterLayout760_word_eq_fieldR]; exact hs_vals.1) hcw_s hy43_s
  have ha1_corr := OddFullPass.HalfConvertOdd.centerOdd_correct StairBoundaryLoan.converterLayout760
    StairBoundaryLoan.converterLayout760_facts.widths
    converterLayout760_wires_nodup Y s_rec m1o (by rw [converterLayout760_word_eq_fieldR]; exact hs_vals.1) hcw_s
  rw [converterLayout760_word_eq_fieldR] at ha1_corr
  have hb1_eq : b1 = run R2SqEp760.center760 m1s s_rec :=
    StairBoundaryLoan.center760Loan_run_eq origin ctx ha Y s_rec m1s m1s hrec
  have hb1_frame : Rolling1588Frame.EncodedFieldFrame false origin (Y / 2) 0 b1 := by
    rw [hb1_eq]; exact (R2SqEp760.center760_frame origin ctx ha Y s_rec m1s hrec).2
  have hb1_corr : b1.phase = s_rec.phase ∧ regValue fieldR b1.basis = centerWord (Y / 2) ∧
      ∀ q, q ∉ fieldR → b1.basis q = s_rec.basis q := by
    rw [hb1_eq, StairBoundaryLoan.center760_eq]
    have hc := HalfConvert.center_correct StairBoundaryLoan.converterLayout760
      StairBoundaryLoan.converterLayout760_facts.widths
      converterLayout760_wires_nodup Y s_rec m1s (by rw [converterLayout760_word_eq_fieldR]; exact hs_vals.1)
        (bcWork_clean_of_encodedCanonical origin ctx ha Y s_rec hrec)
    rw [converterLayout760_word_eq_fieldR] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.2⟩
  have ha1p : a1.phase = s_rec.phase := by change (run _ m1o s_rec).phase = _; rw [ha1_eq]; exact ha1_corr.1
  have ha1out : ∀ q, q ∉ fieldR → a1.basis q = s_rec.basis q := fun q hq => by
    change (run _ m1o s_rec).basis q = _; rw [ha1_eq]; exact ha1_corr.2.2.2 q hq
  have ha1_agR : AgreeOutsideR a1 b1 :=
    ⟨ha1p.trans hb1_corr.1.symm, fun q hq => (ha1out q hq).trans (hb1_corr.2.2 q hq).symm⟩
  -- Step 2: HalfFieldOB5.copyN
  let a2 := run HalfFieldOB5.copyN m2o a1
  let b2 := run HalfFieldOB5.copyN m2s b1
  have hc_a := copyN_step ctx.hn a1 m2o
  have hc_b := copyN_step ctx.hn b1 m2s
  have hb2_frame : Rolling1588Frame.EncodedFieldFrame false origin (Y / 2) (Y / 2) b2 :=
    (Rolling1588HalfFieldOB5.copy_fill ctx.hn origin (Y / 2) b1 m2s hb1_frame).2
  have ha1_R : regValue fieldR a1.basis = P1Life.oddWord (Y / 2) := by
    change regValue fieldR (run _ m1o s_rec).basis = _; rw [ha1_eq]; exact ha1_corr.2.1
  have ha1_Y0 : regValue fieldY a1.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq =>
      ha1out q (fun hr => fieldR_disjoint_fieldY q hr hq))).trans hs_vals.2
  have ha2_R : regValue fieldR a2.basis = P1Life.oddWord (Y / 2) :=
    (regValue_congr _ _ _ (fun q hq => hc_a.2.1 q (fieldR_disjoint_fieldY q hq))).trans ha1_R
  have ha2_Y : regValue fieldY a2.basis = P1Life.oddWord (Y / 2) := by
    rw [hc_a.2.2, ha1_Y0, ha1_R, Nat.zero_xor]
  have ha2_ag : AgreeRY a2 b2 :=
    ⟨hc_a.1.trans (ha1_agR.1.trans hc_b.1.symm), fun q hq => by
      have hny : q ∉ fieldY := fun h => hq ((mem_ryWires_iff q).mpr (Or.inr h))
      have hnr : q ∉ fieldR := fun h => hq ((mem_ryWires_iff q).mpr (Or.inl h))
      rw [hc_a.2.1 q hny, hc_b.2.1 q hny]
      exact ha1_agR.2 q hnr⟩
  -- Step 3: endPacket760OddLoan44 vs placedEndPacket bestLoans false 68
  let a3 := run (renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44) m3o a2
  let b3 := run (StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) m3s b2
  have hsig_a2 := pullState_sig511_agreeRY ha2_ag
  have hzero_b2 := Rolling1588.encoded_zero_region base (base 2409) false ctx.hn (ctx.hp _ (by simp))
    origin ctx.env ctx.legal (Y / 2) (Y / 2) _ hb2_frame
  have hzero_a2 : ∀ q, Placement5.zeroRegion q → (pullState (OB5.sig 511) a2).basis (base q) = false :=
    fun q hq => (hsig_a2.2 (base q) (base_not_ryWires_of_zeroRegion q hq)).trans (hzero_b2 q hq)
  have hflag_b2 : (pullState (OB5.sig 511) b2).basis (base 2409) = false := by
    obtain ⟨raw, _, hpair, henc⟩ := hb2_frame
    have hne : base 2409 ∉ wires (Rolling1588.allEncode base false 102) := fun hw =>
      absurd (List.mem_toFinset.mp (Rolling1588.allEncode_history_support base false 102 (by decide) hw))
        (by decide +kernel)
    rw [henc, run_preserves_outside _ [] raw _ hne]
    exact (hpair.2.2 (base 2409) (by decide +kernel) (by decide +kernel)).trans ctx.hg0
  have ha3_spec := OddFullPass.InverseTailCOdd.endPacket760OddLoan44_frame (Y / 2)
    (pullState (OB5.sig 511) a2) m3o
    (q6Clean_of_agreeRY hsig_a2 (q6Clean_of_encoded5 origin ctx (Y / 2) (Y / 2) _ hb2_frame))
    ((hsig_a2.2 (base 2409) (by decide +kernel)).trans hflag_b2)
    (by rw [endpointL_r_eq, pullState_sig511_regValue_R]; exact ha2_R)
    (by rw [endpointL_y_eq, pullState_sig511_regValue_Y]; exact ha2_Y)
    (Placement5.shifted_zero_boundary Placement5.pi0 Placement5.pi0_outside _ hzero_a2)
    ((hsig_a2.2 (base 760) (by decide +kernel)).trans (R2SqEp760.encoded5_760 origin ctx _ _ _ hb2_frame))
    ((hsig_a2.2 (base 717) (by decide +kernel)).trans (R2SqEp760.encoded5_717 origin ctx _ _ _ hb2_frame))
  rw [endpointL_r_eq] at ha3_spec
  have hb3_eq : run (StairConcrete.bestLoans.endPacket false 68) m3s (pullState (OB5.sig 511) b2) =
      run (R2SqEp760.endPacket760 false) m3s (pullState (OB5.sig 511) b2) := by
    have he : StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false := by
      simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true, if_false, if_true]
    rw [he]
    exact StairEndpointLoan44.endPacket760Loan44_run_eq false origin ctx en (Y / 2) (Y / 2) rfl _ m3s m3s hb2_frame
  have hb3_spec := R2SqEp760.endPacket760_frame false false origin ctx en (Y / 2) (Y / 2)
    (fun h => absurd h (by decide)) (fun _ => rfl) (pullState (OB5.sig 511) b2) m3s hb2_frame
  have hb3_frame : Rolling1588Frame.EncodedFieldFrame false origin
      (Replay5.endPayload false origin (Y / 2, Y / 2)).1
      (Replay5.endPayload false origin (Y / 2, Y / 2)).2 b3 := by
    have hconj := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
      (StairConcrete.bestLoans.endPacket false 68) m3s b2
    change Rolling1588.EncodedFieldFrame5 base (base 2409) false origin _ _ (pullState (OB5.sig 511) b3)
    rw [show pullState (OB5.sig 511) b3 = run (StairConcrete.bestLoans.endPacket false 68) m3s (pullState (OB5.sig 511) b2) from hconj, hb3_eq]
    exact hb3_spec.2
  have h510_eq : (pullState (OB5.sig 511) a2).basis (base 510) = origin (base 510) := by
    refine (hsig_a2.2 (base 510) (by decide +kernel)).trans ?_
    obtain ⟨raw, _, hpair, henc⟩ := hb2_frame
    rw [henc, run_preserves_outside _ [] raw _ (allEncode_510_free false)]
    exact hpair.2.2 (base 510) (by decide +kernel) (by decide +kernel)
  have hV1_eq : (Replay5.endPayload false origin (Y / 2, Y / 2)).1 =
      (if (pullState (OB5.sig 511) a2).basis (base 510) then 1 else 3) * (Y / 2) := by
    rw [h510_eq]; simp only [Replay5.endPayload, mixedTranscriptBit, en, if_true]
    cases origin (base 510) <;> simp <;> ring
  have hV2_eq : (Replay5.endPayload false origin (Y / 2, Y / 2)).2 = Y / 2 := rfl
  have ha3_ag : AgreeRY a3 b3 := by
    have hconj_a := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
      OddFullPass.InverseTailCOdd.endPacket760OddLoan44 m3o a2
    have hconj_b := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
      (StairConcrete.bestLoans.endPacket false 68) m3s b2
    have ha3p : a3.phase = a2.phase :=
      (pullState_phase _ a3).symm.trans ((congrArg State.phase hconj_a).trans
        (ha3_spec.1.trans (pullState_phase _ a2)))
    have hb3p : b3.phase = b2.phase :=
      (pullState_phase _ b3).symm.trans ((congrArg State.phase hconj_b).trans
        (((congrArg State.phase hb3_eq).trans hb3_spec.1).trans (pullState_phase _ b2)))
    have hph : a3.phase = b3.phase := ha3p.trans (ha2_ag.1.trans hb3p.symm)
    have hb3_out := encodedFieldFrame_agreeRY centerWord centerWord false origin _ _ _ _ b3 b2 hb3p hb3_frame hb2_frame
    have hp : AgreeRY (pullState (OB5.sig 511) a3) (pullState (OB5.sig 511) b3) :=
      ⟨(pullState_phase _ a3).trans (hph.trans (pullState_phase _ b3).symm), fun q hq => by
        rw [hconj_a, ha3_spec.2.2 q (fun hr => hq ((mem_ryWires_iff q).mpr (Or.inl hr)))]
        exact (hsig_a2.2 q hq).trans ((pullState_sig511_agreeRY hb3_out).2 q hq).symm⟩
    have hu := pullState_sig511_agreeRY hp
    rwa [StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide)),
         StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide))] at hu
  have ha3_vals : regValue fieldR a3.basis = P1Life.oddWord (Replay5.endPayload false origin (Y / 2, Y / 2)).1 ∧
      regValue fieldY a3.basis = P1Life.oddWord (Replay5.endPayload false origin (Y / 2, Y / 2)).2 := by
    have hconj_a := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
      OddFullPass.InverseTailCOdd.endPacket760OddLoan44 m3o a2
    constructor
    · rw [← pullState_sig511_regValue_R, hconj_a, hV1_eq]; exact ha3_spec.2.1
    · rw [← pullState_sig511_regValue_Y, hconj_a, hV2_eq]
      exact (regValue_congr _ _ _ (fun q hq => ha3_spec.2.2 q (fun hr => fieldR_disjoint_fieldY q hr hq))).trans
        (by rw [pullState_sig511_regValue_Y]; exact ha2_Y)
  have hb3_vals := encodedFieldFrame_values false origin _ _ b3 hb3_frame
  -- Now transfer `P_odd` and `P_std` from `s_rec` to `pullIn b` via `run_local_increment`!
  have hs_rel : OddRel P1Life.oddWord P1Life.oddWord (run P_odd m s_rec) (run P_std m s_rec) := by
    have h1 : run P_odd m s_rec = a3 := by simp only [P_odd, run_append, a3, a2, a1, m1o, m2o, m3o, m12o]
    have h2 : run P_std m s_rec = b3 := by simp only [P_std, run_append, b3, b2, b1, m1s, m2s, m3s, m12s]
    rw [h1, h2]
    exact oddRel_of_agreeRY_values _ _ ha3_ag hb3_vals.1 hb3_vals.2 ha3_vals.1 ha3_vals.2
  have hinc_odd := Arithmetic.run_local_increment P_odd (pullIn b) s_rec m (fun q hq => hpb_rec q (hodd_off q hq))
  have hinc_std := Arithmetic.run_local_increment P_std (pullIn b) s_rec m (fun q hq => hpb_rec q (hstd_off q hq))
  have hout_ag : AgreeRY (run P_odd m (pullIn b)) (run P_std m (pullIn b)) := by
    have hph : (run P_odd m (pullIn b)).phase = (run P_std m (pullIn b)).phase :=
      phase_eq_of_xor hinc_odd.1 (hs_rel.1.1 ▸ hinc_std.1) rfl
    refine ⟨hph, fun q hq => ?_⟩
    by_cases h1 : q ∈ wires P_odd
    · rw [hinc_odd.2 q h1, hinc_std.2 q (hodd_sub_std h1)]; exact hs_rel.1.2 q hq
    · rw [run_preserves_outside P_odd m (pullIn b) q h1]
      by_cases h2 : q ∈ wires P_std
      · rw [hinc_std.2 q h2]
        have h3 := hs_rel.1.2 q hq
        rw [run_preserves_outside P_odd m s_rec q h1] at h3
        exact (hpb_rec q (hstd_off q h2)).trans h3
      · rw [run_preserves_outside P_std m (pullIn b) q h2]
  have hout_vals_odd : regValue fieldR (run P_odd m (pullIn b)).basis = regValue fieldR (run P_odd m s_rec).basis ∧
      regValue fieldY (run P_odd m (pullIn b)).basis = regValue fieldY (run P_odd m s_rec).basis := by
    have hEq (q : Wire) (hq : q ∈ ryWires) : (run P_odd m (pullIn b)).basis q = (run P_odd m s_rec).basis q := by
      by_cases hw : q ∈ wires P_odd
      · exact hinc_odd.2 q hw
      · rw [run_preserves_outside P_odd m (pullIn b) q hw, run_preserves_outside P_odd m s_rec q hw]
        exact hpb_rec q (ryWires_off q hq)
    exact ⟨regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inl hq))),
           regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inr hq)))⟩
  have hout_vals_std : regValue fieldR (run P_std m (pullIn b)).basis = regValue fieldR (run P_std m s_rec).basis ∧
      regValue fieldY (run P_std m (pullIn b)).basis = regValue fieldY (run P_std m s_rec).basis := by
    have hEq (q : Wire) (hq : q ∈ ryWires) : (run P_std m (pullIn b)).basis q = (run P_std m s_rec).basis q := by
      by_cases hw : q ∈ wires P_std
      · exact hinc_std.2 q hw
      · rw [run_preserves_outside P_std m (pullIn b) q hw, run_preserves_outside P_std m s_rec q hw]
        exact hpb_rec q (ryWires_off q hq)
    exact ⟨regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inl hq))),
           regValue_congr _ _ _ (fun q hq => hEq q ((mem_ryWires_iff q).mpr (Or.inr hq)))⟩
  have hout_rel : OddRel P1Life.oddWord P1Life.oddWord (run P_odd m (pullIn b)) (run P_std m (pullIn b)) := by
    refine ⟨hout_ag, ?_, ?_⟩
    · intro X hX; rw [hout_vals_odd.1]; exact hs_rel.2.1 X (by rwa [← hout_vals_std.1])
    · intro Y' hY'; rw [hout_vals_odd.2]; exact hs_rel.2.2 Y' (by rwa [← hout_vals_std.2])
  rw [StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run]
  exact pullOut_oddRel hout_rel


end ECDSAAdd.Entrant.OddStockLockstep

end

end
-- ==== end OddLockstepSteps ====

-- ==== begin OddLockstepDiv ====
section

set_option autoImplicit false

section

namespace ECDSAAdd.Entrant.OddStockLockstep

open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout
open StairLoanExitReachX StairLoanField7Transport StairPacket

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] run measurementCount wires renameProgram cut Rolling1588TickGap.forward

theorem pullState_sig511_injective {a b : State}
    (h : pullState (OB5.sig 511) a = pullState (OB5.sig 511) b) : a = b := by
  have h2 := congrArg (pullState (OB5.sig 511)) h
  rwa [StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide)),
       StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide))] at h2

theorem local_eq_of_sub (P Q : Program) (hsub : wires P ⊆ wires Q) (a b : State) (m : List Bool)
    (hag : ∀ q ∈ wires Q, a.basis q = b.basis q) (heq : run P m b = run Q m b) :
    run P m a = run Q m a := by
  have hp := Arithmetic.run_local_increment P a b m (fun q hq => hag q (hsub hq))
  have hq := Arithmetic.run_local_increment Q a b m hag
  apply State.extensionality
  · have hpeq : (run P m b).phase = (run Q m b).phase := congrArg State.phase heq
    have h1 : ((run P m a).phase ^^ a.phase) = ((run P m b).phase ^^ b.phase) := hp.1
    have h2 : ((run Q m a).phase ^^ a.phase) = ((run P m b).phase ^^ b.phase) := by rw [hpeq]; exact hq.1
    revert h1 h2
    cases (run P m a).phase <;> cases (run Q m a).phase <;> cases a.phase <;>
      cases (run P m b).phase <;> cases b.phase <;> decide
  · funext w
    by_cases h1 : w ∈ wires P
    · rw [hp.2 w h1, hq.2 w (hsub h1), heq]
    · rw [run_preserves_outside P m a w h1]
      by_cases h2 : w ∈ wires Q
      · rw [hq.2 w h2, ← heq, run_preserves_outside P m b w h1]; exact hag w h2
      · rw [run_preserves_outside Q m a w h2]

theorem pullState_fieldMap_basis (s : State) (q : Wire) :
    (pullState fieldMap s).basis q =
      (pullState HostOB5.hostSwap
        (pullState (Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host) s)).basis q := rfl

private theorem sig511_511 : OB5.sig 511 (base 511) = base 511 := by decide +kernel
private theorem regValue_run_disjoint_R (P : Program) (h : ∀ q ∈ wires P, q ∉ fieldR)
    (m : List Bool) (s : State) : regValue fieldR (run P m s).basis = regValue fieldR s.basis :=
  regValue_congr fieldR (run P m s).basis s.basis
    (fun q hq => run_preserves_outside P m s q (fun hw => h q hw hq))

private theorem R0_eq :
    R0 = renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
      (StairSchedule.paritySetup ++ StairSchedule.hostedX) :=
  List.append_inj_left' R0_shape rfl

private def fmInv (q : Wire) : Wire :=
  HostOB5.hostSwap (Equiv.swap FrontierEntry1591Field.work FrontierEntry1591Field.host q)

private theorem fmInv_fieldMap (q : Wire) : fmInv (fieldMap q) = q := by
  simp only [fmInv, fieldMap, Equiv.swap_apply_self, HostOB5.hostSwap_invol]



theorem hostPlan_group_notRY (d : Bool) (def_ start len : Nat) (hd : def_ ≠ 44) :
    ∀ q ∈ hostPlan.group d def_ start len, q ∉ ryWires := by
  rw [hp_group d def_ start len hd]
  intro q hq
  unfold StairV3Primitives.groupHosts at hq
  split_ifs at hq
  · exact hosts_not_ryWires 87 (by decide) q hq
  · exact poolHosts_not_ryWires q hq
  · rcases List.mem_append.mp hq with h1 | h2
    · have hb : StairV3Primitives.budgetOfDeficit def_ ∈ budgets := by
        unfold StairV3Primitives.budgetOfDeficit; split_ifs <;> decide
      exact hosts_not_ryWires _ hb q h1
    · exact poolHosts_not_ryWires q h2

theorem hostPlan1542_group_sub (d : Bool) (def_ start len : Nat)
    (hdef : def_ ∈ [13, 22, 30, 36, 41, 43]) :
    ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group d (def_ + 1) start len,
      q ∈ hostPlan.group d def_ start len := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hdef
  rcases hdef with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [OddFullPass.P1LifeLoan.hostPlan1542] at hq
    split_ifs at hq with h44
    · simp at hq
    · rw [hp_group d _ start len (by decide)]
      unfold StairV3Primitives.groupHosts StairV3Primitives.budgetOfDeficit
      unfold OddFullPass.P1LifeLoan.budgetOfDeficit1542 at hq
      split_ifs at hq ⊢ <;> first | exact List.mem_append_left _ hq | omega

theorem hostPlan1542_group_notRY (d : Bool) (def_ start len : Nat)
    (hdef : def_ ∈ [13, 22, 30, 36, 41, 43]) :
    ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group d (def_ + 1) start len, q ∉ ryWires :=
  fun q hq => hostPlan_group_notRY d def_ start len (by simp at hdef; omega) q
    (hostPlan1542_group_sub d def_ start len hdef q hq)

theorem hostPlan1542_group_fresh_odd (d : Bool) (def_ start len : Nat) (hd : def_ ≤ 43)
    (h1 : 1 ≤ start) (hb : start + len ≤ 102)
    (hdef : def_ ∈ [13, 22, 30, 36, 41, 43])
    (hsched : def_ = 43 ∨ (def_, start, len) ∈ [(13, 85, 5), (22, 90, 3), (30, 93, 3),
      (36, 96, 2), (41, 98, 2)]) :
    ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group d (def_ + 1) start len,
      q ∉ wires (renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups d (def_ + 1) start len)) := by
  have hsub : wires (renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups d (def_ + 1) start len)) ⊆
      wires (renameProgram (OB5.sig 511) (Rolling1588.groups d start len)) := by
    rw [renameProgram_support, renameProgram_support]
    exact Finset.image_subset_image
      ((StairLoanGroupSupport.sequence_sub _ _ _
        (fun k => OddFullPass.P1LifeLoan.packet_wires_sub d (def_ + 1) k (by omega)) _ _).trans
       (StairLoanGroupSupport.groups_sub d (def_ + 1) (by omega) start len))
  intro q hq hw
  rcases hsched with rfl | hs
  · dsimp only [OddFullPass.P1LifeLoan.hostPlan1542] at hq; simp at hq
  · have hfp : q ∈ futurePayload (OddFullPass.P1LifeLoan.budgetOfDeficit1542 (def_ + 1)) := by
      change q ∈ (if def_ + 1 = 44 then [] else hosts (OddFullPass.P1LifeLoan.budgetOfDeficit1542 (def_ + 1))) at hq
      split_ifs at hq with h44
      · simp at hq
      · have hfp_all : ([14, 23, 31, 37, 42] : List Nat).all (fun d' =>
            (hosts (OddFullPass.P1LifeLoan.budgetOfDeficit1542 d')).all (fun w =>
              (futurePayload (OddFullPass.P1LifeLoan.budgetOfDeficit1542 d')).contains w)) = true := by
          decide +kernel
        have hd_mem : def_ + 1 ∈ ([14, 23, 31, 37, 42] : List Nat) := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
          rcases hs with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> simp
        have h1 := List.all_eq_true.mp (List.all_eq_true.mp hfp_all (def_ + 1) hd_mem) q hq
        exact List.contains_iff_mem.mp h1
    have hlim : start + len ≤ startFor (OddFullPass.P1LifeLoan.budgetOfDeficit1542 (def_ + 1)) / 5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    exact StairField2V3Groups.groups_avoid_payload d _ (OddFullPass.P1LifeLoan.budgetOfDeficit1542_mem _) len start hlim q hfp (hsub hw)

private theorem lowMap_eq_fieldPlace (w : Wire) : lowMap w = fieldPlace w := rfl

private theorem grpL_eq (def_ start len : Nat) :
    grpL StairConcrete.bestLoans def_ start len =
      liftF (renameProgram (OB5.sig 511) (StairGroups.groups true def_ start len)) := rfl

private theorem grp_eq (start len : Nat) :
    grp start len = liftF (renameProgram (OB5.sig 511) (Rolling1588.groups true start len)) := rfl

private theorem cutLoan_helper {P : Program} {pre : State → Prop} {d : Bool}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group d 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) :
    ∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (run P m s).basis (fieldPlace q) = false := by
  intro q hq
  exact clean s h m _ (by rw [hp_group d 0 1 84 (by decide)]; exact List.mem_map.mpr ⟨q, hq, rfl⟩)

theorem cleanCut_after {pre : State → Prop} {P1 P2 P12 : Program} {sites : List Wire}
    (h : CutClean pre P12 sites) (hcat : P12 = P1 ++ P2) (s : State) (hs : pre s) (m1 m2 : List Bool) :
    ∀ q ∈ sites, (run P2 m2 (run P1 m1 s)).basis q = false := by
  intro q hq
  have h2 := h s hs (WindowFieldJourney.joinTapes P1 m1 m2) q hq
  rwa [hcat, WindowFieldJourney.joined] at h2

private theorem fullEntryCut3Clean (parts : StairField13V3Fresh.EntryClean) :
    CutClean EntryPre (cut eps 3) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group true 0 1 84).map lowMap) :=
  parts.groupsBefore (3, 0, 1, 84) (List.Mem.head _)


private theorem v_used7_and_safe_chk :
    ((List.range 1024).filter (fun x => !x.testBit 5 && !x.testBit 9)).all (fun x =>
      !decide (Prefix1590Codec.codeOf (MeasuredCodec5.bitsOf x) ∈ Prefix1590Codec.canonicalCodes) ||
      (MeasuredCodec5.safe FourScratchPrefix.V x &&
        let y := MeasuredCodec5.bitRun FourScratchPrefix.V x
        let v := (([1, 2, 3, 4, 6, 7, 8] : List Nat).zipIdx).foldl
          (fun acc p => if y.testBit p.1 then acc + 2 ^ p.2 else acc) 0
        TagPack1542.used7.contains v)) = true := by
  have hc : ∀ (l : List Nat) (a : Nat), l.contains a = decide (a ∈ l) := by
    intro l a
    cases h : decide (a ∈ l)
    · exact Bool.eq_false_iff.mpr (fun hc => (decide_eq_false_iff_not.mp h) (List.contains_iff_mem.mp hc))
    · exact List.contains_iff_mem.mpr (of_decide_eq_true h)
  have hm : ((List.range 1024).filter (fun x => !x.testBit 5 && !x.testBit 9)).all (fun x =>
      !(StairLoan.maskOf Prefix1590Codec.canonicalCodes).testBit
          (Prefix1590Codec.codeOf (MeasuredCodec5.bitsOf x)) ||
      (MeasuredCodec5.safe FourScratchPrefix.V x &&
        let y := MeasuredCodec5.bitRun FourScratchPrefix.V x
        let v := (([1, 2, 3, 4, 6, 7, 8] : List Nat).zipIdx).foldl
          (fun acc p => if y.testBit p.1 then acc + 2 ^ p.2 else acc) 0
        (StairLoan.maskOf TagPack1542.used7).testBit v)) = true := by
    decide +kernel
  simpa only [StairLoan.testBit_maskOf, hc] using hm

private theorem v_in_used7 :
    ∀ x : Fin 1024, x.val.testBit 5 = false → x.val.testBit 9 = false →
      Prefix1590Codec.codeOf (MeasuredCodec5.bitsOf x.val) ∈ Prefix1590Codec.canonicalCodes →
      let y := MeasuredCodec5.bitRun FourScratchPrefix.V x.val
      let v := (([1, 2, 3, 4, 6, 7, 8] : List Nat).zipIdx).foldl
        (fun acc p => if y.testBit p.1 then acc + 2 ^ p.2 else acc) 0
      TagPack1542.used7.contains v = true := by
  intro x h5 h9 hcan
  have hx_mem : x.val ∈ (List.range 1024).filter (fun n => !n.testBit 5 && !n.testBit 9) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr x.isLt, by simp [h5, h9]⟩
  have h := List.all_eq_true.mp v_used7_and_safe_chk x.val hx_mem
  simp only [hcan, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.2

private theorem v_safe_canon :
    ∀ x : Fin 1024, x.val.testBit 5 = false → x.val.testBit 9 = false →
      Prefix1590Codec.codeOf (MeasuredCodec5.bitsOf x.val) ∈ Prefix1590Codec.canonicalCodes →
      MeasuredCodec5.safe FourScratchPrefix.V x.val = true := by
  intro x h5 h9 hcan
  have hx_mem : x.val ∈ (List.range 1024).filter (fun n => !n.testBit 5 && !n.testBit 9) := by
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr x.isLt, by simp [h5, h9]⟩
  have h := List.all_eq_true.mp v_used7_and_safe_chk x.val hx_mem
  simp only [hcan, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  exact h.1

private theorem hlab_p0_1542 : ∀ i : Fin 7, Prefix1590.payload0 ⟨i.val + 1, by omega⟩ =
    FourScratchWindow.label (([1, 2, 3, 4, 6, 7, 8] : List Nat)[i.val]'(by simp)) := by
  decide +kernel

private theorem odd_cut_tagReady (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p)
    (a b record : State)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hagree : AgreeOutside (Δv 87) b record)
    (hcv : CvX x 87 b.basis record.basis)
    (hwin : StairField2V3Win.WinT x record) :
    StairPacket.WindowFieldView.TagReady (pullIn a) := by
  constructor
  · -- Part 1: `regValue WindowFieldCosts.rest87A (pullIn a).basis < 87`
    have hsub_fp : WindowFieldCosts.rest87A.all (fun q => (futurePayload 87).contains q) = true := by decide +kernel
    have hnot_ry : WindowFieldCosts.rest87A.all (fun q => !(ryWires.contains q)) = true := by decide +kernel
    have hnot_rl : WindowFieldCosts.rest87A.all (fun q => !(restLetters 87).contains q) = true := by decide +kernel
    have hreg_eq : StairCodec.reg (physicalLayout 87).A (StairCodec.bitWidth 87) = WindowFieldCosts.rest87A := by decide +kernel
    have hnodup : WindowFieldCosts.rest87A.Nodup := by decide +kernel
    obtain ⟨_, _, hbits⟩ := hcv
    let z := StairBridgeDomain.realNatState x ECDSAAdd.p (startFor 87)
    let σ := StairBridgeDomain.realSign x ECDSAAdd.p (startFor 87)
    let w := z.u - σ.toNat
    have hdom := StairBridgeDomain.real_codecDomain x ECDSAAdd.p (startFor 87)
      (by decide) hx0 (by decide) (by decide) hx (StairField2V3Unpack.coprime_of_lt x hx0 hx) (by decide)
    have hvpos : 0 < z.v := hdom.2.1
    have hbv : 1 ≤ StairCodec.natBitLength z.v := by
      have hne : z.v ≠ 0 := by omega
      simp [StairCodec.natBitLength, hne]
    have hsum : StairCodec.natBitLength z.u + StairCodec.natBitLength z.v ≤ 87 := by
      simpa [show 512 - startFor 87 = 87 from rfl] using hdom.2.2.2.2.1
    have hwu : w ≤ z.u := Nat.sub_le _ _
    have hbl_lt : StairCodec.natBitLength w < 87 := by
      have hm := StairField2V3Unpack.natBitLength_mono w z.u hwu
      omega
    have hag : ∀ q ∈ WindowFieldCosts.rest87A,
        (pullIn a).basis q = StairCodec.registerBasis WindowFieldCosts.rest87A (StairCodec.natBitLength w) q := by
      intro q hq
      have hnr : q ∉ ryWires := by
        have h1 := List.all_eq_true.mp hnot_ry q hq; simpa using h1
      have hfp : q ∈ futurePayload 87 := List.contains_iff_mem.mp (List.all_eq_true.mp hsub_fp q hq)
      have hnrl : q ∉ restLetters 87 := by
        have h1 := List.all_eq_true.mp hnot_rl q hq; simpa using h1
      have h1 := (pullIn_agreeRY hrel.1).2 q hnr
      have h2 : (pullIn b).basis q = StairField2V3Seg.cmpBits 87 x q := (hbits q hfp).2
      rw [h1, h2]
      simp only [StairField2V3Seg.cmpBits, hreg_eq]
      have hfalse : StairCodec.registerBasis (restLetters 87)
          (StairCodec.compactF 87 w z.v + σ.toNat * 2 ^ (87 - 2)) q = false :=
        StairField2V3Codec.registerBasis_not_mem (restLetters 87) _ q hnrl
      rw [hfalse, Bool.false_or]
    rw [regValue_congr WindowFieldCosts.rest87A (pullIn a).basis _ hag]
    have hreg_val : regValue WindowFieldCosts.rest87A
        (StairCodec.registerBasis WindowFieldCosts.rest87A (StairCodec.natBitLength w)) = StairCodec.natBitLength w := by
      have h7 : WindowFieldCosts.rest87A.length = 7 := by decide
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < 7
      · have hb := Arithmetic.regValue_bit WindowFieldCosts.rest87A i 0
          (StairCodec.registerBasis WindowFieldCosts.rest87A (StairCodec.natBitLength w)) (by omega)
        rw [List.getD_eq_getElem _ _ (by omega),
            StairField2V3Codec.registerBasis_get WindowFieldCosts.rest87A hnodup (StairCodec.natBitLength w) i (by omega)] at hb
        rw [Nat.testBit_eq_decide_div_mod_eq, ← hb]
        cases htb : (StairCodec.natBitLength w).testBit i <;> simp [Nat.testBit_eq_decide_div_mod_eq, htb]
      · have hlt7 : regValue WindowFieldCosts.rest87A
            (StairCodec.registerBasis WindowFieldCosts.rest87A (StairCodec.natBitLength w)) < 2 ^ 7 := by
          rw [← h7]; exact Arithmetic.regValue_lt _ _
        have hlt : regValue WindowFieldCosts.rest87A
            (StairCodec.registerBasis WindowFieldCosts.rest87A (StairCodec.natBitLength w)) < 2 ^ i :=
          lt_of_lt_of_le hlt7 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i))
        have hlt2 : StairCodec.natBitLength w < 2 ^ i :=
          lt_of_lt_of_le (by omega : StairCodec.natBitLength w < 2 ^ 7)
            (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i))
        rw [Nat.testBit_lt_two_pow hlt, Nat.testBit_lt_two_pow hlt2]
    rw [hreg_val]
    exact hbl_lt
  · -- Part 2: `regValue WindowFieldCosts.p0Sites (pullIn a).basis ∈ TagPack1542.used7`
    obtain ⟨s1, _, _, _, _, _, cl, cn, _, _, _, _, pay⟩ := hwin
    have hnot_ry : WindowFieldCosts.p0Sites.all (fun q => !(ryWires.contains q)) = true := by decide +kernel
    have hnot_fp : WindowFieldCosts.p0Sites.all (fun q => !((futurePayload 87).contains q)) = true := by decide +kernel
    have hag_rec : ∀ q ∈ WindowFieldCosts.p0Sites, (pullIn a).basis q = (pullIn record).basis q := by
      intro q hq
      have hnr : q ∉ ryWires := by have h1 := List.all_eq_true.mp hnot_ry q hq; simpa using h1
      have hnf : q ∉ futurePayload 87 := by have h1 := List.all_eq_true.mp hnot_fp q hq; simpa using h1
      have h1 := (pullIn_agreeRY hrel.1).2 q hnr
      have h2 : (pullIn b).basis q = (pullIn record).basis q := by
        change b.basis (fieldPlace q) = record.basis (fieldPlace q)
        apply hagree.2
        intro hm
        simp only [Δv, List.mem_toFinset, List.mem_map] at hm
        obtain ⟨r, hr, heq⟩ := hm
        have qr : r = q := by have := congrArg fieldPlaceInv heq; rwa [inv_fieldPlace, inv_fieldPlace] at this
        exact hnf (qr ▸ hr)
      exact h1.trans h2
    let x10 := regValue ((List.range 10).map FourScratchWindow.label) s1.basis
    have hx10_lt : x10 < 1024 := by
      simpa [x10] using Arithmetic.regValue_lt ((List.range 10).map FourScratchWindow.label) s1.basis
    have hbit10 : ∀ q : Nat, q < 12 → (FourScratchWindow.pull s1).basis q = (MeasuredCodec5.bitsOf x10) q := by
      intro q hq
      by_cases h10 : q < 10
      · have hlen10 : ((List.range 10).map FourScratchWindow.label).length = 10 := by simp
        have hb := Arithmetic.regValue_bit ((List.range 10).map FourScratchWindow.label) q 0 s1.basis (by rw [hlen10]; exact h10)
        rw [List.getD_eq_getElem _ _ (by rw [hlen10]; exact h10), List.getElem_map, List.getElem_range] at hb
        change (s1.basis (FourScratchWindow.label q)).toNat = x10 / 2 ^ q % 2 at hb
        simp only [MeasuredCodec5.bitsOf, Nat.testBit_eq_decide_div_mod_eq, ← hb, FourScratchWindow.pull]
        cases s1.basis (FourScratchWindow.label q) <;> simp
      · have hhi : (MeasuredCodec5.bitsOf x10) q = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx10_lt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 10 ≤ q)))
        rw [hhi]
        have : q = 10 ∨ q = 11 := by omega
        rcases this with rfl | rfl
        · exact cl.2.2.1
        · exact cl.2.2.2
    have hx5 : x10.testBit 5 = false := (hbit10 5 (by decide)).symm.trans cl.1
    have hx9 : x10.testBit 9 = false := (hbit10 9 (by decide)).symm.trans cl.2.1
    have hx_can : Prefix1590Codec.codeOf (MeasuredCodec5.bitsOf x10) ∈ Prefix1590Codec.canonicalCodes := by
      have hcongr : Prefix1590Codec.codeOf (MeasuredCodec5.bitsOf x10) =
          Prefix1590Codec.codeOf (FourScratchWindow.pull s1).basis := by
        simp only [Prefix1590Codec.codeOf]
        rw [hbit10 0 (by decide), hbit10 1 (by decide), hbit10 2 (by decide), hbit10 3 (by decide),
            hbit10 4 (by decide), hbit10 6 (by decide), hbit10 7 (by decide), hbit10 8 (by decide)]
      rw [hcongr, FourScratchWindow.code_compat s1]
      exact cn
    have hfin := v_in_used7 ⟨x10, hx10_lt⟩ hx5 hx9 hx_can
    have hsafe := v_safe_canon ⟨x10, hx10_lt⟩ hx5 hx9 hx_can
    have hsim := MeasuredCodec5.run_sim FourScratchPrefix.V [] false x10
    rw [MeasuredCodec5.sim_safe _ _ hsafe] at hsim
    have hrun_v : ∀ q < 12, (run FourScratchWindow.prefixProgram [] s1).basis (FourScratchWindow.label q) =
        (MeasuredCodec5.bitRun FourScratchPrefix.V x10).testBit q := by
      intro q hq
      rw [FourScratchWindow.prefixProgram, (FourScratchWindow.mapped_run FourScratchPrefix.V FourScratchPrefix.support.1 s1 []).2 q hq]
      have hloc := Arithmetic.run_local_increment FourScratchPrefix.V (FourScratchWindow.pull s1)
        ⟨false, MeasuredCodec5.bitsOf x10⟩ [] (fun r hr => hbit10 r (Finset.mem_range.mp (FourScratchPrefix.support.1 hr)))
      by_cases hmem : q ∈ wires FourScratchPrefix.V
      · rw [hloc.2 q hmem, hsim]; rfl
      · rw [run_preserves_outside _ _ _ _ hmem, hbit10 q hq]
        change (⟨false, MeasuredCodec5.bitsOf x10⟩ : State).basis q = _
        rw [← run_preserves_outside FourScratchPrefix.V [] ⟨false, MeasuredCodec5.bitsOf x10⟩ q hmem, hsim]; rfl
    have hval_eq : regValue WindowFieldCosts.p0Sites (pullIn a).basis =
        (([1, 2, 3, 4, 6, 7, 8] : List Nat).zipIdx).foldl
          (fun acc p => if (MeasuredCodec5.bitRun FourScratchPrefix.V x10).testBit p.1 then acc + 2 ^ p.2 else acc) 0 := by
      have hbit_i : ∀ i : Fin 7,
          (pullIn a).basis (Prefix1590.payload0 ⟨i.val + 1, by omega⟩) =
          (MeasuredCodec5.bitRun FourScratchPrefix.V x10).testBit (([1, 2, 3, 4, 6, 7, 8] : List Nat)[i.val]'(by simp)) := by
        intro i
        have hm : Prefix1590.payload0 ⟨i.val + 1, by omega⟩ ∈ WindowFieldCosts.p0Sites := by
          simp only [WindowFieldCosts.p0Sites, List.mem_map, List.mem_finRange, true_and]
          exact ⟨i, rfl⟩
        rw [hag_rec _ hm, pay ⟨i.val + 1, by omega⟩ (Nat.succ_ne_zero _), hlab_p0_1542 i]
        exact hrun_v _ (by fin_cases i <;> decide)
      have hlist : WindowFieldCosts.p0Sites =
          [ Prefix1590.payload0 ⟨1, by decide⟩, Prefix1590.payload0 ⟨2, by decide⟩,
            Prefix1590.payload0 ⟨3, by decide⟩, Prefix1590.payload0 ⟨4, by decide⟩,
            Prefix1590.payload0 ⟨5, by decide⟩, Prefix1590.payload0 ⟨6, by decide⟩,
            Prefix1590.payload0 ⟨7, by decide⟩ ] := rfl
      rw [hlist]
      simp only [regValue, List.foldr_cons, List.foldr_nil]
      rw [hbit_i ⟨0, by decide⟩, hbit_i ⟨1, by decide⟩, hbit_i ⟨2, by decide⟩,
          hbit_i ⟨3, by decide⟩, hbit_i ⟨4, by decide⟩, hbit_i ⟨5, by decide⟩,
          hbit_i ⟨6, by decide⟩]
      have hfold : ∀ (idxs : List Nat) (f : Nat → Bool) (acc k : Nat),
          (idxs.zipIdx k).foldl (fun a p => if f p.1 = true then a + 2 ^ p.2 else a) acc =
          acc + 2 ^ k * List.foldr (fun idx a => (if f idx = true then 1 else 0) + 2 * a) 0 idxs := by
        intro idxs; induction idxs with
        | nil => intro f acc k; simp
        | cons idx idxs ih =>
          intro f acc k
          simp only [List.zipIdx_cons, List.foldl_cons, List.foldr_cons, ih]
          cases f idx <;> simp [Nat.pow_succ] <;> ring
      have h := hfold [1, 2, 3, 4, 6, 7, 8] (MeasuredCodec5.bitRun FourScratchPrefix.V x10).testBit 0 0
      simpa [List.foldr_cons, List.foldr_nil] using h.symm
    rw [hval_eq]
    exact List.contains_iff_mem.mp hfin

theorem entryCut3_pin_loan_full {s : State} (F : EntryFrame s) (m : List Bool) :
    (∃ record, FrameAt F.x 1 record ∧ AgreeOutside (Δv 87) (run (cut eps 3) m s) record ∧
      CvX F.x 87 (run (cut eps 3) m s).basis record.basis ∧
      StairField2V3Win.WinT F.x record) ∧
    (∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (run (cut eps 3) m s).basis (fieldPlace q) = false) := by
  constructor
  · obtain ⟨Q, step⟩ := ern3 F.x (StairOpenWiring.entryPlans F.x)
    obtain ⟨n, hrel, root, tape, ⟨F0, fx⟩, hreach⟩ := step s s ⟨⟨F, rfl⟩, rfl⟩ m
    have pinned := g_first root F0 tape
    rw [fx] at pinned
    rw [ecut3]
    exact ⟨_, hreach.symm ▸ pinned.1, hrel.1, hrel.2, hreach.symm ▸ pinned.2.2⟩
  · exact cutLoan_helper (d := true)
      (fullEntryCut3Clean (entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760)) s ⟨F⟩ m

theorem entryCut3_pin_loan {s : State} (F : EntryFrame s) (m : List Bool) :
    (∃ record, FrameAt F.x 1 record ∧ AgreeOutside (Δv 87) (run (cut eps 3) m s) record) ∧
    (∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (run (cut eps 3) m s).basis (fieldPlace q) = false) := by
  obtain ⟨⟨rec, hf, ha, _, _⟩, hl⟩ := entryCut3_pin_loan_full F m
  exact ⟨⟨rec, hf, ha⟩, hl⟩

/-! ## Section 4: Division stock lockstep (`stockOddDivPrefix3`, `stockOddDivHead`) -/

def stockOddDivBeforeGroup : Program :=
  StairSchedule.fieldRename
    (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true ++
      FourScratchWindow.clearProgram)

def stockOddDivPrefix3 : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp) ++
    stockOddDivBeforeGroup

def stockOddDivRawTail : Program :=
  StairSchedule.forwardSegment cp 87 62 425 450 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 5 ++
  StairSchedule.forwardSegment cp 62 47 450 465 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 3 ++
  StairSchedule.forwardSegment cp 47 32 465 480 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 3 ++
  StairSchedule.forwardSegment cp 32 22 480 490 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 2 ++
  StairSchedule.forwardSegment cp 22 12 490 500 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 2 ++
  StairSchedule.forwardLast cp

def stockOddDivPre : Program :=
  renameProgram ExteriorPorts.fieldEquiv stockOddDivRawTail ++
    StairSchedule.fieldRename FourScratchWindow.unprefix

def stockOddDivBetween : Program :=
  StairSchedule.hostedX ++ StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX

def stockOddDivPost : Program :=
  renameProgram Rolling1588Lifetime.phaseHost Stair44Outer.reverseEnd

def stockOddDivHead : Program :=
  ((Stair44Kernel.divLead ++ stockOddDivBeforeGroup) ++
    renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84)) ++
  ((((stockOddDivPre ++ StairSchedule.paritySetup) ++ stockOddDivBetween) ++
    StairSchedule.paritySetup) ++ stockOddDivPost)

/-- Construct the matching standard-encoded division input state `tStd` from an odd-word input `tOdd`. -/
def stdOfOdd (tOdd : State) (Y : Fp) : State :=
  ⟨tOdd.phase, fun q =>
    if h : q ∈ fieldR then
      (centerWord (Y / 2)).testBit (q - 2072)
    else tOdd.basis q⟩

def stdOfOdd_spec (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s tOdd : State)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (hph : tOdd.phase = s.phase)
    (hsame : ∀ q, q ∉ fieldR → tOdd.basis q = s.basis q)
    (hval : regValue fieldR tOdd.basis = P1Life.oddWord (Y / 2)) :
    PProd (EntryFrame (stdOfOdd tOdd Y)) (AgreeOutsideR tOdd (stdOfOdd tOdd Y)) := by
  let tStd := stdOfOdd tOdd Y
  have hval_std : regValue fieldR tStd.basis = centerWord (Y / 2) := by
    have hlt : centerWord (Y / 2) < 2 ^ 256 := (BalancedField.centerWord_valid (Y / 2)).1
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · have hlen : fieldR.length = 256 := by simp [fieldR, wireBlock_length]
      have hbit := Arithmetic.regValue_bit fieldR i 0 tStd.basis (by omega)
      have hget : fieldR.getD i 0 = base (2056 + i) := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [fieldR, wireBlock]
      rw [hget] at hbit
      have hmem : base (2056 + i) ∈ fieldR :=
        List.mem_map.mpr ⟨2056 + i, by simp only [List.mem_range'_1]; omega, rfl⟩
      have hsub : base (2056 + i) - 2072 = i := by change (2056 + i) + 16 - 2072 = i; omega
      have htb : tStd.basis (base (2056 + i)) = (centerWord (Y / 2)).testBit i := by
        simp only [tStd, stdOfOdd, dif_pos hmem, hsub]
      rw [htb] at hbit
      rw [Nat.testBit_eq_decide_div_mod_eq, ← hbit]
      cases (centerWord (Y / 2)).testBit i <;> decide
    · have hlen : fieldR.length = 256 := by simp [fieldR, wireBlock_length]
      have hlt1 : regValue fieldR tStd.basis < 2 ^ 256 := hlen ▸ Arithmetic.regValue_lt fieldR tStd.basis
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hag : AgreeOutsideR tOdd tStd := ⟨rfl, fun q hq => by simp only [tStd, stdOfOdd, dif_neg hq]⟩
  refine ⟨⟨hn, hlo, ho, hf, x, Y, hx0, hx, s, hin, hg0, hs0, hph,
    fun q hq => (hag.2 q hq).symm.trans (hsame q hq), hval_std⟩, hag⟩

/-! ### Section 4b: Division cut-3 and full-head lockstep -/

private theorem openS_notFieldR : ∀ q ∈ wires (Stair44Kernel.openS true 409), q ∉ fieldR := by
  have hsub_fwd (n k : Nat) :
      wires (Rolling1588.Integer.forward true 1 n) ⊆
        wires (Rolling1588.Integer.forward true 1 (n + k)) := by
    induction k with
    | zero => exact Finset.Subset.refl _
    | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega, Rolling1588.Integer.forward_snoc, wires_append]
      exact ih.trans Finset.subset_union_left
  have h424_508 : wires (Rolling1588TickGap.forward true 1 424) ⊆ wires (Rolling1588.forward true 1 508) := by
    have h1 := Rolling1588TickGap.forward_support true 1 424 (by decide)
    rw [← Rolling1588.Integer.forward_eq_packets] at h1
    have h2 := h1.trans (hsub_fwd 424 84)
    rwa [Rolling1588.Integer.forward_eq_packets] at h2
  have hsub_stack : wires (Rolling1588.forward true 1 508) ⊆ wires (Rolling1588.stackForward true) := by
    simp only [Rolling1588.stackForward, wires_append]
    exact Finset.subset_union_left.trans Finset.subset_union_left
  intro q hq
  have hp : q ∈ skywalkPoolWires base := by
    apply List.mem_toFinset.mp
    apply ParityXExitInverse23Kernel.first_pool true
    simp only [Rolling1588.firstPhase, wires_append, Finset.mem_union]
    simp only [Stair44Kernel.openS, wires_append, Finset.mem_union] at hq
    rcases hq with h1 | h2
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (hsub_stack (h424_508 h2)))
  exact FrontierEntry1591Kernel.pool_away_numerator q hp

private theorem firstPack_notFieldR : ∀ q ∈ wires checkpointPrimitives.firstPack, q ∉ fieldR := by
  have h1 : StairWireCheck.allSites notFieldR (renameProgram StairV3Primitives.xRelabel (StairV3Primitives.orient 425)) = true := by decide +kernel
  have h2 : StairWireCheck.allSites notFieldR (renameProgram (OB5.sig 425) (Rolling1588.Integer.packFirst base true 425)) = true := by decide +kernel
  have h3 : StairWireCheck.allSites notFieldR StairPhysicalLayout.phaseBMove = true := by decide +kernel
  have h4 : (StairPhysicalPrimitives.rowSitesL 87).all (fun q => notFieldR (phaseRelabel q)) = true := by decide +kernel
  intro q hq
  simp only [checkpointPrimitives, StairV3Primitives.primitives, StairV3Primitives.firstPack,
    wires_append, Finset.mem_union] at hq
  rcases hq with ((ha | hb) | hc) | hd
  · exact (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h1 q ha)
  · exact (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h2 q hb)
  · exact (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h3 q hc)
  · rw [renameProgram_support] at hd
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hd
    exact (notFieldR_iff _).mp (List.all_eq_true.mp h4 w (StairPhysicalPrimitives.pack_rows 87 (by decide) w hw))

theorem firstPhase_cp_notFieldR :
    ∀ q ∈ wires (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)), q ∉ fieldR := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rw [WindowStockHead.shapeD, wires_append, Finset.mem_union] at hw
  have hnw : w ∉ fieldR := hw.elim (openS_notFieldR w) (firstPack_notFieldR w)
  intro hmem
  have hfix := phaseHost_fix_fieldR (Rolling1588Lifetime.phaseHost w) hmem
  exact hnw (Rolling1588Lifetime.phaseHost.injective hfix ▸ hmem)

theorem divLead_eq_firstPhase_odd {tOdd tStd : State} (F : EntryFrame tStd)
    (hag : AgreeOutsideR tOdd tStd) (m : List Bool) :
    run Stair44Kernel.divLead m tOdd =
      run (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)) m tOdd := by
  have hin_std := StairField13V3Clean.entryInput F
  have hin_odd : SkywalkArithmeticInput base F.x (regValue fieldR tOdd.basis) tOdd.basis :=
    FrontierEntry1591Kernel.paired_input F.x (centerWord (F.Y / 2)) tStd tOdd hin_std hag.2
  have hpull_odd : pullState Rolling1588Lifetime.phaseHost tOdd = tOdd := by
    have hpull_std := StairField13V3Clean.pull_phaseHost_entry F
    apply State.extensionality
    · rfl
    · funext q
      by_cases hr : q ∈ fieldR
      · change tOdd.basis (Rolling1588Lifetime.phaseHost q) = tOdd.basis q
        rw [phaseHost_fix_fieldR q hr]
      · have hnr : Rolling1588Lifetime.phaseHost q ∉ fieldR := by
          intro hmem
          have hf := phaseHost_fix_fieldR (Rolling1588Lifetime.phaseHost q) hmem
          exact hr (Rolling1588Lifetime.phaseHost.injective hf ▸ hmem)
        change tOdd.basis (Rolling1588Lifetime.phaseHost q) = tOdd.basis q
        rw [hag.2 _ hnr, hag.2 _ hr]
        exact congrFun (congrArg State.basis hpull_std) q
  apply MappedCompressed.pullState_perm_injective Rolling1588Lifetime.phaseHost
  rw [run_rename _ Rolling1588Lifetime.phaseHost.injective,
      run_rename _ Rolling1588Lifetime.phaseHost.injective,
      hpull_odd, WindowStockHead.shapeD]
  exact Stair44Kernel.with_tail true 409 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup tOdd hin_odd _ m

theorem fpSup_not_E : ∀ q, StairWireCheck.fpSup q = true → q ∉ E := by
  have h : E.all (fun q => !StairWireCheck.fpSup q) = true := by decide +kernel
  intro q hq hmem
  have := List.all_eq_true.mp h q hmem
  simp [hq] at this

theorem ryWires_not_E : ∀ q ∈ ryWires, q ∉ E := by
  have h : E.all notRY = true := by decide +kernel
  intro q hq hmem
  exact (notRY_iff q).mp (List.all_eq_true.mp h q hmem) hq

theorem fpSup_not_delta87 : ∀ q, StairWireCheck.fpSup q = true → fieldMap q ∉ Δv 87 := by
  have h : (futurePayload 87).all (fun r => !StairWireCheck.fpSup (fmInv (fieldPlace r))) = true := by
    decide +kernel
  intro q hq hmem
  simp only [Δv, List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨r, hr, heq⟩ := hmem
  have hfm : fmInv (fieldPlace r) = q := by rw [heq, fmInv_fieldMap]
  have h1 := List.all_eq_true.mp h r hr
  rw [hfm, hq] at h1; exact Bool.noConfusion h1

theorem ryWires_not_delta87 : ∀ q ∈ ryWires, fieldMap q ∉ Δv 87 := by
  have h : (futurePayload 87).all (fun r => notRY (fmInv (fieldPlace r))) = true := by
    decide +kernel
  intro q hq hmem
  simp only [Δv, List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨r, hr, heq⟩ := hmem
  have hfm : fmInv (fieldPlace r) = q := by rw [heq, fmInv_fieldMap]
  exact (notRY_iff q).mp (hfm ▸ List.all_eq_true.mp h r hr) hq

private theorem entryClean_v3_inst : StairField13V3Fresh.EntryClean :=
  entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760

theorem exitClean_v3_inst (k : Nat) : StairField13V3Fresh.ExitClean k :=
  exitClean_of_planR StairOpenWiring.exitPlans StairOpenWiring.half760 k

private theorem firstBefore_eps :
    CutClean EntryPre (cut eps 1) ((StairSchedule.exclusiveRoles ++ hostPlan.firstPacket true).map fieldMap) :=
  entryClean_v3_inst.firstBefore

private theorem firstRolesAfter_eps :
    CutClean EntryPre (cut eps 2) (StairSchedule.exclusiveRoles.map fieldMap) :=
  entryClean_v3_inst.firstRolesAfter

private theorem groupsBefore_eps (j def_ start len : Nat)
    (h : (j, def_, start, len) ∈ [(3, 0, 1, 84), (5, 13, 85, 5), (7, 22, 90, 3), (9, 30, 93, 3),
        (11, 36, 96, 2), (13, 41, 98, 2), (17, 43, 100, 2)]) :
    CutClean EntryPre (cut eps j)
      ((StairSchedule.exclusiveRoles.drop def_ ++ hostPlan.group true def_ start len).map lowMap) :=
  entryClean_v3_inst.groupsBefore (j, def_, start, len) h

private theorem groupsRolesAfter_eps (j def_ start len : Nat)
    (h : (j, def_, start, len) ∈ [(3, 0, 1, 84), (5, 13, 85, 5), (7, 22, 90, 3), (9, 30, 93, 3),
        (11, 36, 96, 2), (13, 41, 98, 2), (17, 43, 100, 2)]) :
    CutClean EntryPre (cut eps (j + 1))
      ((StairSchedule.exclusiveRoles.drop def_).map lowMap) :=
  entryClean_v3_inst.groupsRolesAfter (j, def_, start, len) h

private theorem div_piece1_rel {tOdd tStd : State} (F : EntryFrame tStd)
    (hag0 : AgreeOutsideR tOdd tStd) (hR0 : regValue fieldR tOdd.basis = P1Life.oddWord (F.Y / 2))
    (m0 m1 : List Bool) :
    OddRel P1Life.oddWord P1Life.oddWord
      (run (StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true)) m1
        (run (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)) m0 tOdd))
      (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket true)) m1
        (run (cut eps 1) m0 tStd)) := by
  have he1 : cut eps 1 = renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp) := by
    rw [cut_succ eps 0 (eL 0 (by decide)), cut_zero, e0_L, List.nil_append]
  have hag1_raw : AgreeOutsideR
      (run (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)) m0 tOdd)
      (run (cut eps 1) m0 tStd) := by
    rw [he1]
    exact agreeOutsideR_disjoint (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp))
      firstPhase_cp_notFieldR hag0 m0
  have hR1_raw : regValue fieldR
      (run (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)) m0 tOdd).basis =
      P1Life.oddWord (F.Y / 2) :=
    (regValue_run_disjoint_R _ firstPhase_cp_notFieldR m0 tOdd).trans hR0
  have hb1_R_raw : regValue fieldR (run (cut eps 1) m0 tStd).basis = centerWord (F.Y / 2) := by
    rw [he1]
    exact (regValue_run_disjoint_R _ firstPhase_cp_notFieldR m0 tStd).trans F.numerator
  have hcleanIn_raw : ∀ q ∈ (StairSchedule.exclusiveRoles ++ hostPlan.firstPacket true).map fieldMap,
      (run (cut eps 1) m0 tStd).basis q = false :=
    firstBefore_eps tStd ⟨F⟩ m0
  have hcleanOut_raw : ∀ q ∈ StairSchedule.exclusiveRoles.map fieldMap,
      (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket true)) m1 (run (cut eps 1) m0 tStd)).basis q = false :=
    cleanCut_after firstRolesAfter_eps
      (by rw [cut_succ eps 1 (eL 1 (by decide)), e1_L]) tStd ⟨F⟩ m0 m1
  -- Abstract `a1` and `b1` as opaque `State` variables so the kernel never unfolds `run`!
  obtain ⟨a1, ha1⟩ : ∃ s, run (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)) m0 tOdd = s := ⟨_, rfl⟩
  obtain ⟨b1, hb1⟩ : ∃ s, run (cut eps 1) m0 tStd = s := ⟨_, rfl⟩
  rw [ha1] at hag1_raw hR1_raw ⊢
  rw [hb1] at hag1_raw hb1_R_raw hcleanIn_raw hcleanOut_raw ⊢
  -- Relate `b1` to `run R0 mpR root` via `ern1`
  obtain ⟨Q1, hstep1⟩ := ern1 F.x (StairOpenWiring.entryPlans F.x)
  obtain ⟨n0, hrel1, root, mpR, ⟨Froot, fx⟩, hreach1⟩ := hstep1 tStd tStd ⟨⟨F, rfl⟩, rfl⟩ m0
  obtain ⟨r0, hr0⟩ : ∃ s, run R0 mpR root = s := ⟨_, rfl⟩
  have hrel1_b1 : AgreeOutside (Δv 87) b1 r0 := by
    have h1 := hrel1.1
    rw [← ecut1, hb1, hreach1, hr0] at h1
    exact h1
  have actual_r := FrontierEntry1591Kernel.paired_input Froot.x Froot.Y.val Froot.source root Froot.input Froot.outsideNumerator
  let mp := mpR.take (measurementCount (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true)))
  let mS := mpR.drop (measurementCount (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true)))
  obtain ⟨orig_r, facts_r, legal_r, frames_r⟩ := Rolling1588Lifetime.entry_first_prepared
    Froot.sharedNodup Froot.historyAbove Froot.selectorsAway Froot.x Froot.Y Froot.x_pos Froot.x_lt
    Froot.source root mp Froot.input Froot.phase Froot.outsideNumerator Froot.numerator
  have ctx_r := Rolling1588Lifetime.prepared_context Froot.sharedNodup Froot.selectorsAway
    Froot.transcript Froot.x Froot.Y Froot.source orig_r facts_r legal_r Froot.selectorG_zero Froot.selectorS_zero
  have frameA_r := frames_r true
  have bits := Rolling1588Lifetime.first_clean true Froot.sharedNodup Froot.historyAbove Froot.x _ Froot.x_pos Froot.x_lt root mp actual_r
  have work := Rolling1588Lifetime.first_work_zero true Froot.sharedNodup Froot.x _ root mp actual_r
  have parity := Rolling1588Lifetime.first_parity true Froot.sharedNodup Froot.historyAbove Froot.x _ Froot.x_pos Froot.x_lt root mp actual_r
  rw [lf_eq] at frameA_r bits work parity
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase true) mp root = v := ⟨_, rfl⟩
  rw [hv] at frameA_r bits work parity
  have hR0_eq : r0 = run (StairSchedule.paritySetup ++ StairSchedule.hostedX) mS v := by
    rw [← hr0, R0_eq, run_append, first_phase_hosted true Froot.sharedNodup Froot.historyAbove Froot.x _ Froot.x_pos Froot.x_lt root mp actual_r, hv]
  have code := Rolling1588Frame.field_special_at orig_r.basis (Froot.Y / 2) 0 v 511 (by simp) frameA_r
  have in511 : v.basis (base 511) = true :=
    (by rw [sig511_511] at code; exact code : v.basis (base 511) = orig_r.basis (base 511)).trans
      (trace_last Froot.x Froot.x_pos Froot.x_lt orig_r.basis facts_r.trace)
  have in1542 : v.basis (base 1542) = false := bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := field_flags orig_r.basis ctx_r (Froot.Y / 2) 0 v frameA_r
  have hag_fv := hosted_agree_force v flags.1 in511 flags.2 in1542 work parity mS
  let origin' := writeBit orig_r.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set orig_r.basis ctx_r true
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (Froot.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]; exact facts_r.trace
  have input' := Rolling1588.frame_control_set orig_r.basis (Froot.Y / 2) 0 v true frameA_r
  have en' : origin' (base 2400) = true := by simp [origin', writeBit]
  have hpb_fp : ∀ q, StairWireCheck.fpSup q = true → (pullState fieldMap b1).basis q = (force v).basis q := by
    intro q hq
    have h1 := hrel1_b1.2 (fieldMap q) (fpSup_not_delta87 q hq)
    have h2 : (pullState fieldMap r0).basis q = (force v).basis q := by
      rw [hR0_eq, pullState_fieldMap_basis]; exact hag_fv q (fpSup_not_E q hq)
    exact h1.trans h2
  have hpb_ry : ∀ q ∈ ryWires, (pullState fieldMap b1).basis q = (force v).basis q := by
    intro q hq
    have h1 := hrel1_b1.2 (fieldMap q) (ryWires_not_delta87 q hq)
    have h2 : (pullState fieldMap r0).basis q = (force v).basis q := by
      rw [hR0_eq, pullState_fieldMap_basis]; exact hag_fv q (ryWires_not_E q hq)
    exact h1.trans h2
  have hv_vals := encodedFieldFrame_values true origin' (Froot.Y / 2) 0 (force v) input'
  have hYeq : Froot.Y / 2 = F.Y / 2 := by
    have hb1_R_fv : regValue fieldR b1.basis = centerWord (Froot.Y / 2) := by
      rw [← pullState_fieldMap_regValue_R]
      exact (regValue_congr _ _ _ (fun q hq => hpb_ry q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hv_vals.1
    exact centerWord_injective (hb1_R_fv.symm.trans hb1_R_raw)
  have ha1_Y0 : regValue fieldY a1.basis = 0 := by
    have hb1_Y0 : regValue fieldY b1.basis = 0 := by
      rw [← pullState_fieldMap_regValue_Y]
      have hvy := hv_vals.2
      rw [HalfField.centerWord_zero] at hvy
      exact (regValue_congr _ _ _ (fun q hq => hpb_ry q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvy
    exact (regValue_congr _ _ _ (fun q hq => hag1_raw.2 q (fun hr => fieldR_disjoint_fieldY q hr hq))).trans hb1_Y0
  have hfp := firstPacketOdd_step true true origin' ctx' en' Froot.x Froot.x_lt trace' (Froot.Y / 2) 0
    ⟨fun h => absurd h (by decide), fun _ => rfl⟩ a1 b1 (force v) m1
    (agreeRY_of_agreeOutsideR hag1_raw) input' hpb_fp hpb_ry (by rw [hYeq]; exact hR1_raw)
    (by simp [JointOdd1588.firstYIn, HalfField.centerWord_zero, ha1_Y0]) hcleanIn_raw hcleanOut_raw
  exact oddRel_of_agreeRY_values _ _ hfp.1 hfp.2.2.2.1 hfp.2.2.2.2 hfp.2.1 hfp.2.2.1

/-- Cut-3 deliverable for Division: relates `stockOddDivPrefix3` (pieces 0–2) against
`ExteriorEntryCut.stockPrefix` (cut 3 of `entryPieces`) with `OddRel`, `OCut 1`, and `Loan`. -/
theorem stockOddDiv_cut3 {tOdd tStd : State} (F : EntryFrame tStd)
    (hag0 : AgreeOutsideR tOdd tStd) (hR0 : regValue fieldR tOdd.basis = P1Life.oddWord (F.Y / 2))
    (m : List Bool) :
    let a3 := run stockOddDivPrefix3 m tOdd
    (∃ n, OddRel P1Life.oddWord P1Life.oddWord a3 (run (cut eps 3) n tStd)) ∧
    (∃ origin, FrontierReplay1591.Context origin ∧ origin (base 2400) = true ∧
      TraceOK F.x origin ∧ WindowFieldView.OCut 1 origin (pullIn a3) ∧
      StairPacket.WindowFieldView.TagReady (pullIn a3)) := by
  intro a3
  let m0 := m.take (measurementCount (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)))
  let mRest := m.drop (measurementCount (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)))
  let m1 := mRest.take (measurementCount (StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true)))
  let m2 := mRest.drop (measurementCount (StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true)))
  have ha3_eq : a3 = run (StairSchedule.fieldRename FourScratchWindow.clearProgram) m2
      (run (StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true)) m1
        (run (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)) m0 tOdd)) := by
    simp only [a3, stockOddDivPrefix3, stockOddDivBeforeGroup, fieldRename_append, run_append, m0, mRest, m1, m2]
  let n2 := WindowFieldJourney.joinTapes (cut eps 1) m0 m1
  let n3 := WindowFieldJourney.joinTapes (cut eps 2) n2 m2
  have hb3_eq : run (cut eps 3) n3 tStd =
      run (StairSchedule.fieldRename FourScratchWindow.clearProgram) m2
        (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket true)) m1
          (run (cut eps 1) m0 tStd)) := by
    have hc2 : cut eps 2 = cut eps 1 ++ StairSchedule.fieldRename (Rolling1588.placedFirstPacket true) := by
      rw [cut_succ eps 1 (eL 1 (by decide)), e1_L]
    have hc3 : cut eps 3 = cut eps 2 ++ StairSchedule.fieldRename FourScratchWindow.clearProgram := by
      rw [cut_succ eps 2 (eL 2 (by decide)), e2_L]
    rw [hc3, WindowFieldJourney.joined, hc2, WindowFieldJourney.joined]
  have hrel2 := div_piece1_rel F hag0 hR0 m0 m1
  have hrel3 : OddRel P1Life.oddWord P1Life.oddWord a3 (run (cut eps 3) n3 tStd) := by
    rw [ha3_eq, hb3_eq]
    exact oddRel_disjoint _ (disjoint_ryWires_fieldRename clearProgram_notRY) hrel2 m2
  obtain ⟨⟨record, hframe, hagree, hcv, hwin⟩, hloan⟩ := entryCut3_pin_loan_full F n3
  obtain ⟨origin, ctx, en, tr, ocut⟩ :=
    odd_cut_ocut 1 (by decide) (by decide) F.x a3 (run (cut eps 3) n3 tStd) record hrel3 hframe hagree hloan
  exact ⟨⟨n3, hrel3⟩, origin, ctx, en, tr, ocut,
    odd_cut_tagReady F.x F.x_pos F.x_lt a3 (run (cut eps 3) n3 tStd) record hrel3 hagree hcv hwin⟩

private theorem groupsPayload_add_true (origin : BasisState) (j a b : Nat) (V : Fp × Fp) :
    Replay5.groupsPayload true origin (j + a) b (Replay5.groupsPayload true origin j a V) =
      Replay5.groupsPayload true origin j (a + b) V := by
  induction a generalizing j V with
  | zero => simp [Replay5.groupsPayload, PacketSequence.payload]
  | succ a ih =>
    simp only [Replay5.groupsPayload, PacketSequence.payload, if_true] at ih ⊢
    have := ih (j + 1) (CompressedFieldSupport.directionalPayload false
      (mixedTranscriptControls origin (base 2400) (Replay5.letters j)) V)
    rw [show j + (a + 1) = j + 1 + a by omega, show (a + 1) + b = (a + b) + 1 by omega]
    simpa only [PacketSequence.payload, if_true] using this

private def CutPay (origin : BasisState) (V0 : Fp × Fp) (c : Nat) (t : State) : Prop :=
  ∃ s : State,
    Rolling1588.CutFrame c origin (Replay5.groupsPayload true origin 1 (c - 1) V0).1
      (Replay5.groupsPayload true origin 1 (c - 1) V0).2 (pullState (OB5.sig 511) s) ∧
    ∀ q, Off q → (pullIn t).basis q = s.basis q

private theorem cutPay_step (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (en : origin (base 2400) = true) (V0 : Fp × Fp) (j n j' : Nat)
    (hj : 1 ≤ j) (hb : j + n ≤ 102) (hj' : j + n = j') (t : State) (h : CutPay origin V0 j t) (m : List Bool) :
    CutPay origin V0 j' (run (grp j n) m t) := by
  subst hj'
  obtain ⟨s, hcut, hag⟩ := h
  have tri := Rolling1588.groups_cut_frame true j n hj hb origin ctx en _ _
    (pullState (OB5.sig 511) s) m hcut
  have hpay : Replay5.groupsPayload true origin j n (Replay5.groupsPayload true origin 1 (j - 1) V0) =
      Replay5.groupsPayload true origin 1 (j + n - 1) V0 := by
    have h1 : 1 + (j - 1) = j := by omega
    have h2 : (j - 1) + n = j + n - 1 := by omega
    rw [← h2, ← groupsPayload_add_true origin 1 (j - 1) n V0, h1]
  refine ⟨run (renameProgram (OB5.sig 511) (Rolling1588.groups true j n)) m s, ?_, ?_⟩
  · rw [StairField2V3Packet.sig_conj,
        StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide)), ← hpay]
    exact tri.2
  · intro q hq
    unfold grp; rw [pullIn_liftF]
    exact run_agree_offP _ (groups_off j n hj hb) _ _ m hag q hq

/-- Explicit frame at division cut 18 (`run (R6 ++ grp 100 2) m tStd`) with exact `endPayload.1 = Y`! -/
private theorem div_cut18_frame_inner {tStd : State} (F : EntryFrame tStd) (mp mS mF mTail : List Bool) :
    ∃ (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
      (en : origin (base 2400) = true) (X Y : Fp) (s102 : State),
      (Replay5.endPayload true origin (X, Y)).1 = Y ∧
      Rolling1588Frame.EncodedFieldFrame false origin X Y s102 ∧
      (∀ q, Off q → (pullIn (run ((((((grp 1 84 ++ grp 85 5) ++ grp 90 3) ++ grp 93 3) ++ grp 96 2) ++ grp 98 2) ++ grp 100 2) mTail
        (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket true ++ FourScratchWindow.clearProgram)) mF
          (run (StairSchedule.paritySetup ++ StairSchedule.hostedX) mS
            (run (Rolling1588.firstPhase true) mp tStd))))).basis q = s102.basis q) := by
  have actual := FrontierEntry1591Kernel.paired_input F.x F.Y.val F.source tStd F.input F.outsideNumerator
  obtain ⟨orig, facts, legal, frames⟩ := Rolling1588Lifetime.entry_first_prepared
    F.sharedNodup F.historyAbove F.selectorsAway F.x F.Y F.x_pos F.x_lt F.source tStd mp
    F.input F.phase F.outsideNumerator F.numerator
  have ctx := Rolling1588Lifetime.prepared_context F.sharedNodup F.selectorsAway
    F.transcript F.x F.Y F.source orig facts legal F.selectorG_zero F.selectorS_zero
  have bits := Rolling1588Lifetime.first_clean true F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt tStd mp actual
  have work := Rolling1588Lifetime.first_work_zero true F.sharedNodup F.x _ tStd mp actual
  have parity := Rolling1588Lifetime.first_parity true F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt tStd mp actual
  have frameA := frames true
  rw [lf_eq] at frameA bits work parity
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase true) mp tStd = v := ⟨_, rfl⟩
  rw [hv] at frameA bits work parity ⊢
  have code := Rolling1588Frame.field_special_at orig.basis (F.Y / 2) 0 v 511 (by simp) frameA
  have in511 : v.basis (base 511) = true :=
    (by rw [sig511_511] at code; exact code : v.basis (base 511) = orig.basis (base 511)).trans
      (trace_last F.x F.x_pos F.x_lt orig.basis facts.trace)
  have in1542 : v.basis (base 1542) = false := bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := field_flags orig.basis ctx (F.Y / 2) 0 v frameA
  let origin' := writeBit orig.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set orig.basis ctx true
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (F.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]; exact facts.trace
  have input' := Rolling1588.frame_control_set orig.basis (F.Y / 2) 0 v true frameA
  have en' : origin' (base 2400) = true := by simp [origin', writeBit]
  have first := Rolling1588.placedFirstPacket_frame true true origin' ctx' en' F.x F.x_lt
    trace' (F.Y / 2) 0 ⟨fun h => absurd h (by decide), fun _ => rfl⟩ (force v)
    (mF.take (measurementCount (Rolling1588.placedFirstPacket true))) input'
  have agreeY := run_agree_off _ firstPacket_avoidE _ (force v)
    (mF.take (measurementCount (Rolling1588.placedFirstPacket true)))
    (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity mS)
  obtain ⟨s1, hs1⟩ : ∃ s1 : State,
      run (Rolling1588.placedFirstPacket true) (mF.take (measurementCount (Rolling1588.placedFirstPacket true))) (force v) = s1 := ⟨_, rfl⟩
  rw [hs1] at first agreeY
  have codes := Rolling1588.field_prefix_codes origin' ctx' _ _ s1 first.2 F.x F.x_pos F.x_lt trace'
  have clean := FourScratchWindow.field_clean origin' ctx' _ _ s1 first.2 codes.1 codes.2.1
  have z768 := Rolling1588.field_768_zero origin' ctx' _ _ s1 first.2
  have hag_s1 : ∀ q, Off q → (pullIn (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket true ++
      FourScratchWindow.clearProgram)) mF (run (StairSchedule.paritySetup ++ StairSchedule.hostedX) mS v))).basis q = s1.basis q := by
    intro q hq
    rw [field_pullIn, run_append (Rolling1588.placedFirstPacket true)]
    exact window_agree _ s1 _ agreeY clean codes.2.2 z768 q hq.1 hq.2
  obtain ⟨V0, hV0⟩ : ∃ V0 : Fp × Fp, Replay5.firstPayload true origin' (F.Y / 2, 0) = V0 := ⟨_, rfl⟩
  have hfirst_v0 : Rolling1588Frame.EncodedFieldFrame true origin' V0.1 V0.2 s1 := by
    rw [← hV0]; exact first.2
  have hcp1 : CutPay origin' V0 1 (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket true ++
      FourScratchWindow.clearProgram)) mF (run (StairSchedule.paritySetup ++ StairSchedule.hostedX) mS v)) :=
    ⟨s1, (Rolling1588.cutFrame_one origin' V0.1 V0.2 (pullState (OB5.sig 511) s1)).mpr hfirst_v0, hag_s1⟩
  have hcp_chain (u1 : State) (m1 m2 m3 m4 m5 m6 m7 : List Bool) (h1 : CutPay origin' V0 1 u1) :
      CutPay origin' V0 102
        (run (grp 100 2) m7 (run (grp 98 2) m6 (run (grp 96 2) m5 (run (grp 93 3) m4
          (run (grp 90 3) m3 (run (grp 85 5) m2 (run (grp 1 84) m1 u1))))))) := by
    have h2 := cutPay_step origin' ctx' en' V0 1 84 85 (by decide) (by decide) rfl u1 h1 m1
    have h3 := cutPay_step origin' ctx' en' V0 85 5 90 (by decide) (by decide) rfl _ h2 m2
    have h4 := cutPay_step origin' ctx' en' V0 90 3 93 (by decide) (by decide) rfl _ h3 m3
    have h5 := cutPay_step origin' ctx' en' V0 93 3 96 (by decide) (by decide) rfl _ h4 m4
    have h6 := cutPay_step origin' ctx' en' V0 96 2 98 (by decide) (by decide) rfl _ h5 m5
    have h7 := cutPay_step origin' ctx' en' V0 98 2 100 (by decide) (by decide) rfl _ h6 m6
    exact cutPay_step origin' ctx' en' V0 100 2 102 (by decide) (by decide) rfl _ h7 m7
  rw [run_append, run_append, run_append, run_append, run_append, run_append]
  obtain ⟨s8, hc8, ha8⟩ := hcp_chain _ _ _ _ _ _ _ _ hcp1
  have hpay := Replay5.forward_payload origin' F.x (F.Y / 2) F.x_pos F.x_lt trace'
  rw [hV0] at hpay
  obtain ⟨V, hV⟩ : ∃ V : Fp × Fp, Replay5.groupsPayload true origin' 1 101 V0 = V := ⟨_, rfl⟩
  rw [show (102 - 1 : Nat) = 101 from rfl, hV] at hc8
  rw [hV] at hpay
  have hend : (Replay5.endPayload true origin' V).1 = V.2 := by
    have h1 := congrArg Prod.fst hpay
    have h2 := congrArg Prod.snd hpay
    have hsnd : (Replay5.endPayload true origin' V).2 = V.2 := by simp [Replay5.endPayload]
    exact h1.trans (h2.symm.trans hsnd)
  exact ⟨origin', ctx', en', V.1, V.2, s8, hend,
    (Rolling1588.cutFrame_end origin' V.1 V.2 (pullState (OB5.sig 511) s8)).mp hc8, ha8⟩

private theorem div_cut18_frame {tStd : State} (F : EntryFrame tStd) (m : List Bool) :
    ∃ (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
      (en : origin (base 2400) = true) (X Y : Fp) (s102 : State),
      (Replay5.endPayload true origin (X, Y)).1 = Y ∧
      Rolling1588Frame.EncodedFieldFrame false origin X Y s102 ∧
      (∀ q, Off q → (pullIn (run (R6 ++ grp 100 2) m tStd)).basis q = s102.basis q) := by
  have hshape : R6 ++ grp 100 2 =
      ((renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
        (StairSchedule.paritySetup ++ StairSchedule.hostedX)) ++
        StairSchedule.fieldRename (Rolling1588.placedFirstPacket true ++ FourScratchWindow.clearProgram)) ++
      ((((((grp 1 84 ++ grp 85 5) ++ grp 90 3) ++ grp 93 3) ++ grp 96 2) ++ grp 98 2) ++ grp 100 2) := by
    simp only [R6, R5, R4, R3, R2, R1, R0_shape, List.append_assoc]
  rw [hshape,
      run_append ((renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
        (StairSchedule.paritySetup ++ StairSchedule.hostedX)) ++
        StairSchedule.fieldRename (Rolling1588.placedFirstPacket true ++ FourScratchWindow.clearProgram)),
      run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
        (StairSchedule.paritySetup ++ StairSchedule.hostedX)),
      run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true)),
      first_phase_hosted true F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt tStd _
        (FrontierEntry1591Kernel.paired_input F.x F.Y.val F.source tStd F.input F.outsideNumerator)]
  exact div_cut18_frame_inner F _ _ _ _

/-! ## Packet-cut rows on the odd division head -/

/-- The unlifted run of `P` on `pullIn s` reads a wire `q` where the lifted run reads `fieldPlace q`. -/
theorem run_pullIn_basis (P : Program) (m : List Bool) (s : State) (q : Wire) :
    (run P m (pullIn s)).basis q = (run (liftF P) m s).basis (fieldPlace q) := by
  rw [liftF_run]
  show _ = (run P m (pullIn s)).basis (fieldPlaceInv (fieldPlace q))
  rw [inv_fieldPlace]

/-- States that agree outside `ryWires` still agree, after a program whose lift avoids `ryWires`, on every wire
that lifts outside `ryWires`. -/
theorem pullIn_agree {a b : State} (h : AgreeRY a b) (P : Program)
    (hP : ∀ q ∈ wires (liftF P), q ∉ ryWires) (m : List Bool) (q : Wire) (hq : fieldPlace q ∉ ryWires) :
    (run P m (pullIn a)).basis q = (run P m (pullIn b)).basis q := by
  rw [run_pullIn_basis, run_pullIn_basis]
  exact (agreeRY_disjoint (liftF P) hP h m).2 _ hq

theorem oddRowCut1 {tStd : State} (F : EntryFrame tStd) (u : List Bool) (a : State)
    (hag : AgreeRY a (run (cut eps 4) u tStd)) (m : List Bool) :
    ∃ m', run (liftF (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4)) m a =
      run (liftF (StairSchedule.forwardSegment cp 87 62 425 450 ++
        OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 (4 + 1))) m' a := by
  have hH : run ((((entryPieces checkpointPrimitives hostPlan).take 4).map Piece.H).flatten) u tStd =
      run (cut eps 4) u tStd := by
    unfold cut
    exact Stair44HostedCut.entry 4 tStd ⟨F⟩ u
  have hseg : StairSchedule.forwardSegment cp 87 62 425 450 = (StairConcreteAssembly.checkpointPrimitives.unpack 87 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 425 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (425 + 1) (5 * 85 + 5 - (425 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85 + 5)) ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85))) PackCutTrip.E138 ++
        renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85))) Rolling1588.ep ++
        (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1)))
          (5 * 85 + 5 + 1) (450 - (5 * 85 + 5) - 1) ++ checkpointPrimitives.orient 450 ++
          renameProgram (OB5.sig 450) (Rolling1588.Integer.packFirst base true 450) ++ checkpointPrimitives.pack 62)) := by
    rw [PackCutShape.forwardSegment_row 87 62 425 450 85 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.append_assoc]
  have hP : ∀ q ∈ wires (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 87 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 425 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (425 + 1) (5 * 85 + 5 - (425 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85 + 5))), q ∉ ryWires := by
    have hsub : (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 87 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 425 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (425 + 1) (5 * 85 + 5 - (425 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85 + 5))).Sublist (liftF (StairSchedule.forwardSegment cp 87 62 425 450)) := by
      rw [hseg]
      exact PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (List.sublist_append_left _ _)))
    intro q hq
    exact disjoint_ryWires_liftF forward425_notRY q (PackCutSub.wires_sub hsub q hq)
  have hq : ∀ jj : Fin 10, fieldPlace ((History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (425 + 1))) (5 * 85)) jj) ∉ ryWires := by
    intro jj
    exact (notRY_iff _).mp (by revert jj; decide)
  obtain ⟨m', h⟩ := PackCutEntryChain.rowCutOdd1 F.x (StairOpenWiring.entryPlans F.x)
    (StairLoanField7RR.entryReachTransportR_best StairOpenWiring.half760 F.x)
    StairLoanField7Transport.entryGroupSub_best
    (StairField13V3.entrySlotsClean_of _ _ _ (StairField13V3.entrySlots_of_v3 (StairField13V3.entrySlotsV3_of_parts
      (StairField13V3Fresh.entryParts_of_clean
        (StairField13V3Clean.entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760))))) tStd ⟨F, rfl⟩ u a
    (fun t1 jj => by rw [hH]; exact pullIn_agree hag _ hP t1 _ (hq jj)) m
  exact ⟨m', by rw [liftF_run, liftF_run, h]⟩

theorem oddRowCut2 {tStd : State} (F : EntryFrame tStd) (u : List Bool) (a : State)
    (hag : AgreeRY a (run (cut eps 6) u tStd)) (m : List Bool) :
    ∃ m', run (liftF (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2)) m a =
      run (liftF (StairSchedule.forwardSegment cp 62 47 450 465 ++
        OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 (2 + 1))) m' a := by
  have hH : run ((((entryPieces checkpointPrimitives hostPlan).take 6).map Piece.H).flatten) u tStd =
      run (cut eps 6) u tStd := by
    unfold cut
    exact Stair44HostedCut.entry 6 tStd ⟨F⟩ u
  have hseg : StairSchedule.forwardSegment cp 62 47 450 465 = (StairConcreteAssembly.checkpointPrimitives.unpack 62 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 450 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (450 + 1) (5 * 90 + 5 - (450 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90 + 5)) ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90))) PackCutTrip.E138 ++
        renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90))) Rolling1588.ep ++
        (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1)))
          (5 * 90 + 5 + 1) (465 - (5 * 90 + 5) - 1) ++ checkpointPrimitives.orient 465 ++
          renameProgram (OB5.sig 465) (Rolling1588.Integer.packFirst base true 465) ++ checkpointPrimitives.pack 47)) := by
    rw [PackCutShape.forwardSegment_row 62 47 450 465 90 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.append_assoc]
  have hP : ∀ q ∈ wires (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 62 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 450 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (450 + 1) (5 * 90 + 5 - (450 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90 + 5))), q ∉ ryWires := by
    have hsub : (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 62 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 450 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (450 + 1) (5 * 90 + 5 - (450 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90 + 5))).Sublist (liftF (StairSchedule.forwardSegment cp 62 47 450 465)) := by
      rw [hseg]
      exact PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (List.sublist_append_left _ _)))
    intro q hq
    exact disjoint_ryWires_liftF forward450_notRY q (PackCutSub.wires_sub hsub q hq)
  have hq : ∀ jj : Fin 10, fieldPlace ((History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (450 + 1))) (5 * 90)) jj) ∉ ryWires := by
    intro jj
    exact (notRY_iff _).mp (by revert jj; decide)
  obtain ⟨m', h⟩ := PackCutEntryChain.rowCutOdd2 F.x (StairOpenWiring.entryPlans F.x)
    (StairLoanField7RR.entryReachTransportR_best StairOpenWiring.half760 F.x)
    StairLoanField7Transport.entryGroupSub_best
    (StairField13V3.entrySlotsClean_of _ _ _ (StairField13V3.entrySlots_of_v3 (StairField13V3.entrySlotsV3_of_parts
      (StairField13V3Fresh.entryParts_of_clean
        (StairField13V3Clean.entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760))))) tStd ⟨F, rfl⟩ u a
    (fun t1 jj => by rw [hH]; exact pullIn_agree hag _ hP t1 _ (hq jj)) m
  exact ⟨m', by rw [liftF_run, liftF_run, h]⟩

theorem oddRowCut3 {tStd : State} (F : EntryFrame tStd) (u : List Bool) (a : State)
    (hag : AgreeRY a (run (cut eps 8) u tStd)) (m : List Bool) :
    ∃ m', run (liftF (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2)) m a =
      run (liftF (StairSchedule.forwardSegment cp 47 32 465 480 ++
        OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 (2 + 1))) m' a := by
  have hH : run ((((entryPieces checkpointPrimitives hostPlan).take 8).map Piece.H).flatten) u tStd =
      run (cut eps 8) u tStd := by
    unfold cut
    exact Stair44HostedCut.entry 8 tStd ⟨F⟩ u
  have hseg : StairSchedule.forwardSegment cp 47 32 465 480 = (StairConcreteAssembly.checkpointPrimitives.unpack 47 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 465 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (465 + 1) (5 * 93 + 5 - (465 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93 + 5)) ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93))) PackCutTrip.E138 ++
        renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93))) Rolling1588.ep ++
        (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1)))
          (5 * 93 + 5 + 1) (480 - (5 * 93 + 5) - 1) ++ checkpointPrimitives.orient 480 ++
          renameProgram (OB5.sig 480) (Rolling1588.Integer.packFirst base true 480) ++ checkpointPrimitives.pack 32)) := by
    rw [PackCutShape.forwardSegment_row 47 32 465 480 93 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.append_assoc]
  have hP : ∀ q ∈ wires (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 47 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 465 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (465 + 1) (5 * 93 + 5 - (465 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93 + 5))), q ∉ ryWires := by
    have hsub : (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 47 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 465 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (465 + 1) (5 * 93 + 5 - (465 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93 + 5))).Sublist (liftF (StairSchedule.forwardSegment cp 47 32 465 480)) := by
      rw [hseg]
      exact PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (List.sublist_append_left _ _)))
    intro q hq
    exact disjoint_ryWires_liftF forward465_notRY q (PackCutSub.wires_sub hsub q hq)
  have hq : ∀ jj : Fin 10, fieldPlace ((History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (465 + 1))) (5 * 93)) jj) ∉ ryWires := by
    intro jj
    exact (notRY_iff _).mp (by revert jj; decide)
  obtain ⟨m', h⟩ := PackCutEntryChain.rowCutOdd3 F.x (StairOpenWiring.entryPlans F.x)
    (StairLoanField7RR.entryReachTransportR_best StairOpenWiring.half760 F.x)
    StairLoanField7Transport.entryGroupSub_best
    (StairField13V3.entrySlotsClean_of _ _ _ (StairField13V3.entrySlots_of_v3 (StairField13V3.entrySlotsV3_of_parts
      (StairField13V3Fresh.entryParts_of_clean
        (StairField13V3Clean.entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760))))) tStd ⟨F, rfl⟩ u a
    (fun t1 jj => by rw [hH]; exact pullIn_agree hag _ hP t1 _ (hq jj)) m
  exact ⟨m', by rw [liftF_run, liftF_run, h]⟩

theorem oddRowCut4 {tStd : State} (F : EntryFrame tStd) (u : List Bool) (a : State)
    (hag : AgreeRY a (run (cut eps 10) u tStd)) (m : List Bool) :
    ∃ m', run (liftF (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1)) m a =
      run (liftF (StairSchedule.forwardSegment cp 32 22 480 490 ++
        OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 (1 + 1))) m' a := by
  have hH : run ((((entryPieces checkpointPrimitives hostPlan).take 10).map Piece.H).flatten) u tStd =
      run (cut eps 10) u tStd := by
    unfold cut
    exact Stair44HostedCut.entry 10 tStd ⟨F⟩ u
  have hseg : StairSchedule.forwardSegment cp 32 22 480 490 = (StairConcreteAssembly.checkpointPrimitives.unpack 32 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 480 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (480 + 1) (5 * 96 + 5 - (480 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96 + 5)) ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96))) PackCutTrip.E138 ++
        renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96))) Rolling1588.ep ++
        (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1)))
          (5 * 96 + 5 + 1) (490 - (5 * 96 + 5) - 1) ++ checkpointPrimitives.orient 490 ++
          renameProgram (OB5.sig 490) (Rolling1588.Integer.packFirst base true 490) ++ checkpointPrimitives.pack 22)) := by
    rw [PackCutShape.forwardSegment_row 32 22 480 490 96 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.append_assoc]
  have hP : ∀ q ∈ wires (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 32 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 480 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (480 + 1) (5 * 96 + 5 - (480 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96 + 5))), q ∉ ryWires := by
    have hsub : (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 32 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 480 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (480 + 1) (5 * 96 + 5 - (480 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96 + 5))).Sublist (liftF (StairSchedule.forwardSegment cp 32 22 480 490)) := by
      rw [hseg]
      exact PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (List.sublist_append_left _ _)))
    intro q hq
    exact disjoint_ryWires_liftF forward480_notRY q (PackCutSub.wires_sub hsub q hq)
  have hq : ∀ jj : Fin 10, fieldPlace ((History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (480 + 1))) (5 * 96)) jj) ∉ ryWires := by
    intro jj
    exact (notRY_iff _).mp (by revert jj; decide)
  obtain ⟨m', h⟩ := PackCutEntryChain.rowCutOdd4 F.x (StairOpenWiring.entryPlans F.x)
    (StairLoanField7RR.entryReachTransportR_best StairOpenWiring.half760 F.x)
    StairLoanField7Transport.entryGroupSub_best
    (StairField13V3.entrySlotsClean_of _ _ _ (StairField13V3.entrySlots_of_v3 (StairField13V3.entrySlotsV3_of_parts
      (StairField13V3Fresh.entryParts_of_clean
        (StairField13V3Clean.entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760))))) tStd ⟨F, rfl⟩ u a
    (fun t1 jj => by rw [hH]; exact pullIn_agree hag _ hP t1 _ (hq jj)) m
  exact ⟨m', by rw [liftF_run, liftF_run, h]⟩

theorem oddRowCut5 {tStd : State} (F : EntryFrame tStd) (u : List Bool) (a : State)
    (hag : AgreeRY a (run (cut eps 12) u tStd)) (m : List Bool) :
    ∃ m', run (liftF (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1)) m a =
      run (liftF (StairSchedule.forwardSegment cp 22 12 490 500 ++
        OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 (1 + 1))) m' a := by
  have hH : run ((((entryPieces checkpointPrimitives hostPlan).take 12).map Piece.H).flatten) u tStd =
      run (cut eps 12) u tStd := by
    unfold cut
    exact Stair44HostedCut.entry 12 tStd ⟨F⟩ u
  have hseg : StairSchedule.forwardSegment cp 22 12 490 500 = (StairConcreteAssembly.checkpointPrimitives.unpack 22 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 490 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (490 + 1) (5 * 98 + 5 - (490 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98 + 5)) ++
      (renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98))) PackCutTrip.E138 ++
        renameProgram (MeasuredCodec5.label (History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98))) Rolling1588.ep ++
        (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1)))
          (5 * 98 + 5 + 1) (500 - (5 * 98 + 5) - 1) ++ checkpointPrimitives.orient 500 ++
          renameProgram (OB5.sig 500) (Rolling1588.Integer.packFirst base true 500) ++ checkpointPrimitives.pack 12)) := by
    rw [PackCutShape.forwardSegment_row 22 12 490 500 98 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [List.append_assoc]
  have hP : ∀ q ∈ wires (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 22 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 490 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (490 + 1) (5 * 98 + 5 - (490 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98 + 5))), q ∉ ryWires := by
    have hsub : (liftF (StairConcreteAssembly.checkpointPrimitives.unpack 22 ++
        StairConcreteAssembly.checkpointPrimitives.tickForward 490 ++
        StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (490 + 1) (5 * 98 + 5 - (490 + 1)) ++
        TickRanges.tick (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98 + 5))).Sublist (liftF (StairSchedule.forwardSegment cp 22 12 490 500)) := by
      rw [hseg]
      exact PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (List.sublist_append_left _ _)))
    intro q hq
    exact disjoint_ryWires_liftF forward490_notRY q (PackCutSub.wires_sub hsub q hq)
  have hq : ∀ jj : Fin 10, fieldPlace ((History5.historyMap (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (490 + 1))) (5 * 98)) jj) ∉ ryWires := by
    intro jj
    exact (notRY_iff _).mp (by revert jj; decide)
  obtain ⟨m', h⟩ := PackCutEntryChain.rowCutOdd5 F.x (StairOpenWiring.entryPlans F.x)
    (StairLoanField7RR.entryReachTransportR_best StairOpenWiring.half760 F.x)
    StairLoanField7Transport.entryGroupSub_best
    (StairField13V3.entrySlotsClean_of _ _ _ (StairField13V3.entrySlots_of_v3 (StairField13V3.entrySlotsV3_of_parts
      (StairField13V3Fresh.entryParts_of_clean
        (StairField13V3Clean.entryClean_of_planR StairOpenWiring.entryPlans StairOpenWiring.half760))))) tStd ⟨F, rfl⟩ u a
    (fun t1 jj => by rw [hH]; exact pullIn_agree hag _ hP t1 _ (hq jj)) m
  exact ⟨m', by rw [liftF_run, liftF_run, h]⟩


/-- The odd division field's rows with the five packet-cut rows. -/
def stockOddDivRawTailCut : Program :=
  PackCutOdd.cutRowOdd 87 62 425 450 14 85 4 ++ (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2 ++ (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2 ++ (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1 ++ (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1 ++ StairSchedule.forwardLast cp))))

def stockOddDivPreCut : Program :=
  renameProgram ExteriorPorts.fieldEquiv stockOddDivRawTailCut ++
    StairSchedule.fieldRename FourScratchWindow.unprefix

def stockOddDivHeadCut : Program :=
  ((Stair44Kernel.divLead ++ stockOddDivBeforeGroup) ++
    renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84)) ++
  ((((stockOddDivPreCut ++ StairSchedule.paritySetup) ++ stockOddDivBetween) ++
    StairSchedule.paritySetup) ++ stockOddDivPost)

end ECDSAAdd.Entrant.OddStockLockstep

end

end

/-! ## PACK-CUT odd exit: the last packet's letters before its closing `ep`, and the row cut (late) -/

section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.PackCutOddExit
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 BalancedField


/-- The odd exit packet head takes the packet's A-code frame to the stage-2 code frame followed by `twist`. -/
theorem oddHeadF_frame (d j : Nat) (hd : d ≤ 44) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp) :
    Rolling1588.StateTriple
      (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
        (Rolling1588.codeEncodeAt false (History5.historyMap base (5 * j))) origin X Y)
      (oddHeadF d j)
      (fun state => ∃ X' Y' : Fp, RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
        (Rolling1588.stageCodeAt false 2 (History5.historyMap base (5 * j)) ++
          Rolling1588.onPacket j ParityCodec5New.twist) origin X' Y' state) := by
  have hlaw := OddFullPassBridge.half760OddLoan_law d false hd
  have hsup := OddFullPassBridge.half760OddLoan_support d false hd
  let Frame (k : Nat) (V : Fp × Fp) :=
    RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
      (Rolling1588.stageCodeAt false k (History5.historyMap base (5 * j))) origin V.1 V.2
  have opening (V : Fp × Fp) : Rolling1588.StateTriple
      (RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
        (Rolling1588.codeEncodeAt false (History5.historyMap base (5 * j))) origin V.1 V.2)
      (Rolling1588.onPacket j Rolling1588.stageOpen) (Frame 0 V) :=
    fun s r h => RouteA.Rolling1588.regular_open_frame P1Life.oddWord P1Life.oddWord false j hj origin ctx
      V.1 V.2 s r h
  have step (k logical physical : Nat) (hk : k < 3)
      (used : (logical, physical) ∈ Rolling1588.activeSlots false k) (V : Fp × Fp) :
      ∃ W : Fp × Fp, Rolling1588.StateTriple (Frame k V) (RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j physical 2)
        (Frame k W) :=
    ⟨_, fun s r h => RouteA.Rolling1588.regular_cellWith_frame (OddFullPass.P1LifeLoan.half760OddLoan d false) false P1Life.oddWord P1Life.oddWord hlaw hsup
        j k logical physical hj hk used origin ctx enabled V.1 V.2 s r h⟩
  have transfer (k : Nat) (hk : k < 2) (V : Fp × Fp) :
      Rolling1588.StateTriple (Frame k V) (Rolling1588.onPacket j (Rolling1588.stageTransition false k))
        (Frame (k + 1) V) :=
    fun s r h => RouteA.Rolling1588.regular_transition_frame P1Life.oddWord P1Life.oddWord false j k hj hk
      origin ctx V.1 V.2 s r h
  obtain ⟨V1, s1⟩ := step 0 4 4 (by decide) (by decide) (X, Y)
  obtain ⟨V2, s2⟩ := step 1 3 3 (by decide) (by decide) V1
  obtain ⟨V3, s3⟩ := step 1 2 4 (by decide) (by decide) V2
  obtain ⟨V4, s4⟩ := step 2 1 4 (by decide) (by decide) V3
  obtain ⟨V5, s5⟩ := step 2 0 3 (by decide) (by decide) V4
  have result := (opening (X, Y)).seq (s1.seq ((transfer 0 (by decide) V1).seq (s2.seq (s3.seq
    ((transfer 1 (by decide) V3).seq (s4.seq (s5.seq (twist_frame j _ origin V5.1 V5.2))))))))
  have hprog : Rolling1588.onPacket j Rolling1588.stageOpen ++ (RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 4 2 ++
      (Rolling1588.onPacket j (Rolling1588.stageTransition false 0) ++ (RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 3 2 ++
      (RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 4 2 ++ (Rolling1588.onPacket j (Rolling1588.stageTransition false 1) ++
      (RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 4 2 ++ (RouteA.Rolling1588.cellWith false (OddFullPass.P1LifeLoan.half760OddLoan d false) j 3 2 ++
        Rolling1588.onPacket j ParityCodec5New.twist))))))) = oddHeadF d j := by
    simp only [oddHeadF, Rolling1588.stageOpen, Rolling1588.stageTransition, Rolling1588.onPacket,
      PackCutShape.rename_app, List.append_assoc, if_true, if_false, Bool.false_eq_true, show ¬(1 : Nat) = 0 from by decide]
  intro state records input
  have r := result state records input
  rw [hprog] at r
  exact ⟨r.1, V5.1, V5.2, r.2⟩

attribute [local irreducible] run measurementCount wires renameProgram

theorem head_sub (d j : Nat) (hd : d ≤ 44) :
    wires (oddHeadF d j) ⊆ wires (Rolling1588.basePacket false j) := by
  have hfull : wires (OddFullPass.P1LifeLoan.basePacket false d j) ⊆ wires (Rolling1588.basePacket false j) := by
    have hp := OddFullPass.P1LifeLoan.packet_wires_sub false d j hd
    have hps := StairLoanGroupSupport.packet_sub false d j (by omega)
    have hcomb := hp.trans hps
    rw [OddFullPass.P1LifeLoan.packet, StairGroups.packet_zero, Rolling1588.packet,
        renameProgram_support, renameProgram_support] at hcomb
    intro q hq
    obtain ⟨v, hv, eq⟩ := Finset.mem_image.mp (hcomb (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
    exact (Equiv.injective _ eq) ▸ hv
  rw [basePacket_false_tail, wires_append] at hfull
  exact Finset.subset_union_left.trans hfull

theorem mem_single (w : Wire) : w ∈ wires [Instr.X w] := by
  simp [wires, Instr.wires]

theorem single_sub (w : Wire) (S : Finset Wire) (h : w ∈ S) : wires [Instr.X w] ⊆ S := by
  intro q hq
  have : q = w := by simpa [wires, Instr.wires] using hq
  subst this
  exact h

open MeasuredCodec5 PackCutExit PackCutExitCut in
set_option maxRecDepth 20000 in
/-- On an odd record cut frame at `j + 1`, after the odd head of packet `j` (all but its closing `ep`),
the packet's ten letters are the shortened encode of a legal word. -/
theorem oddHeadF_cut_bits (d j : Nat) (hd : d ≤ 44) (hj1 : 1 ≤ j) (hj : j < 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp)
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * j) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * j))
    (state : State) (records : List Bool)
    (input : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (j + 1) origin X Y state) :
    ∃ x, x < 1024 ∧ legalNat x = true ∧ ∀ i : Fin 10,
      (run (oddHeadF d j) records state).basis (History5.historyMap base (5 * j) i) =
        (bitRun E138x x).testBit i := by
  have nonzero : j ≠ 0 := by omega
  obtain ⟨raw, rawPhase, rawFrame, encoded⟩ := input
  let current := run (Rolling1588.encodeGroup base (decide (j + 1 ≤ j)) j) [] raw
  have currentPhase := Rolling1588.encodeGroup_zero_phase base (decide (j + 1 ≤ j)) base_pool_nodup j
    (by omega) raw
  have cf : RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
      (Rolling1588.encodeGroup base (decide (j + 1 ≤ j)) j) origin X Y current :=
    ⟨raw, currentPhase.symm, rawFrame, rfl⟩
  have normalized : RouteA.Rolling1588.CodeFrame P1Life.oddWord P1Life.oddWord
      (Rolling1588.codeEncodeAt false (History5.historyMap base (5 * j))) origin X Y current := by
    simpa [Rolling1588.encodeGroup, nonzero, show ¬j + 1 ≤ j from by omega] using cf
  have res := oddHeadF_frame d j hd hj origin ctx enabled X Y current records normalized
  obtain ⟨X', Y', raw', _, pf', enc'⟩ := res.2
  have legal' : MeasuredCodec5.legalAt (History5.historyMap base (5 * j)) raw'.basis :=
    RouteA.Rolling1588.route_raw_current_legal P1Life.oddWord P1Life.oddWord j hj origin ctx X' Y' raw' pf'
  have hsup := (head_sub d j hd).trans (Rolling1588.basePacket_read_support false j hj)
  have disj := Rolling1588.otherEncodeCut_body_disjoint (j + 1) j hj origin ctx _ hsup
  have factor := Rolling1588.allEncodeCut_factor base (j + 1) base_pool_nodup 102 j (by decide) hj raw
  have actual : run (oddHeadF d j) records state =
      run (Rolling1588.otherEncodeCut base (j + 1) j 102) [] (run (oddHeadF d j) records current) := by
    rw [encoded, factor]
    exact (Arithmetic.run_disjoint_commute (Rolling1588.otherEncodeCut base (j + 1) j 102)
      (oddHeadF d j) disj [] records current).symm
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

theorem shifted_oddHead_bits (d j : Nat) (hj : j < 102) (s : State) (m : List Bool)
    (hz : ∀ q, Placement5.zeroRegion q → s.basis (base q) = false)
    (hfixF : ∀ i : Fin 10, Placement5.pi j (History5.historyId (5 * j) i) = History5.historyId (5 * j) i)
    (i : Fin 10) :
    (run (renameProgram (shifted (Placement5.pi j)) (oddHeadF d j)) m s).basis
        (History5.historyMap base (5 * j) i) =
      (run (oddHeadF d j) m s).basis (History5.historyMap base (5 * j) i) := by
  have h := run_rename (shifted (Placement5.pi j)) (shifted (Placement5.pi j)).injective
    (oddHeadF d j) m s
  rw [Placement5.shifted_zero_boundary (Placement5.pi j) (fun q hq => Placement5.pi_outside j q hj hq) s hz] at h
  have e := congrArg (fun st : State => st.basis (History5.historyMap base (5 * j) i)) h
  simp only [pullState] at e
  have hfix : shifted (Placement5.pi j) (History5.historyMap base (5 * j) i) =
      History5.historyMap base (5 * j) i := by
    show shifted (Placement5.pi j) (base (History5.historyId (5 * j) i)) = base (History5.historyId (5 * j) i)
    rw [shifted_base, hfixF i]
  rw [hfix] at e
  exact e

open MeasuredCodec5 PackCutExit in
set_option maxRecDepth 20000 in
/-- The odd exit group of packets `first .. first + c` without its last closing `ep`, on the odd record cut
frame at `first + c + 1`: the last packet's letters are the shortened encode of a legal word. -/
theorem oddGroup_head_bits (d first c : Nat) (hd : d ≤ 44)
    (h1 : 1 ≤ first) (hb : first + c + 1 ≤ 102)
    (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (enabled : origin (base 2400) = true) (X Y : Fp)
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * first) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * first))
    (hfixF : ∀ i : Fin 10, Placement5.pi first (History5.historyId (5 * first) i) = History5.historyId (5 * first) i)
    (s : State) (m : List Bool)
    (input : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (first + c + 1) origin X Y s) :
    ∃ x, x < 1024 ∧ legalNat x = true ∧ ∀ i : Fin 10,
      (run (OddFullPass.P1LifeLoan.groups false d (first + 1) c ++
          renameProgram (shifted (Placement5.pi first)) (oddHeadF d first)) m s).basis
        (History5.historyMap base (5 * first) i) = (bitRun E138x x).testBit i := by
  have gf := OddFullPassBridge.groups_oddLoan_cut_frame d false hd (first + 1) c (by omega) (by omega)
    origin ctx enabled X Y
  have inp : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord
      (if false = true then first + 1 else first + 1 + c) origin X Y s := by
    simpa [show first + 1 + c = first + c + 1 by omega] using input
  have r := gf s (m.take (measurementCount (OddFullPass.P1LifeLoan.groups false d (first + 1) c))) inp
  set s2 := run (OddFullPass.P1LifeLoan.groups false d (first + 1) c)
    (m.take (measurementCount (OddFullPass.P1LifeLoan.groups false d (first + 1) c))) s with hs2
  have f2 : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord (first + 1) origin
      (Replay5.groupsPayload false origin (first + 1) c (X, Y)).1
      (Replay5.groupsPayload false origin (first + 1) c (X, Y)).2 s2 := by
    have r2 := r.2
    simp only [Bool.false_eq_true, if_false] at r2
    exact r2
  have hz := RouteA.Rolling1588.cutFrame_zero_region P1Life.oddWord P1Life.oddWord (first + 1) origin ctx _ _ s2 f2
  obtain ⟨x, hx, lx, hbits⟩ := oddHeadF_cut_bits d first hd h1 (by omega) origin ctx enabled
    (Replay5.groupsPayload false origin (first + 1) c (X, Y)).1
    (Replay5.groupsPayload false origin (first + 1) c (X, Y)).2 hF s2
    (m.drop (measurementCount (OddFullPass.P1LifeLoan.groups false d (first + 1) c))) f2
  refine ⟨x, hx, lx, fun i => ?_⟩
  rw [run_append, ← hs2, shifted_oddHead_bits d first (by omega) s2 _ hz hfixF i]
  exact hbits i


end ECDSAAdd.Entrant.PackCutOddExit

namespace ECDSAAdd.Entrant.PackCutOddExit
open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout
open StairLoanExitReachX StairPacket OddStockLockstep

attribute [local irreducible] run measurementCount wires renameProgram

open MeasuredCodec5 PackCutExit in
set_option maxRecDepth 30000 in
/-- Odd exit row bits: on the odd lockstep relation at the group's start (the hypotheses of
`odd_hostedGroup_step`), after the hosted odd group without its last closing `ep`, the last packet's ten
letters (at `Fs`) are the shortened encode of a legal word. -/
theorem oddRow_bits (def_ first c B x : Nat)
    (hdef : def_ ≤ 44) (h1 : 1 ≤ first) (hb : first + c + 1 ≤ 102)
    (hB_mem : B = 0 ∨ B ∈ budgets)
    (havoid_payload : B ≠ 0 → ∀ q ∈ futurePayload B,
      q ∉ wires (renameProgram (OB5.sig 511) (Rolling1588.groups false first (c + 1))))
    (a b record : State) (m : List Bool)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hframe : FrameAt x (first + (c + 1)) record)
    (hagree : if B = 0 then b = record else AgreeOutside (Δv B) b record)
    (hcleanIn : ∀ q ∈ (StairSchedule.exclusiveRoles.drop def_ ++ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1)).map lowMap,
      b.basis q = false)
    (hhosts_notRY : ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1), q ∉ ryWires)
    (Fs : Fin 10 → Wire)
    (hsig : ∀ i, OB5.sig 511 (History5.historyMap base (5 * first) i) = Fs i)
    (hRH : ∀ i, Fs i ∉ StairSchedule.exclusiveRoles.drop def_ ++ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1))
    (hOff : ∀ i, Off (Fs i)) (hfp : ∀ i, B ≠ 0 → Fs i ∉ futurePayload B) (hnRY : ∀ i, Fs i ∉ ryWires)
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * first) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * first))
    (hfixF : ∀ i : Fin 10, Placement5.pi first (History5.historyId (5 * first) i) = History5.historyId (5 * first) i) :
    ∃ x', x' < 1024 ∧ legalNat x' = true ∧ ∀ i : Fin 10,
      (run (StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop def_) (OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1))
          (renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups false def_ (first + 1) c ++
            renameProgram (shifted (Placement5.pi first)) (oddHeadF def_ first))))
        m (pullIn a)).basis (Fs i) = (bitRun E138x x').testBit i := by
  let G : Program := OddFullPass.P1LifeLoan.groups false def_ (first + 1) c ++
    renameProgram (shifted (Placement5.pi first)) (oddHeadF def_ first)
  let PG := renameProgram (OB5.sig 511) G
  let P_odd := renameProgram (OB5.sig 511) (OddFullPass.P1LifeLoan.groups false def_ first (c + 1))
  let P_rec := renameProgram (OB5.sig 511) (Rolling1588.groups false first (c + 1))
  have hG_sub : wires PG ⊆ wires P_odd := by
    show wires (renameProgram (OB5.sig 511) G) ⊆ wires (renameProgram (OB5.sig 511) _)
    rw [oddPlaced_false_tail, wires_append]
    exact Finset.subset_union_left
  have hsub_odd : wires P_odd ⊆ wires P_rec := by
    have h1 : wires (OddFullPass.P1LifeLoan.groups false def_ first (c + 1)) ⊆
        wires (StairGroups.groups false def_ first (c + 1)) :=
      StairLoanGroupSupport.sequence_sub _ _ _
        (fun k => OddFullPass.P1LifeLoan.packet_wires_sub false def_ k hdef) _ _
    have h2 := StairLoanGroupSupport.groups_sub false def_ (by omega) first (c + 1)
    show wires (renameProgram (OB5.sig 511) _) ⊆ wires (renameProgram (OB5.sig 511) _)
    rw [renameProgram_support, renameProgram_support]
    exact Finset.image_subset_image (h1.trans h2)
  have hrec_off : ∀ q ∈ wires P_rec, Off q := StairField2V3ExitRec.groupsF_off first (c + 1) h1 (by omega)
  obtain ⟨origin, X, Y, s_rec, ctx, en, tr, cut_rec, agree_rec⟩ := hframe
  have hpb_rec : ∀ q, Off q → (B ≠ 0 → q ∉ futurePayload B) → (pullIn b).basis q = s_rec.basis q := by
    intro q hq hnp
    have hbr : (pullIn b).basis q = (pullIn record).basis q := by
      by_cases hB0 : B = 0
      · simp only [hB0, if_true] at hagree; rw [hagree]
      · simp only [hB0, if_false] at hagree
        change b.basis (fieldPlace q) = record.basis (fieldPlace q)
        apply hagree.2
        intro hmem
        simp only [Δv, List.mem_toFinset, List.mem_map] at hmem
        obtain ⟨r, hr, heq⟩ := hmem
        have qr : r = q := by
          have := congrArg fieldPlaceInv heq
          rwa [inv_fieldPlace, inv_fieldPlace] at this
        exact hnp hB0 (qr ▸ hr)
    exact hbr.trans (agree_rec q hq)
  have hb_vals : regValue fieldR b.basis = centerWord X ∧ regValue fieldY b.basis = centerWord Y := by
    have hrec_vals := cutFrame_std_values _ origin X Y _ cut_rec
    rw [pullState_sig511_regValue_R, pullState_sig511_regValue_Y] at hrec_vals
    have hEq_ry : ∀ q ∈ ryWires, (pullIn b).basis q = s_rec.basis q := by
      intro q hq
      apply hpb_rec q (ryWires_off q hq)
      intro hB0 hfp'
      rcases hB_mem with rfl | hBm
      · exact hB0 rfl
      · exact futurePayload_not_ryWires B hBm q hfp' hq
    constructor
    · rw [← pullIn_regValue_R]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hrec_vals.1
    · rw [← pullIn_regValue_Y]
      exact (regValue_congr _ _ _ (fun q hq => hEq_ry q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hrec_vals.2
  have ha_vals : regValue fieldR a.basis = P1Life.oddWord X ∧ regValue fieldY a.basis = P1Life.oddWord Y :=
    ⟨hrel.2.1 X hb_vals.1, hrel.2.2 Y hb_vals.2⟩
  let s_odd : State := spliceRY (pullIn a) s_rec
  have hcut_odd : RouteA.Rolling1588.CutFrame P1Life.oddWord P1Life.oddWord
      (first + (c + 1)) origin X Y (pullState (OB5.sig 511) s_odd) :=
    cutFrame_spliceRY P1Life.oddWord P1Life.oddWord _ origin X Y (pullIn a) s_rec cut_rec
      (by rw [pullIn_regValue_R]; exact ha_vals.1) (by rw [pullIn_regValue_Y]; exact ha_vals.2)
  have hpa_sodd : ∀ q ∈ wires PG, (pullIn a).basis q = s_odd.basis q := by
    intro q hq
    by_cases hry : q ∈ ryWires
    · simp only [s_odd, spliceRY, hry, if_true]
    · simp only [s_odd, spliceRY, hry, if_false]
      have hq' := hsub_odd (hG_sub hq)
      have h1' := (pullIn_agreeRY hrel.1).2 q hry
      have h2' := hpb_rec q (hrec_off q hq') (fun hB0 hfp' => havoid_payload hB0 q hfp' hq')
      exact h1'.trans h2'
  have hinc := Arithmetic.run_local_increment PG (pullIn a) s_odd m hpa_sodd
  -- the hosted roles / hosts are zero on `pullIn a`
  have hclean_a_in : ∀ q ∈ StairSchedule.exclusiveRoles.drop def_ ++ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1),
      (pullIn a).basis q = false := by
    intro q hq
    have hnot : q ∉ ryWires := by
      rcases List.mem_append.mp hq with hr | hh
      · exact exclusiveRoles_not_ryWires q (List.mem_of_mem_drop hr)
      · exact hhosts_notRY q hh
    have h1' := (pullIn_agreeRY hrel.1).2 q hnot
    have h2' : (pullIn b).basis q = false := hcleanIn (lowMap q) (List.mem_map.mpr ⟨q, hq, rfl⟩)
    exact h1'.trans h2'
  -- the record-frame bits on the spliced state
  obtain ⟨x', hx', lx', hbits⟩ := oddGroup_head_bits def_ first c hdef h1 hb origin ctx en X Y hF hfixF
    (pullState (OB5.sig 511) s_odd) m hcut_odd
  refine ⟨x', hx', lx', fun i => ?_⟩
  rw [PackCutExitTransport.hosted_bits _ _ _ m (pullIn a) hclean_a_in (Fs i) (hRH i)]
  have step1 : (run PG m (pullIn a)).basis (Fs i) = (run PG m s_odd).basis (Fs i) := by
    by_cases hw : Fs i ∈ wires PG
    · exact hinc.2 _ hw
    · rw [run_preserves_outside _ m _ _ hw, run_preserves_outside _ m _ _ hw]
      simp only [s_odd, spliceRY, hnRY i, if_false]
      exact ((pullIn_agreeRY hrel.1).2 _ (hnRY i)).trans (hpb_rec _ (hOff i) (hfp i))
  show (run PG m (pullIn a)).basis (Fs i) = _
  rw [step1]
  have e := ECDSAAdd.run_rename (OB5.sig 511) (OB5.sig_injective 511 (le_refl _)) G m s_odd
  have e2 := congrArg (fun st : State => st.basis (History5.historyMap base (5 * first) i)) e
  simp only [pullState] at e2
  rw [← hsig i, e2]
  exact hbits i


end ECDSAAdd.Entrant.PackCutOddExit

namespace ECDSAAdd.Entrant.PackCutOddExit
open ECDSAAdd Arithmetic MappedCompressed
open StairConcreteAssembly StairPhysicalLayout StairField2V3RecScratch OddStockLockstep

attribute [local irreducible] run measurementCount wires renameProgram

open MeasuredCodec5 PackCutExit in
set_option maxRecDepth 30000 in
/-- PACK-CUT odd exit row: the odd hosted group's last closing `ep` and the next segment's due-read `dp` cancel. -/
theorem oddExit_row_full (def_ first c B x : Nat)
    (hdef : def_ ≤ 44) (h1 : 1 ≤ first) (hb : first + c + 1 ≤ 102)
    (hB_mem : B = 0 ∨ B ∈ budgets)
    (havoid_payload : B ≠ 0 → ∀ q ∈ futurePayload B,
      q ∉ wires (renameProgram (OB5.sig 511) (Rolling1588.groups false first (c + 1))))
    (a b record : State)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hframe : StairField2V3LastRecX.FrameAt x (first + (c + 1)) record)
    (hagree : if B = 0 then b = record else StairField2V3Replay.AgreeOutside (StairField2V3Delta.Δv B) b record)
    (hcleanIn : ∀ q ∈ (StairSchedule.exclusiveRoles.drop def_ ++ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1)).map
      StairField13V3.lowMap, b.basis q = false)
    (hhosts_notRY : ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1), q ∉ ryWires)
    (Fs : Fin 10 → Wire) (hFinj : Function.Injective Fs)
    (hsig : ∀ i, OB5.sig 511 (History5.historyMap base (5 * first) i) = Fs i)
    (hRH : ∀ i, Fs i ∉ StairSchedule.exclusiveRoles.drop def_ ++ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1))
    (hOff : ∀ i, Off (Fs i)) (hfp : ∀ i, B ≠ 0 → Fs i ∉ futurePayload B) (hnRY : ∀ i, Fs i ∉ ryWires)
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * first) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * first))
    (hfixF : ∀ i : Fin 10, Placement5.pi first (History5.historyId (5 * first) i) = History5.historyId (5 * first) i)
    (SEG M Bx : Program) (hseg : SEG = M ++ renameProgram (label Fs) Rolling1588.dp ++ Bx)
    (hM : ∀ q ∈ (Finset.range 10).image (label Fs), q ∉ wires M)
    (hep : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop def_) (OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.ep))) = renameProgram (label Fs) Rolling1588.ep)
    (m : List Bool) :
    ∃ m', run (AhOdd def_ first c ++ M ++ Bx) m (StairField2V3Seg.pullIn a) =
      run (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false def_ first (c + 1) ++ SEG) m'
        (StairField2V3Seg.pullIn a) := by
  obtain ⟨m', h⟩ := PackCutExitBits.exit_row_cut_bits (AhOdd def_ first c) M _ Bx Fs hFinj rfl hM
    (StairField2V3Seg.pullIn a) m
    (fun tA => oddRow_bits def_ first c B x hdef h1 hb hB_mem havoid_payload a b record tA hrel hframe hagree
      hcleanIn hhosts_notRY Fs hsig hRH hOff hfp hnRY hF hfixF)
  refine ⟨m', ?_⟩
  rw [h, oddHostedGroup_false_tail, hep, hseg]
  simp only [AhOdd, List.append_assoc]


end ECDSAAdd.Entrant.PackCutOddExit

namespace ECDSAAdd.Entrant.PackCutOddExit
open ECDSAAdd Arithmetic MappedCompressed
open StairConcreteAssembly StairPhysicalLayout StairField2V3RecScratch OddStockLockstep StairPacket

attribute [local irreducible] run measurementCount wires renameProgram

open MeasuredCodec5 PackCutExit in
set_option maxRecDepth 30000 in
/-- The odd exit row cut in physical (field-placed) coordinates, as the odd lockstep chain runs it. -/
theorem oddCutRow_runeq (def_ first c B x : Nat)
    (hdef : def_ ≤ 44) (h1 : 1 ≤ first) (hb : first + c + 1 ≤ 102)
    (hB_mem : B = 0 ∨ B ∈ budgets)
    (havoid_payload : B ≠ 0 → ∀ q ∈ futurePayload B,
      q ∉ wires (renameProgram (OB5.sig 511) (Rolling1588.groups false first (c + 1))))
    (a b record : State)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hframe : StairField2V3LastRecX.FrameAt x (first + (c + 1)) record)
    (hagree : if B = 0 then b = record else StairField2V3Replay.AgreeOutside (StairField2V3Delta.Δv B) b record)
    (hcleanIn : ∀ q ∈ (StairSchedule.exclusiveRoles.drop def_ ++ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1)).map
      StairField13V3.lowMap, b.basis q = false)
    (hhosts_notRY : ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1), q ∉ ryWires)
    (Fs : Fin 10 → Wire) (hFinj : Function.Injective Fs)
    (hsig : ∀ i, OB5.sig 511 (History5.historyMap base (5 * first) i) = Fs i)
    (hRH : ∀ i, Fs i ∉ StairSchedule.exclusiveRoles.drop def_ ++ OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1))
    (hOff : ∀ i, Off (Fs i)) (hfp : ∀ i, B ≠ 0 → Fs i ∉ futurePayload B) (hnRY : ∀ i, Fs i ∉ ryWires)
    (hF : ∀ i : Fin 10, History5.historyMap base (5 * first) i ∈
      NewHistory5.groupReadSites base (base 2400) (base 2409) (base 2410) (5 * first))
    (hfixF : ∀ i : Fin 10, Placement5.pi first (History5.historyId (5 * first) i) = History5.historyId (5 * first) i)
    (SEG M Bx : Program) (hseg : SEG = M ++ renameProgram (label Fs) Rolling1588.dp ++ Bx)
    (hM : ∀ q ∈ (Finset.range 10).image (label Fs), q ∉ wires M)
    (hep : StairLoan.rebindMany (StairSchedule.exclusiveRoles.drop def_) (OddFullPass.P1LifeLoan.hostPlan1542.group false def_ first (c + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.ep))) = renameProgram (label Fs) Rolling1588.ep)
    (m : List Bool) :
    ∃ m', run (StairField2V3Entry.liftF (AhOdd def_ first c ++ M ++ Bx)) m a =
      run (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false def_ first (c + 1)) ++
        StairField2V3Entry.liftF SEG) m' a := by
  obtain ⟨m', h⟩ := oddExit_row_full def_ first c B x hdef h1 hb hB_mem havoid_payload a b record hrel hframe
    hagree hcleanIn hhosts_notRY Fs hFinj hsig hRH hOff hfp hnRY hF hfixF SEG M Bx hseg hM hep m
  refine ⟨m', ?_⟩
  rw [show renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false def_ first (c + 1)) =
      StairField2V3Entry.liftF (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false def_ first (c + 1)) from
      (ExteriorPorts.placedShape _).symm,
    ← StairField13V3Clean.liftF_append, StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run, h]


end ECDSAAdd.Entrant.PackCutOddExit
end

-- ==== end OddLockstepDiv ====

-- ==== begin OddLockstepMul ====
section

set_option autoImplicit false

section

namespace ECDSAAdd.Entrant.OddStockLockstep

open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout
open StairLoanExitReachX StairLoanField7Transport StairPacket

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] run measurementCount wires renameProgram cut

private theorem local_eq_of_sub₂ (P Q : Program) (hsub : wires P ⊆ wires Q)
    (a b : State) (m1 m2 : List Bool)
    (hag : ∀ q ∈ wires Q, a.basis q = b.basis q)
    (heq : run P m1 b = run Q m2 b) :
    run P m1 a = run Q m2 a := by
  have hp := Arithmetic.run_local_increment P a b m1 (fun q hq => hag q (hsub hq))
  have hq := Arithmetic.run_local_increment Q a b m2 hag
  apply State.extensionality
  · have hpeq : (run P m1 b).phase = (run Q m2 b).phase := congrArg State.phase heq
    have h1 : ((run P m1 a).phase ^^ a.phase) = ((run P m1 b).phase ^^ b.phase) := hp.1
    have h2 : ((run Q m2 a).phase ^^ a.phase) = ((run P m1 b).phase ^^ b.phase) := by rw [hpeq]; exact hq.1
    revert h1 h2
    cases (run P m1 a).phase <;> cases (run Q m2 a).phase <;> cases a.phase <;>
      cases (run P m1 b).phase <;> cases b.phase <;> decide
  · funext w
    by_cases h1 : w ∈ wires P
    · rw [hp.2 w h1, hq.2 w (hsub h1), heq]
    · rw [run_preserves_outside P m1 a w h1]
      by_cases h2 : w ∈ wires Q
      · rw [hq.2 w h2, ← heq, run_preserves_outside P m1 b w h1]; exact hag w h2
      · rw [run_preserves_outside Q m2 a w h2]

private theorem sig511_511_mul : OB5.sig 511 (base 511) = base 511 := by decide +kernel

private theorem regValue_run_disjoint_R_mul (P : Program) (h : ∀ q ∈ wires P, q ∉ fieldR)
    (m : List Bool) (s : State) : regValue fieldR (run P m s).basis = regValue fieldR s.basis :=
  regValue_congr fieldR (run P m s).basis s.basis
    (fun q hq => run_preserves_outside P m s q (fun hw => h q hw hq))

private theorem cutLoan_exit_helper {P : Program} {pre : State → Prop}
    (clean : CutClean pre P ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap))
    (s : State) (h : pre s) (m : List Bool) :
    ∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (run P m s).basis (fieldPlace q) = false := by
  intro q hq
  exact clean s h m _ (by rw [hp_group false 0 1 84 (by decide)]; exact List.mem_map.mpr ⟨q, hq, rfl⟩)

private theorem exitFirstBefore_xps (k : Nat) :
    CutClean (ExitPre k) (cut (xps k) 23) ((StairSchedule.exclusiveRoles ++ hostPlan.firstPacket false).map fieldMap) :=
  (exitClean_v3_inst k).firstBefore

private theorem exitFirstRolesAfter_xps (k : Nat) :
    CutClean (ExitPre k) (cut (xps k) 24) (StairSchedule.exclusiveRoles.map fieldMap) :=
  (exitClean_v3_inst k).firstRolesAfter

private theorem exitGroupsBefore_xps (k j def_ start len : Nat)
    (h : (j, def_, start, len) ∈ [(7, 43, 100, 2), (11, 41, 98, 2), (13, 36, 96, 2), (15, 30, 93, 3),
        (17, 22, 90, 3), (19, 13, 85, 5), (21, 0, 1, 84)]) :
    CutClean (ExitPre k) (cut (xps k) j)
      ((StairSchedule.exclusiveRoles.drop def_ ++ hostPlan.group false def_ start len).map lowMap) :=
  (exitClean_v3_inst k).groupsBefore (j, def_, start, len) h

private theorem exitGroupsRolesAfter_xps (k j def_ start len : Nat)
    (h : (j, def_, start, len) ∈ [(7, 43, 100, 2), (11, 41, 98, 2), (13, 36, 96, 2), (15, 30, 93, 3),
        (17, 22, 90, 3), (19, 13, 85, 5), (21, 0, 1, 84)]) :
    CutClean (ExitPre k) (cut (xps k) (j + 1))
      ((StairSchedule.exclusiveRoles.drop def_).map lowMap) :=
  (exitClean_v3_inst k).groupsRolesAfter (j, def_, start, len) h

private theorem fullExitCut21Clean (k : Nat) (parts : StairField13V3Fresh.ExitClean k) :
    CutClean (ExitPre k) (cut (xps k) 21) ((StairSchedule.exclusiveRoles.drop 0 ++ hp.group false 0 1 84).map lowMap) :=
  parts.groupsBefore (21, 0, 1, 84) (by simp)

private theorem reach_YE_win (k x : Nat) (t : State) (h : ReachE k x YE t) :
    StairField2V3Win.WinT x t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold YE YD YC YB YA
  rw [run_append _ (StairField2V3ExitPlan.grpF 85 5), run_append _ (StairField2V3ExitPlan.grpF 90 3),
      run_append _ (StairField2V3ExitPlan.grpF 93 3), run_append _ (StairField2V3ExitPlan.grpF 96 2),
      run_append _ (StairField2V3ExitPlan.grpF 98 2)]
  apply StairField2V3Win.winT_lift x _ (StairField2V3ExitRec.groupsF_off 85 5 (by decide) (by decide))
  apply StairField2V3Win.winT_lift x _ (StairField2V3ExitRec.groupsF_off 90 3 (by decide) (by decide))
  apply StairField2V3Win.winT_lift x _ (StairField2V3ExitRec.groupsF_off 93 3 (by decide) (by decide))
  apply StairField2V3Win.winT_lift x _ (StairField2V3ExitRec.groupsF_off 96 2 (by decide) (by decide))
  apply StairField2V3Win.winT_lift x _ (StairField2V3ExitRec.groupsF_off 98 2 (by decide) (by decide))
  exact (StairField2V3ExitRec.inv_head_w k x s0 hs0 _).2

theorem exitCut21_pin_loan_full (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    (∃ record, FrameAt F.x 85 record ∧ AgreeOutside (Δv 87) (run (cut (xps k) 21) m s) record ∧
      CvX F.x 87 (run (cut (xps k) 21) m s).basis record.basis ∧
      StairField2V3Win.WinT F.x record) ∧
    (∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (run (cut (xps k) 21) m s).basis (fieldPlace q) = false) := by
  constructor
  · rw [xcut21, run_append]
    obtain ⟨Q, link⟩ := rch21 k F.x (StairOpenWiring.exitPlans k F.x) StairOpenWiring.half760
    obtain ⟨old, rel, reachable⟩ := link _ _ ⟨⟨s, F, rfl, _, rfl⟩, rfl⟩ _
    have hre := reachX_E StairOpenWiring.half760 k F.x _ reachable
    exact ⟨_, WindowFieldView.exitFrame 85 F.x _ (StairField2V3ExitRec.reach_YE k F.x _ hre),
      rel.1, rel.2, reach_YE_win k F.x _ hre⟩
  · exact cutLoan_exit_helper (fullExitCut21Clean k (exitClean_v3_inst k)) s ⟨F⟩ m

theorem exitCut21_pin_loan (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    (∃ record, FrameAt F.x 85 record ∧ AgreeOutside (Δv 87) (run (cut (xps k) 21) m s) record) ∧
    (∀ q ∈ StairSchedule.exclusiveRoles ++ hosts 87, (run (cut (xps k) 21) m s).basis (fieldPlace q) = false) := by
  obtain ⟨⟨rec, hf, ha, _, _⟩, hl⟩ := exitCut21_pin_loan_full k F m
  exact ⟨⟨rec, hf, ha⟩, hl⟩

theorem outMap_symm_fix_fieldR : ∀ q ∈ fieldR, Stair44Kernel.outMap.symm q = q := fun q hq => by
  have h := outMap_fix_fieldR q hq
  have h2 := congrArg Stair44Kernel.outMap.symm h
  rw [Equiv.symm_apply_apply] at h2
  exact h2.symm

private theorem regValue_pull_put_eq_R (f : Wire → Wire) (hfix : ∀ q ∈ fieldR, f q = q)
    (rk : State) (p : Wire) (hp : p ∉ fieldR) (b : Bool) :
    regValue fieldR (pullState f (ParityEven.put rk p b)).basis = regValue fieldR rk.basis := by
  apply regValue_congr fieldR _ rk.basis
  intro q hq
  change (ParityEven.put rk p b).basis (f q) = rk.basis q
  rw [hfix q hq]
  have hne : q ≠ p := fun e => hp (e ▸ hq)
  simp only [ParityEven.put, writeBit, Function.update_of_ne hne]

/-! ## Section 5: Multiplication stock lockstep (`stockOddMulPrefix21`, `stockOddMulHead`) -/

def stockOddMulBeforeParity : Program :=
  StairSchedule.hostedX ++ StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542)

def stockOddMulBeforeGroup : Program :=
  StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram ++
  StairSchedule.fieldRename (renameProgram Prefix1590.borrow
    (StairSchedule.reverseLast cp ++
    PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1 ++
    PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1 ++
    PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2 ++
    PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2 ++
    PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4))

def stockOddMulLeading : Program :=
  StairSchedule.paritySetup ++ stockOddMulBeforeParity ++ StairSchedule.paritySetup ++ stockOddMulBeforeGroup

def stockOddMulPrefix21 : Program :=
  StairField2V3Replay.exitReferenceOpening ++ stockOddMulLeading

def stockOddMulAfterGroup : Program :=
  StairSchedule.fieldRename (FourScratchWindow.unprefix ++
    JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false)

def stockOddMulHead : Program :=
  (((Stair44Kernel.mulLead ++ stockOddMulLeading) ++
    renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84)) ++
    stockOddMulAfterGroup) ++
  renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack

/-- Explicit cut-21 lockstep for Multiplication: `stockOddMulPrefix21` vs `cut (xps k) 21`
with `OddRel` and `OCut 85`! -/
theorem stockOddMul_cut21 (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    let a21 := run stockOddMulPrefix21 m s
    (∃ n, OddRel P1Life.oddWord P1Life.oddWord a21 (run (cut (xps k) 21) n s)) ∧
    (∃ origin, FrontierReplay1591.Context origin ∧ origin (base 2400) = true ∧
      TraceOK F.x origin ∧ WindowFieldView.OCut 85 origin (pullIn a21) ∧
      StairPacket.WindowFieldView.TagReady (pullIn a21)) := by
  intro a21
  -- Define `MulCut j a b := (∃ u, b = run (cut (xps k) j) u s) ∧ OddRel oddWord oddWord a b`
  let MulCut (j : Nat) (a b : State) : Prop :=
    (∃ u, b = run (cut (xps k) j) u s) ∧ OddRel P1Life.oddWord P1Life.oddWord a b
  have step_disj (j : Nat) (hj : j < 25) (P : Program) (hP : ((xps k)[j]'(xL k j hj)).L = P)
      (hnot : ∀ q ∈ wires P, q ∉ ryWires) :
      ∀ a b m', MulCut j a b → MulCut (j + 1) (run P m' a) (run P m' b) := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    refine ⟨⟨WindowFieldJourney.joinTapes (cut (xps k) j) u m', ?_⟩, oddRel_disjoint P hnot hrel m'⟩
    rw [cut_succ (xps k) j (xL k j hj), hP, WindowFieldJourney.joined]
  have step_grp (j B def_ start len : Nat) (hj : j < 25)
      (hL : ((xps k)[j]'(xL k j hj)).L = grpFL StairConcrete.bestLoans def_ start len)
      (hB : B = 0 ∨ B ∈ budgets) (hstartB : B ≠ 0 → start + len ≤ startFor B / 5)
      (hd : def_ ≤ 43) (hdef0 : def_ ≠ 0) (h1 : 1 ≤ start) (hb : start + len ≤ 102)
      (hmem : (j, def_, start, len) ∈ [(7, 43, 100, 2), (11, 41, 98, 2), (13, 36, 96, 2),
          (15, 30, 93, 3), (17, 22, 90, 3), (19, 13, 85, 5), (21, 0, 1, 84)])
      (hsched : def_ = 43 ∨ (def_, start, len) ∈ [(0, 1, 84), (13, 85, 5), (22, 90, 3), (30, 93, 3),
          (36, 96, 2), (41, 98, 2)])
      (hpin : ∀ u, ∃ rec, FrameAt F.x (start + len) rec ∧ (if B = 0 then run (cut (xps k) j) u s = rec else AgreeOutside (Δv B) (run (cut (xps k) j) u s) rec)) :
      ∀ a b m', MulCut j a b →
        MulCut (j + 1)
          (run (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false (def_ + 1) start len)) m' a)
          (run (grpFL StairConcrete.bestLoans def_ start len) m' b) := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨rec, hframe, hagree⟩ := hpin u
    have hclIn : ∀ q ∈ (StairSchedule.exclusiveRoles.drop def_ ++ hostPlan.group false def_ start len).map lowMap,
        (run (cut (xps k) j) u s).basis q = false :=
      exitGroupsBefore_xps k j def_ start len hmem s ⟨F⟩ u
    have hclOut : ∀ q ∈ (StairSchedule.exclusiveRoles.drop def_).map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups false def_ start len))) m' (run (cut (xps k) j) u s)).basis q = false :=
      cleanCut_after (exitGroupsRolesAfter_xps k j def_ start len hmem)
        (by rw [cut_succ (xps k) j (xL k j hj), hL]; rfl) s ⟨F⟩ u m'
    have havoid : B ≠ 0 → ∀ q ∈ futurePayload B, q ∉ wires (renameProgram (OB5.sig 511) (Rolling1588.groups false start len)) := by
      intro hne
      rcases hB with rfl | hBm
      · exact absurd rfl hne
      · exact StairField2V3Groups.groups_avoid_payload false B hBm len start (by have := hstartB hne; omega)
    have hdef_mem : def_ ∈ ([13, 22, 30, 36, 41, 43] : List Nat) := by
      rcases hsched with rfl | hs
      · decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
        rcases hs with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩
        · exact absurd rfl hdef0
        all_goals simp
    have hsched1542 : def_ = 43 ∨ (def_, start, len) ∈ [(13, 85, 5), (22, 90, 3), (30, 93, 3), (36, 96, 2), (41, 98, 2)] := by
      rcases hsched with rfl | hs
      · exact Or.inl rfl
      · right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
        rcases hs with ⟨rfl, _, _⟩ | hrest
        · exact absurd rfl hdef0
        · exact hrest
    have hclIn' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop (def_ + 1) ++
          OddFullPass.P1LifeLoan.hostPlan1542.group false (def_ + 1) start len).map lowMap,
        (run (cut (xps k) j) u s).basis q = false := by
      intro q hq
      apply hclIn q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (Nat.le_succ def_)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false def_ start len hdef_mem w hh)
    have hclOut' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop (def_ + 1)).map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups false def_ start len))) m' (run (cut (xps k) j) u s)).basis q = false := by
      intro q hq
      apply hclOut q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      exact ⟨w, (List.drop_sublist_drop_left _ (Nat.le_succ def_)).subset hw, rfl⟩
    have hstep := odd_hostedGroup_step false (def_ + 1) def_ start len B F.x (hpOdd := OddFullPass.P1LifeLoan.hostPlan1542)
      (by omega) hd h1 hb hB havoid
      a (run (cut (xps k) j) u s) rec m' hrel hframe hagree
      hclIn' hclOut' (hostPlan1542_group_notRY false def_ start len hdef_mem)
      (hostPlan1542_group_fresh_odd false def_ start len hd h1 hb hdef_mem hsched1542)
    have hgrpFL_eq : grpFL StairConcrete.bestLoans def_ start len =
        liftF (renameProgram (OB5.sig 511) (StairGroups.groups false def_ start len)) := rfl
    rw [← hgrpFL_eq] at hstep
    refine ⟨⟨WindowFieldJourney.joinTapes (cut (xps k) j) u m', ?_⟩, hstep⟩
    rw [cut_succ (xps k) j (xL k j hj), hL, WindowFieldJourney.joined]
  -- Pieces 0–6: pieces 0–3 identical on `s`, then pieces 4–6 via `mulHeadCore_step`!
  have hcut7 (m7 : List Bool) :
      let P03 := StairField2V3Replay.exitReferenceOpening ++ StairSchedule.paritySetup ++
        StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram
      let CoreOdd := liftF (OddFullPass.HalfConvertOdd.center760OddLoan ++ HalfFieldOB5.copyN ++
        renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44)
      MulCut 7 (run (P03 ++ CoreOdd) m7 s) (run (cut (xps k) 7) m7 s) := by
    intro P03 CoreOdd
    have hcut4 : cut (xps k) 4 = P03 := by
      rw [cut_succ (xps k) 3 (xL k 3 (by decide)), cut_succ (xps k) 2 (xL k 2 (by decide)),
          cut_succ (xps k) 1 (xL k 1 (by decide)), cut_succ (xps k) 0 (xL k 0 (by decide)),
          cut_zero, x0_L, x1_L, x2_L, x3_L]
      simp only [P03, List.nil_append, List.append_assoc]
    have hcut7_eq : cut (xps k) 7 = P03 ++ liftF (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
        StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) := by
      rw [cut_succ (xps k) 6 (xL k 6 (by decide)), cut_succ (xps k) 5 (xL k 5 (by decide)),
          cut_succ (xps k) 4 (xL k 4 (by decide)), hcut4, x4_L, x5_L, x6_L]
      simp only [liftF_append, List.append_assoc]
    let m0 := m7.take (measurementCount P03)
    let m1 := m7.drop (measurementCount P03)
    let b4 := run P03 m0 s
    let mOpen := m0.take (measurementCount StairField2V3Replay.exitReferenceOpening)
    let mRest := m0.drop (measurementCount StairField2V3Replay.exitReferenceOpening)
    have hopen : run StairField2V3Replay.exitReferenceOpening mOpen s =
        run (Rolling1588.firstPhase false) mOpen s :=
      first_phase_hosted false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
    obtain ⟨orig, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
      F.sharedNodup F.historyAbove F.selectorsAway F.x F.Y F.x_pos F.x_lt s mOpen F.input
    have ctx := Rolling1588Lifetime.prepared_context F.sharedNodup F.selectorsAway
      F.transcript F.x F.Y s orig facts legal F.selectorG_zero F.selectorS_zero
    have bits := Rolling1588Lifetime.first_clean false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
    have work := Rolling1588Lifetime.first_work_zero false F.sharedNodup F.x F.Y.val s mOpen F.input
    have parity := Rolling1588Lifetime.first_parity false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
    have input := frames false
    rw [lf_eq] at input bits work parity
    obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) mOpen s = v := ⟨_, rfl⟩
    rw [hv] at input bits work parity
    have code := Rolling1588Frame.canonical_special_at orig.basis F.Y 0 v 511 (by simp) input
    have in511 : v.basis (base 511) = true :=
      (by rw [sig511_511_mul] at code; exact code : v.basis (base 511) = orig.basis (base 511)).trans
        (trace_last F.x F.x_pos F.x_lt orig.basis facts.trace)
    have in1542 : v.basis (base 1542) = false := bits _ (by simp [FrontierEntry1591Native.workSites])
    have flags := canonical_flags orig.basis ctx F.Y 0 v input
    let origin' := writeBit orig.basis (base 2400) true
    have ctx' := FrontierEntry1591.context_control_set orig.basis ctx true
    have ha' := FrontierEntry1591.source_zero_control_set orig.basis true facts.sourceZero
    have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
        SkywalkTrace.trace 512 (SkywalkRails.encode false false (F.x : Int) (p : Int)) := by
      rw [FrontierEntry1591.trace_control_set]; exact facts.trace
    have input' := Rolling1588.canonical_control_set orig.basis F.Y 0 v true input
    have en' : origin' (base 2400) = true := by simp [origin', writeBit]
    have codes := Rolling1588.canonical_prefix_codes origin' ctx' F.Y 0 (force v) input' F.x F.x_pos F.x_lt trace'
    have clean := FourScratchWindow.canonical_clean origin' ctx' ha' F.Y (force v) input' codes.1 codes.2.1
    have z768 := Rolling1588.canonical_768_zero origin' ctx' F.Y 0 (force v) input'
    have hpb_fv : ∀ q, Off q → (pullIn b4).basis q = (force v).basis q := by
      intro q hq
      have hb4_eq : b4 = run (StairSchedule.fieldRename FourScratchWindow.clearProgram)
          (mRest.drop (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX)))
          (run (StairSchedule.paritySetup ++ StairSchedule.hostedX)
            (mRest.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX))) v) := by
        have hsh : P03 = StairField2V3Replay.exitReferenceOpening ++
            ((StairSchedule.paritySetup ++ StairSchedule.hostedX) ++
              StairSchedule.fieldRename FourScratchWindow.clearProgram) := by
          simp only [P03, List.append_assoc]
        dsimp only [b4]; rw [hsh, run_append, run_append, hopen, hv]
      rw [hb4_eq, field_pullIn]
      exact window_agree _ (force v) _ (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _)
        clean codes.2.2 z768 q hq.1 hq.2
    have hcore := mulHeadCore_step origin' ctx' ha' en' F.Y b4 (force v) m1 input' hpb_fv
    refine ⟨⟨m7, rfl⟩, ?_⟩
    rw [hcut7_eq, run_append P03, run_append P03]
    exact hcore
  -- Pin helpers for pieces 7, 11, 13, 15, 17, 19
  have pin7 : ∀ u, ∃ rec, FrameAt F.x 102 rec ∧ (if (0 : Nat) = 0 then run (cut (xps k) 7) u s = rec else AgreeOutside (Δv 0) (run (cut (xps k) 7) u s) rec) := by
    intro u
    have hcut4 : cut (xps k) 7 = StairField2V3Replay.exitReferenceOpening ++
        ((StairSchedule.paritySetup ++ StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram) ++
          liftF (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
            StairSchedule.placedEndPacket StairConcrete.bestLoans false 68)) := by
      rw [cut_succ (xps k) 6 (xL k 6 (by decide)), cut_succ (xps k) 5 (xL k 5 (by decide)),
          cut_succ (xps k) 4 (xL k 4 (by decide)), cut_succ (xps k) 3 (xL k 3 (by decide)),
          cut_succ (xps k) 2 (xL k 2 (by decide)), cut_succ (xps k) 1 (xL k 1 (by decide)),
          cut_succ (xps k) 0 (xL k 0 (by decide)), cut_zero,
          x0_L, x1_L, x2_L, x3_L, x4_L, x5_L, x6_L]
      simp only [liftF_append, List.nil_append, List.append_assoc]
    let mOpen := u.take (measurementCount StairField2V3Replay.exitReferenceOpening)
    let mTail := u.drop (measurementCount StairField2V3Replay.exitReferenceOpening)
    let mA := mTail.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram))
    let mB := mTail.drop (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram))
    have hopen : run StairField2V3Replay.exitReferenceOpening mOpen s =
        run (Rolling1588.firstPhase false) mOpen s :=
      first_phase_hosted false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
    obtain ⟨orig, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
      F.sharedNodup F.historyAbove F.selectorsAway F.x F.Y F.x_pos F.x_lt s mOpen F.input
    have ctx := Rolling1588Lifetime.prepared_context F.sharedNodup F.selectorsAway
      F.transcript F.x F.Y s orig facts legal F.selectorG_zero F.selectorS_zero
    have bits := Rolling1588Lifetime.first_clean false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
    have work := Rolling1588Lifetime.first_work_zero false F.sharedNodup F.x F.Y.val s mOpen F.input
    have parity := Rolling1588Lifetime.first_parity false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
    have input := frames false
    rw [lf_eq] at input bits work parity
    obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) mOpen s = v := ⟨_, rfl⟩
    rw [hv] at input bits work parity
    have code := Rolling1588Frame.canonical_special_at orig.basis F.Y 0 v 511 (by simp) input
    have in511 : v.basis (base 511) = true :=
      (by rw [sig511_511_mul] at code; exact code : v.basis (base 511) = orig.basis (base 511)).trans
        (trace_last F.x F.x_pos F.x_lt orig.basis facts.trace)
    have in1542 : v.basis (base 1542) = false := bits _ (by simp [FrontierEntry1591Native.workSites])
    have flags := canonical_flags orig.basis ctx F.Y 0 v input
    let origin' := writeBit orig.basis (base 2400) true
    have ctx' := FrontierEntry1591.context_control_set orig.basis ctx true
    have ha' := FrontierEntry1591.source_zero_control_set orig.basis true facts.sourceZero
    have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
        SkywalkTrace.trace 512 (SkywalkRails.encode false false (F.x : Int) (p : Int)) := by
      rw [FrontierEntry1591.trace_control_set]; exact facts.trace
    have input' := Rolling1588.canonical_control_set orig.basis F.Y 0 v true input
    have en' : origin' (base 2400) = true := by simp [origin', writeBit]
    have codes := Rolling1588.canonical_prefix_codes origin' ctx' F.Y 0 (force v) input' F.x F.x_pos F.x_lt trace'
    have clean := FourScratchWindow.canonical_clean origin' ctx' ha' F.Y (force v) input' codes.1 codes.2.1
    have z768 := Rolling1588.canonical_768_zero origin' ctx' F.Y 0 (force v) input'
    let mC := mB.take (measurementCount StairConcrete.bestLoans.center)
    let mRest := mB.drop (measurementCount StairConcrete.bestLoans.center)
    let mCopy := mRest.take (measurementCount HalfFieldOB5.copyN)
    let mEnd := mRest.drop (measurementCount HalfFieldOB5.copyN)
    let mB' := WindowFieldJourney.joinTapes (R2SqEp760.center760 ++ HalfFieldOB5.copyN)
      (WindowFieldJourney.joinTapes R2SqEp760.center760 [] mCopy) mEnd
    obtain ⟨X', Y', hcut102⟩ := headCore_frame origin' ctx' ha' en' F.Y (force v) input' mB'
    have hcore_eq : run (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
          StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) mB (force v) =
        run headCore mB' (force v) := by
      have hc_eq := StairBoundaryLoan.center760Loan_run_eq origin' ctx' ha' F.Y (force v) mC [] input'
      have hcopy_f := (Rolling1588HalfFieldOB5.copy_fill ctx'.hn origin' (F.Y / 2)
        (run R2SqEp760.center760 [] (force v)) mCopy
        (R2SqEp760.center760_frame origin' ctx' ha' F.Y (force v) [] input').2).2
      have hcopyN_eq : Rolling1588HalfFieldOB5.copyN = HalfFieldOB5.copyN := rfl
      rw [hcopyN_eq] at hcopy_f
      have he_eq : StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false := by
        simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true, if_false, if_true]
      have hctr_eq : StairConcrete.bestLoans.center = StairBoundaryLoan.center760Loan := rfl
      have hsplit_lhs : run (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
            StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) mB (force v) =
          run (StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) mEnd
            (run HalfFieldOB5.copyN mCopy (run StairConcrete.bestLoans.center mC (force v))) := by
        rw [List.append_assoc, run_append StairConcrete.bestLoans.center, run_append HalfFieldOB5.copyN]
      have hsplit_rhs : run headCore mB' (force v) =
          run (renameProgram (OB5.sig 511) (R2SqEp760.endPacket760 false)) mEnd
            (run HalfFieldOB5.copyN mCopy (run R2SqEp760.center760 [] (force v))) := by
        simp only [headCore, mB', WindowFieldJourney.joined]
      rw [hsplit_lhs, hsplit_rhs, hctr_eq, hc_eq, StairSchedule.placedEndPacket, he_eq]
      obtain ⟨s_cp, hs_cp⟩ : ∃ st, run HalfFieldOB5.copyN mCopy (run R2SqEp760.center760 [] (force v)) = st := ⟨_, rfl⟩
      rw [hs_cp] at hcopy_f ⊢
      apply pullState_sig511_injective
      rw [run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)),
          run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))]
      exact StairEndpointLoan44.endPacket760Loan44_run_eq false origin' ctx' en' (F.Y / 2) (F.Y / 2) rfl _ mEnd mEnd hcopy_f
    have hsub_core : wires (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
        StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) ⊆ wires headCore := by
      have hctr_eq : StairConcrete.bestLoans.center = StairBoundaryLoan.center760Loan := rfl
      have h1 : wires StairConcrete.bestLoans.center ⊆ wires R2SqEp760.center760 := by
        rw [hctr_eq]; exact StairLoanConverterSupport.center760Loan_sub
      have h2 : wires (StairSchedule.placedEndPacket StairConcrete.bestLoans false 68) ⊆
          wires (renameProgram (OB5.sig 511) (R2SqEp760.endPacket760 false)) := by
        have he_eq : StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false := by
          simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true, if_false, if_true]
        rw [StairSchedule.placedEndPacket, he_eq, renameProgram_support, renameProgram_support]
        exact Finset.image_subset_image (fun q hq => StairEndpointLoan44.endPacket760Loan44_support hq)
      simp only [headCore, wires_append]
      exact Finset.union_subset_union (Finset.union_subset_union h1 (Finset.Subset.refl _)) h2
    obtain ⟨sA, hsA⟩ : ∃ st, run (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram) mA v = st := ⟨_, rfl⟩
    have hrun7 : run (cut (xps k) 7) u s =
        run (liftF (StairConcrete.bestLoans.center ++ HalfFieldOB5.copyN ++
          StairSchedule.placedEndPacket StairConcrete.bestLoans false 68)) mB sA := by
      have hmO : u.take (measurementCount StairField2V3Replay.exitReferenceOpening) = mOpen := rfl
      have hmT : u.drop (measurementCount StairField2V3Replay.exitReferenceOpening) = mTail := rfl
      have hmA_eq : mTail.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
          StairSchedule.fieldRename FourScratchWindow.clearProgram)) = mA := rfl
      have hmB_eq : mTail.drop (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
          StairSchedule.fieldRename FourScratchWindow.clearProgram)) = mB := rfl
      rw [hcut4, run_append StairField2V3Replay.exitReferenceOpening, hmO, hmT, hopen, hv,
          run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
            StairSchedule.fieldRename FourScratchWindow.clearProgram), hmA_eq, hmB_eq, hsA]
    have hpre_ag : ∀ r, Off r → (pullIn sA).basis r = (force v).basis r := by
      intro r hr
      rw [← hsA, run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX), field_pullIn]
      exact window_agree _ (force v) _ (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _)
        clean codes.2.2 z768 r hr.1 hr.2
    have hloc := local_eq_of_sub₂ _ _ hsub_core (pullIn sA) (force v) mB mB'
      (fun r hr => hpre_ag r (headCore_off r hr)) hcore_eq
    refine ⟨run (cut (xps k) 7) u s, ?_, by simp only [if_true]⟩
    refine ⟨origin', X', Y', run headCore mB' (force v), ctx', en',
      ⟨F.x_pos, F.x_lt, trace', ctx'.legal⟩, hcut102, ?_⟩
    intro q hq
    rw [hrun7, pullIn_liftF, hloc]
    exact run_agree_offP _ headCore_off (pullIn sA) (force v) mB' hpre_ag q hq
  have pin_of_x {j B c : Nat} {Z YP : Program} (hBne : B ≠ 0) (hxcut : cut (xps k) j = StairField2V3Replay.exitReferenceOpening ++ Z)
      (hrch : ∃ Q, CRel (XPreX k F.x) (RowRelL k F.x B YP) Z Q)
      (hinv : ∀ t, ReachBy (ExitMiddleX k F.x) YP t → InvE F.x c t) :
      ∀ u, ∃ rec, FrameAt F.x c rec ∧ (if B = 0 then run (cut (xps k) j) u s = rec else AgreeOutside (Δv B) (run (cut (xps k) j) u s) rec) := by
    intro u
    rw [hxcut, run_append]
    obtain ⟨Q, hcr⟩ := hrch
    obtain ⟨_, hrel, hreach⟩ := hcr _ _ ⟨⟨s, F, rfl, _, rfl⟩, rfl⟩ _
    exact ⟨_, WindowFieldView.exitFrame c F.x _ (hinv _ hreach), by simp only [hBne, if_false]; exact hrel.1⟩
  have pin11 := pin_of_x (by decide) (xcut11 k) (rch11 k F.x (StairOpenWiring.exitPlans k F.x) StairOpenWiring.half760)
    (fun t ht => StairField2V3ExitRec.reach_head k F.x t (reachX_head StairOpenWiring.half760 k F.x t ht))
  have pin13 := pin_of_x (by decide) (xcut13 k) (rch13 k F.x (StairOpenWiring.exitPlans k F.x) StairOpenWiring.half760)
    (fun t ht => StairField2V3ExitRec.reach_YA k F.x t (reachX_A StairOpenWiring.half760 k F.x t ht))
  have pin15 := pin_of_x (by decide) (xcut15 k) (rch15 k F.x (StairOpenWiring.exitPlans k F.x) StairOpenWiring.half760)
    (fun t ht => StairField2V3ExitRec.reach_YB k F.x t (reachX_B StairOpenWiring.half760 k F.x t ht))
  have pin17 := pin_of_x (by decide) (xcut17 k) (rch17 k F.x (StairOpenWiring.exitPlans k F.x) StairOpenWiring.half760)
    (fun t ht => StairField2V3ExitRec.reach_YC k F.x t (reachX_C StairOpenWiring.half760 k F.x t ht))
  have pin19 := pin_of_x (by decide) (xcut19 k) (rch19 k F.x (StairOpenWiring.exitPlans k F.x) StairOpenWiring.half760)
    (fun t ht => StairField2V3ExitRec.reach_YD k F.x t (reachX_D StairOpenWiring.half760 k F.x t ht))
  have s7 := step_grp 7 0 43 100 2 (by decide) (x7_L k) (Or.inl rfl) (fun h => absurd rfl h) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inl rfl) pin7
  have s8 := step_disj 8 (by decide) _ (x8_L k) (disjoint_ryWires_append (disjoint_ryWires_fieldRename unprefix_notRY) paritySetup_notRY)
  have s9 := step_disj 9 (by decide) _ (x9_L k) (disjoint_ryWires_append hostedX_notRY (disjoint_ryWires_fieldRename clearProgram_notRY))
  have s10 := step_disj 10 (by decide) _ (x10_L k) (disjoint_ryWires_liftF reverseLast_notRY)
  have s11 := step_grp 11 12 41 98 2 (by decide) (x11_L k) (Or.inr (by decide)) (fun _ => by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin11
  have s12 := step_disj 12 (by decide) _ (x12_L k) (disjoint_ryWires_liftF reverse490_notRY)
  have s13 := step_grp 13 22 36 96 2 (by decide) (x13_L k) (Or.inr (by decide)) (fun _ => by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin13
  have s14 := step_disj 14 (by decide) _ (x14_L k) (disjoint_ryWires_liftF reverse480_notRY)
  have s15 := step_grp 15 32 30 93 3 (by decide) (x15_L k) (Or.inr (by decide)) (fun _ => by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin15
  have s16 := step_disj 16 (by decide) _ (x16_L k) (disjoint_ryWires_liftF reverse465_notRY)
  have s17 := step_grp 17 47 22 90 3 (by decide) (x17_L k) (Or.inr (by decide)) (fun _ => by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin17
  have s18 := step_disj 18 (by decide) _ (x18_L k) (disjoint_ryWires_liftF reverse450_notRY)
  have s19 := step_grp 19 62 13 85 5 (by decide) (x19_L k) (Or.inr (by decide)) (fun _ => by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin19
  have s20 := step_disj 20 (by decide) _ (x20_L k) (disjoint_ryWires_liftF reverse425_notRY)
  have c11 : ∀ (a b : State) (m' : List Bool), MulCut 11 a b →
      ∃ b', MulCut 13 (run (liftF (PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨rec, hframe, hagree⟩ := pin11 u
    have hcl11 : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 42 ++
          OddFullPass.P1LifeLoan.hostPlan1542.group false 42 98 (1 + 1)).map StairField13V3.lowMap,
        (run (cut (xps k) 11) u s).basis q = false := by
      intro q hq
      apply exitGroupsBefore_xps k 11 41 98 (1 + 1) (by simp) s ⟨F⟩ u q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 41 ≤ 42)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 41 98 (1 + 1) (by decide) w hh)
    have hrh11 : ∀ i, History5.historyMap (PackCutExitRows.segW 490) (5 * 98) i ∉
        StairSchedule.exclusiveRoles.drop 42 ++ OddFullPass.P1LifeLoan.hostPlan1542.group false 42 98 (1 + 1) := by
      intro i hm
      apply PackCutExitInst.rh4 i
      rcases List.mem_append.mp hm with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 41 ≤ 42)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 41 98 (1 + 1) (by decide) _ hh)
    obtain ⟨m2, heq⟩ := PackCutOddExit.oddCutRow_runeq 42 98 1 12 F.x (by decide) (by decide)
      (by decide) (Or.inr (by decide))
      (fun _ => StairField2V3Groups.groups_avoid_payload false 12 (by decide) (1 + 1) 98 (by decide))
      a (run (cut (xps k) 11) u s) rec hrel hframe hagree
      hcl11
      (hostPlan1542_group_notRY false 41 98 (1 + 1) (by decide))
      (History5.historyMap (PackCutExitRows.segW 490) (5 * 98)) PackCutExitRows.inj4 PackCutExitInst.sig4
      hrh11 PackCutExitInst.off4 (fun i _ => PackCutExitInst.fp4 i) (by decide +kernel)
      PackCutExitInst.rs4 PackCutExitInst.fix4
      _ _ _ PackCutExitRows.seg4 PackCutExitRows.mid4 PackCutOddExit.hep4_1542 m'
    have hseg' : StairField2V3Entry.liftF (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 22 12 490 500) =
        StairField2V3ExitPlan.rseg cp 22 12 490 500 := rfl
    have heq' : run (liftF (PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1)) m' a = _ := heq
    rw [heq', hseg', run_append]
    exact ⟨_, s12 _ _ _ (s11 _ _ _ ⟨⟨u, rfl⟩, hrel⟩)⟩
  have c13 : ∀ (a b : State) (m' : List Bool), MulCut 13 a b →
      ∃ b', MulCut 15 (run (liftF (PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨rec, hframe, hagree⟩ := pin13 u
    have hcl13 : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 37 ++
          OddFullPass.P1LifeLoan.hostPlan1542.group false 37 96 (1 + 1)).map StairField13V3.lowMap,
        (run (cut (xps k) 13) u s).basis q = false := by
      intro q hq
      apply exitGroupsBefore_xps k 13 36 96 (1 + 1) (by simp) s ⟨F⟩ u q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 36 ≤ 37)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 36 96 (1 + 1) (by decide) w hh)
    have hrh13 : ∀ i, History5.historyMap (PackCutExitRows.segW 480) (5 * 96) i ∉
        StairSchedule.exclusiveRoles.drop 37 ++ OddFullPass.P1LifeLoan.hostPlan1542.group false 37 96 (1 + 1) := by
      intro i hm
      apply PackCutExitInst.rh3 i
      rcases List.mem_append.mp hm with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 36 ≤ 37)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 36 96 (1 + 1) (by decide) _ hh)
    obtain ⟨m2, heq⟩ := PackCutOddExit.oddCutRow_runeq 37 96 1 22 F.x (by decide) (by decide)
      (by decide) (Or.inr (by decide))
      (fun _ => StairField2V3Groups.groups_avoid_payload false 22 (by decide) (1 + 1) 96 (by decide))
      a (run (cut (xps k) 13) u s) rec hrel hframe hagree
      hcl13
      (hostPlan1542_group_notRY false 36 96 (1 + 1) (by decide))
      (History5.historyMap (PackCutExitRows.segW 480) (5 * 96)) PackCutExitRows.inj3 PackCutExitInst.sig3
      hrh13 PackCutExitInst.off3 (fun i _ => PackCutExitInst.fp3 i) (by decide +kernel)
      PackCutExitInst.rs3 PackCutExitInst.fix3
      _ _ _ PackCutExitRows.seg3 PackCutExitRows.mid3 PackCutOddExit.hep3_1542 m'
    have hseg' : StairField2V3Entry.liftF (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 32 22 480 490) =
        StairField2V3ExitPlan.rseg cp 32 22 480 490 := rfl
    have heq' : run (liftF (PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1)) m' a = _ := heq
    rw [heq', hseg', run_append]
    exact ⟨_, s14 _ _ _ (s13 _ _ _ ⟨⟨u, rfl⟩, hrel⟩)⟩
  have c15 : ∀ (a b : State) (m' : List Bool), MulCut 15 a b →
      ∃ b', MulCut 17 (run (liftF (PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨rec, hframe, hagree⟩ := pin15 u
    have hcl15 : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 31 ++
          OddFullPass.P1LifeLoan.hostPlan1542.group false 31 93 (2 + 1)).map StairField13V3.lowMap,
        (run (cut (xps k) 15) u s).basis q = false := by
      intro q hq
      apply exitGroupsBefore_xps k 15 30 93 (2 + 1) (by simp) s ⟨F⟩ u q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 30 ≤ 31)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 30 93 (2 + 1) (by decide) w hh)
    have hrh15 : ∀ i, History5.historyMap (PackCutExitRows.segW 465) (5 * 93) i ∉
        StairSchedule.exclusiveRoles.drop 31 ++ OddFullPass.P1LifeLoan.hostPlan1542.group false 31 93 (2 + 1) := by
      intro i hm
      apply PackCutExitInst.rh2 i
      rcases List.mem_append.mp hm with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 30 ≤ 31)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 30 93 (2 + 1) (by decide) _ hh)
    obtain ⟨m2, heq⟩ := PackCutOddExit.oddCutRow_runeq 31 93 2 32 F.x (by decide) (by decide)
      (by decide) (Or.inr (by decide))
      (fun _ => StairField2V3Groups.groups_avoid_payload false 32 (by decide) (2 + 1) 93 (by decide))
      a (run (cut (xps k) 15) u s) rec hrel hframe hagree
      hcl15
      (hostPlan1542_group_notRY false 30 93 (2 + 1) (by decide))
      (History5.historyMap (PackCutExitRows.segW 465) (5 * 93)) PackCutExitRows.inj2 PackCutExitInst.sig2
      hrh15 PackCutExitInst.off2 (fun i _ => PackCutExitInst.fp2 i) (by decide +kernel)
      PackCutExitInst.rs2 PackCutExitInst.fix2
      _ _ _ PackCutExitRows.seg2 PackCutExitRows.mid2 PackCutOddExit.hep2_1542 m'
    have hseg' : StairField2V3Entry.liftF (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 47 32 465 480) =
        StairField2V3ExitPlan.rseg cp 47 32 465 480 := rfl
    have heq' : run (liftF (PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2)) m' a = _ := heq
    rw [heq', hseg', run_append]
    exact ⟨_, s16 _ _ _ (s15 _ _ _ ⟨⟨u, rfl⟩, hrel⟩)⟩
  have c17 : ∀ (a b : State) (m' : List Bool), MulCut 17 a b →
      ∃ b', MulCut 19 (run (liftF (PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨rec, hframe, hagree⟩ := pin17 u
    have hcl17 : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 23 ++
          OddFullPass.P1LifeLoan.hostPlan1542.group false 23 90 (2 + 1)).map StairField13V3.lowMap,
        (run (cut (xps k) 17) u s).basis q = false := by
      intro q hq
      apply exitGroupsBefore_xps k 17 22 90 (2 + 1) (by simp) s ⟨F⟩ u q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 22 ≤ 23)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 22 90 (2 + 1) (by decide) w hh)
    have hrh17 : ∀ i, History5.historyMap (PackCutExitRows.segW 450) (5 * 90) i ∉
        StairSchedule.exclusiveRoles.drop 23 ++ OddFullPass.P1LifeLoan.hostPlan1542.group false 23 90 (2 + 1) := by
      intro i hm
      apply PackCutExitInst.rh1 i
      rcases List.mem_append.mp hm with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 22 ≤ 23)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 22 90 (2 + 1) (by decide) _ hh)
    obtain ⟨m2, heq⟩ := PackCutOddExit.oddCutRow_runeq 23 90 2 47 F.x (by decide) (by decide)
      (by decide) (Or.inr (by decide))
      (fun _ => StairField2V3Groups.groups_avoid_payload false 47 (by decide) (2 + 1) 90 (by decide))
      a (run (cut (xps k) 17) u s) rec hrel hframe hagree
      hcl17
      (hostPlan1542_group_notRY false 22 90 (2 + 1) (by decide))
      (History5.historyMap (PackCutExitRows.segW 450) (5 * 90)) PackCutExitRows.inj1 PackCutExitInst.sig1
      hrh17 PackCutExitInst.off1 (fun i _ => PackCutExitInst.fp1 i) (by decide +kernel)
      PackCutExitInst.rs1 PackCutExitInst.fix1
      _ _ _ PackCutExitRows.seg1 PackCutExitRows.mid1 PackCutOddExit.hep1_1542 m'
    have hseg' : StairField2V3Entry.liftF (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 62 47 450 465) =
        StairField2V3ExitPlan.rseg cp 62 47 450 465 := rfl
    have heq' : run (liftF (PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2)) m' a = _ := heq
    rw [heq', hseg', run_append]
    exact ⟨_, s18 _ _ _ (s17 _ _ _ ⟨⟨u, rfl⟩, hrel⟩)⟩
  have c19 : ∀ (a b : State) (m' : List Bool), MulCut 19 a b →
      ∃ b', MulCut 21 (run (liftF (PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨rec, hframe, hagree⟩ := pin19 u
    have hcl19 : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 14 ++
          OddFullPass.P1LifeLoan.hostPlan1542.group false 14 85 (4 + 1)).map StairField13V3.lowMap,
        (run (cut (xps k) 19) u s).basis q = false := by
      intro q hq
      apply exitGroupsBefore_xps k 19 13 85 (4 + 1) (by simp) s ⟨F⟩ u q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 13 ≤ 14)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 13 85 (4 + 1) (by decide) w hh)
    have hrh19 : ∀ i, History5.historyMap (PackCutExitRows.segW 425) (5 * 85) i ∉
        StairSchedule.exclusiveRoles.drop 14 ++ OddFullPass.P1LifeLoan.hostPlan1542.group false 14 85 (4 + 1) := by
      intro i hm
      apply PackCutExitInst.rh0 i
      rcases List.mem_append.mp hm with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 13 ≤ 14)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub false 13 85 (4 + 1) (by decide) _ hh)
    obtain ⟨m2, heq⟩ := PackCutOddExit.oddCutRow_runeq 14 85 4 62 F.x (by decide) (by decide)
      (by decide) (Or.inr (by decide))
      (fun _ => StairField2V3Groups.groups_avoid_payload false 62 (by decide) (4 + 1) 85 (by decide))
      a (run (cut (xps k) 19) u s) rec hrel hframe hagree
      hcl19
      (hostPlan1542_group_notRY false 13 85 (4 + 1) (by decide))
      (History5.historyMap (PackCutExitRows.segW 425) (5 * 85)) PackCutExitRows.inj0 PackCutExitInst.sig0
      hrh19 PackCutExitInst.off0 (fun i _ => PackCutExitInst.fp0 i) (by decide +kernel)
      PackCutExitInst.rs0 PackCutExitInst.fix0
      _ _ _ PackCutExitRows.seg0 PackCutExitRows.mid0 PackCutOddExit.hep0_1542 m'
    have hseg' : StairField2V3Entry.liftF (StairSchedule.reverseSegment StairConcreteAssembly.checkpointPrimitives 87 62 425 450) =
        StairField2V3ExitPlan.rseg cp 87 62 425 450 := rfl
    have heq' : run (liftF (PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4)) m' a = _ := heq
    rw [heq', hseg', run_append]
    exact ⟨_, s20 _ _ _ (s19 _ _ _ ⟨⟨u, rfl⟩, hrel⟩)⟩
  have hshape21p : stockOddMulPrefix21 =
      ((((((((((StairField2V3Replay.exitReferenceOpening ++ StairSchedule.paritySetup ++
        StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram) ++
        liftF (OddFullPass.HalfConvertOdd.center760OddLoan ++ HalfFieldOB5.copyN ++
          renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44)) ++
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 44 100 2)) ++
        (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup)) ++
        (StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram)) ++
        liftF (StairSchedule.reverseLast cp)) ++
        liftF (PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1)) ++
        liftF (PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1)) ++
        liftF (PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2)) ++
        liftF (PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2)) ++
        liftF (PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4) := by
    have hfr_bor (P : Program) : StairSchedule.fieldRename (renameProgram Prefix1590.borrow P) = liftF P := rfl
    simp only [stockOddMulPrefix21, stockOddMulLeading, stockOddMulBeforeParity, stockOddMulBeforeGroup,
      OddFullPass.P1LifeLoan.exitLowPrefixOdd, OddFullPass.P1LifeLoan.exitHeadPrefixOdd,
      fieldRename_append, Six505.rename_append, hfr_bor, liftF_append, List.append_assoc]
    rw [← ExteriorPorts.placedShape (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 44 100 2)]
    simp only [hfr_bor]
  have hchain21p (s7_ : State) (m7 m8 m9 m10 m11 m13 m15 m17 m19 : List Bool)
      (h7 : ∃ b7, MulCut 7 s7_ b7) :
      ∃ b21, MulCut 21
        (run (liftF (PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4)) m19
        (run (liftF (PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2)) m17
        (run (liftF (PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2)) m15
        (run (liftF (PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1)) m13
        (run (liftF (PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1)) m11
        (run (liftF (StairSchedule.reverseLast cp)) m10
        (run (StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram) m9
        (run (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup) m8
        (run (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 44 100 2)) m7 s7_))))))))) b21 := by
    obtain ⟨b7, d7⟩ := h7
    have d8 := s7 _ _ m7 d7
    have d9 := s8 _ _ m8 d8
    have d10 := s9 _ _ m9 d9
    have d11 := s10 _ _ m10 d10
    obtain ⟨b13, d13⟩ := c11 _ _ m11 d11
    obtain ⟨b15, d15⟩ := c13 _ _ m13 d13
    obtain ⟨b17, d17⟩ := c15 _ _ m15 d15
    obtain ⟨b19, d19⟩ := c17 _ _ m17 d17
    exact c19 _ _ m19 d19
  have hd21 : ∃ b21, MulCut 21 a21 b21 := by
    change ∃ b21, MulCut 21 (run stockOddMulPrefix21 m s) b21
    rw [hshape21p,
        run_append _ (liftF (PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4)),
        run_append _ (liftF (PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2)),
        run_append _ (liftF (PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2)),
        run_append _ (liftF (PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1)),
        run_append _ (liftF (PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1)),
        run_append _ (liftF (StairSchedule.reverseLast cp)),
        run_append _ (StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram),
        run_append _ (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup),
        run_append _ (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 44 100 2))]
    exact hchain21p _ _ _ _ _ _ _ _ _ _ ⟨_, hcut7 _⟩
  obtain ⟨b21, ⟨u21, hb21⟩, hrel21⟩ := hd21
  rw [hb21] at hrel21
  obtain ⟨⟨rec, hframe, hagree, hcv, hwin⟩, hloan⟩ := exitCut21_pin_loan_full k F u21
  obtain ⟨origin, ctx, en, tr, ocut⟩ :=
    odd_cut_ocut 85 (by decide) (by decide) F.x a21 (run (cut (xps k) 21) u21 s) rec hrel21 hframe hagree hloan
  exact ⟨⟨u21, hrel21⟩, origin, ctx, en, tr, ocut,
    odd_cut_tagReady F.x F.x_pos F.x_lt a21 (run (cut (xps k) 21) u21 s) rec hrel21 hagree hcv hwin⟩


/-- Explicit frame at multiplication cut 23 (`run (exitReferenceOpening ++ (YE ++ grpF 1 84) ++ fieldRename unprefix)`)! -/
private theorem mul_cut23_frame (k : Nat) {s : State} (F : ExitFrame k s) (mOpen mBody : List Bool) :
    ∃ (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
      (en : origin (base 2400) = true)
      (tr : skywalkTapeControls origin (skywalkSharedTape base) =
        SkywalkTrace.trace 512 (SkywalkRails.encode false false (F.x : Int) (p : Int)))
      (s23 : State),
      Rolling1588Frame.EncodedFieldFrame true origin (Rolling1588.exitHeadPayload origin F.Y).1
        (Rolling1588.exitHeadPayload origin F.Y).2 s23 ∧
      (∀ q, q ∉ E →
        (pullState fieldMap (run ((YE ++ StairField2V3ExitPlan.grpF 1 84) ++ StairSchedule.fieldRename FourScratchWindow.unprefix) mBody
          (run StairField2V3Replay.exitReferenceOpening mOpen s))).basis q = s23.basis q) := by
  have hopen : run StairField2V3Replay.exitReferenceOpening mOpen s =
      run (Rolling1588.firstPhase false) mOpen s :=
    first_phase_hosted false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
  rw [hopen]
  obtain ⟨orig, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
    F.sharedNodup F.historyAbove F.selectorsAway F.x F.Y F.x_pos F.x_lt s mOpen F.input
  have ctx := Rolling1588Lifetime.prepared_context F.sharedNodup F.selectorsAway
    F.transcript F.x F.Y s orig facts legal F.selectorG_zero F.selectorS_zero
  have bits := Rolling1588Lifetime.first_clean false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
  have work := Rolling1588Lifetime.first_work_zero false F.sharedNodup F.x F.Y.val s mOpen F.input
  have parity := Rolling1588Lifetime.first_parity false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
  have input := frames false
  rw [lf_eq] at input bits work parity
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) mOpen s = v := ⟨_, rfl⟩
  rw [hv] at input bits work parity ⊢
  have code := Rolling1588Frame.canonical_special_at orig.basis F.Y 0 v 511 (by simp) input
  have in511 : v.basis (base 511) = true :=
    (by rw [sig511_511_mul] at code; exact code : v.basis (base 511) = orig.basis (base 511)).trans
      (trace_last F.x F.x_pos F.x_lt orig.basis facts.trace)
  have in1542 : v.basis (base 1542) = false := bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := canonical_flags orig.basis ctx F.Y 0 v input
  let origin' := writeBit orig.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set orig.basis ctx true
  have ha' := FrontierEntry1591.source_zero_control_set orig.basis true facts.sourceZero
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (F.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]; exact facts.trace
  have input' := Rolling1588.canonical_control_set orig.basis F.Y 0 v true input
  have en' : origin' (base 2400) = true := by simp [origin', writeBit]
  -- Show `(YE ++ grpF 1 84) ++ fieldRename unprefix = (paritySetup ++ hostedX) ++ fieldRename (clearProgram ++ renameProgram borrow exitHead ++ unprefix)`!
  have hgrp_split (j a b : Nat) :
      Rolling1588.groups false (j + a) b ++ Rolling1588.groups false j a = Rolling1588.groups false j (a + b) := by
    induction a generalizing j with
    | zero => simp [Rolling1588.groups, PacketSequence.program]
    | succ a ih =>
      have h1 : a + 1 + b = (a + b) + 1 := by omega
      rw [h1]
      simp only [Rolling1588.groups, PacketSequence.program, Bool.false_eq_true, if_false, ← List.append_assoc]
      have h2 := ih (j + 1)
      rw [show j + 1 + a = j + (a + 1) by omega] at h2
      simp only [Rolling1588.groups] at h2
      rw [h2]
  have h101 : Rolling1588.groups false 100 2 ++ Rolling1588.groups false 98 2 ++
      Rolling1588.groups false 96 2 ++ Rolling1588.groups false 93 3 ++
      Rolling1588.groups false 90 3 ++ Rolling1588.groups false 85 5 ++
      Rolling1588.groups false 1 84 = Rolling1588.groups false 1 101 := by
    rw [hgrp_split 98 2 2, hgrp_split 96 2 4, hgrp_split 93 3 6,
        hgrp_split 90 3 9, hgrp_split 85 5 12, hgrp_split 1 84 17]
  let W := FourScratchWindow.clearProgram ++ (renameProgram Prefix1590.borrow Rolling1588.exitHead ++ FourScratchWindow.unprefix)
  let mS := mBody.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX))
  let mW := mBody.drop (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX))
  have hbody : (YE ++ StairField2V3ExitPlan.grpF 1 84) ++ StairSchedule.fieldRename FourScratchWindow.unprefix =
      (StairSchedule.paritySetup ++ StairSchedule.hostedX) ++ StairSchedule.fieldRename W := by
    have hYE : YE ++ StairField2V3ExitPlan.grpF 1 84 = (StairSchedule.paritySetup ++ StairSchedule.hostedX) ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram ++ liftF Rolling1588.exitHead := by
      rw [Rolling1588.exitHead, ← h101]
      simp only [YE, YD, YC, YB, YA, StairField2V3ExitPlan.headE, StairField2V3ExitPlan.grpF, liftF, headCore,
        fieldRename_append, Six505.rename_append, List.append_assoc]
    rw [hYE]
    simp only [W, liftF, fieldRename_append, List.append_assoc]
  have hmS : mBody.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX)) = mS := rfl
  have hmW : mBody.drop (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX)) = mW := rfl
  rw [hbody, run_append, hmS, hmW]
  have hW_avoidE : ∀ q ∈ E, q ∉ wires W := by
    have hcl_notE : StairWireCheck.allSites (fun q => !(decide (q ∈ E))) FourScratchWindow.clearProgram = true := by decide +kernel
    have hun_notE : StairWireCheck.allSites (fun q => !(decide (q ∈ E))) FourScratchWindow.unprefix = true := by decide +kernel
    have hbor_E : ∀ q ∈ E, Prefix1590.borrow q = q := by
      have h : E.all (fun q => decide (Prefix1590.borrow q = q)) = true := by decide +kernel
      intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)
    intro q hE hq
    simp only [W, wires_append, Finset.mem_union] at hq
    rcases hq with h1 | h2 | h3
    · have := StairWireCheck.allSites_sound _ _ hcl_notE q h1; simp [hE] at this
    · rw [renameProgram_support] at h2
      obtain ⟨r, hr, heq⟩ := Finset.mem_image.mp h2
      have hrq : r = q := Prefix1590.borrow.injective (heq.trans (hbor_E q hE).symm)
      exact (exitHead_avoid r hr).1 (hrq ▸ hE)
    · have := StairWireCheck.allSites_sound _ _ hun_notE q h3; simp [hE] at this
  have hrun_W : run W mW (force v) = run Rolling1588.exitHead (mW.drop 6) (force v) := by
    have hres := Rolling1588.exitHead_frame origin' ctx' ha' en' F.Y (force v) (mW.drop 6) input'
    have hbef := Rolling1588.canonical_prefix_codes origin' ctx' F.Y 0 (force v) input' F.x F.x_pos F.x_lt trace'
    have haft := Rolling1588.field_prefix_codes origin' ctx' _ _ _ hres.2 F.x F.x_pos F.x_lt trace'
    exact FourScratchWindow.window_run_eq Rolling1588.exitHead W rfl Rolling1588.exitHead_payload_free
      (force v) mW
      (FourScratchWindow.canonical_clean origin' ctx' ha' F.Y (force v) input' hbef.1 hbef.2.1)
      (FourScratchWindow.field_clean origin' ctx' _ _ _ hres.2 haft.1 haft.2.1)
      (Rolling1588.canonical_768_zero origin' ctx' F.Y 0 (force v) input')
      (Rolling1588.field_768_zero origin' ctx' _ _ _ hres.2) hbef.2.2
  have hframe23 := (Rolling1588.exitHead_frame origin' ctx' ha' en' F.Y (force v) (mW.drop 6) input').2
  obtain ⟨rS, hrS⟩ : ∃ st, run (StairSchedule.paritySetup ++ StairSchedule.hostedX) mS v = st := ⟨_, rfl⟩
  have hS_ag : ∀ q, q ∉ E → (pullState fieldMap rS).basis q = (force v).basis q := fun q hq => by
    rw [pullState_fieldMap_basis]
    have h := hosted_agree_force v flags.1 in511 flags.2 in1542 work parity mS q hq
    rwa [hrS] at h
  refine ⟨origin', ctx', en', trace', run Rolling1588.exitHead (mW.drop 6) (force v), hframe23, ?_⟩
  intro q hq
  rw [hrS, fieldRename_eq, run_rename fieldMap fieldMap_injective, ← hrun_W]
  exact run_agree_off W hW_avoidE (pullState fieldMap rS) (force v) mW hS_ag q hq

/-- Full multiplication head lockstep: `AgreeOutsideR` + `regValue fieldR = oddWord (Y * x / 2)`
between `stockOddMulHead` and `WindowMiddleContract.oldMulHead`! -/
theorem stockOddMulHead_agree_oldMulHead (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    ∃ n, AgreeOutsideR (run stockOddMulHead m s) (run WindowMiddleContract.oldMulHead n s) ∧
      regValue fieldR (run stockOddMulHead m s).basis = P1Life.oddWord (F.Y * (F.x : Fp) / 2) := by
  -- Step 1: replace `mulLead` by `exitReferenceOpening` on `stockOddMulHead`!
  have hlead_eq : run stockOddMulHead m s =
      run ((((stockOddMulPrefix21 ++ renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84)) ++
        StairSchedule.fieldRename FourScratchWindow.unprefix) ++
        StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false)) ++
        renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack) m s := by
    have h1 : stockOddMulHead = (Stair44Kernel.mulLead ++
        (stockOddMulLeading ++ renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84) ++
          StairSchedule.fieldRename FourScratchWindow.unprefix ++
          StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false) ++
          renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack)) := by
      simp only [stockOddMulHead, stockOddMulAfterGroup, fieldRename_append, List.append_assoc]
    have h2 : ((((stockOddMulPrefix21 ++ renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84)) ++
        StairSchedule.fieldRename FourScratchWindow.unprefix) ++
        StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false)) ++
        renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack) =
        StairField2V3Replay.exitReferenceOpening ++
        (stockOddMulLeading ++ renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84) ++
          StairSchedule.fieldRename FourScratchWindow.unprefix ++
          StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false) ++
          renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack) := by
      simp only [stockOddMulPrefix21, List.append_assoc]
    rw [h1, h2, run_append Stair44Kernel.mulLead, run_append StairField2V3Replay.exitReferenceOpening,
        WindowStockHead.leadM k F, WindowStockHead.countM]
  rw [hlead_eq]
  let P21 := stockOddMulPrefix21
  let POg := renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84)
  let PUn := StairSchedule.fieldRename FourScratchWindow.unprefix
  let PFp := StairSchedule.fieldRename (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false)
  let PFu := renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack
  let m1234 := m.take (measurementCount (((P21 ++ POg) ++ PUn) ++ PFp))
  let m25 := m.drop (measurementCount (((P21 ++ POg) ++ PUn) ++ PFp))
  let m123 := m1234.take (measurementCount ((P21 ++ POg) ++ PUn))
  let mFp := m1234.drop (measurementCount ((P21 ++ POg) ++ PUn))
  let m12 := m123.take (measurementCount (P21 ++ POg))
  let mUn := m123.drop (measurementCount (P21 ++ POg))
  let m21 := m12.take (measurementCount P21)
  let mOg := m12.drop (measurementCount P21)
  have hsplit5 : run ((((P21 ++ POg) ++ PUn) ++ PFp) ++ PFu) m s =
      run PFu m25 (run PFp mFp (run PUn mUn (run POg mOg (run P21 m21 s)))) := by
    rw [run_append (((P21 ++ POg) ++ PUn) ++ PFp),
        run_append ((P21 ++ POg) ++ PUn),
        run_append (P21 ++ POg),
        run_append P21]
  rw [hsplit5]
  -- Cut 21: `stockOddMul_cut21` gives `u21` with `OddRel a21 (run (cut (xps k) 21) u21 s)`!
  obtain ⟨⟨u21, hrel21⟩, _⟩ := stockOddMul_cut21 k F m21
  let a21 := run P21 m21 s
  let a22 := run POg mOg a21
  let a23 := run PUn mUn a22
  let a24 := run PFp mFp a23
  -- Piece 21: `ogroup false 1 84` vs `grpFL bestLoans 0 1 84`!
  obtain ⟨⟨rec21, hframe21, hagree21⟩, hloan21⟩ := exitCut21_pin_loan k F u21
  have hgrpFL0_eq : grpFL StairConcrete.bestLoans 0 1 84 =
      liftF (renameProgram (OB5.sig 511) (StairGroups.groups false 0 1 84)) := rfl
  have hclIn21 : ∀ q ∈ (StairSchedule.exclusiveRoles ++ hostPlan.group false 0 1 84).map lowMap,
      (run (cut (xps k) 21) u21 s).basis q = false := by
    intro q hq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
    rw [hp_group false 0 1 84 (by decide)] at hw
    rw [show lowMap w = fieldPlace w from rfl]
    exact hloan21 w hw
  have hclOut21' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 0).map lowMap,
      (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups false 0 1 84))) mOg (run (cut (xps k) 21) u21 s)).basis q = false :=
    cleanCut_after (exitGroupsRolesAfter_xps k 21 0 1 84 (by simp))
      (by rw [cut_succ (xps k) 21 (xL k 21 (by decide)), x21_L, hgrpFL0_eq]) s ⟨F⟩ u21 mOg
  have hclOut21 : ∀ q ∈ StairSchedule.exclusiveRoles.map lowMap,
      (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups false 0 1 84))) mOg (run (cut (xps k) 21) u21 s)).basis q = false :=
    fun q hq => hclOut21' q (by simpa only [List.drop_zero] using hq)
  have hrel22 := odd_ogroup84_step false F.x a21 (run (cut (xps k) 21) u21 s) rec21 mOg hrel21 hframe21 hagree21 hclIn21 hclOut21
  rw [← hgrpFL0_eq] at hrel22
  let u22 := WindowFieldJourney.joinTapes (cut (xps k) 21) u21 mOg
  have hb22 : run (grpFL StairConcrete.bestLoans 0 1 84) mOg (run (cut (xps k) 21) u21 s) = run (cut (xps k) 22) u22 s := by
    rw [cut_succ (xps k) 21 (xL k 21 (by decide)), x21_L, WindowFieldJourney.joined]
  rw [hb22] at hrel22
  -- Piece 22: `fieldRename FourScratchWindow.unprefix` (disjoint from `ryWires`)!
  have hrel23 := oddRel_disjoint PUn (disjoint_ryWires_fieldRename unprefix_notRY) hrel22 mUn
  let u23 := WindowFieldJourney.joinTapes (cut (xps k) 22) u22 mUn
  have hb23 : run PUn mUn (run (cut (xps k) 22) u22 s) =
      run (cut (xps k) 23) u23 s := by
    rw [cut_succ (xps k) 22 (xL k 22 (by decide)), x22_L, WindowFieldJourney.joined]
  rw [hb23] at hrel23
  -- Piece 23: relate `b23 = run (cut (xps k) 23) u23 s` to `s23` (`EncodedFieldFrame true origin (exitHeadPayload origin F0.Y)`) via `rch21` + `mul_cut23_frame`!
  have h23_pin : ∃ (Y0 : Fp) (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
      (en : origin (base 2400) = true)
      (tr : skywalkTapeControls origin (skywalkSharedTape base) =
        SkywalkTrace.trace 512 (SkywalkRails.encode false false (F.x : Int) (p : Int)))
      (s23 : State),
      Rolling1588Frame.EncodedFieldFrame true origin (Rolling1588.exitHeadPayload origin Y0).1
        (Rolling1588.exitHeadPayload origin Y0).2 s23 ∧
      (∀ q, StairWireCheck.fpSup q = true → (pullState fieldMap (run (cut (xps k) 23) u23 s)).basis q = s23.basis q) ∧
      (∀ q ∈ ryWires, (pullState fieldMap (run (cut (xps k) 23) u23 s)).basis q = s23.basis q) := by
    obtain ⟨Q21, hcr21⟩ := rch21 k F.x (StairOpenWiring.exitPlans k F.x) StairOpenWiring.half760
    have hcr23 : CRel (XPreX k F.x) (fun a b => AgreeOutside (Δv 87) a b ∧
        ReachE k F.x ((YE ++ StairField2V3ExitPlan.grpF 1 84) ++ StairSchedule.fieldRename FourScratchWindow.unprefix) b)
        XS23 ((Q21 ++ grpFL StairConcrete.bestLoans 0 1 84) ++ StairSchedule.fieldRename FourScratchWindow.unprefix) := by
      have h21' : CRel (XPreX k F.x) (fun a b => RelX F.x 87 a b ∧ ReachE k F.x YE b) XS21 Q21 :=
        crel_mono (fun _ _ w => w) (fun _ _ w => ⟨w.1, reachX_E StairOpenWiring.half760 k F.x _ w.2⟩) hcr21
      -- Step 21 (`grpFL bestLoans 0 1 84` vs `grpF 1 84` on `YE`):
      -- Note: `grpFL bestLoans 0 1 84` and `grpF 1 84` act identically on `YE` (cut 85) via `StairGroups.groups_run_eq`!
      -- Even simpler: `grpFL StairConcrete.bestLoans 0 1 84 = grpF 1 84`? YES!! `def_ = 0`, `StairGroups.groups_zero`!!
      have hgrp0 : grpFL StairConcrete.bestLoans 0 1 84 = StairField2V3ExitPlan.grpF 1 84 := by
        simp only [grpFL, StairField2V3ExitPlan.grpF, StairSchedule.placedGroups, StairConcrete.bestLoans, StairGroups.groups_zero]
      have hstep21 : CRel (fun a b => RelX F.x 87 a b ∧ ReachE k F.x YE b)
          (fun a b => RelX F.x 87 a b ∧ ReachE k F.x (YE ++ StairField2V3ExitPlan.grpF 1 84) b)
          (grpFL StairConcrete.bestLoans 0 1 84) (grpFL StairConcrete.bestLoans 0 1 84) := by
        rintro a b ⟨hrel, ⟨s0, m0, hs0, rfl⟩⟩ m21
        have hs := shared_step (Δv 87) (CvX F.x 87) (cvX_local F.x 87)
          (grpFL StairConcrete.bestLoans 0 1 84)
          (away_of_sub _ _ _ exitGroupSub_best.2.2.2.2.2 (StairField2V3Delta.grpF_away 87 (by decide) 1 84 (by decide)))
          a (run YE m0 s0) hrel m21
        obtain ⟨n21, hn21⟩ := hs
        refine ⟨n21, hn21, s0, WindowFieldJourney.joinTapes YE m0 n21, hs0, ?_⟩
        rw [hgrp0, WindowFieldJourney.joined]
      have hstep22 : CRel (fun a b => RelX F.x 87 a b ∧ ReachE k F.x (YE ++ StairField2V3ExitPlan.grpF 1 84) b)
          (fun a b => AgreeOutside (Δv 87) a b ∧
            ReachE k F.x ((YE ++ StairField2V3ExitPlan.grpF 1 84) ++ StairSchedule.fieldRename FourScratchWindow.unprefix) b)
          (StairSchedule.fieldRename FourScratchWindow.unprefix)
          (StairSchedule.fieldRename FourScratchWindow.unprefix) := by
        rintro a b ⟨hrel, ⟨s0, m0, hs0, rfl⟩⟩ m22
        have hs := shared_step (Δv 87) (CvX F.x 87) (cvX_local F.x 87)
          (StairSchedule.fieldRename FourScratchWindow.unprefix)
          (away_of_sub _ _ _ unprefix_sub StairField2V3ExitPlanR.low_away)
          a (run (YE ++ StairField2V3ExitPlan.grpF 1 84) m0 s0) hrel m22
        obtain ⟨n22, hn22⟩ := hs
        refine ⟨n22, hn22.1, s0, WindowFieldJourney.joinTapes (YE ++ StairField2V3ExitPlan.grpF 1 84) m0 n22, hs0, ?_⟩
        rw [WindowFieldJourney.joined]
      exact crel_append (crel_append h21' hstep21) hstep22
    rw [xcut23 k, run_append]
    obtain ⟨_, hagree23, t0, mBody, ⟨s0, F0, fx0, mOpen, rfl⟩, hrec23⟩ :=
      hcr23 _ _ ⟨⟨s, F, rfl, _, rfl⟩, rfl⟩ _
    obtain ⟨origin, ctx, en, tr, s23, hfr23, hag23⟩ := mul_cut23_frame k F0 mOpen mBody
    obtain ⟨r23, hr23⟩ : ∃ st, run ((YE ++ StairField2V3ExitPlan.grpF 1 84) ++ StairSchedule.fieldRename FourScratchWindow.unprefix)
        mBody (run StairField2V3Replay.exitReferenceOpening mOpen s0) = st := ⟨_, rfl⟩
    rw [hr23] at hrec23 hag23
    obtain ⟨c23, hc23⟩ : ∃ st, run XS23 (u23.drop (measurementCount StairField2V3Replay.exitReferenceOpening))
        (run StairField2V3Replay.exitReferenceOpening (u23.take (measurementCount StairField2V3Replay.exitReferenceOpening)) s) = st := ⟨_, rfl⟩
    rw [hc23] at hagree23 ⊢
    refine ⟨F0.Y, origin, ctx, en, by rw [← fx0]; exact tr, s23, hfr23, ?_, ?_⟩
    · intro q hq
      have h1 := hagree23.2 (fieldMap q) (fpSup_not_delta87 q hq)
      have h2 := hag23 q (fpSup_not_E q hq)
      exact (h1.trans (congrArg (fun st : State => st.basis (fieldMap q)) hrec23)).trans h2
    · intro q hq
      have h1 := hagree23.2 (fieldMap q) (ryWires_not_delta87 q hq)
      have h2 := hag23 q (ryWires_not_E q hq)
      exact (h1.trans (congrArg (fun st : State => st.basis (fieldMap q)) hrec23)).trans h2
  obtain ⟨Y0, origin, ctx, en, tr, s23, hfr23, hpb_fp, hpb_ry⟩ := h23_pin
  obtain ⟨P23, hP23⟩ : ∃ P : Fp × Fp, Rolling1588.exitHeadPayload origin Y0 = P := ⟨_, rfl⟩
  rw [hP23] at hfr23
  have hcleanIn23 : ∀ q ∈ (StairSchedule.exclusiveRoles ++ hostPlan.firstPacket false).map fieldMap,
      (run (cut (xps k) 23) u23 s).basis q = false :=
    exitFirstBefore_xps k s ⟨F⟩ u23
  have hcleanOut23 : ∀ q ∈ StairSchedule.exclusiveRoles.map fieldMap,
      (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket false)) mFp (run (cut (xps k) 23) u23 s)).basis q = false :=
    cleanCut_after (exitFirstRolesAfter_xps k)
      (by rw [cut_succ (xps k) 23 (xL k 23 (by decide))]; rfl) s ⟨F⟩ u23 mFp
  have hb23_vals : regValue fieldR (run (cut (xps k) 23) u23 s).basis = centerWord P23.1 ∧
      regValue fieldY (run (cut (xps k) 23) u23 s).basis = centerWord P23.2 := by
    have hvs := encodedFieldFrame_values true origin P23.1 P23.2 s23 hfr23
    constructor
    · rw [← pullState_fieldMap_regValue_R]
      exact (regValue_congr _ _ _ (fun q hq => hpb_ry q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hvs.1
    · rw [← pullState_fieldMap_regValue_Y]
      exact (regValue_congr _ _ _ (fun q hq => hpb_ry q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hvs.2
  have hz23 : FirstZero.FirstHyp false origin P23.1 P23.2 := by
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    rw [Prod.mk.eta, ← hP23]
    exact Rolling1588.exitHead_first_zero origin F.x Y0 F.x_pos F.x_lt tr
  have hfp23 := firstPacketOdd_step false true origin ctx en F.x F.x_lt tr P23.1 P23.2 hz23
    a23 (run (cut (xps k) 23) u23 s) s23 mFp hrel23.1 hfr23 hpb_fp hpb_ry
    (hrel23.2.1 _ hb23_vals.1) (by simp [JointOdd1588.firstYIn]; exact hrel23.2.2 _ hb23_vals.2)
    hcleanIn23 hcleanOut23
  have hpay_inv := Replay5.inverse_payload origin F.x (Y0 / 2) F.x_pos F.x_lt tr
  have hV_eq : Replay5.firstPayload false origin (P23.1, P23.2) = (Y0 / 2 * (F.x : Fp), 0) := by
    rw [Prod.mk.eta, ← hP23, Rolling1588.exitHeadPayload]
    simpa only [en, if_true] using hpay_inv
  have ha24_agR : AgreeOutsideR a24
      (run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket false)) mFp (run (cut (xps k) 23) u23 s)) := by
    apply agreeOutsideR_of_agreeRY hfp23.1
    apply basis_eq_of_regValue_eq
    have h1 := hfp23.2.2.1
    have h2 := hfp23.2.2.2.2
    rw [hV_eq] at h1 h2
    simp only [JointOdd1588.firstYOut, HalfField.centerWord_zero] at h1 h2
    exact h1.trans h2.symm
  -- Piece 24: `renameProgram phaseHost checkpointPrimitives.firstUnpack` (disjoint from `fieldR`!)
  let u24 := WindowFieldJourney.joinTapes (cut (xps k) 23) u23 mFp
  have hb24_eq : run (StairSchedule.fieldRename (Rolling1588.placedFirstPacket false)) mFp (run (cut (xps k) 23) u23 s) =
      run (cut (xps k) 24) u24 s := by
    have hc24 : cut (xps k) 24 = cut (xps k) 23 ++ StairSchedule.fieldRename (Rolling1588.placedFirstPacket false) := by
      rw [cut_succ (xps k) 23 (xL k 23 (by decide))]; rfl
    rw [hc24, WindowFieldJourney.joined]
  rw [hb24_eq] at ha24_agR
  have hag25 := agreeOutsideR_disjoint PFu firstUnpack_notFieldR ha24_agR m25
  -- Relate `run (renameProgram phaseHost firstUnpack) m25 (run (cut (xps k) 24) u24 s)` to `run oldMulHead u25_H s`!
  let u25_H := WindowFieldJourney.joinTapes (Stair44MultiplyCut.beforeClose hostPlan) u24 m25
  have hold25 : run WindowMiddleContract.oldMulHead u25_H s =
      run PFu m25 (run (cut (xps k) 24) u24 s) := by
    have hsh : WindowMiddleContract.oldMulHead = Stair44Kernel.beforeX := rfl
    rw [hsh, WindowStockHead.beforeM k F, Stair44Kernel.stockBeforeX, WindowFieldJourney.joined,
        ← Stair44MultiplyCut.selected k hostPlan]
    exact congrArg (run PFu m25)
      (by unfold cut; exact Stair44HostedCut.exit k 24 s ⟨F⟩ u24)
  -- Identify `Y0 / 2 * F.x = F.Y * F.x / 2` via `Stair44Kernel.mul_run` + `centerWord_injective`!
  have hY0_eq : Y0 / 2 * (F.x : Fp) = F.Y * (F.x : Fp) / 2 := by
    have hb24_R : regValue fieldR (run (cut (xps k) 24) u24 s).basis = centerWord (Y0 / 2 * (F.x : Fp)) := by
      rw [← hb24_eq]
      have h1 := hfp23.2.2.2.1
      rw [hV_eq] at h1
      exact h1
    have hb25_R : regValue fieldR (run WindowMiddleContract.oldMulHead u25_H s).basis = centerWord (Y0 / 2 * (F.x : Fp)) := by
      rw [hold25, regValue_run_disjoint_R_mul PFu firstUnpack_notFieldR m25]
      exact hb24_R
    let mFull := WindowFieldJourney.joinTapes WindowMiddleContract.oldMulHead u25_H []
    have hfull_R1 : regValue fieldR (run (Stair44Kernel.multiplication k) mFull s).basis = centerWord (Y0 / 2 * (F.x : Fp)) := by
      have hmt : Stair44WalkRun.backward true 409 ++ renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k) =
          Stair44Kernel.mulRawTail k := rfl
      rw [WindowMiddleContract.old_mul_head_split k, hmt, WindowFieldJourney.joined,
          regValue_run_disjoint_R_mul _ (mulRawTail_notFieldR k) []]
      exact hb25_R
    have hfull_R2 : regValue fieldR (run (Stair44Kernel.multiplication k) mFull s).basis = centerWord (F.Y * (F.x : Fp) / 2) := by
      have hpk_notR : ParityXExitInverse23Kernel.pkP ∉ fieldR := (notFieldR_iff _).mp (by decide)
      rw [Stair44Kernel.mul_run k F mFull,
          StairCallerReplay.hostedExit_pw Stair44Kernel.hostReplay k F.k_lt F.sharedNodup F.historyAbove
            F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt s mFull F.input F.selectorG_zero F.selectorS_zero]
      have hkx := (ParityXExitInverse23Kernel.kernelX_correct k F.k_lt F.sharedNodup F.historyAbove
        F.selectorsAway F.transcript F.x F.Y F.x_pos F.x_lt s mFull F.input F.selectorG_zero F.selectorS_zero).2.1
      have hnum_eq : skywalkArithmeticNumerator base = fieldR := rfl
      rw [hnum_eq] at hkx
      exact (regValue_pull_put_eq_R _ outMap_symm_fix_fieldR _ _ hpk_notR _).trans hkx
    exact centerWord_injective (hfull_R1.symm.trans hfull_R2)
  refine ⟨u25_H, by rw [hold25]; exact hag25, ?_⟩
  have ha25_R : regValue fieldR (run PFu m25 a24).basis = P1Life.oddWord (Y0 / 2 * (F.x : Fp)) := by
    rw [regValue_run_disjoint_R_mul PFu firstUnpack_notFieldR m25 a24]
    have h1 := hfp23.2.1
    rw [hV_eq] at h1
    exact h1
  rw [← hY0_eq]; exact ha25_R


end ECDSAAdd.Entrant.OddStockLockstep

end

end
-- ==== end OddLockstepMul ====

-- ==== begin: multiplication lockstep ====
section

set_option autoImplicit false

namespace ECDSAAdd.Entrant.OddStockLockstep

open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout
open StairLoanExitReachX StairLoanField7Transport StairPacket

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] run measurementCount wires renameProgram cut

theorem mulConvWork_off : ∀ q ∈ OddFullPass.HalfConvertOdd.convWork StairBoundaryLoan.converterLayout760, Off q := by
  have h : (OddFullPass.HalfConvertOdd.convWork StairBoundaryLoan.converterLayout760).all
      (fun q => decide (q ∉ EP)) = true := by decide +kernel
  intro q hq
  exact off_of_not_EP q (of_decide_eq_true (List.all_eq_true.mp h q hq))

/-- Canonical-frame register values: `fieldR = Y.val`, `fieldY = 0`. -/
theorem mulCanonical_RY (origin : BasisState) (Y : Fp) (s_rec : State)
    (hrec : Rolling1588Frame.EncodedCanonicalFrame false origin Y 0 s_rec) :
    regValue fieldR s_rec.basis = Y.val ∧ regValue fieldY s_rec.basis = 0 := by
  obtain ⟨raw, _, hpair, henc⟩ := hrec
  have hpR : regValue fieldR raw.basis = Y.val := by
    have h1 := hpair.1
    rw [skywalkSharedField_z_eq_fieldR, Arithmetic.regValue_append] at h1
    have hlen : fieldR.length = 256 := by simp [fieldR, wireBlock_length]
    have hlt : Y.val < 2 ^ 256 := lt_trans Y.val_lt (by decide)
    rw [hlen] at h1
    have hbit0 : regValue [base 2312] raw.basis = 0 := by
      by_contra hne
      have hge : 2 ^ 256 ≤ 2 ^ 256 * regValue [base 2312] raw.basis :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
      omega
    rw [hbit0, Nat.mul_zero, Nat.add_zero] at h1
    exact h1
  have hpY : regValue fieldY raw.basis = 0 := by
    have h1 := hpair.2.1
    rw [skywalkSharedField_a_eq_fieldY, Arithmetic.regValue_append, ZMod.val_zero] at h1
    omega
  have keep : ∀ q, q ∈ ryWires → (run (Rolling1588.allEncode base false 102) [] raw).basis q = raw.basis q :=
    fun q hq => run_preserves_outside _ [] raw q (fun hw => allEncode_notRY false q hw hq)
  constructor
  · rw [← pullState_sig511_regValue_R, henc]
    exact (regValue_congr fieldR _ _ (fun q hq => keep q ((mem_ryWires_iff q).mpr (Or.inl hq)))).trans hpR
  · rw [← pullState_sig511_regValue_Y, henc]
    exact (regValue_congr fieldY _ _ (fun q hq => keep q ((mem_ryWires_iff q).mpr (Or.inr hq)))).trans hpY

/-- The odd-word centering converter is absorbed: on a field state whose pulled view agrees on `Off`
with a canonical record, `liftF center760OddLoan` produces exactly any state that agrees outside
`fieldR` and holds `oddWord (Y / 2)` there. -/
theorem mulCenter_absorb (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (ha : regValue (skywalkSharedField base).a origin = 0) (Y : Fp) (b s_rec : State)
    (hrec : Rolling1588Frame.EncodedCanonicalFrame false origin Y 0 s_rec)
    (hpb : ∀ q, Off q → (pullIn b).basis q = s_rec.basis q)
    (b' : State) (hag : AgreeOutsideR b' b) (hval : regValue fieldR b'.basis = P1Life.oddWord (Y / 2))
    (mc : List Bool) :
    run (liftF OddFullPass.HalfConvertOdd.center760OddLoan) mc b = b' := by
  have hs := mulCanonical_RY origin Y s_rec hrec
  have hcw_s := convWork_clean_of_encodedCanonical origin ctx ha Y s_rec hrec
  let u := pullIn b
  have huR : regValue fieldR u.basis = Y.val :=
    (regValue_congr _ _ _ (fun q hq => hpb q (ryWires_off q ((mem_ryWires_iff q).mpr (Or.inl hq))))).trans hs.1
  have hcw : ∀ q ∈ OddFullPass.HalfConvertOdd.convWork StairBoundaryLoan.converterLayout760, u.basis q = false :=
    fun q hq => (hpb q (mulConvWork_off q hq)).trans (hcw_s q hq)
  have hy43 : ∀ q ∈ OddFullPass.HalfConvertOdd.yHosts44, u.basis q = false := fun q hq => by
    have hy := yHosts44_sub_fieldY q hq
    exact (hpb q (ryWires_off q ((mem_ryWires_iff q).mpr (Or.inr hy)))).trans
      ((regValue_zero fieldY s_rec.basis).mp hs.2 q hy)
  have heq := OddFullPass.HalfConvertOdd.center760OddLoan_run_eq_centerOdd Y u mc
    (by rw [converterLayout760_word_eq_fieldR]; exact huR) hcw hy43
  have hc := OddFullPass.HalfConvertOdd.centerOdd_correct StairBoundaryLoan.converterLayout760
    StairBoundaryLoan.converterLayout760_facts.widths converterLayout760_wires_nodup Y u mc
    (by rw [converterLayout760_word_eq_fieldR]; exact huR) hcw
  rw [converterLayout760_word_eq_fieldR] at hc
  rw [liftF_run, heq]
  apply State.extensionality
  · exact hc.1.trans hag.1.symm
  · funext q
    change (run _ mc u).basis (fieldPlaceInv q) = b'.basis q
    by_cases hq : q ∈ fieldR
    · rw [fieldPlaceInv_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inl hq))]
      have hv : regValue fieldR (run (OddFullPass.HalfConvertOdd.centerOdd StairBoundaryLoan.converterLayout760) mc u).basis =
          regValue fieldR b'.basis := hc.2.1.trans hval.symm
      exact (regValue_eq_iff _ _ _).mp hv q hq
    · have hq' : fieldPlaceInv q ∉ fieldR := by
        intro hmem
        have e := fieldPlace_fix_ryWires _ ((mem_ryWires_iff _).mpr (Or.inl hmem))
        rw [fieldPlace_inv] at e
        exact hq (e ▸ hmem)
      rw [hc.2.2.2 _ hq']
      change b.basis (fieldPlace (fieldPlaceInv q)) = b'.basis q
      rw [fieldPlace_inv]
      exact (hag.2 q hq).symm

theorem mulOpening_odd (k : Nat) {s : State} (F : ExitFrame k s) {t : State}
    (hag : AgreeOutsideR t s) (m : List Bool) :
    AgreeOutsideR (run StairField2V3Replay.exitReferenceOpening m t)
      (run StairField2V3Replay.exitReferenceOpening m s) ∧
    regValue fieldR (run StairField2V3Replay.exitReferenceOpening m t).basis = regValue fieldR t.basis := by
  have hin_t : SkywalkArithmeticInput base F.x (regValue fieldR t.basis) t.basis :=
    FrontierEntry1591Kernel.paired_input F.x F.Y.val s t F.input hag.2
  have ht := first_phase_hosted false F.sharedNodup F.historyAbove F.x _ F.x_pos F.x_lt t m hin_t
  have hs := first_phase_hosted false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s m F.input
  have avoid : ∀ q ∈ wires (Rolling1588.firstPhase false), q ∉ fieldR := fun q hq =>
    FrontierEntry1591Kernel.pool_away_numerator q
      (List.mem_toFinset.mp (ParityXExitInverse23Kernel.first_pool false hq))
  rw [StairField2V3Replay.exitReferenceOpening, ht, hs]
  exact ⟨agreeOutsideR_disjoint _ avoid hag m, regValue_fieldR_disjoint _ avoid t m⟩

theorem mulP03tail_notFieldR : ∀ q ∈ wires (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename FourScratchWindow.clearProgram), q ∉ fieldR := by
  have h : StairWireCheck.allSites notFieldR (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename FourScratchWindow.clearProgram) = true := by decide +kernel
  exact fun q hq => (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h q hq)


def stockOddMulBeforeParityNC : Program :=
  StairSchedule.hostedX ++ StairSchedule.fieldRename (WindowParityCaller.exitLowPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542)

def stockOddMulLeadingNC : Program :=
  StairSchedule.paritySetup ++ stockOddMulBeforeParityNC ++ StairSchedule.paritySetup ++ stockOddMulBeforeGroup

def stockOddMulPrefix21NC : Program :=
  StairField2V3Replay.exitReferenceOpening ++ stockOddMulLeadingNC

def stockOddMulHeadNC : Program :=
  (((Stair44Kernel.mulLead ++ stockOddMulLeadingNC) ++
    renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84)) ++
    stockOddMulAfterGroup) ++
  renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack

/-- Pieces 0-3 of the stock multiplication head, shared by the old and the new prefix. -/
def mulP03 : Program :=
  StairField2V3Replay.exitReferenceOpening ++ StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename FourScratchWindow.clearProgram

/-- What follows the centering converter in the old cut-21 prefix. -/
def mulR21 : Program :=
  liftF (WindowParityCaller.exitHeadPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup ++ stockOddMulBeforeGroup

theorem prefix21_split : stockOddMulPrefix21 =
    mulP03 ++ (liftF OddFullPass.HalfConvertOdd.center760OddLoan ++ mulR21) := by
  simp only [stockOddMulPrefix21, stockOddMulLeading, stockOddMulBeforeParity, mulP03, mulR21,
    OddFullPass.P1LifeLoan.exitLowPrefixOdd, OddFullPass.P1LifeLoan.exitHeadPrefixOdd, WindowParityCaller.exitHeadPrefixOddNC,
    liftF, fieldRename_append, Six505.rename_append, List.append_assoc]

theorem prefix21NC_split : stockOddMulPrefix21NC = mulP03 ++ mulR21 := by
  simp only [stockOddMulPrefix21NC, stockOddMulLeadingNC, stockOddMulBeforeParityNC, mulP03, mulR21,
    WindowParityCaller.exitLowPrefixOddNC, liftF, fieldRename_append, Six505.rename_append, List.append_assoc]

/-- The record facts at the input of the centering converter (pieces 0-3 run on `s`). -/
theorem cut4_record (k : Nat) {s : State} (F : ExitFrame k s) (m0 : List Bool) :
    ∃ origin, FrontierReplay1591.Context origin ∧ regValue (skywalkSharedField base).a origin = 0 ∧
      ∃ s_rec, Rolling1588Frame.EncodedCanonicalFrame false origin F.Y 0 s_rec ∧
        ∀ q, Off q → (pullIn (run mulP03 m0 s)).basis q = s_rec.basis q := by
  let mOpen := m0.take (measurementCount StairField2V3Replay.exitReferenceOpening)
  let mRest := m0.drop (measurementCount StairField2V3Replay.exitReferenceOpening)
  have hopen : run StairField2V3Replay.exitReferenceOpening mOpen s =
      run (Rolling1588.firstPhase false) mOpen s :=
    first_phase_hosted false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
  obtain ⟨orig, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
    F.sharedNodup F.historyAbove F.selectorsAway F.x F.Y F.x_pos F.x_lt s mOpen F.input
  have ctx := Rolling1588Lifetime.prepared_context F.sharedNodup F.selectorsAway
    F.transcript F.x F.Y s orig facts legal F.selectorG_zero F.selectorS_zero
  have bits := Rolling1588Lifetime.first_clean false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
  have work := Rolling1588Lifetime.first_work_zero false F.sharedNodup F.x F.Y.val s mOpen F.input
  have parity := Rolling1588Lifetime.first_parity false F.sharedNodup F.historyAbove F.x F.Y.val F.x_pos F.x_lt s mOpen F.input
  have input := frames false
  rw [lf_eq] at input bits work parity
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) mOpen s = v := ⟨_, rfl⟩
  rw [hv] at input bits work parity
  have code := Rolling1588Frame.canonical_special_at orig.basis F.Y 0 v 511 (by simp) input
  have in511 : v.basis (base 511) = true :=
    (by rw [sig511_511_mul] at code; exact code : v.basis (base 511) = orig.basis (base 511)).trans
      (trace_last F.x F.x_pos F.x_lt orig.basis facts.trace)
  have in1542 : v.basis (base 1542) = false := bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := canonical_flags orig.basis ctx F.Y 0 v input
  let origin' := writeBit orig.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set orig.basis ctx true
  have ha' := FrontierEntry1591.source_zero_control_set orig.basis true facts.sourceZero
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (F.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]; exact facts.trace
  have input' := Rolling1588.canonical_control_set orig.basis F.Y 0 v true input
  have codes := Rolling1588.canonical_prefix_codes origin' ctx' F.Y 0 (force v) input' F.x F.x_pos F.x_lt trace'
  have clean := FourScratchWindow.canonical_clean origin' ctx' ha' F.Y (force v) input' codes.1 codes.2.1
  have z768 := Rolling1588.canonical_768_zero origin' ctx' F.Y 0 (force v) input'
  refine ⟨origin', ctx', ha', force v, input', ?_⟩
  intro q hq
  have hb4_eq : run mulP03 m0 s = run (StairSchedule.fieldRename FourScratchWindow.clearProgram)
      (mRest.drop (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX)))
      (run (StairSchedule.paritySetup ++ StairSchedule.hostedX)
        (mRest.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX))) v) := by
    have hsh : mulP03 = StairField2V3Replay.exitReferenceOpening ++
        ((StairSchedule.paritySetup ++ StairSchedule.hostedX) ++
          StairSchedule.fieldRename FourScratchWindow.clearProgram) := by
      simp only [mulP03, List.append_assoc]
    rw [hsh, run_append, run_append, hopen, hv]
  rw [hb4_eq, field_pullIn]
  exact window_agree _ (force v) _ (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _)
    clean codes.2.2 z768 q hq.1 hq.2

theorem mulP03_agree (k : Nat) {s : State} (F : ExitFrame k s) {t : State}
    (hag : AgreeOutsideR t s) (m0 : List Bool) :
    AgreeOutsideR (run mulP03 m0 t) (run mulP03 m0 s) ∧
      regValue fieldR (run mulP03 m0 t).basis = regValue fieldR t.basis := by
  have hsh : mulP03 = StairField2V3Replay.exitReferenceOpening ++
      (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram) := by
    simp only [mulP03, List.append_assoc]
  have op := mulOpening_odd k F hag (m0.take (measurementCount StairField2V3Replay.exitReferenceOpening))
  have e (u : State) : run mulP03 m0 u = run (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram)
      (m0.drop (measurementCount StairField2V3Replay.exitReferenceOpening))
      (run StairField2V3Replay.exitReferenceOpening
        (m0.take (measurementCount StairField2V3Replay.exitReferenceOpening)) u) := by
    rw [hsh, run_append]
  rw [e t, e s]
  exact ⟨agreeOutsideR_disjoint _ mulP03tail_notFieldR op.1 _,
    (regValue_fieldR_disjoint _ mulP03tail_notFieldR _ _).trans op.2⟩

/-- The new cut-21 prefix on the odd-word input `t` is the old prefix on the canonical input `s`. -/
theorem prefix21NC_eq (k : Nat) {s : State} (F : ExitFrame k s) {t : State}
    (hag : AgreeOutsideR t s) (hval : regValue fieldR t.basis = P1Life.oddWord (F.Y / 2)) (m : List Bool) :
    run stockOddMulPrefix21NC m t =
      run stockOddMulPrefix21 (WindowFieldJourney.joinTapes mulP03 (m.take (measurementCount mulP03))
        (WindowFieldJourney.joinTapes (liftF OddFullPass.HalfConvertOdd.center760OddLoan) []
          (m.drop (measurementCount mulP03)))) s := by
  rw [prefix21_split, prefix21NC_split, WindowFieldJourney.joined, WindowFieldJourney.joined, run_append]
  obtain ⟨origin, ctx, ha, s_rec, hrec, hpb⟩ := cut4_record k F (m.take (measurementCount mulP03))
  have ag := mulP03_agree k F hag (m.take (measurementCount mulP03))
  exact congrArg (run mulR21 (m.drop (measurementCount mulP03)))
    (mulCenter_absorb origin ctx ha F.Y _ s_rec hrec hpb _ ag.1 (ag.2.trans hval) []).symm

theorem mulPullPhaseHost_odd (k : Nat) {s : State} (F : ExitFrame k s) {t : State}
    (hag : AgreeOutsideR t s) : pullState Rolling1588Lifetime.phaseHost t = t := by
  have hpull_s := StairField13V3Clean.pull_phaseHost_exit F
  apply State.extensionality
  · rfl
  · funext q
    by_cases hr : q ∈ fieldR
    · change t.basis (Rolling1588Lifetime.phaseHost q) = t.basis q
      rw [phaseHost_fix_fieldR q hr]
    · have hnr : Rolling1588Lifetime.phaseHost q ∉ fieldR := by
        intro hmem
        have hf := phaseHost_fix_fieldR (Rolling1588Lifetime.phaseHost q) hmem
        exact hr (Rolling1588Lifetime.phaseHost.injective hf ▸ hmem)
      change t.basis (Rolling1588Lifetime.phaseHost q) = t.basis q
      rw [hag.2 _ hnr, hag.2 _ hr]
      exact congrFun (congrArg State.basis hpull_s) q

/-- `mulLead` replays as `exitReferenceOpening` also on the odd-word input (it never reads `fieldR`). -/
theorem leadM_odd (k : Nat) {s : State} (F : ExitFrame k s) {t : State} (hag : AgreeOutsideR t s)
    (m : List Bool) :
    run Stair44Kernel.mulLead m t = run StairField2V3Replay.exitReferenceOpening m t := by
  have hin_t : SkywalkArithmeticInput base F.x (regValue fieldR t.basis) t.basis :=
    FrontierEntry1591Kernel.paired_input F.x F.Y.val s t F.input hag.2
  have hpull := mulPullPhaseHost_odd k F hag
  apply MappedCompressed.pullState_perm_injective Rolling1588Lifetime.phaseHost
  rw [Stair44Kernel.mulLead, StairField2V3Replay.exitReferenceOpening,
    run_rename _ Rolling1588Lifetime.phaseHost.injective, run_rename _ Rolling1588Lifetime.phaseHost.injective,
    hpull, WindowStockHead.shapeM]
  exact Stair44Kernel.with_tail false 489 F.x _ (by decide) F.x_pos F.x_lt F.sharedNodup t hin_t _ m

private theorem mulSwapHead (A B V : Program) (s : State) (m : List Bool)
    (cnt : measurementCount A = measurementCount B) (same : ∀ u, run A u s = run B u s) :
    run (A ++ V) m s = run (B ++ V) m s := by
  rw [run_append, run_append, cnt, same]

def mulHeadTail : Program :=
  renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup false 1 84) ++ stockOddMulAfterGroup ++
    renameProgram Rolling1588Lifetime.phaseHost checkpointPrimitives.firstUnpack

/-- The new stock multiplication head on the odd-word input `t` is the old one on `s`. -/
theorem mulHeadNC_eq (k : Nat) {s : State} (F : ExitFrame k s) {t : State}
    (hag : AgreeOutsideR t s) (hval : regValue fieldR t.basis = P1Life.oddWord (F.Y / 2)) (m : List Bool) :
    ∃ M, run stockOddMulHeadNC m t = run stockOddMulHead M s := by
  have hNC : stockOddMulHeadNC = Stair44Kernel.mulLead ++ (stockOddMulLeadingNC ++ mulHeadTail) := by
    simp only [stockOddMulHeadNC, mulHeadTail, List.append_assoc]
  have hOld : stockOddMulHead = Stair44Kernel.mulLead ++ (stockOddMulLeading ++ mulHeadTail) := by
    simp only [stockOddMulHead, mulHeadTail, List.append_assoc]
  have p21NC : StairField2V3Replay.exitReferenceOpening ++ (stockOddMulLeadingNC ++ mulHeadTail) =
      stockOddMulPrefix21NC ++ mulHeadTail := by
    simp only [stockOddMulPrefix21NC, List.append_assoc]
  have p21 : StairField2V3Replay.exitReferenceOpening ++ (stockOddMulLeading ++ mulHeadTail) =
      stockOddMulPrefix21 ++ mulHeadTail := by
    simp only [stockOddMulPrefix21, List.append_assoc]
  let c := measurementCount stockOddMulPrefix21NC
  let M := WindowFieldJourney.joinTapes stockOddMulPrefix21
    (WindowFieldJourney.joinTapes mulP03 ((m.take c).take (measurementCount mulP03))
      (WindowFieldJourney.joinTapes (liftF OddFullPass.HalfConvertOdd.center760OddLoan) []
        ((m.take c).drop (measurementCount mulP03)))) (m.drop c)
  refine ⟨M, ?_⟩
  rw [hNC, hOld, mulSwapHead _ _ _ t m WindowStockHead.countM (leadM_odd k F hag),
    mulSwapHead _ _ _ s M WindowStockHead.countM (WindowStockHead.leadM k F), p21NC, p21,
    WindowFieldJourney.joined, run_append, prefix21NC_eq k F hag hval]

theorem stockOddMulNC_cut21 (k : Nat) {s : State} (F : ExitFrame k s) {t : State}
    (hag : AgreeOutsideR t s) (hval : regValue fieldR t.basis = P1Life.oddWord (F.Y / 2)) (m : List Bool) :
    let a21 := run stockOddMulPrefix21NC m t
    (∃ n, OddRel P1Life.oddWord P1Life.oddWord a21 (run (cut (xps k) 21) n s)) ∧
    (∃ origin, FrontierReplay1591.Context origin ∧ origin (base 2400) = true ∧
      TraceOK F.x origin ∧ WindowFieldView.OCut 85 origin (pullIn a21) ∧
      StairPacket.WindowFieldView.TagReady (pullIn a21)) := by
  intro a21
  have e : a21 = _ := prefix21NC_eq k F hag hval m
  rw [e]
  exact stockOddMul_cut21 k F _

theorem stockOddMulHeadNC_agree_oldMulHead (k : Nat) {s : State} (F : ExitFrame k s) {t : State}
    (hag : AgreeOutsideR t s) (hval : regValue fieldR t.basis = P1Life.oddWord (F.Y / 2)) (m : List Bool) :
    ∃ n, AgreeOutsideR (run stockOddMulHeadNC m t) (run WindowMiddleContract.oldMulHead n s) ∧
      regValue fieldR (run stockOddMulHeadNC m t).basis = P1Life.oddWord (F.Y * (F.x : Fp) / 2) := by
  obtain ⟨M, hM⟩ := mulHeadNC_eq k F hag hval m
  rw [hM]
  exact stockOddMulHead_agree_oldMulHead k F M

end ECDSAAdd.Entrant.OddStockLockstep

end
-- ==== end: multiplication lockstep ====

-- ==== begin MainTail ====
section

section

section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelReplay
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime FlagEntry StairConcreteAssembly StockArchiveBanks
open WindowMiddleContract WindowStockHead
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount wires renameProgram

theorem tail (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (cut:421+n∈[425,505,506])
    (a ref:State) (P:Program) (m:List Bool)
    (pair:Paired d x (pullState phaseHost a) (pullState phaseHost ref) (StockRowVector.rows x p))
    (known:Endpoint d x (420+n) (pullState phaseHost ref)):
    ∃old,run (renameProgram phaseHost (WindowWalkCosts.backward d n++P)) m a=
      run (renameProgram phaseHost (Stair44WalkRun.backward d (405+n)++P)) old ref:=by
  obtain ⟨s,enc,stage,ag⟩:=known
  obtain ⟨old,eq⟩:=StockWalkEndpoints.closed d n x nz lt cut s _ _ m enc stage pair ag
  let A:=WindowWalkCosts.backward d n
  let B:=Stair44WalkRun.backward d (405+n)
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
  exact compose (old:=head) (tail false 85 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (div_endpoint F head))

theorem mul_run (geometry:WindowMiddleContract.exit) (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    ∃old,run (WindowKernelPrograms.multiplication k) m t=run (Stair44Kernel.multiplication k) old t:=by
  obtain ⟨head,v⟩:=geometry k F m
  rw [mul_head_split,old_mul_head_split]
  exact compose (old:=head) (tail true 4 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (mul_endpoint k F head))

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

private theorem stdOfOdd_val (tOdd : State) (Y : Fp) :
    regValue OddStockLockstep.fieldR (OddStockLockstep.stdOfOdd tOdd Y).basis = BalancedField.centerWord (Y / 2) := by
  let tStd := OddStockLockstep.stdOfOdd tOdd Y
  have hlt : BalancedField.centerWord (Y / 2) < 2 ^ 256 := (BalancedField.centerWord_valid (Y / 2)).1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 256
  · have hlen : OddStockLockstep.fieldR.length = 256 := by simp [OddStockLockstep.fieldR, wireBlock_length]
    have hbit := Arithmetic.regValue_bit OddStockLockstep.fieldR i 0 tStd.basis (by omega)
    have hget : OddStockLockstep.fieldR.getD i 0 = base (2056 + i) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp [OddStockLockstep.fieldR, wireBlock]
    rw [hget] at hbit
    have hmem : base (2056 + i) ∈ OddStockLockstep.fieldR :=
      List.mem_map.mpr ⟨2056 + i, by simp only [List.mem_range'_1]; omega, rfl⟩
    have hsub : base (2056 + i) - 2072 = i := by change (2056 + i) + 16 - 2072 = i; omega
    have htb : tStd.basis (base (2056 + i)) = (BalancedField.centerWord (Y / 2)).testBit i := by
      simp only [tStd, OddStockLockstep.stdOfOdd, dif_pos hmem, hsub]
    rw [htb] at hbit
    rw [Nat.testBit_eq_decide_div_mod_eq, ← hbit]
    cases (BalancedField.centerWord (Y / 2)).testBit i <;> decide
  · have hlen : OddStockLockstep.fieldR.length = 256 := by simp [OddStockLockstep.fieldR, wireBlock_length]
    have hlt1 : regValue OddStockLockstep.fieldR tStd.basis < 2 ^ 256 := hlen ▸ Arithmetic.regValue_lt OddStockLockstep.fieldR tStd.basis
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]

private theorem stdOfOdd_agree (tOdd : State) (Y : Fp) :
    OddStockLockstep.AgreeOutsideR tOdd (OddStockLockstep.stdOfOdd tOdd Y) :=
  ⟨rfl, fun q hq => by simp only [OddStockLockstep.stdOfOdd, dif_neg hq]⟩

private theorem outMap_clean_exit {k : Nat} {s : State} (F : ExitFrame k s) :
    pullState Stair44Kernel.outMap.symm s = s := by
  let pairs : List (Wire × Wire) := [(base 1542, base 500), (base 1026, base 501), (base 1541, base 502),
    (base 723, base 503), (base 724, base 504)]
  let ok (q : Wire) := phaseHost q ∈ skywalkSharedWires base ∧ phaseHost q ∉ wireBlock base 770 256 ∧
    phaseHost q ∉ wireBlock base 2056 256
  have small : ∀ ab ∈ pairs, ok ab.1 ∧ ok ab.2 := by unfold ok; decide +kernel
  have z (q : Wire) (hq : ok q) : (pullState phaseHost s).basis q = false := F.input.2.2 _ hq.1 hq.2.1 hq.2.2
  have fixed : pullState Stair44Kernel.rawOut (pullState phaseHost s) = pullState phaseHost s :=
    (Stair44PointMap.clean_chain pairs id _ _ (fun ab hab => ⟨z _ (small ab hab).1, z _ (small ab hab).2⟩)).mpr rfl
  have inv := congrArg (pullState Stair44Kernel.rawOut.symm) fixed
  rw [Stair44PlacedHead.unpull] at inv
  apply MappedCompressed.pullState_perm_injective phaseHost
  apply State.extensionality
  · rfl
  · funext q
    have hconj : ((phaseHost.symm.trans Stair44Kernel.rawOut).trans phaseHost).symm (phaseHost q) =
        phaseHost (Stair44Kernel.rawOut.symm q) := by
      simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    exact (congrArg s.basis hconj).trans (congrFun (congrArg State.basis inv.symm) q)

private theorem regValue_pull_eq_R_tail (f : Wire → Wire) (hfix : ∀ q ∈ OddStockLockstep.fieldR, f q = q)
    (st : State) : regValue OddStockLockstep.fieldR (pullState f st).basis = regValue OddStockLockstep.fieldR st.basis :=
  regValue_congr OddStockLockstep.fieldR (pullState f st).basis st.basis
    (fun q hq => by change st.basis (f q) = st.basis q; rw [hfix q hq])

private theorem regValue_run_disjoint_R_tail (P : Program) (h : ∀ q ∈ wires P, q ∉ OddStockLockstep.fieldR)
    (m : List Bool) (s : State) :
    regValue OddStockLockstep.fieldR (run P m s).basis = regValue OddStockLockstep.fieldR s.basis :=
  regValue_congr OddStockLockstep.fieldR (run P m s).basis s.basis
    (fun q hq => run_preserves_outside P m s q (fun hw => h q hw hq))

private theorem pullState_basis_tail (f : Wire → Wire) (st : State) (q : Wire) :
    (pullState f st).basis q = st.basis (f q) := rfl

private theorem pullState_phase_tail (f : Wire → Wire) (st : State) :
    (pullState f st).phase = st.phase := rfl

private theorem unpull_symm (e : Equiv.Perm Wire) (s : State) :
    pullState e (pullState e.symm s) = s := by
  apply State.extensionality
  · rfl
  · funext q
    change s.basis (e.symm (e q)) = s.basis q
    rw [e.symm_apply_apply]

end ECDSAAdd.Entrant.StairPacket.WindowKernelReplay

end

-- ==== begin: multiplication kernel ====
section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelPrograms
open Arithmetic MappedCompressed Baselines Stair44Placement Stair44PointMap Stair44WalkMap Stair44Kernel
open Stair44Outer Rolling1588Lifetime Secp256k1 StairConcreteAssembly StairSemanticFinal
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
def mulBeforeNC : Program :=
  (renameProgram phaseHost (openWalk false 84 ++ Stair44Outer.forwardEnd) ++
    WindowParityCaller.exitFieldHostedNC checkpointPrimitives) ++ renameProgram phaseHost checkpointPrimitives.firstUnpack
def multiplicationNC (k : Nat) : Program := mulBeforeNC ++ renameProgram phaseHost (mulAfter k)

theorem mul_splitNC (k : Nat) : FrontierEntry1591Callers.exit (multiplicationNC k) layout =
    Stair44Splits.tick ++ WindowParityCaller.multiplyNC k := by
  change kernelPlace (multiplicationNC k) = _
  simp only [multiplicationNC, mulBeforeNC, mulAfter, openWalk, WindowParityCaller.multiplyNC, kernelPlace,
    Six505.rename_append, List.append_assoc]
  change phasePlace Stair44Kernel.firstR ++ _ = Stair44Splits.tick ++ _
  rw [Stair44Splits.tick_eq]
  rw [show Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k)) =
      phasePlace (renameProgram rawX (ParityXExitInverse23Kernel.x1N k)) from
    (Stair44Splits.placeMove rawX duringX (fun q => (maps q).2.1) _).symm]
  rfl
end ECDSAAdd.Entrant.StairPacket.WindowKernelPrograms

namespace ECDSAAdd.Entrant.StairPacket.WindowMiddleContract
open Arithmetic MappedCompressed Rolling1588Lifetime Secp256k1 StairConcreteAssembly
open WindowKernelPrograms StockArchiveBanks
def mulHeadNC := mulBeforeNC
theorem mul_head_splitNC (k : Nat) : WindowKernelPrograms.multiplicationNC k = mulHeadNC ++ renameProgram phaseHost
    (WindowWalkCosts.backward true 4 ++ renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)) := rfl
end ECDSAAdd.Entrant.StairPacket.WindowMiddleContract

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelReplay
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime FlagEntry StairConcreteAssembly StockArchiveBanks
open WindowMiddleContract WindowStockHead
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount wires renameProgram

def OddExitContractNC : Prop :=
  ∀ (k : Nat) {s t : State} (F : ExitFrame k s), OddStockLockstep.AgreeOutsideR t s →
    regValue OddStockLockstep.fieldR t.basis = P1Life.oddWord (F.Y / 2) → ∀ (m : List Bool),
    ∃ old, Paired true F.x (pullState phaseHost (run mulHeadNC m t))
      (pullState phaseHost (run OddStockLockstep.stockOddMulHeadNC old t)) (StockRowVector.rows F.x p)

theorem outMap_clean_odd {k : Nat} {s : State} (F : ExitFrame k s) {t : State}
    (hag : OddStockLockstep.AgreeOutsideR t s) : pullState Stair44Kernel.outMap.symm t = t := by
  have hs := outMap_clean_exit F
  apply State.extensionality
  · rfl
  · funext q
    change t.basis (Stair44Kernel.outMap.symm q) = t.basis q
    by_cases hr : q ∈ OddStockLockstep.fieldR
    · rw [OddStockLockstep.outMap_symm_fix_fieldR q hr]
    · have hnr : Stair44Kernel.outMap.symm q ∉ OddStockLockstep.fieldR := by
        intro hmem
        have hf := OddStockLockstep.outMap_fix_fieldR _ hmem
        rw [Equiv.apply_symm_apply] at hf
        rw [← hf] at hmem
        exact hr hmem
      rw [hag.2 _ hnr, hag.2 _ hr]
      exact congrFun (congrArg State.basis hs) q

/-- The multiplication kernel without `center760OddLoan` meets the odd-input exit contract. -/
theorem multiplication_oddNC (geometry : OddExitContractNC) :
    ∀ k, k < p → SqOddContract.ExitMatchesOddNC
      (renameProgram Stair44Kernel.outMap.symm (WindowKernelPrograms.multiplicationNC k)) k := by
  intro k hk hn hlo ho hf x Y hx0 hx s t m input hg0 hs0 hph hsame hval
  let F : ExitFrame k s := ⟨hk, hn, hlo, ho, hf, x, Y, hx0, hx, input, hg0, hs0⟩
  have hag : OddStockLockstep.AgreeOutsideR t s := ⟨hph, hsame⟩
  have hval' : regValue OddStockLockstep.fieldR t.basis = P1Life.oddWord (F.Y / 2) := hval
  obtain ⟨head, v⟩ := geometry k F hag hval' (m.take (measurementCount mulHeadNC))
  obtain ⟨nOld, hAgHead, hValHead⟩ := OddStockLockstep.stockOddMulHeadNC_agree_oldMulHead k F hag hval' head
  have hEndOdd : Endpoint true x 424 (pullState phaseHost (run OddStockLockstep.stockOddMulHeadNC head t)) := by
    obtain ⟨s0, enc, st, hpool⟩ := mul_endpoint k F nOld
    refine ⟨s0, enc, st, fun q hq => ?_⟩
    have hq_notR : phaseHost q ∉ OddStockLockstep.fieldR :=
      OddStockLockstep.fieldR_disjoint_pool (phaseHost q) (Stair44DivTerm.host_pool q (List.mem_toFinset.mp hq))
    rw [pullState_basis_tail]
    have hhp := hpool q hq
    rw [pullState_basis_tail] at hhp
    exact (hAgHead.2 (phaseHost q) hq_notR).trans hhp
  obtain ⟨post, htail⟩ := tail true 4 x hx0 hx (by decide)
    (run mulHeadNC (m.take (measurementCount mulHeadNC)) t)
    (run OddStockLockstep.stockOddMulHeadNC head t)
    (renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k))
    (m.drop (measurementCount mulHeadNC)) v hEndOdd
  have hmt : Stair44WalkRun.backward true 409 ++ renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k) =
      Stair44Kernel.mulRawTail k := rfl
  have hmul_eq : run (WindowKernelPrograms.multiplicationNC k) m t =
      run (renameProgram phaseHost (Stair44Kernel.mulRawTail k))
        post (run OddStockLockstep.stockOddMulHeadNC head t) := by
    rw [mul_head_splitNC k, run_append mulHeadNC, ← hmt]; exact htail
  let mFull := WindowFieldJourney.joinTapes oldMulHead nOld post
  have hold_eq : run (Stair44Kernel.multiplication k) mFull s =
      run (renameProgram phaseHost (Stair44Kernel.mulRawTail k))
        post (run oldMulHead nOld s) := by
    rw [old_mul_head_split k, hmt, WindowFieldJourney.joined]
  have hAgFull : OddStockLockstep.AgreeOutsideR
      (run (WindowKernelPrograms.multiplicationNC k) m t)
      (run (Stair44Kernel.multiplication k) mFull s) := by
    rw [hmul_eq, hold_eq]
    exact OddStockLockstep.agreeOutsideR_disjoint _ (OddStockLockstep.mulRawTail_notFieldR k) hAgHead post
  have hValFull : regValue OddStockLockstep.fieldR (run (WindowKernelPrograms.multiplicationNC k) m t).basis =
      P1Life.oddWord (Y * (x : Fp) / 2) := by
    rw [hmul_eq, regValue_run_disjoint_R_tail _ (OddStockLockstep.mulRawTail_notFieldR k) post]
    exact hValHead
  have hren := run_rename Stair44Kernel.outMap.symm Stair44Kernel.outMap.symm.injective
    (WindowKernelPrograms.multiplicationNC k) m t
  rw [outMap_clean_odd F hag] at hren
  have hout_eq : run (renameProgram Stair44Kernel.outMap.symm (WindowKernelPrograms.multiplicationNC k)) m t =
      pullState Stair44Kernel.outMap (run (WindowKernelPrograms.multiplicationNC k) m t) := by
    have h1 := congrArg (pullState Stair44Kernel.outMap) hren
    rwa [unpull_symm] at h1
  have hold_eq_m : run (Stair44Kernel.multiplication k) mFull s = run (Stair44Kernel.multiplication k) m s :=
    State.extensionality _ _ ((old_phase k F mFull).trans (old_phase k F m).symm)
      (Arithmetic.run_basis_records _ _ _ _ _ rfl)
  have href_eq : pullState Stair44Kernel.outMap (run (Stair44Kernel.multiplication k) mFull s) =
      ParityEven.put (run (ParityXExitInverse23Kernel.kernelX k) m s)
        ParityXExitInverse23Kernel.pkP (s.basis (base 2400) && decide (k < x)) := by
    rw [hold_eq_m, Stair44Kernel.mul_run k F m, unpull_symm]
    exact StairCallerReplay.hostedExit_pw Stair44Kernel.hostReplay k hk hn hlo ho hf x Y hx0 hx s m input hg0 hs0
  dsimp only
  rw [hout_eq, ← href_eq]
  refine ⟨by rw [pullState_phase_tail, pullState_phase_tail]; exact hAgFull.1, ?_, ?_⟩
  · exact (regValue_pull_eq_R_tail (⇑Stair44Kernel.outMap) OddStockLockstep.outMap_fix_fieldR _).trans hValFull
  · intro q hq
    have hnr : Stair44Kernel.outMap q ∉ OddStockLockstep.fieldR := by
      intro hmem
      have hfix := OddStockLockstep.outMap_symm_fix_fieldR (Stair44Kernel.outMap q) hmem
      rw [Equiv.symm_apply_apply] at hfix
      exact hq (hfix.symm ▸ hmem)
    rw [pullState_basis_tail, pullState_basis_tail]
    exact hAgFull.2 (Stair44Kernel.outMap q) hnr
end ECDSAAdd.Entrant.StairPacket.WindowKernelReplay

end
-- ==== end: multiplication kernel ====

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify WindowParityDirty
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option linter.unusedSimpArgs false
def delta (d : Bool) (r : Nat) :=
  ((parity (ArchivePortAction.code d)).testBit r) ^^ ((parity (StairArchiveNativeCut.canonical d d)).testBit r)
def Active (j : Nat) := j=10 ∨ j=13 ∨ j=16 ∨ j=19 ∨ j=22 ∨ j=25 ∨ j=28 ∨ j=31 ∨ j=35 ∨ j=39 ∨ j=43 ∨ j=47 ∨ j=51 ∨ j=55 ∨ j=59 ∨ j=63 ∨ j=67 ∨ j=70 ∨ j=73 ∨ j=76 ∨ j=79 ∨ j=82
private theorem mesh : wires region⊆Finset.range 31 :=
  ECDSAAdd.Entrant.WSlimMain.wires_subset_range_of_all (by decide +kernel)
private theorem portDistinct : ∀ j∈([10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]:List Nat), ((List.range 31).map (port j)).Nodup := by
  have h : ∀ j∈([10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]:List Nat),
      StairLoan.nodupMask ((List.range 31).map (port j)) 0 = true := by decide +kernel
  exact fun j hj => StairLoan.nodup_of_mask _ (h j hj)
private theorem inj {j : Nat} (hj : Active j) :
    ∀a∈Finset.range 31,∀b∈Finset.range 31, port j a=port j b → a=b := by
  intro a ha b hb eq
  have mem : j∈([10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]:List Nat) := by rcases hj with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h]
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
      (((((((((((((((((((((delta (dirs 10) (rows 10) ^^ delta (dirs 13) (rows 13)) ^^ delta (dirs 16) (rows 16)) ^^ delta (dirs 19) (rows 19)) ^^ delta (dirs 22) (rows 22)) ^^ delta (dirs 25) (rows 25)) ^^ delta (dirs 28) (rows 28)) ^^ delta (dirs 31) (rows 31)) ^^ delta (dirs 35) (rows 35)) ^^ delta (dirs 39) (rows 39)) ^^ delta (dirs 43) (rows 43)) ^^ delta (dirs 47) (rows 47)) ^^ delta (dirs 51) (rows 51)) ^^ delta (dirs 55) (rows 55)) ^^ delta (dirs 59) (rows 59)) ^^ delta (dirs 63) (rows 63)) ^^ delta (dirs 67) (rows 67)) ^^ delta (dirs 70) (rows 70)) ^^ delta (dirs 73) (rows 73)) ^^ delta (dirs 76) (rows 76)) ^^ delta (dirs 79) (rows 79)) ^^ delta (dirs 82) (rows 82)) s := by
  have a0 : Active 10 := (Or.inl rfl)
  have a1 : Active 13 := (Or.inr (Or.inl rfl))
  have a2 : Active 16 := (Or.inr (Or.inr (Or.inl rfl)))
  have a3 : Active 19 := (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have a4 : Active 22 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have a5 : Active 25 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have a6 : Active 28 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have a7 : Active 31 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have a8 : Active 35 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have a9 : Active 39 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have a10 : Active 43 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have a11 : Active 47 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have a12 : Active 51 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
  have a13 : Active 55 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))
  have a14 : Active 59 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))
  have a15 : Active 63 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))
  have a16 : Active 67 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))
  have a17 : Active 70 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))
  have a18 : Active 73 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))
  have a19 : Active 76 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))))
  have a20 : Active 79 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))))))
  have a21 : Active 82 := (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl))))))))))))))))))))))
  simp only [correction,run_append,run_take]
  rw [    bank_run 10 a0 _ _ (hr _ a0) _ s (hd _ a0),
    bank_run 13 a1 _ _ (hr _ a1) _ _ (data_flip _ _ a1 (hd _ a1)),
    bank_run 16 a2 _ _ (hr _ a2) _ _ (data_flip _ _ a2 (data_flip _ _ a2 (hd _ a2))),
    bank_run 19 a3 _ _ (hr _ a3) _ _ (data_flip _ _ a3 (data_flip _ _ a3 (data_flip _ _ a3 (hd _ a3)))),
    bank_run 22 a4 _ _ (hr _ a4) _ _ (data_flip _ _ a4 (data_flip _ _ a4 (data_flip _ _ a4 (data_flip _ _ a4 (hd _ a4))))),
    bank_run 25 a5 _ _ (hr _ a5) _ _ (data_flip _ _ a5 (data_flip _ _ a5 (data_flip _ _ a5 (data_flip _ _ a5 (data_flip _ _ a5 (hd _ a5)))))),
    bank_run 28 a6 _ _ (hr _ a6) _ _ (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (hd _ a6))))))),
    bank_run 31 a7 _ _ (hr _ a7) _ _ (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (hd _ a7)))))))),
    bank_run 35 a8 _ _ (hr _ a8) _ _ (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (hd _ a8))))))))),
    bank_run 39 a9 _ _ (hr _ a9) _ _ (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (hd _ a9)))))))))),
    bank_run 43 a10 _ _ (hr _ a10) _ _ (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (hd _ a10))))))))))),
    bank_run 47 a11 _ _ (hr _ a11) _ _ (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (hd _ a11)))))))))))),
    bank_run 51 a12 _ _ (hr _ a12) _ _ (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (hd _ a12))))))))))))),
    bank_run 55 a13 _ _ (hr _ a13) _ _ (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (hd _ a13)))))))))))))),
    bank_run 59 a14 _ _ (hr _ a14) _ _ (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (hd _ a14))))))))))))))),
    bank_run 63 a15 _ _ (hr _ a15) _ _ (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (hd _ a15)))))))))))))))),
    bank_run 67 a16 _ _ (hr _ a16) _ _ (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (hd _ a16))))))))))))))))),
    bank_run 70 a17 _ _ (hr _ a17) _ _ (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (hd _ a17)))))))))))))))))),
    bank_run 73 a18 _ _ (hr _ a18) _ _ (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (hd _ a18))))))))))))))))))),
    bank_run 76 a19 _ _ (hr _ a19) _ _ (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (data_flip _ _ a19 (hd _ a19)))))))))))))))))))),
    bank_run 79 a20 _ _ (hr _ a20) _ _ (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (data_flip _ _ a20 (hd _ a20))))))))))))))))))))),
    bank_run 82 a21 _ _ (hr _ a21) _ _ (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (data_flip _ _ a21 (hd _ a21))))))))))))))))))))))]
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
theorem programNC_eq (C : Secp256k1.Point) : WindowParityCaller.programNC C = WindowParityCaller.program C := by
  cases C <;> rfl

theorem certificate (replay : Window45Dialog.GenericReplay):
    Challenge.Certificate WindowParityRelease.entryNC WindowParityRelease.boundsNC:=
  WindowParityRelease.certificateOfSemanticsNC (fun C b R => by
    rw [programNC_eq]
    exact Window45Dialog.correct replay C b R)
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

open Stair44PointDivision
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
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h,bankIds]
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
  have hlt : ∀ (v : Bank) (u : Fin 16), 8*groupId v+u.val < 816 := by decide +kernel
  have hno : ∀ (v : Bank) (u : Fin 16), ¬ Elsewhere (8*groupId v+u.val) := by
    intro v u; revert v u; unfold Elsewhere; decide +kernel
  have hi_lt : i < 816 := by unfold Elsewhere at hi; omega
  have k := addr_inj (a:=8*groupId b+q.val) (b:=i) (hlt b q) hi_lt eq
  exact hno b q (k ▸ hi)
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
theorem division (g:wires WindowParityCaller.entryFieldHostedCut⊆callerDomain):
    wires WindowKernelPrograms.division⊆callerDomain:=by
  have original:=Stair44CallerSupport.division
  have f:=phaseHost_caller _ (WindowIntegerSites.forward true 4 (by decide))
  have b:=phaseHost_caller _ (WindowIntegerSites.backward false 85 (by decide))
  simp only [WindowKernelPrograms.division,WindowKernelPrograms.divBefore,WindowKernelPrograms.divAfter,
    WindowKernelPrograms.openWalk,Stair44Kernel.division,Stair44Kernel.divLead,Stair44Kernel.openR,
    Stair44DivTerm.routedClose,Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,
    Six505.rename_append,wires_append,Finset.union_subset_iff] at original ⊢
  tauto
theorem multiplication (k:Nat) (g:wires (WindowParityCaller.exitFieldHosted checkpointPrimitives)⊆callerDomain):
    wires (WindowKernelPrograms.multiplication k)⊆callerDomain:=by
  have original:=Stair44CallerSupport.multiplication k
  have f:=phaseHost_caller _ (WindowIntegerSites.forward false 84 (by decide))
  have b:=phaseHost_caller _ (WindowIntegerSites.backward true 4 (by decide))
  simp only [WindowKernelPrograms.multiplication,WindowKernelPrograms.mulBefore,WindowKernelPrograms.mulAfter,
    WindowKernelPrograms.openWalk,Stair44Kernel.multiplication,Stair44Kernel.beforeX,Stair44Kernel.mulLead,Stair44Kernel.openR,
    Stair44Kernel.mulRawTail,Stair44Kernel.finishM,Stair44Outer.forwardEnd,
    Six505.rename_append,wires_append,Finset.union_subset_iff] at original ⊢
  tauto

end ECDSAAdd.Entrant.StairPacket.WindowReleaseProof

end
end

-- ==== end PrizeTail05e06b1e9 ====

-- ==== begin PrizeTaila22007f05 ====
section

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Stair44Outer StockArchiveBanks StairV3Primitives StairPhysicalPhase
def free (q:Wire):Bool:=!(205773114712187275122282265982765293605562563561189812287139891611589843445849597337103538494103336978362213714661966168451171851648096542974182730298938690363272409754698411001089266389078812285291449861766214794211333330842948986826888135717666812766266187006046759537055486313122308420383943763511987145123427459459516126487590571586904268547089117918011279036204763364901996160144223273307447875459693702879511493135943689368591511483737771298575471633784665705161978870541934630194604427888602806707054647786582470712223963572206094038073344:Nat).testBit q
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
def beforeParityOdd := StairSchedule.hostedX ++ StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542)
def beforeGroup := StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram ++
  StairSchedule.fieldRename (renameProgram Prefix1590.borrow
    (StairSchedule.reverseLast cp ++ hostedGroup hostPlan false 41 98 2 ++
    StairSchedule.reverseSegment cp 22 12 490 500 ++ hostedGroup hostPlan false 36 96 2 ++
    StairSchedule.reverseSegment cp 32 22 480 490 ++ hostedGroup hostPlan false 30 93 3 ++
    StairSchedule.reverseSegment cp 47 32 465 480 ++ hostedGroup hostPlan false 22 90 3 ++
    StairSchedule.reverseSegment cp 62 47 450 465 ++ hostedGroup hostPlan false 13 85 5 ++
    StairSchedule.reverseSegment cp 87 62 425 450))
def beforeGroupOdd := StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram ++
  StairSchedule.fieldRename (renameProgram Prefix1590.borrow
    (StairSchedule.reverseLast cp ++
    PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1 ++
    PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1 ++
    PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2 ++
    PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2 ++
    PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4))
def afterGroup := StairSchedule.fieldRename (FourScratchWindow.unprefix ++
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false) (Rolling1588.placedFirstPacket false))
def afterGroupOdd := StairSchedule.fieldRename (FourScratchWindow.unprefix ++
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket false)
    (JointOdd1588.placedFirstPacketOdd WindowCallerCosts.oddFirstHalf false))
def leading (setup : Program) := setup ++ beforeParity ++ setup ++ beforeGroup
def leadingOdd (setup : Program) := setup ++ beforeParityOdd ++ setup ++ beforeGroupOdd
def field (setup group : Program) := leading setup ++ renameProgram fieldEquiv group ++ afterGroup
def fieldOdd (setup group : Program) := leadingOdd setup ++ renameProgram fieldEquiv group ++ afterGroupOdd

theorem ordinary : StairHostsSchedule.exitFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (WindowFieldCosts.group false 1 84) := by
  simp only [field,leading,beforeParity,beforeGroup,afterGroup,StairHostsSchedule.exitFieldHosted,
    exitLowSuffix,exitHeadSuffix,WindowFieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : WindowParityCaller.exitFieldHosted cp =
    fieldOdd WindowFieldParity.setup (WindowFieldCosts.group84 false) := by
  simp only [fieldOdd,leadingOdd,beforeParityOdd,beforeGroupOdd,afterGroupOdd,WindowParityCaller.exitFieldHosted,
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
private def past (q:Wire):Bool:=(180939578497055528381340555886972105278508634386471692433344651056468842455492551968605753108720236510606156341375616254805889977801910117699643979599013346951331785567366854493054705746989936027101548883133753420750226259356410440051146502167827208772920478394656641415965145086803519272414845853530467261180647566909180489658681653141169362245534189956705224747886492356240073856782829434037665175587309741396045870269781290955637990096896:Nat).testBit q
/-- The bank sites sit off the placement's zero region, so no packet permutation moves them. -/
private theorem src_fix (j : Nat) (hj : j < 102) (b : Bank) (i : Fin 16)
    (h16 : 16 ≤ OB5.sig 511 (siteAt b i))
    (hw : ¬ Placement5.workRegion (OB5.sig 511 (siteAt b i) - 16))
    (hh : ¬ Placement5.holeRegion (OB5.sig 511 (siteAt b i) - 16)) :
    src j b i = OB5.sig 511 (siteAt b i) := by
  unfold src
  generalize OB5.sig 511 (siteAt b i) = x at h16 hw hh ⊢
  apply (Equiv.symm_apply_eq (shifted (Placement5.pi j))).mpr
  have hx : x = base (x - 16) := by simp only [base, Wire] at *; omega
  rw [hx, shifted_base, Placement5.pi_outside j _ hj (fun h => h.elim hw hh)]
private theorem fixedSources:∀j∈List.range' 85 17,∀(b:Bank)(i:Fin 16),src j b i=src 85 b i:=by
  have hc : ∀ (b:Bank) (i:Fin 16), 16 ≤ OB5.sig 511 (siteAt b i) ∧
      ¬ Placement5.workRegion (OB5.sig 511 (siteAt b i) - 16) ∧
      ¬ Placement5.holeRegion (OB5.sig 511 (siteAt b i) - 16) := by decide +kernel
  intro j hj b i
  have hj' := List.mem_range'_1.mp hj
  obtain ⟨h16, hw, hh⟩ := hc b i
  rw [src_fix j (by omega) b i h16 hw hh, src_fix 85 (by omega) b i h16 hw hh]
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

theorem groups1542_std (d:Bool) (k j n:Nat) (lo:85≤j) (hi:j+n≤102) (dk:k≤68)
    (safe:∀q∈OddFullPass.P1LifeLoan.hostPlan1542.group d k j n,free q=true):
    Clear (hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 d k j n):=by
  have roles:∀q∈StairSchedule.exclusiveRoles,free q=true:=by decide +kernel
  intro q hit used
  obtain ⟨b,i,rfl⟩:=StockArchiveBanks.bank_rep q hit
  obtain host|role|inner:=StairWireCheck.rebindMany_support _ _ _ _ used
  · have ok:=safe _ host;rw [occupied] at ok;contradiction
  · have ok:=roles _ (List.mem_of_mem_drop role);rw [occupied] at ok;contradiction
  · exact regular d j n lo hi _ ((StockArchiveBanks.mem b i)) (placedGroups_sub d k dk j n inner)

theorem groups1542 (d:Bool) (k j n:Nat) (lo:85≤j) (hi:j+n≤102) (dk:k≤44)
    (safe:∀q∈OddFullPass.P1LifeLoan.hostPlan1542.group d k j n,free q=true):
    Clear (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 d k j n):=
  fun q hit used => groups1542_std d k j n lo hi (by omega) safe q hit
    (OddFullPass.P1LifeLoan.hostedGroup_wires_sub OddFullPass.P1LifeLoan.hostPlan1542 d k j n dk used)
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment425Ori:Clear (checkpointPrimitives.orient 450):=checked (by decide +kernel)
private theorem segment425OriR:Clear (checkpointPrimitives.orientR 450):=checked (by decide +kernel)
private theorem segment425P:Clear (renameProgram (OB5.sig 450) (Rolling1588.Integer.packFirst base true 450)):=checked (by decide +kernel)
private theorem segment425U:Clear (renameProgram (OB5.sig 450) (Rolling1588.unpackAtTick true 450)):=checked (by decide +kernel)
theorem forward425:Clear (StairSchedule.forwardSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 87 (by decide)) (tfFree 87 (by decide))) (mfFree 87 (by decide))) segment425Ori) segment425P) (packFree 62 (by decide))
theorem reverse425:Clear (StairSchedule.reverseSegment checkpointPrimitives 87 62 425 450):=
  both (both (both (both (both (unpackFree 62 (by decide)) segment425U) segment425OriR) (mrFree 87 (by decide))) (trFree 87 (by decide))) (packFree 87 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment450Ori:Clear (checkpointPrimitives.orient 465):=checked (by decide +kernel)
private theorem segment450OriR:Clear (checkpointPrimitives.orientR 465):=checked (by decide +kernel)
private theorem segment450P:Clear (renameProgram (OB5.sig 465) (Rolling1588.Integer.packFirst base true 465)):=checked (by decide +kernel)
private theorem segment450U:Clear (renameProgram (OB5.sig 465) (Rolling1588.unpackAtTick true 465)):=checked (by decide +kernel)
theorem forward450:Clear (StairSchedule.forwardSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 62 (by decide)) (tfFree 62 (by decide))) (mfFree 62 (by decide))) segment450Ori) segment450P) (packFree 47 (by decide))
theorem reverse450:Clear (StairSchedule.reverseSegment checkpointPrimitives 62 47 450 465):=
  both (both (both (both (both (unpackFree 47 (by decide)) segment450U) segment450OriR) (mrFree 62 (by decide))) (trFree 62 (by decide))) (packFree 62 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment465Ori:Clear (checkpointPrimitives.orient 480):=checked (by decide +kernel)
private theorem segment465OriR:Clear (checkpointPrimitives.orientR 480):=checked (by decide +kernel)
private theorem segment465P:Clear (renameProgram (OB5.sig 480) (Rolling1588.Integer.packFirst base true 480)):=checked (by decide +kernel)
private theorem segment465U:Clear (renameProgram (OB5.sig 480) (Rolling1588.unpackAtTick true 480)):=checked (by decide +kernel)
theorem forward465:Clear (StairSchedule.forwardSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 47 (by decide)) (tfFree 47 (by decide))) (mfFree 47 (by decide))) segment465Ori) segment465P) (packFree 32 (by decide))
theorem reverse465:Clear (StairSchedule.reverseSegment checkpointPrimitives 47 32 465 480):=
  both (both (both (both (both (unpackFree 32 (by decide)) segment465U) segment465OriR) (mrFree 47 (by decide))) (trFree 47 (by decide))) (packFree 47 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment480Ori:Clear (checkpointPrimitives.orient 490):=checked (by decide +kernel)
private theorem segment480OriR:Clear (checkpointPrimitives.orientR 490):=checked (by decide +kernel)
private theorem segment480P:Clear (renameProgram (OB5.sig 490) (Rolling1588.Integer.packFirst base true 490)):=checked (by decide +kernel)
private theorem segment480U:Clear (renameProgram (OB5.sig 490) (Rolling1588.unpackAtTick true 490)):=checked (by decide +kernel)
theorem forward480:Clear (StairSchedule.forwardSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 32 (by decide)) (tfFree 32 (by decide))) (mfFree 32 (by decide))) segment480Ori) segment480P) (packFree 22 (by decide))
theorem reverse480:Clear (StairSchedule.reverseSegment checkpointPrimitives 32 22 480 490):=
  both (both (both (both (both (unpackFree 22 (by decide)) segment480U) segment480OriR) (mrFree 32 (by decide))) (trFree 32 (by decide))) (packFree 32 (by decide))
end ECDSAAdd.Entrant.StairPacket.ExteriorPorts

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorPorts
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly
set_option maxRecDepth 50000
set_option maxHeartbeats 3500000
private theorem segment490Ori:Clear (checkpointPrimitives.orient 500):=checked (by decide +kernel)
private theorem segment490OriR:Clear (checkpointPrimitives.orientR 500):=checked (by decide +kernel)
private theorem segment490P:Clear (renameProgram (OB5.sig 500) (Rolling1588.Integer.packFirst base true 500)):=checked (by decide +kernel)
private theorem segment490U:Clear (renameProgram (OB5.sig 500) (Rolling1588.unpackAtTick true 500)):=checked (by decide +kernel)
theorem forward490:Clear (StairSchedule.forwardSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 22 (by decide)) (tfFree 22 (by decide))) (mfFree 22 (by decide))) segment490Ori) segment490P) (packFree 12 (by decide))
theorem reverse490:Clear (StairSchedule.reverseSegment checkpointPrimitives 22 12 490 500):=
  both (both (both (both (both (unpackFree 12 (by decide)) segment490U) segment490OriR) (mrFree 22 (by decide))) (trFree 22 (by decide))) (packFree 22 (by decide))
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
def beginW := opening false 84 ++ endF
def beginR := original false 84 ++ endF

theorem refBegin : beginR = Stair44Kernel.mulLead := by
  simp only [beginR,original,endF,Stair44Kernel.mulLead,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]

theorem begin_pair (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    ∃n, Paired false F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening false 84
  let B := original false 84
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

private theorem template (A P G T U : Program) :
    (A ++ ((P ++ G) ++ T)) ++ U = (((A ++ P) ++ G) ++ (T ++ U)) := by
  simp only [List.append_assoc]

def gROdd := renameProgram fieldEquiv (WindowFieldCosts.ogroup false 1 84)

def RCutOdd (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (a r : State) : Prop :=
  Paired false x a r rows ∧
  ∃ origin, FrontierReplay1591.Context origin ∧ origin (base 2400) = true ∧
    StairField2V3Seg.TraceOK x origin ∧ WindowFieldView.OCut 85 origin (StairField2V3Seg.pullIn r) ∧
    StairPacket.WindowFieldView.TagReady (StairField2V3Seg.pullIn r)

private theorem windowOddRel (x : Nat) (rows : StockArchiveBanks.Bank → Nat) :
    Relates gW gROdd (RCutOdd x rows) (Fits (fieldRows rows) C1) := by
  rintro a r ⟨pair, origin, ctx, en, tr, ocut, htag⟩ m
  refine ⟨WindowFieldJourney.oreferenceTape1542 false m, ?_⟩
  have ids : ∀ j ∈ bankIds, fieldRows rows j < 63145 := by
    intro j hj; obtain ⟨b, rfl⟩ := idAt j hj; rw [rowsAt]; exact (pair.labels b).1
  have chronological : ∀ j ∈ bankIds, ArchiveStockRows.Chronology (5 * j - 5) x p (fieldRows rows j) := by
    intro j hj; obtain ⟨b, rfl⟩ := idAt j hj; rw [rowsAt]
    have times : ∀ k : StockArchiveBanks.Bank, 5 * groupId k - 5 = StockArchiveBanks.tick k := by decide +kernel
    rw [times]; exact (pair.labels b).2
  apply hosted
  have hpull := fitsPull fieldEquiv fieldEquiv.injective fieldFix (fits pair)
  have hfe : pullState fieldEquiv r = StairField2V3Seg.pullIn r := rfl
  rw [hfe] at hpull ⊢
  exact WindowFieldView.ocaller false x (fieldRows rows) ids chronological origin ctx en tr
    (pullState fieldEquiv a) r m hpull ocut htag

private theorem pullState_basis_exit (f : Wire → Wire) (st : State) (q : Wire) :
    (pullState f st).basis q = st.basis (f q) := rfl

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
theorem noRole : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairSchedule.exclusiveRoles := by
  have h : ∀(b : Bank)(i : Fin 16),
      (StairLoan.maskOf StairSchedule.exclusiveRoles).testBit (siteAt b i) = false := by decide +kernel
  exact fun b i => StairLoan.not_mem_of_maskOf (h b i)
theorem noHost : ∀(b : Bank)(i : Fin 16), siteAt b i∉StairPhysicalLayout.hosts 87 := by
  have h : ∀(b : Bank)(i : Fin 16),
      (StairLoan.maskOf (StairPhysicalLayout.hosts 87)).testBit (siteAt b i) = false := by decide +kernel
  exact fun b i => StairLoan.not_mem_of_maskOf (h b i)
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

theorem firstOdd (d : Bool) : Clear (StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket d)
    (JointOdd1588.placedFirstPacketOdd WindowCallerCosts.oddFirstHalf d)) :=
  rebind (hostPlan.firstPacket d) rfl
    (JointOdd1588.placedFirstPacketOdd_passSup WindowCallerCosts.oddFirstHalf d
      (WindowCallerCosts.oddFirstHalf_support d))

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
theorem endPartOdd : Clear (afterGroupOdd ++ WindowExitStages.unpack) :=
  both (WindowExitClear.fieldClear (both unprefixSafe (WindowExteriorFixed.firstOdd false)))
    (WindowExitClear.renameClear Rolling1588Lifetime.phaseHost Rolling1588Lifetime.phaseHost.injective
      phaseFix firstUnpack_free)
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

theorem beforeOdd : Clear beforeGroupOdd := by
  have hclear1542 (dep f c : Nat) (lo : 85 ≤ f) (hi : f + c ≤ 102) (hd : dep ≤ 44)
      (tab : (OddFullPass.P1LifeLoan.hostPlan1542.group false dep f c).all ExteriorPorts.free = true) :
      Clear (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false dep f c) :=
    ExteriorPorts.groups1542 false dep f c lo hi hd (List.all_eq_true.mp tab)
  have hrows : Clear (StairSchedule.reverseLast checkpointPrimitives ++
      OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 42 98 2 ++ StairSchedule.reverseSegment checkpointPrimitives 22 12 490 500 ++
      OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 37 96 2 ++ StairSchedule.reverseSegment checkpointPrimitives 32 22 480 490 ++
      OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 31 93 3 ++ StairSchedule.reverseSegment checkpointPrimitives 47 32 465 480 ++
      OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 23 90 3 ++ StairSchedule.reverseSegment checkpointPrimitives 62 47 450 465 ++
      OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 14 85 5 ++ StairSchedule.reverseSegment checkpointPrimitives 87 62 425 450) := by
    apply both _ reverse425
    apply both _ (hclear1542 14 85 5 (by decide) (by decide) (by decide) (by decide +kernel))
    apply both _ reverse450
    apply both _ (hclear1542 23 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
    apply both _ reverse465
    apply both _ (hclear1542 31 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
    apply both _ reverse480
    apply both _ (hclear1542 37 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
    apply both _ reverse490
    apply both _ (hclear1542 42 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
    exact reverseLast
  apply both (both hostedX (fieldRename_free clearSafe))
  rw [placedShape]
  apply fieldMapped
  exact fun q hq hw => hrows q hq (PackCutOddExit.cutRows_sub hw)
end ECDSAAdd.Entrant.StairPacket.WindowExitReady

end

-- ==== begin: multiplication exit geometry ====
section

namespace ECDSAAdd.Entrant.StairPacket.WindowStartStates
open Arithmetic MappedCompressed Secp256k1 WideReference Stair44Kernel Rolling1588Lifetime StairConcreteAssembly
open WindowKernelPrograms StockArchiveBanks
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
attribute [local irreducible] run measurementCount FrontierEntry1591Native.forward
theorem multiplicationNC (k : Nat) {s t : State} (F : ExitFrame k s) (hag : OddStockLockstep.AgreeOutsideR t s)
    (m : List Bool) :
    Paired false F.x (pullState phaseHost (run (opening false 84) m t))
      (pullState phaseHost (run (original false 84) m t)) (StockRowVector.rows F.x p) := by
  have hin_t : SkywalkArithmeticInput base F.x (regValue (wireBlock base 2056 256) t.basis) t.basis :=
    FrontierEntry1591Kernel.paired_input F.x F.Y.val s t F.input hag.2
  rw [opening, original, run_rename _ phaseHost.injective, run_rename _ phaseHost.injective,
    OddStockLockstep.mulPullPhaseHost_odd k F hag]
  exact open_raw false 84 F.x _ F.x_pos F.x_lt (by decide) F.sharedNodup t hin_t m
end ECDSAAdd.Entrant.StairPacket.WindowStartStates

namespace ECDSAAdd.Entrant.StairPacket.WindowExitPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires
def beforeParityOddNC := StairSchedule.hostedX ++
  StairSchedule.fieldRename (WindowParityCaller.exitLowPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542)
def leadingOddNC (setup : Program) := setup ++ beforeParityOddNC ++ setup ++ beforeGroupOdd
def fieldOddNC (setup group : Program) := leadingOddNC setup ++ renameProgram fieldEquiv group ++ afterGroupOdd
theorem correctedNC : WindowParityCaller.exitFieldHostedNC cp =
    fieldOddNC WindowFieldParity.setup (WindowFieldCosts.group84 false) := by
  simp only [fieldOddNC,leadingOddNC,beforeParityOddNC,beforeGroupOdd,afterGroupOdd,WindowParityCaller.exitFieldHostedNC,
    WindowCallerCosts.exitLowSuffix,WindowCallerCosts.exitHeadSuffix,←placedShape,fieldRename_append,rename_append,List.append_assoc]
end ECDSAAdd.Entrant.StairPacket.WindowExitPieces

namespace ECDSAAdd.Entrant.StairPacket.WindowExitStages
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates WindowMiddlePieces ExteriorPorts WindowExitPieces
open WindowFieldMask WindowFieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount
theorem begin_pairNC (k : Nat) {s t : State} (F : ExitFrame k s) (hag : OddStockLockstep.AgreeOutsideR t s)
    (m : List Bool) :
    ∃n, Paired false F.x (run beginW m t) (run beginR n t) (StockRowVector.rows F.x p) := by
  let A := opening false 84
  let B := original false 84
  let u := m.drop (measurementCount A)
  refine ⟨joinTapes B m u,?_⟩
  rw [beginW,beginR,joined,run_append,run_take]
  apply pairUnpull phaseHost phaseFix
  rw [endF,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective]
  exact (WindowStartStates.multiplicationNC k F hag m).through _ forwardEnd_free _

theorem begin_recordNC (k : Nat) {s t : State} (F : ExitFrame k s) (hag : OddStockLockstep.AgreeOutsideR t s)
    (m : List Bool) :
    run beginR m t = run StairField2V3Replay.exitReferenceOpening m t := by
  rw [refBegin]
  exact OddStockLockstep.leadM_odd k F hag m

def newPNC := (beginW ++ WindowParityCaller.exitFieldHostedNC checkpointPrimitives) ++ unpack

theorem newShapeNC : WindowMiddleContract.mulHeadNC = newPNC := by
  simp only [WindowMiddleContract.mulHeadNC,WindowKernelPrograms.mulBeforeNC,newPNC,beginW,opening,endF,unpack,
    Six505.rename_append,List.append_assoc]
end ECDSAAdd.Entrant.StairPacket.WindowExitStages

namespace ECDSAAdd.Entrant.StairPacket.WindowExitReplay
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates WindowMiddlePieces ExteriorPorts WindowExitPieces
open WindowFieldMask WindowFieldJourney WindowExitStages
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] run measurementCount wires

private theorem beginRelNC (k : Nat) {s t : State} (F : ExitFrame k s) (hag : OddStockLockstep.AgreeOutsideR t s) :
    Relates beginW beginR (fun a r=>a=t ∧ r=t) (RStart F.x (StockRowVector.rows F.x p) t) := by
  rintro a r ⟨rfl,eq⟩ m
  subst r
  obtain ⟨n,rel⟩ := begin_pairNC k F hag m
  exact ⟨n,rel,n,begin_recordNC k F hag n⟩

def leadingOddOKNC : Prop := ∀ (x : Nat) (rows : StockArchiveBanks.Bank → Nat) (a r : State) (m : List Bool),
  Paired false x a r rows → ∃ n, Paired false x (run (leadingOddNC WindowFieldParity.setup) m a)
    (run (leadingOddNC StairSchedule.paritySetup) n r) rows

private theorem leadingOddRelNC (ok : leadingOddOKNC) (k : Nat) {s t : State} (F : ExitFrame k s)
    (hag : OddStockLockstep.AgreeOutsideR t s)
    (hval : regValue OddStockLockstep.fieldR t.basis = P1Life.oddWord (F.Y / 2))
    (rows : StockArchiveBanks.Bank → Nat) :
    Relates (leadingOddNC WindowFieldParity.setup) (leadingOddNC StairSchedule.paritySetup)
      (RStart F.x rows t) (RCutOdd F.x rows) := by
  rintro a r ⟨pair, u, rfl⟩ m
  obtain ⟨n, h⟩ := ok _ _ _ _ m pair
  have hsh : StairField2V3Replay.exitReferenceOpening ++ leadingOddNC StairSchedule.paritySetup =
      OddStockLockstep.stockOddMulPrefix21NC := by
    simp only [OddStockLockstep.stockOddMulPrefix21NC, OddStockLockstep.stockOddMulLeadingNC,
      OddStockLockstep.stockOddMulBeforeParityNC, OddStockLockstep.stockOddMulBeforeGroup,
      leadingOddNC, beforeParityOddNC, beforeGroupOdd, List.append_assoc]
  have hcut := (OddStockLockstep.stockOddMulNC_cut21 k F hag hval
    (WindowFieldJourney.joinTapes StairField2V3Replay.exitReferenceOpening u n)).2
  rw [← hsh, WindowFieldJourney.joined] at hcut
  exact ⟨n, h, hcut⟩

private theorem newPathOddNC : WindowMiddleContract.mulHeadNC =
    (((beginW ++ leadingOddNC WindowFieldParity.setup) ++ gW) ++ (afterGroupOdd ++ unpack)) := by
  rw [newShapeNC, newPNC, correctedNC]
  exact template _ _ _ _ _

private theorem stockOddPathNC : OddStockLockstep.stockOddMulHeadNC =
    (((beginR ++ leadingOddNC StairSchedule.paritySetup) ++ gROdd) ++ (afterGroupOdd ++ unpack)) := by
  simp only [OddStockLockstep.stockOddMulHeadNC, OddStockLockstep.stockOddMulLeadingNC,
    OddStockLockstep.stockOddMulBeforeParityNC, OddStockLockstep.stockOddMulBeforeGroup,
    OddStockLockstep.stockOddMulAfterGroup, refBegin, leadingOddNC, beforeParityOddNC,
    beforeGroupOdd, gROdd, afterGroupOdd, unpack, JointOdd1588.hostedFirstPacketOdd,
    StairConcreteAssembly.hostPlan, List.append_assoc]

theorem exitOddNC (leadingLaw : leadingOddOKNC) (endClear : Clear (afterGroupOdd ++ unpack)) :
    WindowKernelReplay.OddExitContractNC := by
  intro k s t F hag hval m
  have keep := pass (rows := fieldRows (StockRowVector.rows F.x p)) (cs := C1)
    (P := afterGroupOdd ++ unpack) (fun q h => endClear q ((whole_iff q).mp h))
  have total := compose (compose (compose (beginRelNC k F hag) (leadingOddRelNC leadingLaw k F hag hval _))
    (windowOddRel _ _)) keep
  obtain ⟨n, out⟩ := total t t ⟨rfl, rfl⟩ m
  rw [← newPathOddNC, ← stockOddPathNC] at out
  have paired := fitsPull phaseHost phaseHost.injective phaseFix out
  obtain ⟨nOld, hAg, _⟩ := OddStockLockstep.stockOddMulHeadNC_agree_oldMulHead k F hag hval n
  have nativeOld := WindowEndBytes.mul_native k F nOld
  have nativeOdd : ∀ b, nativeAt true b (StockRowVector.rows F.x p b)
      (pullState phaseHost (run OddStockLockstep.stockOddMulHeadNC n t)) := by
    intro b i
    have hnotR : phaseHost (siteAt b i) ∉ OddStockLockstep.fieldR :=
      OddStockLockstep.fieldR_disjoint_pool _
        (Stair44DivTerm.host_pool _ (List.mem_toFinset.mp (StockInverseReplay.archives_pool _ (StockArchiveBanks.mem b i))))
    have hb := nativeOld.bytes b i
    rw [pullState_basis_exit] at hb ⊢
    exact (hAg.2 (phaseHost (siteAt b i)) hnotR).trans hb
  exact ⟨n, pairFinished paired nativeOld.ids nativeOdd⟩
end ECDSAAdd.Entrant.StairPacket.WindowExitReplay

namespace ECDSAAdd.Entrant.StairPacket.WindowExitClear
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime StairConcreteAssembly
open StockArchiveBanks WindowExitPieces WindowExitStages ExteriorPorts StairField13V3
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] wires run measurementCount
theorem leadingOddNC (pre : Clear beforeParityOddNC) (next : Clear beforeGroupOdd) :
    WindowExitReplay.leadingOddOKNC := by
  intro x rows a r m pair
  exact compose (compose (compose parity (pass pre)) parity) (pass next) a r pair m
end ECDSAAdd.Entrant.StairPacket.WindowExitClear

namespace ECDSAAdd.Entrant.StairPacket.WindowExitOuter
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts WindowExitPieces
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires
theorem preOddNC : Clear beforeParityOddNC := by
  apply both hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  apply WindowExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel)
  have h44 : Clear (StairHostsSchedule.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 44 100 2) :=
    ExteriorPorts.groups1542_std false 44 100 2 (by decide) (by decide) (by decide)
      (fun _ h => by simp [OddFullPass.P1LifeLoan.hostPlan1542] at h)
  have hsub : wires (WindowParityCaller.exitHeadPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ⊆
      wires (OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    have e : OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542 =
        OddFullPass.HalfConvertOdd.center760OddLoan ++
          WindowParityCaller.exitHeadPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542 := by
      simp only [OddFullPass.P1LifeLoan.exitHeadPrefixOdd, WindowParityCaller.exitHeadPrefixOddNC, List.append_assoc]
    rw [e, wires_append]
    exact Finset.subset_union_right
  intro q hq hw
  have hu := OddFullPass.P1LifeLoan.exitHeadPrefixOdd_wires_sub OddFullPass.P1LifeLoan.hostPlan1542 (hsub hw)
  simp only [Finset.mem_union] at hu
  rcases hu with ((h1 | h2) | h3) | h4
  · exact WindowExteriorFixed.center q hq h1
  · exact WindowExteriorFixed.copy q hq h2
  · exact WindowExteriorFixed.mulEndpoint q hq h3
  · exact h44 q hq h4
end ECDSAAdd.Entrant.StairPacket.WindowExitOuter

namespace ECDSAAdd.Entrant.StairPacket.WindowExitReady
open Arithmetic MappedCompressed StairConcreteAssembly StairHostsSchedule ExteriorPorts WindowExitPieces WindowExitOuter
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires
theorem exitOddNC : WindowKernelReplay.OddExitContractNC :=
  WindowExitReplay.exitOddNC (WindowExitClear.leadingOddNC preOddNC beforeOdd) endPartOdd
end ECDSAAdd.Entrant.StairPacket.WindowExitReady

end
-- ==== end: multiplication exit geometry ====
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
def beforeGroupOdd := StairSchedule.fieldRename (StairLoan.rebindMany StairSchedule.exclusiveRoles
  (hostPlan.firstPacket true) (JointOdd1588.placedFirstPacketOdd WindowCallerCosts.oddFirstHalf true) ++
  FourScratchWindow.clearProgram)
def rawTail := StairSchedule.forwardSegment cp 87 62 425 450 ++ hostedGroup hostPlan true 13 85 5 ++
    StairSchedule.forwardSegment cp 62 47 450 465 ++ hostedGroup hostPlan true 22 90 3 ++
    StairSchedule.forwardSegment cp 47 32 465 480 ++ hostedGroup hostPlan true 30 93 3 ++
    StairSchedule.forwardSegment cp 32 22 480 490 ++ hostedGroup hostPlan true 36 96 2 ++
    StairSchedule.forwardSegment cp 22 12 490 500 ++ hostedGroup hostPlan true 41 98 2 ++ StairSchedule.forwardLast cp
def rawTailOdd := StairSchedule.forwardSegment cp 87 62 425 450 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 5 ++
    StairSchedule.forwardSegment cp 62 47 450 465 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 3 ++
    StairSchedule.forwardSegment cp 47 32 465 480 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 3 ++
    StairSchedule.forwardSegment cp 32 22 480 490 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 2 ++
    StairSchedule.forwardSegment cp 22 12 490 500 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 2 ++ StairSchedule.forwardLast cp
def pre := renameProgram fieldEquiv rawTail ++ StairSchedule.fieldRename FourScratchWindow.unprefix
def preOdd := renameProgram fieldEquiv rawTailOdd ++ StairSchedule.fieldRename FourScratchWindow.unprefix
def between := StairSchedule.hostedX ++ StairSchedule.fieldRename (entryLowSuffix hostPlan) ++ StairSchedule.hostedX
def betweenOdd := StairSchedule.hostedX ++ StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++ StairSchedule.hostedX
def post := renameProgram phaseHost Stair44Outer.reverseEnd
def field (S G : Program) := (((beforeGroup ++ renameProgram fieldEquiv G) ++ pre) ++ S) ++ between ++ S
def fieldOdd (S G : Program) := (((beforeGroupOdd ++ renameProgram fieldEquiv G) ++ preOdd) ++ S) ++ betweenOdd ++ S

theorem ordinary : StairHostsSchedule.entryFieldHosted cp hostPlan =
    field StairSchedule.paritySetup (WindowFieldCosts.group true 1 84) := by
  simp only [field,beforeGroup,pre,between,rawTail,StairHostsSchedule.entryFieldHosted,
    entryLowPrefix,entryTailPrefix,WindowFieldCosts.group,←placedShape,fieldRename_append,rename_append,List.append_assoc]

theorem corrected : WindowParityCaller.entryFieldHosted cp =
    fieldOdd WindowFieldParity.setup (WindowFieldCosts.group84 true) := by
  simp only [fieldOdd,beforeGroupOdd,preOdd,betweenOdd,rawTailOdd,WindowParityCaller.entryFieldHosted,
    WindowCallerCosts.entryLowPrefix,WindowCallerCosts.entryTailPrefix,←placedShape,fieldRename_append,rename_append,List.append_assoc]

/-- The odd field rows with the five packet-cut rows. -/
def rawTailOddCut := PackCutOdd.cutRowOdd 87 62 425 450 14 85 4 ++ (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2 ++ (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2 ++ (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1 ++ (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1 ++ StairSchedule.forwardLast cp))))
def preOddCut := renameProgram fieldEquiv rawTailOddCut ++ StairSchedule.fieldRename FourScratchWindow.unprefix
def fieldOddCut (S G : Program) := (((beforeGroupOdd ++ renameProgram fieldEquiv G) ++ preOddCut) ++ S) ++ betweenOdd ++ S

theorem correctedCut : WindowParityCaller.entryFieldHostedCut =
    fieldOddCut WindowFieldParity.setup (WindowFieldCosts.group84 true) := by
  simp only [fieldOddCut,beforeGroupOdd,preOddCut,betweenOdd,rawTailOddCut,WindowParityCaller.entryFieldHostedCut,
    WindowCallerCosts.entryLowPrefixCut,WindowCallerCosts.entryTailPrefixCut,←placedShape,fieldRename_append,
    rename_append,List.append_assoc]

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
theorem beforeOddFree : Clear beforeGroupOdd := fieldRename_free (both (WindowExteriorFixed.firstOdd true) clearSafe)
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
private theorem clear_hostedGroup1542 (d : Bool) (dep f c : Nat) (lo : 85 ≤ f) (hi : f + c ≤ 102) (hd : dep ≤ 44)
    (tab : (OddFullPass.P1LifeLoan.hostPlan1542.group d dep f c).all ExteriorPorts.free = true) :
    Clear (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 d dep f c) :=
  ExteriorPorts.groups1542 d dep f c lo hi hd (List.all_eq_true.mp tab)

theorem preOddFree : Clear preOdd := by
  apply both _ (fieldRename_free unprefixSafe)
  apply fieldMapped
  apply both _ forwardLast
  apply both _ (clear_hostedGroup1542 true 42 98 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward490
  apply both _ (clear_hostedGroup1542 true 37 96 2 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward480
  apply both _ (clear_hostedGroup1542 true 31 93 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward465
  apply both _ (clear_hostedGroup1542 true 23 90 3 (by decide) (by decide) (by decide) (by decide +kernel))
  apply both _ forward450
  exact both forward425 (clear_hostedGroup1542 true 14 85 5 (by decide) (by decide) (by decide) (by decide +kernel))

theorem preOddCut_sub : preOddCut.Sublist preOdd := by
  have e : rawTailOdd =
      (StairSchedule.forwardSegment StairField13V3Clean.cp 87 62 425 450 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 (4 + 1)) ++
      ((StairSchedule.forwardSegment StairField13V3Clean.cp 62 47 450 465 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 (2 + 1)) ++
      ((StairSchedule.forwardSegment StairField13V3Clean.cp 47 32 465 480 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 (2 + 1)) ++
      ((StairSchedule.forwardSegment StairField13V3Clean.cp 32 22 480 490 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 (1 + 1)) ++
      ((StairSchedule.forwardSegment StairField13V3Clean.cp 22 12 490 500 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 (1 + 1)) ++
        StairSchedule.forwardLast StairField13V3Clean.cp)))) := by
    simp only [rawTailOdd, List.append_assoc]
  unfold preOddCut preOdd
  rw [e]
  exact (PackCutSub.rename_sub _ ((PackCutOdd.row_subOdd 87 62 425 450 14 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp1_1542).append
      ((PackCutOdd.row_subOdd 62 47 450 465 23 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp2_1542).append
      ((PackCutOdd.row_subOdd 47 32 465 480 31 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp3_1542).append
      ((PackCutOdd.row_subOdd 32 22 480 490 37 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp4_1542).append
      ((PackCutOdd.row_subOdd 22 12 490 500 42 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp5_1542).append
      (List.Sublist.refl _))))))).append (List.Sublist.refl _)

theorem preOddCutFree : Clear preOddCut :=
  fun q hq hw => preOddFree q hq (PackCutSub.wires_sub preOddCut_sub q hw)

theorem betweenOddFree : Clear betweenOdd := by
  apply both _ WindowExitOuter.hostedX
  apply both WindowExitOuter.hostedX
  apply fieldRename_free
  apply both _ unprefixSafe
  apply both clearSafe
  apply WindowExitClear.renameClear Prefix1590.borrow Prefix1590.borrow.injective
    (by unfold Fixed; decide +kernel)
  have h44 : Clear (hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 44 100 2) :=
    ExteriorPorts.groups1542_std true 44 100 2 (by decide) (by decide) (by decide) (fun _ h => by simp [OddFullPass.P1LifeLoan.hostPlan1542] at h)
  intro q hq hw
  have hu := OddFullPass.P1LifeLoan.entryTailSuffixOdd_wires_sub OddFullPass.P1LifeLoan.hostPlan1542 hw
  simp only [Finset.mem_union] at hu
  rcases hu with ((h1 | h2) | h3) | h4
  · exact h44 q hq h1
  · exact WindowExteriorFixed.divEndpoint q hq h2
  · exact WindowExteriorFixed.copy q hq h3
  · exact WindowExteriorFixed.canon q hq h4
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
def beginW := opening true 4 ++ pack
def beginR := original true 4 ++ pack
def prefixW := (beginW ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group84 true)
def prefixR := (beginR ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group true 1 84)

theorem refBegin : beginR = Stair44Kernel.divLead := by
  simp only [beginR,original,pack,Stair44Kernel.divLead,Six505.rename_append]

theorem begin_pair {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃n, Paired true F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening true 4
  let B := original true 4
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

def prefixWOdd := (beginW ++ beforeGroupOdd) ++ renameProgram fieldEquiv (WindowFieldCosts.group84 true)
def prefixROdd := (beginR ++ beforeGroupOdd) ++ renameProgram fieldEquiv (WindowFieldCosts.ogroup true 1 84)

theorem stockOddShapeCut : OddStockLockstep.stockOddDivHeadCut =
    prefixROdd ++ WindowReturningTail.program preOddCut betweenOdd post StairSchedule.paritySetup := by
  simp only [OddStockLockstep.stockOddDivHeadCut, OddStockLockstep.stockOddDivBeforeGroup,
    OddStockLockstep.stockOddDivPreCut, OddStockLockstep.stockOddDivRawTailCut,
    OddStockLockstep.stockOddDivBetween, OddStockLockstep.stockOddDivPost,
    prefixROdd, refBegin, beforeGroupOdd, preOddCut, rawTailOddCut, betweenOdd, post,
    JointOdd1588.hostedFirstPacketOdd, StairConcreteAssembly.hostPlan, WindowReturningTail.program, List.append_assoc]

theorem newShapeOddCut : WindowMiddleContract.divHead =
    prefixWOdd ++ WindowReturningTail.program preOddCut betweenOdd post WindowFieldParity.setup := by
  simp only [WindowMiddleContract.divHead, WindowKernelPrograms.divBefore, correctedCut, fieldOddCut,
    prefixWOdd, beginW, opening, pack, post, WindowReturningTail.program, Six505.rename_append, List.append_assoc]

theorem stockOddShape : OddStockLockstep.stockOddDivHead =
    prefixROdd ++ WindowReturningTail.program preOdd betweenOdd post StairSchedule.paritySetup := by
  simp only [OddStockLockstep.stockOddDivHead, OddStockLockstep.stockOddDivBeforeGroup,
    OddStockLockstep.stockOddDivPre, OddStockLockstep.stockOddDivRawTail,
    OddStockLockstep.stockOddDivBetween, OddStockLockstep.stockOddDivPost,
    prefixROdd, refBegin, beforeGroupOdd, preOdd, rawTailOdd, betweenOdd, post,
    JointOdd1588.hostedFirstPacketOdd, StairConcreteAssembly.hostPlan, WindowReturningTail.program, List.append_assoc]

private theorem begin_pair_odd {tOdd tStd : State} (FStd : EntryFrame tStd)
    (hag : OddStockLockstep.AgreeOutsideR tOdd tStd) (m : List Bool) :
    ∃ n, Paired true FStd.x (run beginW m tOdd) (run beginR n tOdd) (StockRowVector.rows FStd.x p) := by
  let A := opening true 4
  let B := original true 4
  let t := m.drop (measurementCount A)
  have hnum : skywalkArithmeticNumerator base = OddStockLockstep.fieldR := rfl
  have hinOdd : SkywalkArithmeticInput base FStd.x (regValue OddStockLockstep.fieldR tOdd.basis) tOdd.basis :=
    FrontierEntry1591Kernel.paired_input FStd.x (BalancedField.centerWord (FStd.Y / 2)) tStd tOdd
      (StairField13V3Clean.entryInput FStd) (fun q hq => hag.2 q (hnum ▸ hq))
  have hpullOdd : pullState phaseHost tOdd = tOdd := by
    have hpullStd := StairField13V3Clean.pull_phaseHost_entry FStd
    apply State.extensionality
    · rfl
    · funext q
      by_cases hr : q ∈ OddStockLockstep.fieldR
      · change tOdd.basis (phaseHost q) = tOdd.basis q
        rw [OddStockLockstep.phaseHost_fix_fieldR q hr]
      · have hnr : phaseHost q ∉ OddStockLockstep.fieldR := by
          intro hmem
          have hf := OddStockLockstep.phaseHost_fix_fieldR (phaseHost q) hmem
          exact hr (phaseHost.injective hf ▸ hmem)
        change tOdd.basis (phaseHost q) = tOdd.basis q
        rw [hag.2 _ hnr, hag.2 _ hr]
        exact congrFun (congrArg State.basis hpullStd) q
  have hopen : Paired true FStd.x (pullState phaseHost (run A m tOdd))
      (pullState phaseHost (run B m tOdd)) (StockRowVector.rows FStd.x p) := by
    dsimp only [A, B]
    rw [opening, original, run_rename _ phaseHost.injective, run_rename _ phaseHost.injective, hpullOdd]
    exact WindowStartStates.open_raw true 4 FStd.x _ FStd.x_pos FStd.x_lt (by decide) FStd.sharedNodup tOdd hinOdd _
  refine ⟨joinTapes B m t, ?_⟩
  rw [beginW, beginR, joined, run_append, run_take]
  apply pairUnpull phaseHost phaseFix
  rw [pack, run_rename _ phaseHost.injective, run_rename _ phaseHost.injective]
  exact hopen.through _ firstPack_free _

private theorem pull_fieldEquiv_eq_pullIn (st : State) :
    pullState ExteriorPorts.fieldEquiv st = StairField2V3Seg.pullIn st := rfl

private theorem starts_odd {tOdd tStd : State} (FStd : EntryFrame tStd)
    (hag : OddStockLockstep.AgreeOutsideR tOdd tStd)
    (hval : regValue OddStockLockstep.fieldR tOdd.basis = P1Life.oddWord (FStd.Y / 2))
    (m : List Bool) :
    ∃ old, Fits (fieldRows (StockRowVector.rows FStd.x p)) (finalCode true (plan true) (initialCode true))
      (run prefixWOdd m tOdd) (run prefixROdd old tOdd) := by
  obtain ⟨n0, pair0⟩ := begin_pair_odd FStd hag m
  let tBef := m.drop (measurementCount beginW)
  let n1 := joinTapes beginR n0 tBef
  have pair1 : Paired true FStd.x (run (beginW ++ beforeGroupOdd) m tOdd)
      (run (beginR ++ beforeGroupOdd) n1 tOdd) (StockRowVector.rows FStd.x p) := by
    rw [run_append, run_take, joined]
    exact pair0.through _ beforeOddFree _
  have heq3 : run (beginR ++ beforeGroupOdd) n1 tOdd = run OddStockLockstep.stockOddDivPrefix3 n1 tOdd := by
    have hcp : StairField13V3Clean.cp = checkpointPrimitives := rfl
    have h409 : (405 : Nat) + 4 = 409 := rfl
    have hmc : measurementCount beginR = measurementCount (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase StairField13V3Clean.cp)) := by
      rw [beginR, original, h409, pack, hcp, WindowStockHead.shapeD, measurementCount_append,
          (renameProgram_counts _ _).2, (renameProgram_counts _ _).2, (renameProgram_counts _ _).2,
          measurementCount_append, Stair44Kernel.open_count]
    have hbg : beforeGroupOdd = OddStockLockstep.stockOddDivBeforeGroup := by
      simp only [beforeGroupOdd, OddStockLockstep.stockOddDivBeforeGroup,
        JointOdd1588.hostedFirstPacketOdd, StairConcreteAssembly.hostPlan]
    have hlead := OddStockLockstep.divLead_eq_firstPhase_odd FStd hag (n1.take (measurementCount beginR))
    rw [← refBegin] at hlead
    rw [OddStockLockstep.stockOddDivPrefix3, run_append beginR,
        run_append (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase StairField13V3Clean.cp)),
        ← hmc, hbg, hlead]
  obtain ⟨_, origin, ctx, en, tr, ocut, htag⟩ := OddStockLockstep.stockOddDiv_cut3 FStd hag hval n1
  rw [← heq3] at ocut htag
  let tGrp := m.drop (measurementCount (beginW ++ beforeGroupOdd))
  let tape := oreferenceTape1542 true tGrp
  refine ⟨joinTapes (beginR ++ beforeGroupOdd) n1 tape, ?_⟩
  rw [prefixWOdd, prefixROdd, run_append, run_take, joined]
  obtain ⟨bound, trace⟩ := ExteriorEntryCut.history pair1.labels
  apply hosted
  obtain ⟨a1, ha1⟩ : ∃ st, run (beginW ++ beforeGroupOdd) m tOdd = st := ⟨_, rfl⟩
  obtain ⟨r1, hr1⟩ : ∃ st, run (beginR ++ beforeGroupOdd) n1 tOdd = st := ⟨_, rfl⟩
  rw [ha1, hr1] at pair1 ⊢
  rw [hr1] at ocut htag
  have hpull := fitsPull fieldEquiv fieldEquiv.injective fieldFix (fits pair1)
  rw [pull_fieldEquiv_eq_pullIn] at hpull ⊢
  exact WindowFieldView.ocaller true FStd.x (fieldRows (StockRowVector.rows FStd.x p)) bound trace
    origin ctx en tr (StairField2V3Seg.pullIn a1) r1 tGrp hpull ocut htag

end ECDSAAdd.Entrant.StairPacket.ExteriorDivReady

end

-- ==== begin: division ====

section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelPrograms
open Arithmetic MappedCompressed Baselines Stair44Placement Stair44PointMap Stair44WalkMap Stair44Kernel
open Stair44Outer Rolling1588Lifetime Secp256k1 StairConcreteAssembly StairSemanticFinal
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

/-- The division kernel without `canon760OddLoan`. -/
def divBeforeNC : Program :=
  renameProgram phaseHost (openWalk true 4 ++ checkpointPrimitives.firstPack) ++
    WindowParityCaller.entryFieldHostedCutNC
def divisionNC : Program := divBeforeNC ++ renameProgram phaseHost divAfter

theorem div_splitNC :
    FrontierEntry1591Callers.entry divisionNC layout = Stair44Splits.tick ++ WindowParityCaller.divideNC := by
  change kernelPlace (divBeforeNC ++ renameProgram phaseHost divAfter) = _
  simp only [divBeforeNC, divAfter, openWalk, WindowParityCaller.divideNC, kernelPlace, Six505.rename_append,
    List.append_assoc]
  change phasePlace Stair44Kernel.firstR ++ _ = Stair44Splits.tick ++ _
  rw [Stair44Splits.tick_eq]
  rfl

end ECDSAAdd.Entrant.StairPacket.WindowKernelPrograms

namespace ECDSAAdd.Entrant.StairPacket.WindowMiddleContract
open Arithmetic MappedCompressed Rolling1588Lifetime Secp256k1 StairConcreteAssembly
open WindowKernelPrograms StockArchiveBanks

def divHeadNC := divBeforeNC ++ renameProgram phaseHost Stair44Outer.reverseEnd

theorem div_head_splitNC : WindowKernelPrograms.divisionNC = divHeadNC ++ renameProgram phaseHost
    (WindowWalkCosts.backward false 85 ++ renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)) := by
  simp only [WindowKernelPrograms.divisionNC, divAfter, divHeadNC, Six505.rename_append, List.append_assoc]

end ECDSAAdd.Entrant.StairPacket.WindowMiddleContract

end

section
set_option autoImplicit false

namespace ECDSAAdd.Entrant.OddStockLockstep

open ECDSAAdd Arithmetic RecordedQuantum Challenge MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairHostsSchedule StairField2V3Seg StairField2V3Replay
open StairField2V3Delta StairField2V3Couple StairField2V3Entry StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastRecX StairField2V3EntryPlanR StairField2V3ExitPlanR
open StairField13V3 StairField13V3Clean StairOuterPlacement StairPhysicalLayout
open StairLoanExitReachX StairLoanField7Transport StairPacket

set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] run measurementCount wires renameProgram cut Rolling1588TickGap.forward

theorem pullOut_agreeOutsideR_NC {a b : State} (h : AgreeOutsideR a b) :
    AgreeOutsideR (pullOut a) (pullOut b) := by
  refine ⟨h.1, fun q hq => ?_⟩
  change a.basis (fieldPlaceInv q) = b.basis (fieldPlaceInv q)
  apply h.2
  intro hmem
  have eq := fieldPlace_fix_ryWires _ ((mem_ryWires_iff _).mpr (Or.inl hmem))
  rw [fieldPlace_inv] at eq
  exact hq (eq ▸ hmem)

theorem pullOut_regValue_R_NC (s : State) : regValue fieldR (pullOut s).basis = regValue fieldR s.basis :=
  regValue_congr _ _ _ (fun q hq => by
    change s.basis (fieldPlaceInv q) = s.basis q
    rw [fieldPlaceInv_fix_ryWires q ((mem_ryWires_iff q).mpr (Or.inl hq))])

/-- Pieces 18–19 of the NC division (`endPacket760DivOddLoan ++ copyN`, no `canon760OddLoan`) against
pieces 18–20 of the stock division (`divEndpoint ++ copyN ++ canon`): the two runs agree outside `fieldR`;
the odd run holds `oddWord Y` there and the stock run `(2 * Y).val`. -/
theorem divEndTailNC (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
    (en : origin (base 2400) = true) (X Y : Fp)
    (hend : (Replay5.endPayload true origin (X, Y)).1 = Y)
    (a b s_rec : State) (m : List Bool)
    (hrel : OddRel P1Life.oddWord P1Life.oddWord a b)
    (hframe : Rolling1588Frame.EncodedFieldFrame false origin X Y s_rec)
    (hpb_rec : ∀ q, Off q → (pullIn b).basis q = s_rec.basis q) :
    AgreeOutsideR
        (run (liftF (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
          HalfFieldOB5.copyN)) m a)
        (run (liftF (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint ++
          HalfFieldOB5.copyN ++ StairConcrete.bestLoans.canon)) m b) ∧
      regValue fieldR (run (liftF (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
          HalfFieldOB5.copyN)) m a).basis = P1Life.oddWord Y ∧
      regValue fieldR (run (liftF (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint ++
          HalfFieldOB5.copyN ++ StairConcrete.bestLoans.canon)) m b).basis = (2 * Y).val := by
  let P1o := renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan
  let P1s := renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint
  let P_odd := P1o ++ HalfFieldOB5.copyN
  let P_std := (P1s ++ HalfFieldOB5.copyN) ++ StairConcrete.bestLoans.canon
  have hdiv_off : ∀ q ∈ wires P1s, Off q := by
    have hnotz : EP.all (fun e =>
        let v := Equiv.swap (base 760) (base 717) (OB5.sig 511 e)
        decide (16 ≤ v) && !(decide (Placement5.workRegion (v - 16))) &&
          !(decide (Placement5.holeRegion (v - 16)))) = true := by decide +kernel
    have hpi0_fix_ep : ∀ e ∈ EP,
        shifted Placement5.pi0 (Equiv.swap (base 760) (base 717) (OB5.sig 511 e)) =
          Equiv.swap (base 760) (base 717) (OB5.sig 511 e) := by
      intro e he
      set v := Equiv.swap (base 760) (base 717) (OB5.sig 511 e)
      have hb := List.all_eq_true.mp hnotz e he
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hb
      have hsub : base (v - 16) = v := Nat.sub_add_cancel hb.1.1
      rw [← hsub, shifted_base, Placement5.pi0_outside (v - 16) (fun hz => hz.elim hb.1.2 hb.2)]
    have hok : DecoderBiasReuse.fixedLayout.wires.all (fun w =>
        !(decide (OB5.sig 511 (Equiv.swap (base 760) (base 717)
          (Equiv.swap (base 719) (base 510) w)) ∈ EP))) = true := by decide +kernel
    have hok_ep : ∀ w, OB5.sig 511 (Equiv.swap (base 760) (base 717) (shifted Placement5.pi0 w)) ∈ EP →
        OB5.sig 511 (Equiv.swap (base 760) (base 717) w) ∈ EP := by
      intro w hm
      have hfix := hpi0_fix_ep _ hm
      rw [OB5.sig_invol 511 (by decide), Equiv.swap_apply_self] at hfix
      have hweq : w = shifted Placement5.pi0 w :=
        ((shifted Placement5.pi0).injective hfix).symm
      rwa [← hweq] at hm
    intro q hq
    rw [show P1s = renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint from rfl,
        renameProgram_support, StairConcrete.bestLoans_divEndpoint] at hq
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
    unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hy
    rw [renameProgram_support] at hy; obtain ⟨u1, hu1, rfl⟩ := Finset.mem_image.mp hy
    rw [renameProgram_support] at hu1; obtain ⟨u2, hu2, rfl⟩ := Finset.mem_image.mp hu1
    apply off_of_not_EP
    intro hmem
    have hm' := hok_ep u2 hmem
    rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hu2) with h | h
    · rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl <;> exact absurd hm' (by decide +kernel)
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
      rw [wires_append, Finset.mem_union] at hz
      rcases hz with hz | hz
      · have h1 := List.all_eq_true.mp hok z (List.mem_toFinset.mp (CompareDecoder.support (CompareDecoder.BoundaryLoan.Inclusion.cellDecoderLoan_sub hz)))
        simp [hm'] at h1
      · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
        rw [Finset.mem_singleton] at hc; rw [hc] at hm'; exact absurd hm' (by decide +kernel)
  have hcopy_off : ∀ q ∈ wires HalfFieldOB5.copyN, Off q := by
    have hok : StairWireCheck.allSites (fun q => !(decide (q ∈ EP))) HalfFieldOB5.copyN = true := by
      decide +kernel
    intro q hq
    exact off_of_not_EP q (by simpa using StairWireCheck.allSites_sound _ _ hok q hq)
  have hcanon_off : ∀ q ∈ wires StairConcrete.bestLoans.canon, Off q := by
    have hok1 : EP.all (fun e => !(decide (StairBoundaryLoan.converterPerm_k4a.symm e ∈ HalfField.tgt.wires))) = true := by
      decide +kernel
    have hok2 : StairBoundaryLoan.converterHosts.all (fun q => !(decide (q ∈ EP))) = true := by
      decide +kernel
    have hlt_eq : StairBoundaryLoan.converterLayout760.wires =
        HalfField.tgt.wires.map StairBoundaryLoan.converterRename := by
      simp only [BalancedConvert.Layout.wires, StairBoundaryLoan.converterLayout760,
        BalancedConvert.Layout.word, List.map_append, List.map_cons, List.map_nil]
    intro q hq
    apply off_of_not_EP
    intro hmem
    rcases Finset.mem_union.mp (StairBoundaryLoan.canon760Loan_envelope hq) with h1 | h2
    · rw [StairBoundaryLoan.canon760_eq] at h1
      have hm := List.mem_toFinset.mp ((HalfConvert.support _ StairBoundaryLoan.converterLayout760_facts.widths).2 h1)
      rw [hlt_eq] at hm
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
      have hbad := List.all_eq_true.mp hok1 _ hmem
      rw [StairBoundaryLoan.converterRename_apply_k4a, Equiv.symm_apply_apply] at hbad
      simp [hw] at hbad
    · have hbad := List.all_eq_true.mp hok2 q (List.mem_toFinset.mp h2)
      simp [hmem] at hbad
  have hstd_off : ∀ q ∈ wires P_std, Off q := by
    intro q hq
    simp only [P_std, wires_append, Finset.mem_union] at hq
    rcases hq with (h | h) | h
    · exact hdiv_off q h
    · exact hcopy_off q h
    · exact hcanon_off q h
  have hodd_sub_std : wires P_odd ⊆ wires P_std := by
    have h1 : wires P1o ⊆ wires P1s := by
      simp only [P1o, P1s, renameProgram_support, StairConcrete.bestLoans_divEndpoint]
      exact Finset.image_subset_image OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_wires_sub
    intro q hq
    simp only [P_odd, P_std, wires_append, Finset.mem_union] at hq ⊢
    rcases hq with ha | hb
    · exact Or.inl (Or.inl (h1 ha))
    · exact Or.inl (Or.inr hb)
  have hry_sub_std : ∀ q ∈ ryWires, q ∈ wires P_std := by
    have hcopy_mem : ∀ (a b : List Wire), a.length = b.length →
        ∀ q ∈ a ++ b, q ∈ wires (copyRegister none a b) := by
      intro a
      induction a with
      | nil => intro b hb q hq; cases b <;> simp_all
      | cons x xs ih =>
        intro b hb q hq
        cases b with
        | nil => simp at hb
        | cons y ys =>
          simp only [copyRegister, copyGate, wires_append, wires, Instr.wires, Finset.mem_union,
            Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]
          simp only [List.mem_append, List.mem_cons] at hq
          rcases hq with (rfl | hx) | (rfl | hy)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr (ih ys (by simpa using hb) q (List.mem_append_left _ hx))
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (ih ys (by simpa using hb) q (List.mem_append_right _ hy))
    have hlen : fieldR.length = fieldY.length := by simp [fieldR, fieldY, wireBlock_length]
    intro q hq
    simp only [P_std, wires_append, Finset.mem_union]
    exact Or.inl (Or.inr (hcopy_mem fieldR fieldY hlen q hq))
  -- First prove exact equality on `s_odd := spliceRY (pullIn a) s_rec` vs `s_rec`!
  let a0 := spliceRY (pullIn a) s_rec
  let b0 := s_rec
  have hrel0 : OddRel P1Life.oddWord P1Life.oddWord a0 b0 := by
    have hb_vals_rec := encodedFieldFrame_values false origin X Y s_rec hframe
    have hb_vals : regValue fieldR b.basis = centerWord X ∧ regValue fieldY b.basis = centerWord Y := by
      constructor
      · rw [← pullIn_regValue_R]
        exact (regValue_congr _ _ _ (fun q hq => hpb_rec q (ryWires_off q ((mem_ryWires_iff q).mpr (Or.inl hq))))).trans hb_vals_rec.1
      · rw [← pullIn_regValue_Y]
        exact (regValue_congr _ _ _ (fun q hq => hpb_rec q (ryWires_off q ((mem_ryWires_iff q).mpr (Or.inr hq))))).trans hb_vals_rec.2
    have ha_vals : regValue fieldR a0.basis = P1Life.oddWord X ∧ regValue fieldY a0.basis = P1Life.oddWord Y := by
      constructor
      · rw [show regValue fieldR a0.basis = regValue fieldR (pullIn a).basis from
              regValue_congr _ _ _ (fun q hq => by simp only [a0, spliceRY, (mem_ryWires_iff q).mpr (Or.inl hq), if_true]),
            pullIn_regValue_R]
        exact hrel.2.1 X hb_vals.1
      · rw [show regValue fieldY a0.basis = regValue fieldY (pullIn a).basis from
              regValue_congr _ _ _ (fun q hq => by simp only [a0, spliceRY, (mem_ryWires_iff q).mpr (Or.inr hq), if_true]),
            pullIn_regValue_Y]
        exact hrel.2.2 Y hb_vals.2
    exact oddRel_of_agreeRY_values X Y ⟨rfl, fun q hq => by simp only [a0, b0, spliceRY, hq, if_false]⟩
      hb_vals_rec.1 hb_vals_rec.2 ha_vals.1 ha_vals.2
  have hb0_vals := encodedFieldFrame_values false origin X Y b0 hframe
  have ha0_vals : regValue fieldR a0.basis = P1Life.oddWord X ∧ regValue fieldY a0.basis = P1Life.oddWord Y :=
    ⟨hrel0.2.1 X hb0_vals.1, hrel0.2.2 Y hb0_vals.2⟩
  -- Split tape: odd `endPacket, copyN`; stock `endPacket, copyN, canon`
  let m1o := m.take (measurementCount P1o)
  let m2o := m.drop (measurementCount P1o)
  let m12s := m.take (measurementCount (P1s ++ HalfFieldOB5.copyN))
  let m1s := m12s.take (measurementCount P1s)
  let m2s := m12s.drop (measurementCount P1s)
  let m3s := m.drop (measurementCount (P1s ++ HalfFieldOB5.copyN))
  -- Step 1: endPacketDiv
  let a1 := run P1o m1o a0
  let b1 := run P1s m1s b0
  have hsig_a0 : AgreeRY (pullState (OB5.sig 511) a0) (pullState (OB5.sig 511) b0) :=
    pullState_sig511_agreeRY hrel0.1
  have h510_notRY : base 510 ∉ ryWires := by decide +kernel
  have h2409_notRY : base 2409 ∉ ryWires := by decide +kernel
  have h760_notRY : base 760 ∉ ryWires := by decide +kernel
  have h717_notRY : base 717 ∉ ryWires := by decide +kernel
  have hzero_b0 := Rolling1588.encoded_zero_region base (base 2409) false ctx.hn (ctx.hp _ (by simp))
    origin ctx.env ctx.legal X Y _ hframe
  have hzero_a0 : ∀ q, Placement5.zeroRegion q → (pullState (OB5.sig 511) a0).basis (base q) = false :=
    fun q hq => (hsig_a0.2 (base q) (base_not_ryWires_of_zeroRegion q hq)).trans (hzero_b0 q hq)
  have hXeq : X = (if (pullState (OB5.sig 511) a0).basis (base 510) then 1 else 3) * Y := by
    obtain ⟨raw, _, hpair, henc⟩ := hframe
    have hout510 : raw.basis (base 510) = origin (base 510) :=
      hpair.2.2 (base 510) (by decide +kernel) (by decide +kernel)
    have h510_b : (pullState (OB5.sig 511) b0).basis (base 510) = origin (base 510) := by
      rw [henc]
      have h510_ne : base 510 ∉ wires (Rolling1588.allEncode base false 102) := fun hw =>
        allEncode_510_free false hw
      rw [run_preserves_outside _ [] raw _ h510_ne, hout510]
    have h510_a : (pullState (OB5.sig 511) a0).basis (base 510) = origin (base 510) :=
      (hsig_a0.2 (base 510) h510_notRY).trans h510_b
    rw [h510_a]
    have hd : (X + (if origin (base 510) then Y else -Y)) / 2 = Y := by
      simpa only [Replay5.endPayload, mixedTranscriptBit, en, if_true] using hend
    have h2 : (2 : Fp) ≠ 0 := by decide
    have hmul : X + (if origin (base 510) then Y else -Y) = 2 * Y := by
      have h1 : ((X + (if origin (base 510) then Y else -Y)) / 2) * 2 = Y * 2 := congrArg (· * 2) hd
      rw [div_mul_cancel₀ _ h2] at h1
      exact h1.trans (mul_comm Y 2)
    cases h : origin (base 510) <;> simp only [h, Bool.false_eq_true, if_true, if_false] at hmul ⊢ <;> linear_combination hmul
  have hflag_b0 : (pullState (OB5.sig 511) b0).basis (base 2409) = false := by
    obtain ⟨raw, _, hpair, henc⟩ := hframe
    have hne : base 2409 ∉ wires (Rolling1588.allEncode base false 102) := fun hw =>
      absurd (List.mem_toFinset.mp (Rolling1588.allEncode_history_support base false 102 (by decide) hw))
        (by decide +kernel)
    rw [henc, run_preserves_outside _ [] raw _ hne]
    exact (hpair.2.2 (base 2409) (by decide +kernel) (by decide +kernel)).trans ctx.hg0
  have ha1_spec := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_frame Y
    (pullState (OB5.sig 511) a0) m1o
    (q6Clean_of_agreeRY hsig_a0 (q6Clean_of_encoded5 origin ctx X Y _ hframe))
    ((hsig_a0.2 (base 2409) h2409_notRY).trans hflag_b0)
    (by rw [fixedLayout_y_eq, pullState_sig511_regValue_Y]; exact ha0_vals.2)
    (by rw [fixedLayout_r_eq, pullState_sig511_regValue_R, ← hXeq]; exact ha0_vals.1)
    (Placement5.shifted_zero_boundary Placement5.pi0 Placement5.pi0_outside _ hzero_a0)
    ((hsig_a0.2 (base 760) h760_notRY).trans (R2SqEp760.encoded5_760 origin ctx X Y _ hframe))
    ((hsig_a0.2 (base 717) h717_notRY).trans (R2SqEp760.encoded5_717 origin ctx X Y _ hframe))
  rw [fixedLayout_r_eq] at ha1_spec
  have hb1_eq : run StairConcrete.bestLoans.divEndpoint m1s (pullState (OB5.sig 511) b0) =
      run (R2SqEp760.endPacket760 true) m1s (pullState (OB5.sig 511) b0) := by
    rw [StairConcrete.bestLoans_divEndpoint]
    exact CompareDecoder.BoundaryLoan.endPacket760DivLoan_run_eq false origin ctx en X Y hend _ m1s m1s hframe
  have hb1_spec := R2SqEp760.endPacket760_frame false true origin ctx en X Y (fun _ => hend)
    (fun h => absurd h (by decide)) (pullState (OB5.sig 511) b0) m1s hframe
  have hb1_frame : Rolling1588Frame.EncodedFieldFrame false origin Y Y b1 := by
    have hconj := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)) StairConcrete.bestLoans.divEndpoint m1s b0
    change Rolling1588.EncodedFieldFrame5 base (base 2409) false origin Y Y (pullState (OB5.sig 511) b1)
    rw [show pullState (OB5.sig 511) b1 = run StairConcrete.bestLoans.divEndpoint m1s (pullState (OB5.sig 511) b0) from hconj, hb1_eq]
    have hs2 := hb1_spec.2
    rw [hend] at hs2
    exact hs2
  have ha1_ag : AgreeRY a1 b1 := by
    have hconj_a := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
      OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan m1o a0
    have hconj_b := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
      StairConcrete.bestLoans.divEndpoint m1s b0
    have ha1p : a1.phase = a0.phase :=
      (pullState_phase _ a1).symm.trans ((congrArg State.phase hconj_a).trans
        (ha1_spec.1.trans (pullState_phase _ a0)))
    have hb1p : b1.phase = b0.phase :=
      (pullState_phase _ b1).symm.trans ((congrArg State.phase hconj_b).trans
        (((congrArg State.phase hb1_eq).trans hb1_spec.1).trans (pullState_phase _ b0)))
    have hph : a1.phase = b1.phase := ha1p.trans (hrel0.1.1.trans hb1p.symm)
    have ha1_out : ∀ q, q ∉ ryWires → (pullState (OB5.sig 511) a1).basis q = (pullState (OB5.sig 511) a0).basis q := by
      intro q hq
      rw [hconj_a]
      exact ha1_spec.2.2 q (fun hr => hq ((mem_ryWires_iff q).mpr (Or.inl hr)))
    have hb1_out : ∀ q, q ∉ ryWires → (pullState (OB5.sig 511) b1).basis q = (pullState (OB5.sig 511) b0).basis q := by
      intro q hq
      have h1 := encodedFieldFrame_agreeRY centerWord centerWord false origin Y Y X Y b1 b0 hb1p hb1_frame hframe
      exact (pullState_sig511_agreeRY h1).2 q hq
    have hp : AgreeRY (pullState (OB5.sig 511) a1) (pullState (OB5.sig 511) b1) :=
      ⟨(pullState_phase _ a1).trans (hph.trans (pullState_phase _ b1).symm),
       fun q hq => (ha1_out q hq).trans ((hsig_a0.2 q hq).trans (hb1_out q hq).symm)⟩
    have hu := pullState_sig511_agreeRY hp
    rwa [StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide)),
         StairReplay.pullState_involutive (OB5.sig 511) (OB5.sig_invol 511 (by decide))] at hu
  have ha1_vals : regValue fieldR a1.basis = P1Life.oddWord Y ∧ regValue fieldY a1.basis = P1Life.oddWord Y := by
    have hconj_a := run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))
      OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan m1o a0
    constructor
    · rw [← pullState_sig511_regValue_R, hconj_a]; exact ha1_spec.2.1
    · rw [← pullState_sig511_regValue_Y, hconj_a]
      exact (regValue_congr _ _ _ (fun q hq => ha1_spec.2.2 q (fun hr => fieldR_disjoint_fieldY q hr hq))).trans
        (by rw [pullState_sig511_regValue_Y]; exact ha0_vals.2)
  -- Step 2: HalfFieldOB5.copyN
  let a2 := run HalfFieldOB5.copyN m2o a1
  let b2 := run HalfFieldOB5.copyN m2s b1
  have hc_a := copyN_step ctx.hn a1 m2o
  have hc_b := copyN_step ctx.hn b1 m2s
  have hb2_frame : Rolling1588Frame.EncodedFieldFrame false origin Y 0 b2 :=
    (Rolling1588HalfFieldOB5.copy_clear ctx.hn origin Y b1 m2s hb1_frame).2
  have ha2_R : regValue fieldR a2.basis = P1Life.oddWord Y :=
    (regValue_congr _ _ _ (fun q hq => hc_a.2.1 q (fieldR_disjoint_fieldY q hq))).trans ha1_vals.1
  have ha2_Y0 : regValue fieldY a2.basis = 0 := by
    rw [hc_a.2.2, ha1_vals.1, ha1_vals.2, Nat.xor_self]
  have hb2_vals := encodedFieldFrame_values false origin Y 0 b2 hb2_frame
  have hb2_Y0 : regValue fieldY b2.basis = 0 := by rw [hb2_vals.2, HalfField.centerWord_zero]
  have ha2_agR : AgreeOutsideR a2 b2 := by
    apply agreeOutsideR_of_agreeRY
    · refine ⟨hc_a.1.trans (ha1_ag.1.trans hc_b.1.symm), fun q hq => ?_⟩
      have hny : q ∉ fieldY := fun h => hq ((mem_ryWires_iff q).mpr (Or.inr h))
      rw [hc_a.2.1 q hny, hc_b.2.1 q hny]
      exact ha1_ag.2 q hq
    · exact basis_eq_of_regValue_eq fieldY a2.basis b2.basis (ha2_Y0.trans hb2_Y0.symm)
  -- Step 3 (stock only): canon760Loan
  let b3 := run StairConcrete.bestLoans.canon m3s b2
  have hb3_eq : b3 = run R2SqEp760.canon760 m3s b2 :=
    StairBoundaryLoan.canon760Loan_run_eq origin ctx Y b2 m3s m3s hb2_frame
  have hb3_corr : b3.phase = b2.phase ∧ regValue fieldR b3.basis = (2 * Y).val ∧
      ∀ q, q ∉ fieldR → b3.basis q = b2.basis q := by
    rw [hb3_eq, StairBoundaryLoan.canon760_eq]
    have hc := HalfConvert.canonical_correct StairBoundaryLoan.converterLayout760
      StairBoundaryLoan.converterLayout760_facts.widths
      converterLayout760_wires_nodup Y b2 m3s (by rw [converterLayout760_word_eq_fieldR]; exact hb2_vals.1)
        (bcWork_clean_of_encodedField origin ctx Y b2 hb2_frame)
    rw [converterLayout760_word_eq_fieldR] at hc
    exact ⟨hc.1, hc.2.1, hc.2.2.2⟩
  have hcore : AgreeOutsideR (run P_odd m a0) (run P_std m b0) ∧
      regValue fieldR (run P_odd m a0).basis = P1Life.oddWord Y ∧
      regValue fieldR (run P_std m b0).basis = (2 * Y).val := by
    have h1 : run P_odd m a0 = a2 := run_append P1o HalfFieldOB5.copyN m a0
    have h2 : run P_std m b0 = b3 := by
      change run ((P1s ++ HalfFieldOB5.copyN) ++ StairConcrete.bestLoans.canon) m b0 = b3
      rw [run_append, run_append]
    rw [h1, h2]
    exact ⟨⟨ha2_agR.1.trans hb3_corr.1.symm, fun q hq => (ha2_agR.2 q hq).trans (hb3_corr.2.2 q hq).symm⟩,
      ha2_R, hb3_corr.2.1⟩
  -- Transfer from `(a0, b0)` to `(pullIn a, pullIn b)` via `run_local_increment`
  have hpa_a0 : ∀ q ∈ wires P_odd, (pullIn a).basis q = a0.basis q := by
    intro q hq
    by_cases hry : q ∈ ryWires
    · simp only [a0, spliceRY, hry, if_true]
    · simp only [a0, spliceRY, hry, if_false]
      exact ((pullIn_agreeRY hrel.1).2 q hry).trans (hpb_rec q (hstd_off q (hodd_sub_std hq)))
  have hpb_b0 : ∀ q ∈ wires P_std, (pullIn b).basis q = b0.basis q := fun q hq =>
    hpb_rec q (hstd_off q hq)
  have hinc_odd := Arithmetic.run_local_increment P_odd (pullIn a) a0 m hpa_a0
  have hinc_std := Arithmetic.run_local_increment P_std (pullIn b) b0 m hpb_b0
  have hpeq : (run P_odd m a0).phase = (run P_std m b0).phase := hcore.1.1
  have hinc2 : ((run P_std m (pullIn b)).phase ^^ (pullIn b).phase) = ((run P_odd m a0).phase ^^ a0.phase) := by
    rw [hpeq]; exact hinc_std.1
  have hph : (run P_odd m (pullIn a)).phase = (run P_std m (pullIn b)).phase :=
    phase_eq_of_xor hinc_odd.1 hinc2 hrel.1.1
  have hag : AgreeOutsideR (run P_odd m (pullIn a)) (run P_std m (pullIn b)) := by
    refine ⟨hph, fun q hq => ?_⟩
    by_cases h1 : q ∈ wires P_odd
    · rw [hinc_odd.2 q h1, hinc_std.2 q (hodd_sub_std h1)]
      exact hcore.1.2 q hq
    · rw [run_preserves_outside P_odd m (pullIn a) q h1]
      by_cases h2 : q ∈ wires P_std
      · rw [hinc_std.2 q h2, ← hcore.1.2 q hq, run_preserves_outside P_odd m a0 q h1]
        by_cases hry : q ∈ ryWires
        · simp only [a0, spliceRY, hry, if_true]
        · simp only [a0, spliceRY, hry, if_false]
          exact ((pullIn_agreeRY hrel.1).2 q hry).trans (hpb_rec q (hstd_off q h2))
      · rw [run_preserves_outside P_std m (pullIn b) q h2]
        exact (pullIn_agreeRY hrel.1).2 q (fun hry => h2 (hry_sub_std q hry))
  have hvR_odd : regValue fieldR (run P_odd m (pullIn a)).basis = P1Life.oddWord Y := by
    refine (regValue_congr _ _ _ (fun q hq => ?_)).trans hcore.2.1
    have hry : q ∈ ryWires := (mem_ryWires_iff q).mpr (Or.inl hq)
    by_cases h1 : q ∈ wires P_odd
    · exact hinc_odd.2 q h1
    · rw [run_preserves_outside P_odd m (pullIn a) q h1, run_preserves_outside P_odd m a0 q h1]
      simp only [a0, spliceRY, hry, if_true]
  have hvR_std : regValue fieldR (run P_std m (pullIn b)).basis = (2 * Y).val :=
    (regValue_congr _ _ _ (fun q hq =>
      hinc_std.2 q (hry_sub_std q ((mem_ryWires_iff q).mpr (Or.inl hq))))).trans hcore.2.2
  rw [StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run]
  exact ⟨pullOut_agreeOutsideR_NC hag, (pullOut_regValue_R_NC _).trans hvR_odd,
    (pullOut_regValue_R_NC _).trans hvR_std⟩

/-- NC division output relation: `a` (odd run) and `b` (stock run) agree outside `fieldR`, `a` holds
    `oddWord Yh` and `b` holds `(2 * Yh).val` on `fieldR`. -/
def DivNCOut (a b : State) : Prop :=
  ∃ Yh : Fp, AgreeOutsideR a b ∧ regValue fieldR a.basis = P1Life.oddWord Yh ∧
    regValue fieldR b.basis = (2 * Yh).val

theorem regValue_run_notFieldR_NC (P : Program) (h : ∀ q ∈ wires P, q ∉ fieldR)
    (m : List Bool) (s : State) :
    regValue fieldR (run P m s).basis = regValue fieldR s.basis :=
  regValue_congr fieldR (run P m s).basis s.basis
    (fun q hq => run_preserves_outside P m s q (fun hw => h q hw hq))

theorem divNCOut_run (P : Program) (hP : ∀ q ∈ wires P, q ∉ fieldR) {a b : State}
    (h : DivNCOut a b) (m : List Bool) : DivNCOut (run P m a) (run P m b) := by
  obtain ⟨Yh, hag, ha, hb⟩ := h
  exact ⟨Yh, agreeOutsideR_disjoint P hP hag m, (regValue_run_notFieldR_NC P hP m a).trans ha,
    (regValue_run_notFieldR_NC P hP m b).trans hb⟩

theorem tail2123_notFieldR : ∀ q ∈ wires (StairSchedule.fieldRename FourScratchWindow.unprefix ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup), q ∉ fieldR := by
  have h := disjoint_ryWires_append (disjoint_ryWires_append (disjoint_ryWires_fieldRename unprefix_notRY)
    hostedX_notRY) paritySetup_notRY
  exact fun q hq hr => h q hq ((mem_ryWires_iff q).mpr (Or.inl hr))

theorem divPost_notFieldR :
    ∀ q ∈ wires (renameProgram Rolling1588Lifetime.phaseHost Stair44Outer.reverseEnd), q ∉ fieldR := by
  have h : StairWireCheck.allSites notFieldR
      (renameProgram Rolling1588Lifetime.phaseHost Stair44Outer.reverseEnd) = true := by decide +kernel
  exact fun q hq => (notFieldR_iff q).mp (StairWireCheck.allSites_sound notFieldR _ h q hq)

def stockOddDivBetweenNC : Program :=
  StairSchedule.hostedX ++ StairSchedule.fieldRename
    (WindowParityCaller.entryLowSuffixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX

def stockOddDivHeadCutNC : Program :=
  ((Stair44Kernel.divLead ++ stockOddDivBeforeGroup) ++
    renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84)) ++
  ((((stockOddDivPreCut ++ StairSchedule.paritySetup) ++ stockOddDivBetweenNC) ++
    StairSchedule.paritySetup) ++ stockOddDivPost)

/-- The NC division head (no `canon760OddLoan`) against the stock division head: the runs agree
outside `fieldR`; the odd run holds `oddWord Yh` there and the stock run `(2 * Yh).val`. -/
theorem stockOddDivHeadCutNC_agree_oldDivHead {tOdd tStd : State} (F : EntryFrame tStd)
    (hag0 : AgreeOutsideR tOdd tStd) (hR0 : regValue fieldR tOdd.basis = P1Life.oddWord (F.Y / 2))
    (m : List Bool) :
    ∃ n, DivNCOut (run stockOddDivHeadCutNC m tOdd) (run WindowMiddleContract.oldDivHead n tStd) := by
  -- Both `stockOddDivHead` and `oldDivHead` end with `post := renameProgram phaseHost reverseEnd`.
  -- Strip `post` and `divLead` first, then run the 24-piece lockstep!
  have hmc_divLead : measurementCount Stair44Kernel.divLead =
      measurementCount (renameProgram Rolling1588Lifetime.phaseHost (StairSchedule.firstPhase cp)) := by
    rw [WindowStockHead.shapeD, (renameProgram_counts _ _).2, (renameProgram_counts _ _).2,
        measurementCount_append, measurementCount_append, Stair44Kernel.open_count]
  let mPre := m.take (measurementCount ((Stair44Kernel.divLead ++ stockOddDivBeforeGroup) ++
      renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84) ++
      ((((stockOddDivPreCut ++ StairSchedule.paritySetup) ++ stockOddDivBetweenNC) ++ StairSchedule.paritySetup))))
  let mPost := m.drop (measurementCount ((Stair44Kernel.divLead ++ stockOddDivBeforeGroup) ++
      renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84) ++
      ((((stockOddDivPreCut ++ StairSchedule.paritySetup) ++ stockOddDivBetweenNC) ++ StairSchedule.paritySetup))))
  -- Step-by-step piece relation `DivCut j a b := (∃ u, b = run (cut eps j) u tStd) ∧ OddRel oddWord oddWord a b`
  let DivCut (j : Nat) (a b : State) : Prop :=
    (∃ u, b = run (cut eps j) u tStd) ∧ OddRel P1Life.oddWord P1Life.oddWord a b
  have step_disj (j : Nat) (hj : j < 25) (P : Program) (hP : (eps[j]'(eL j hj)).L = P)
      (hnot : ∀ q ∈ wires P, q ∉ ryWires) :
      ∀ a b m', DivCut j a b → DivCut (j + 1) (run P m' a) (run P m' b) := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    refine ⟨⟨WindowFieldJourney.joinTapes (cut eps j) u m', ?_⟩, oddRel_disjoint P hnot hrel m'⟩
    rw [cut_succ eps j (eL j hj), hP, WindowFieldJourney.joined]
  have step_grp (j B def_ start len : Nat) (hj : j < 25)
      (hL : (eps[j]'(eL j hj)).L = grpL StairConcrete.bestLoans def_ start len)
      (hB : B ∈ budgets) (hstartB : start + len ≤ startFor B / 5)
      (hd : def_ ≤ 43) (hdef0 : def_ ≠ 0) (h1 : 1 ≤ start) (hb : start + len ≤ 102)
      (hmem : (j, def_, start, len) ∈ [(3, 0, 1, 84), (5, 13, 85, 5), (7, 22, 90, 3), (9, 30, 93, 3),
          (11, 36, 96, 2), (13, 41, 98, 2), (17, 43, 100, 2)])
      (hsched : def_ = 43 ∨ (def_, start, len) ∈ [(0, 1, 84), (13, 85, 5), (22, 90, 3), (30, 93, 3),
          (36, 96, 2), (41, 98, 2)])
      (hpin : ∀ u, ∃ rec, FrameAt F.x start rec ∧ AgreeOutside (Δv B) (run (cut eps j) u tStd) rec) :
      ∀ a b m', DivCut j a b →
        DivCut (j + 1)
          (run (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true (def_ + 1) start len)) m' a)
          (run (grpL StairConcrete.bestLoans def_ start len) m' b) := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨rec, hframe, hagree⟩ := hpin u
    have hclIn : ∀ q ∈ (StairSchedule.exclusiveRoles.drop def_ ++ hostPlan.group true def_ start len).map lowMap,
        (run (cut eps j) u tStd).basis q = false :=
      groupsBefore_eps j def_ start len hmem tStd ⟨F⟩ u
    have hclOut : ∀ q ∈ (StairSchedule.exclusiveRoles.drop def_).map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups true def_ start len))) m' (run (cut eps j) u tStd)).basis q = false :=
      cleanCut_after (groupsRolesAfter_eps j def_ start len hmem)
        (by rw [cut_succ eps j (eL j hj), hL, grpL_eq]) tStd ⟨F⟩ u m'
    have hBne : B ≠ 0 := by rcases (by simpa [budgets] using hB : B = 87 ∨ B = 62 ∨ B = 47 ∨ B = 32 ∨ B = 22 ∨ B = 12) with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have havoid : B ≠ 0 → ∀ q ∈ futurePayload B, q ∉ wires (renameProgram (OB5.sig 511) (Rolling1588.groups true start len)) :=
      fun _ => StairField2V3Groups.groups_avoid_payload true B hB len start (by omega)
    have hdef_mem : def_ ∈ ([13, 22, 30, 36, 41, 43] : List Nat) := by
      rcases hsched with rfl | hs
      · decide
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
        rcases hs with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩
        · exact absurd rfl hdef0
        all_goals simp
    have hsched1542 : def_ = 43 ∨ (def_, start, len) ∈ [(13, 85, 5), (22, 90, 3), (30, 93, 3), (36, 96, 2), (41, 98, 2)] := by
      rcases hsched with rfl | hs
      · exact Or.inl rfl
      · right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
        rcases hs with ⟨rfl, _, _⟩ | hrest
        · exact absurd rfl hdef0
        · exact hrest
    have hclIn' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop (def_ + 1) ++
          OddFullPass.P1LifeLoan.hostPlan1542.group true (def_ + 1) start len).map lowMap,
        (run (cut eps j) u tStd).basis q = false := by
      intro q hq
      apply hclIn q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (Nat.le_succ def_)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub true def_ start len hdef_mem w hh)
    have hclOut' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop (def_ + 1)).map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups true def_ start len))) m' (run (cut eps j) u tStd)).basis q = false := by
      intro q hq
      apply hclOut q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      exact ⟨w, (List.drop_sublist_drop_left _ (Nat.le_succ def_)).subset hw, rfl⟩
    have hstep := odd_hostedGroup_step true (def_ + 1) def_ start len B F.x (hpOdd := OddFullPass.P1LifeLoan.hostPlan1542)
      (by omega) hd h1 hb (Or.inr hB) havoid
      a (run (cut eps j) u tStd) rec m' hrel hframe (by simp only [hBne, if_false]; exact hagree)
      hclIn' hclOut' (hostPlan1542_group_notRY true def_ start len hdef_mem)
      (hostPlan1542_group_fresh_odd true def_ start len hd h1 hb hdef_mem hsched1542)
    rw [← grpL_eq] at hstep
    refine ⟨⟨WindowFieldJourney.joinTapes (cut eps j) u m', ?_⟩, hstep⟩
    rw [cut_succ eps j (eL j hj), hL, WindowFieldJourney.joined]
  -- Helper to extract `FrameAt` + `AgreeOutside (Δv B)` from `ern*` + `g_R*`
  have V := StairLoanField7RR.entryReachTransportR_best StairOpenWiring.half760 F.x
  have pin_of {j B : Nat} {Z R : Program} (hecut : cut eps j = Z)
      (hern : ∃ Q, CRel (EPreX F.x) (RowRelEn F.x B R) Z Q)
      (hg : ∀ t, ReachEn F.x R t → FrameAt F.x (if B = 62 then 85 else if B = 47 then 90 else if B = 32 then 93 else if B = 22 then 96 else 98) t) :
      ∀ u, ∃ rec, FrameAt F.x (if B = 62 then 85 else if B = 47 then 90 else if B = 32 then 93 else if B = 22 then 96 else 98) rec ∧
        AgreeOutside (Δv B) (run (cut eps j) u tStd) rec := by
    intro u
    obtain ⟨Q, hcr⟩ := hern
    obtain ⟨_, hrr⟩ := hcr tStd tStd ⟨⟨F, rfl⟩, rfl⟩ u
    rw [hecut]
    exact ⟨_, hg _ hrr.2, hrr.1.1⟩
  have pin5 := pin_of ecut5 (ern5 F.x (StairOpenWiring.entryPlans F.x) V)
    (fun t ht => by obtain ⟨s0, m0, ⟨F0, fx⟩, rfl⟩ := V.r1 t ht; rw [← fx]; exact (g_R1 s0 F0 m0).1)
  have pin7 := pin_of ecut7 (ern7 F.x (StairOpenWiring.entryPlans F.x) V)
    (fun t ht => by obtain ⟨s0, m0, ⟨F0, fx⟩, rfl⟩ := V.r2 t ht; rw [← fx]; exact (g_R2 s0 F0 m0).1)
  have pin9 := pin_of ecut9 (ern9 F.x (StairOpenWiring.entryPlans F.x) V)
    (fun t ht => by obtain ⟨s0, m0, ⟨F0, fx⟩, rfl⟩ := V.r3 t ht; rw [← fx]; exact (g_R3 s0 F0 m0).1)
  have pin11 := pin_of ecut11 (ern11 F.x (StairOpenWiring.entryPlans F.x) V)
    (fun t ht => by obtain ⟨s0, m0, ⟨F0, fx⟩, rfl⟩ := V.r4 t ht; rw [← fx]; exact (g_R4 s0 F0 m0).1)
  have pin13 := pin_of ecut13 (ern13 F.x (StairOpenWiring.entryPlans F.x) V)
    (fun t ht => by obtain ⟨s0, m0, ⟨F0, fx⟩, rfl⟩ := V.r5 t ht; rw [← fx]; exact (g_R5 s0 F0 m0).1)
  -- Cut 3: `stockOddDivPrefix3` vs `cut eps 3`
  have hcut3 (m3 : List Bool) : ∃ b3, DivCut 3 (run (Stair44Kernel.divLead ++ stockOddDivBeforeGroup) m3 tOdd) b3 := by
    have hlead : run (Stair44Kernel.divLead ++ stockOddDivBeforeGroup) m3 tOdd =
        run stockOddDivPrefix3 m3 tOdd := by
      rw [stockOddDivPrefix3, run_append, run_append, divLead_eq_firstPhase_odd F hag0, hmc_divLead]
    rw [hlead]
    obtain ⟨⟨n3, hrel3⟩, _⟩ := stockOddDiv_cut3 F hag0 hR0 m3
    exact ⟨run (cut eps 3) n3 tStd, ⟨n3, rfl⟩, hrel3⟩
  -- Piece 3: `ogroup true 1 84` vs `grpL bestLoans 0 1 84`
  have step3 : ∀ a b m', DivCut 3 a b →
      DivCut 4 (run (renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84)) m' a)
        (run (grpL StairConcrete.bestLoans 0 1 84) m' b) := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨⟨rec, hframe, hagree⟩, hloan⟩ := entryCut3_pin_loan F u
    have hclIn : ∀ q ∈ (StairSchedule.exclusiveRoles ++ hostPlan.group true 0 1 84).map lowMap,
        (run (cut eps 3) u tStd).basis q = false := by
      intro q hq
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
      rw [hp_group true 0 1 84 (by decide)] at hw
      rw [lowMap_eq_fieldPlace]
      exact hloan w hw
    have hclOut' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 0).map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups true 0 1 84))) m' (run (cut eps 3) u tStd)).basis q = false :=
      cleanCut_after (groupsRolesAfter_eps 3 0 1 84 (List.Mem.head _))
        (by rw [cut_succ eps 3 (eL 3 (by decide)), e3_L, grpL_eq]) tStd ⟨F⟩ u m'
    have hclOut : ∀ q ∈ StairSchedule.exclusiveRoles.map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups true 0 1 84))) m' (run (cut eps 3) u tStd)).basis q = false :=
      fun q hq => hclOut' q (by simpa only [List.drop_zero] using hq)
    have hstep := odd_ogroup84_step true F.x a (run (cut eps 3) u tStd) rec m' hrel hframe hagree hclIn hclOut
    rw [← grpL_eq] at hstep
    refine ⟨⟨WindowFieldJourney.joinTapes (cut eps 3) u m', ?_⟩, hstep⟩
    rw [cut_succ eps 3 (eL 3 (by decide)), e3_L, WindowFieldJourney.joined]
  -- Pieces 4..16
  have step4 := step_disj 4 (by decide) _ e4_L (disjoint_ryWires_liftF forward425_notRY)
  have step5 := step_grp 5 62 13 85 5 (by decide) e5_L (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin5
  have step6 := step_disj 6 (by decide) _ e6_L (disjoint_ryWires_liftF forward450_notRY)
  have step7 := step_grp 7 47 22 90 3 (by decide) e7_L (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin7
  have step8 := step_disj 8 (by decide) _ e8_L (disjoint_ryWires_liftF forward465_notRY)
  have step9 := step_grp 9 32 30 93 3 (by decide) e9_L (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin9
  have step10 := step_disj 10 (by decide) _ e10_L (disjoint_ryWires_liftF forward480_notRY)
  have step11 := step_grp 11 22 36 96 2 (by decide) e11_L (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin11
  have step12 := step_disj 12 (by decide) _ e12_L (disjoint_ryWires_liftF forward490_notRY)
  have step13 := step_grp 13 12 41 98 2 (by decide) (show (eps[13]'(eL 13 (by decide))).L = grpL StairConcrete.bestLoans 41 98 2 from rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (Or.inr (by simp)) pin13
  have stepCut1 : ∀ a b m', DivCut 4 a b →
      ∃ b', DivCut 6 (run (liftF (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨m2, h⟩ := oddRowCut1 F u a hrel.1 m'
    have dA := step4 _ _ (m2.take (measurementCount (liftF (StairSchedule.forwardSegment cp 87 62 425 450)))) ⟨⟨u, rfl⟩, hrel⟩
    have dB := step5 _ _ (m2.drop (measurementCount (liftF (StairSchedule.forwardSegment cp 87 62 425 450)))) dA
    have e : liftF (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 (4 + 1)) =
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 5) :=
      ExteriorPorts.placedShape _
    rw [h, liftF_append, run_append, e]
    exact ⟨_, dB⟩
  have stepCut2 : ∀ a b m', DivCut 6 a b →
      ∃ b', DivCut 8 (run (liftF (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨m2, h⟩ := oddRowCut2 F u a hrel.1 m'
    have dA := step6 _ _ (m2.take (measurementCount (liftF (StairSchedule.forwardSegment cp 62 47 450 465)))) ⟨⟨u, rfl⟩, hrel⟩
    have dB := step7 _ _ (m2.drop (measurementCount (liftF (StairSchedule.forwardSegment cp 62 47 450 465)))) dA
    have e : liftF (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 (2 + 1)) =
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 3) :=
      ExteriorPorts.placedShape _
    rw [h, liftF_append, run_append, e]
    exact ⟨_, dB⟩
  have stepCut3 : ∀ a b m', DivCut 8 a b →
      ∃ b', DivCut 10 (run (liftF (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨m2, h⟩ := oddRowCut3 F u a hrel.1 m'
    have dA := step8 _ _ (m2.take (measurementCount (liftF (StairSchedule.forwardSegment cp 47 32 465 480)))) ⟨⟨u, rfl⟩, hrel⟩
    have dB := step9 _ _ (m2.drop (measurementCount (liftF (StairSchedule.forwardSegment cp 47 32 465 480)))) dA
    have e : liftF (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 (2 + 1)) =
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 3) :=
      ExteriorPorts.placedShape _
    rw [h, liftF_append, run_append, e]
    exact ⟨_, dB⟩
  have stepCut4 : ∀ a b m', DivCut 10 a b →
      ∃ b', DivCut 12 (run (liftF (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨m2, h⟩ := oddRowCut4 F u a hrel.1 m'
    have dA := step10 _ _ (m2.take (measurementCount (liftF (StairSchedule.forwardSegment cp 32 22 480 490)))) ⟨⟨u, rfl⟩, hrel⟩
    have dB := step11 _ _ (m2.drop (measurementCount (liftF (StairSchedule.forwardSegment cp 32 22 480 490)))) dA
    have e : liftF (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 (1 + 1)) =
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 2) :=
      ExteriorPorts.placedShape _
    rw [h, liftF_append, run_append, e]
    exact ⟨_, dB⟩
  have stepCut5 : ∀ a b m', DivCut 12 a b →
      ∃ b', DivCut 14 (run (liftF (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1)) m' a) b' := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨m2, h⟩ := oddRowCut5 F u a hrel.1 m'
    have dA := step12 _ _ (m2.take (measurementCount (liftF (StairSchedule.forwardSegment cp 22 12 490 500)))) ⟨⟨u, rfl⟩, hrel⟩
    have dB := step13 _ _ (m2.drop (measurementCount (liftF (StairSchedule.forwardSegment cp 22 12 490 500)))) dA
    have e : liftF (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 (1 + 1)) =
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 2) :=
      ExteriorPorts.placedShape _
    rw [h, liftF_append, run_append, e]
    exact ⟨_, dB⟩
  have step14 := step_disj 14 (by decide) (liftF (StairSchedule.forwardLast cp)) (by rfl) (disjoint_ryWires_liftF forwardLast_notRY)
  have step15 := step_disj 15 (by decide) (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup) (by rfl) (disjoint_ryWires_append (disjoint_ryWires_fieldRename unprefix_notRY) paritySetup_notRY)
  have step16 := step_disj 16 (by decide) (StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram) (by rfl) (disjoint_ryWires_append hostedX_notRY (disjoint_ryWires_fieldRename clearProgram_notRY))
  -- Cut 17 → Exact `b17 = run R6 nR6 s0` via `EntryPlanR.lastStep`, then piece 17 (`grpL bestLoans 43 100 2`) + pieces 18–20 (`divEndTail_eq`)!
  have h17_eq_R6 : ∀ u, ∃ (s0 : State) (F0 : EntryFrame s0) (nR6 : List Bool),
      F0.x = F.x ∧ run (cut eps 17) u tStd = run R6 nR6 s0 := by
    intro u
    obtain ⟨Q13, h13⟩ := ern13 F.x (StairOpenWiring.entryPlans F.x) V
    have h14 := crel_append h13 (sharedEn F.x 12 (grpL StairConcrete.bestLoans 41 98 2)
      (R5L StairConcrete.bestLoans) (away_of_sub _ _ _ entryGroupSub_best.2.2.2.2.2 (grp_away 12 (by decide) 98 2 (by decide))))
    have hcut17 : cut eps 17 = (ES13 ++ grpL StairConcrete.bestLoans 41 98 2) ++ lastSeg cp := by
      rw [cut_succ eps 16 (eL 16 (by decide)), cut_succ eps 15 (eL 15 (by decide)),
          cut_succ eps 14 (eL 14 (by decide)), cut_succ eps 13 (eL 13 (by decide)), ecut13,
          show (eps[13]'(eL 13 (by decide))).L = grpL StairConcrete.bestLoans 41 98 2 from rfl,
          show (eps[14]'(eL 14 (by decide))).L = liftF (StairSchedule.forwardLast cp) from rfl,
          show (eps[15]'(eL 15 (by decide))).L = StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup from rfl,
          show (eps[16]'(eL 16 (by decide))).L = StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram from rfl]
      simp only [lastSeg, List.append_assoc]
    obtain ⟨n14, hrr14⟩ := h14 tStd tStd ⟨⟨F, rfl⟩, rfl⟩
      (u.take (measurementCount (ES13 ++ grpL StairConcrete.bestLoans 41 98 2)))
    obtain ⟨nL, heqL⟩ := (StairOpenWiring.entryPlans F.x).lastStep _ _ ⟨hrr14.1, V.r6 _ hrr14.2⟩
      (u.drop (measurementCount (ES13 ++ grpL StairConcrete.bestLoans 41 98 2)))
    obtain ⟨s0, nR6, ⟨F0, fx⟩, hs0⟩ := V.r6 _ hrr14.2
    refine ⟨s0, F0, nR6, fx, ?_⟩
    rw [hcut17, run_append, heqL]
    exact (by simp [run] : run [] nL _ = _).trans hs0
  -- Step 17 (`grpL bestLoans 43 100 2`): exact `b17 = run R6 nR6 s0` gives `FrameAt F.x 100 b17` + `AgreeOutside (Δv 0) b17 b17`!
  have step17 : ∀ a b m', DivCut 17 a b →
      DivCut 18
        (run (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 44 100 2)) m' a)
        (run (grpL StairConcrete.bestLoans 43 100 2) m' b) ∧
      (∃ (origin : BasisState) (ctx : FrontierReplay1591.Context origin)
        (en : origin (base 2400) = true) (X Y : Fp) (s102 : State),
        (Replay5.endPayload true origin (X, Y)).1 = Y ∧
        Rolling1588Frame.EncodedFieldFrame false origin X Y s102 ∧
        (∀ q, Off q → (pullIn (run (grpL StairConcrete.bestLoans 43 100 2) m' b)).basis q = s102.basis q)) := by
    rintro a b m' ⟨⟨u, rfl⟩, hrel⟩
    obtain ⟨s0, F0, nR6, fx, heq17⟩ := h17_eq_R6 u
    have hframe17 : FrameAt F.x 100 (run (cut eps 17) u tStd) := by
      rw [heq17, ← fx]; exact (g_R6 s0 F0 nR6).1
    have hagree17 : AgreeOutside (Δv 0) (run (cut eps 17) u tStd) (run (cut eps 17) u tStd) :=
      ⟨rfl, fun _ _ => rfl⟩
    have hclIn : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 43 ++ hostPlan.group true 43 100 2).map lowMap,
        (run (cut eps 17) u tStd).basis q = false :=
      groupsBefore_eps 17 43 100 2 (by simp) tStd ⟨F⟩ u
    have hclOut : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 43).map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups true 43 100 2))) m' (run (cut eps 17) u tStd)).basis q = false :=
      cleanCut_after (groupsRolesAfter_eps 17 43 100 2 (by simp))
        (by rw [cut_succ eps 17 (eL 17 (by decide)),
                show (eps[17]'(eL 17 (by decide))).L = grpL StairConcrete.bestLoans 43 100 2 from rfl, grpL_eq]) tStd ⟨F⟩ u m'
    have hclIn' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 44 ++
          OddFullPass.P1LifeLoan.hostPlan1542.group true 44 100 2).map lowMap,
        (run (cut eps 17) u tStd).basis q = false := by
      intro q hq
      apply hclIn q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      refine ⟨w, ?_, rfl⟩
      rcases List.mem_append.mp hw with hr | hh
      · exact List.mem_append_left _ ((List.drop_sublist_drop_left _ (by decide : 43 ≤ 44)).subset hr)
      · exact List.mem_append_right _ (hostPlan1542_group_sub true 43 100 2 (by decide) w hh)
    have hclOut' : ∀ q ∈ (StairSchedule.exclusiveRoles.drop 44).map lowMap,
        (run (liftF (renameProgram (OB5.sig 511) (StairGroups.groups true 43 100 2))) m' (run (cut eps 17) u tStd)).basis q = false := by
      intro q hq
      apply hclOut q
      rw [List.mem_map] at hq ⊢
      obtain ⟨w, hw, rfl⟩ := hq
      exact ⟨w, (List.drop_sublist_drop_left _ (by decide : 43 ≤ 44)).subset hw, rfl⟩
    have hstep := odd_hostedGroup_step true 44 43 100 2 0 F.x (hpOdd := OddFullPass.P1LifeLoan.hostPlan1542)
      (by decide) (by decide) (by decide) (by decide)
      (Or.inl rfl) (fun h => absurd rfl h) a (run (cut eps 17) u tStd) (run (cut eps 17) u tStd) m'
      hrel hframe17 (by simp only [if_true]) hclIn' hclOut' (hostPlan1542_group_notRY true 43 100 2 (by decide))
      (hostPlan1542_group_fresh_odd true 43 100 2 (by decide) (by decide) (by decide) (by decide) (Or.inl rfl))
    rw [← grpL_eq] at hstep
    -- Also show `run (grpL bestLoans 43 100 2) m' (run R6 nR6 s0) = run (R6 ++ grp 100 2) (joinTapes R6 nR6 m') s0`!
    -- Wait: `StairGroups.groups true 43 100 2` agrees with `Rolling1588.groups true 100 2` on `s7` via `StairGroups.groups_cut_frame`
    -- AND `div_cut18_frame F0` gives `EncodedFieldFrame false origin X Y s102` + `AgreeOff`!
    -- Specifically, `run (grpL bestLoans 43 100 2) m' (run R6 nR6 s0) = run (grp 100 2) m' (run R6 nR6 s0)`:
    have hgrp_eq : run (grpL StairConcrete.bestLoans 43 100 2) m' (run R6 nR6 s0) =
        run (grp 100 2) m' (run R6 nR6 s0) := by
      have hg6 := (g_R6 s0 F0 nR6).1
      obtain ⟨orig, X, Y, s_rec, ctx, en, _, hcut, hagree_rec⟩ := hg6
      have hsub : wires (renameProgram (OB5.sig 511) (StairGroups.groups true 43 100 2)) ⊆
          wires (renameProgram (OB5.sig 511) (Rolling1588.groups true 100 2)) := by
        rw [renameProgram_support, renameProgram_support]
        exact Finset.image_subset_image (StairLoanGroupSupport.groups_sub true 43 (by decide) 100 2)
      have hoff : ∀ q ∈ wires (renameProgram (OB5.sig 511) (Rolling1588.groups true 100 2)), Off q :=
        groups_off 100 2 (by decide) (by decide)
      have hrun_eq : run (renameProgram (OB5.sig 511) (StairGroups.groups true 43 100 2)) m' s_rec =
          run (renameProgram (OB5.sig 511) (Rolling1588.groups true 100 2)) m' s_rec := by
        apply pullState_sig511_injective
        rw [run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide)),
            run_rename (OB5.sig 511) (OB5.sig_injective 511 (by decide))]
        exact StairLoanReplay.groups_run_eq StairOpenWiring.half760 true 43 100 2 (by decide) (by decide) (by decide)
          orig ctx en X Y (pullState (OB5.sig 511) s_rec) m' m' hcut
      rw [grpL_eq, grp_eq, StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run]
      apply congrArg pullOut
      exact local_eq_of_sub _ _ hsub (pullIn (run R6 nR6 s0)) s_rec m'
        (fun q hq => hagree_rec q (hoff q hq)) hrun_eq
    refine ⟨⟨⟨WindowFieldJourney.joinTapes (cut eps 17) u m', ?_⟩, hstep⟩, ?_⟩
    · rw [cut_succ eps 17 (eL 17 (by decide)),
          show (eps[17]'(eL 17 (by decide))).L = grpL StairConcrete.bestLoans 43 100 2 from rfl,
          WindowFieldJourney.joined]
    · rw [heq17, hgrp_eq, ← WindowFieldJourney.joined R6 (grp 100 2) nR6 m' s0]
      exact div_cut18_frame F0 (WindowFieldJourney.joinTapes R6 nR6 m')
  -- Assemble the full 24-piece run equality: `run odd24NC mPre tOdd = run (cut eps 24) n24 tStd`!
  let odd24NC : Program :=
    ((Stair44Kernel.divLead ++ stockOddDivBeforeGroup) ++
      renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84)) ++
    ((((stockOddDivPreCut ++ StairSchedule.paritySetup) ++ stockOddDivBetweenNC) ++ StairSchedule.paritySetup))
  have hodd24NC_shape : odd24NC =
      (((((((((((((Stair44Kernel.divLead ++ stockOddDivBeforeGroup) ++
        renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84)) ++
        liftF (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4)) ++
        liftF (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2)) ++
        liftF (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2)) ++
        liftF (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1)) ++
        liftF (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1)) ++
        liftF (StairSchedule.forwardLast cp)) ++
        (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup)) ++
        (StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram)) ++
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 44 100 2)) ++
        liftF (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
          HalfFieldOB5.copyN)) ++
        (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.hostedX ++ StairSchedule.paritySetup)) := by
    have hlt_eq (P : Program) : liftF P = renameProgram ExteriorPorts.fieldEquiv P :=
      ExteriorPorts.placedShape P
    have hraw : renameProgram ExteriorPorts.fieldEquiv stockOddDivRawTailCut =
        liftF (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4) ++
        liftF (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2) ++
        liftF (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2) ++
        liftF (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1) ++
        liftF (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1) ++
        liftF (StairSchedule.forwardLast cp) := by
      simp only [stockOddDivRawTailCut, Six505.rename_append, hlt_eq, List.append_assoc]
    have hbet : stockOddDivBetweenNC =
        StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram ++
        renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 44 100 2) ++
        liftF (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
          HalfFieldOB5.copyN) ++
        StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.hostedX := by
      simp only [stockOddDivBetweenNC, WindowParityCaller.entryLowSuffixOddNC,
        WindowParityCaller.entryTailSuffixOddNC, fieldRename_append, Six505.rename_append,
        liftF, List.append_assoc]
      rw [← ExteriorPorts.placedShape (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 44 100 2)]
    simp only [odd24NC, stockOddDivPreCut, hraw, hbet, List.append_assoc]
  have hchain (s3 : State) (m3 m4 m6 m8 m10 m12 m14 m15 m16 m17 m1820 m2123 : List Bool)
      (h3 : ∃ b3, DivCut 3 s3 b3) :
      ∃ n24, DivNCOut
        (run (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.hostedX ++ StairSchedule.paritySetup) m2123
          (run (liftF (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
            HalfFieldOB5.copyN)) m1820
          (run (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 44 100 2)) m17
          (run (StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram) m16
          (run (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup) m15
          (run (liftF (StairSchedule.forwardLast cp)) m14
          (run (liftF (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1)) m12
          (run (liftF (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1)) m10
          (run (liftF (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2)) m8
          (run (liftF (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2)) m6
          (run (liftF (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4)) m4
          (run (renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84)) m3 s3))))))))))))
        (run (cut eps 24) n24 tStd) := by
    obtain ⟨b3, d3⟩ := h3
    have d4 := step3 _ _ m3 d3
    obtain ⟨b6, d6⟩ := stepCut1 _ _ m4 d4
    obtain ⟨b8, d8⟩ := stepCut2 _ _ m6 d6
    obtain ⟨b10, d10⟩ := stepCut3 _ _ m8 d8
    obtain ⟨b12, d12⟩ := stepCut4 _ _ m10 d10
    obtain ⟨b14, d14⟩ := stepCut5 _ _ m12 d12
    have d15 := step14 _ _ m14 d14
    have d16 := step15 _ _ m15 d15
    have d17 := step16 _ _ m16 d16
    obtain ⟨⟨⟨u18, hb18⟩, hrel18⟩, origin, ctx, en, X, Y, s102, hend, hfr102, hag102⟩ := step17 _ _ m17 d17
    rw [hb18] at hrel18 hag102
    have htail := divEndTailNC origin ctx en X Y hend _ _ s102 m1820 hrel18 hfr102 hag102
    let mTail := WindowFieldJourney.joinTapes
      (liftF (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint ++
        HalfFieldOB5.copyN ++ StairConcrete.bestLoans.canon)) m1820 m2123
    refine ⟨WindowFieldJourney.joinTapes (cut eps 18) u18 mTail, ?_⟩
    have hc24 : cut eps 24 = cut eps 18 ++
        (liftF (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint ++
          HalfFieldOB5.copyN ++ StairConcrete.bestLoans.canon) ++
        (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.hostedX ++ StairSchedule.paritySetup)) := by
      rw [cut_succ eps 23 (eL 23 (by decide)), cut_succ eps 22 (eL 22 (by decide)),
          cut_succ eps 21 (eL 21 (by decide)), cut_succ eps 20 (eL 20 (by decide)),
          cut_succ eps 19 (eL 19 (by decide)), cut_succ eps 18 (eL 18 (by decide)),
          show (eps[18]'(eL 18 (by decide))).L = liftF (renameProgram (OB5.sig 511) StairConcrete.bestLoans.divEndpoint) from rfl,
          show (eps[19]'(eL 19 (by decide))).L = liftF HalfFieldOB5.copyN from rfl,
          show (eps[20]'(eL 20 (by decide))).L = liftF StairConcrete.bestLoans.canon from rfl,
          show (eps[21]'(eL 21 (by decide))).L = StairSchedule.fieldRename FourScratchWindow.unprefix from rfl,
          show (eps[22]'(eL 22 (by decide))).L = StairSchedule.hostedX from rfl,
          show (eps[23]'(eL 23 (by decide))).L = StairSchedule.paritySetup from rfl]
      simp only [liftF_append, List.append_assoc]
    rw [hc24, WindowFieldJourney.joined, WindowFieldJourney.joined]
    exact divNCOut_run _ tail2123_notFieldR ⟨Y, htail⟩ m2123
  have h24 : ∃ n24, DivNCOut (run odd24NC mPre tOdd) (run (cut eps 24) n24 tStd) := by
    rw [hodd24NC_shape,
        run_append _ (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.hostedX ++ StairSchedule.paritySetup),
        run_append _ (liftF (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
          HalfFieldOB5.copyN)),
        run_append _ (renameProgram ExteriorPorts.fieldEquiv (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 44 100 2)),
        run_append _ (StairSchedule.hostedX ++ StairSchedule.fieldRename FourScratchWindow.clearProgram),
        run_append _ (StairSchedule.fieldRename FourScratchWindow.unprefix ++ StairSchedule.paritySetup),
        run_append _ (liftF (StairSchedule.forwardLast cp)),
        run_append _ (liftF (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1)),
        run_append _ (liftF (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1)),
        run_append _ (liftF (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2)),
        run_append _ (liftF (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2)),
        run_append _ (liftF (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4)),
        run_append _ (renameProgram ExteriorPorts.fieldEquiv (WindowFieldCosts.ogroup true 1 84))]
    exact hchain _ _ _ _ _ _ _ _ _ _ _ _ _ (hcut3 _)
  obtain ⟨n24, hn24⟩ := h24
  have hold24 : run (Stair44Kernel.divLead ++ Stair44Kernel.fieldD) n24 tStd = run (cut eps 24) n24 tStd := by
    rw [WindowStockHead.beforeD F, ← Stair44DivisionCut.selected cp hostPlan]
    unfold cut
    exact Stair44HostedCut.entry 24 tStd ⟨F⟩ n24
  refine ⟨WindowFieldJourney.joinTapes (Stair44Kernel.divLead ++ Stair44Kernel.fieldD) n24 mPost, ?_⟩
  have hsh : stockOddDivHeadCutNC = odd24NC ++ stockOddDivPost := by
    simp only [stockOddDivHeadCutNC, odd24NC, stockOddDivPost, List.append_assoc]
  have hpost : stockOddDivPost = renameProgram Rolling1588Lifetime.phaseHost Stair44Outer.reverseEnd := rfl
  have hmPre : m.take (measurementCount odd24NC) = mPre := rfl
  have hmPost : m.drop (measurementCount odd24NC) = mPost := rfl
  rw [hsh, run_append, hmPre, hmPost, hpost, WindowMiddleContract.oldDivHead, WindowFieldJourney.joined, hold24]
  exact divNCOut_run _ divPost_notFieldR hn24 mPost



attribute [local irreducible] FrontierEntry1591NativeH.inverse FrontierEntry1591Native.inverse

set_option exponentiation.threshold 1024 in
/-- The stock division tail after the head (`backward false 490` and the native inverse) never
    touches `fieldR`. -/
theorem divRawTail_notFieldR :
    ∀ q ∈ wires (renameProgram Rolling1588Lifetime.phaseHost (Stair44WalkRun.backward false 490 ++
      renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))), q ∉ fieldR := by
  have first_fix : ∀ q ∈ fieldR, Stair44WalkMap.first q = q := by
    have h : fieldR.all (fun q => decide (Stair44WalkMap.first q = q)) = true := by decide +kernel
    intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)
  have rest_fix : ∀ q ∈ fieldR, Stair44WalkMap.rest q = q := by
    have h : fieldR.all (fun q => decide (Stair44WalkMap.rest q = q)) = true := by decide +kernel
    intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)
  have inv : ∀ q ∈ wires (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)),
      q ∉ fieldR := by
    have table : (NativeFirstDirect.prefixSites base).all
        (fun z => decide (z = base 1797) || notFieldR (Stair44WalkMap.first z)) = true := by decide +kernel
    have h511 : notFieldR (Stair44WalkMap.first (base 511)) = true := by decide +kernel
    intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    have h := (FrontierEntry1591Native.support base base_pool_nodup).2
      (FrontierEntry1591NativeH.wires_sub base base_pool_nodup hx)
    have m : x ≠ base 1797 ∧ x ∈ insert (base 511) (NativeFirstDirect.prefixSites base).toFinset :=
      Finset.mem_erase.mp h
    rcases Finset.mem_insert.mp m.2 with eq | inside
    · rw [eq]; exact (notFieldR_iff _).mp h511
    · have t := List.all_eq_true.mp table x (List.mem_toFinset.mp inside)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at t
      exact (notFieldR_iff _).mp (t.resolve_left m.1)
  have bwd : ∀ q ∈ wires (Stair44WalkRun.backward false 490), q ∉ fieldR := by
    intro q hq hfr
    unfold Stair44WalkRun.backward at hq
    rw [wires_append, Finset.mem_union] at hq
    rcases hq with h1 | h2
    · rw [renameProgram_support] at h1
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h1
      have eq := rest_fix _ hfr
      exact reverse_notFieldR false 490 16 (by decide) (by decide) w hw
        ((Stair44WalkMap.rest.injective eq) ▸ hfr)
    · rw [renameProgram_support] at h2
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h2
      have eq := first_fix _ hfr
      exact reverse_notFieldR false 15 1 (by decide) (by decide) w hw
        ((Stair44WalkMap.first.injective eq) ▸ hfr)
  intro q hq hfr
  rw [renameProgram_support] at hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  have hw_fr : w ∈ fieldR := (Rolling1588Lifetime.phaseHost.injective (phaseHost_fix_fieldR _ hfr)) ▸ hfr
  rw [wires_append, Finset.mem_union] at hw
  exact hw.elim (fun h => bwd w h hw_fr) (fun h => inv w h hw_fr)

end ECDSAAdd.Entrant.OddStockLockstep

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly StairField13V3 StairField13V3Clean
open StairField2V3Replay StairHostsSchedule ExteriorPorts Rolling1588Lifetime
set_option maxRecDepth 14000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires

def betweenOddNC := StairSchedule.hostedX ++
  StairSchedule.fieldRename (WindowParityCaller.entryLowSuffixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ++
  StairSchedule.hostedX
def fieldOddCutNC (S G : Program) := (((beforeGroupOdd ++ renameProgram fieldEquiv G) ++ preOddCut) ++ S) ++ betweenOddNC ++ S

theorem correctedCutNC : WindowParityCaller.entryFieldHostedCutNC =
    fieldOddCutNC WindowFieldParity.setup (WindowFieldCosts.group84 true) := by
  simp only [fieldOddCutNC,beforeGroupOdd,preOddCut,betweenOddNC,rawTailOddCut,WindowParityCaller.entryFieldHostedCutNC,
    WindowCallerCosts.entryLowPrefixCut,WindowCallerCosts.entryTailPrefixCut,←placedShape,fieldRename_append,
    rename_append,List.append_assoc]

theorem betweenOddNC_sub : betweenOddNC.Sublist betweenOdd := by
  unfold betweenOddNC betweenOdd
  refine ((List.Sublist.refl _).append ?_).append (List.Sublist.refl _)
  rw [OddFullPass.P1LifeLoan.entryLowSuffixOdd, WindowParityCaller.entryLowSuffixOddNC,
    WindowParityCaller.entryTailSuffixOdd_eqNC]
  unfold StairSchedule.fieldRename StairSchedule.parityRename
  exact PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (((List.Sublist.refl _).append
    (PackCutSub.rename_sub _ (List.sublist_append_left _ _))).append (List.Sublist.refl _)))

theorem betweenOddNCFree : Clear betweenOddNC :=
  fun q hq hw => betweenOddFree q hq (PackCutSub.wires_sub betweenOddNC_sub q hw)

end ECDSAAdd.Entrant.StairPacket.ExteriorDivPieces

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelReplay
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime FlagEntry StairConcreteAssembly StockArchiveBanks
open WindowMiddleContract WindowStockHead
set_option linter.unusedVariables false

/-- `OddEntryContract` for the NC division head, paired with the NC stock-odd head (not the
    balanced head: the two differ on `fieldR`). -/
def OddEntryContractNC : Prop :=
  ∀ (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (x : Nat) (Y : Fp) (hx0 : 0 < x) (hx : x < p) (s tOdd : State) (m : List Bool)
    (hin : SkywalkArithmeticInput base x Y.val s.basis)
    (hg0 : s.basis (base 2409) = false) (hs0 : s.basis (base 2410) = false)
    (hph : tOdd.phase = s.phase)
    (hsame : ∀ q, q ∉ wireBlock base 2056 256 → tOdd.basis q = s.basis q)
    (hval : regValue (wireBlock base 2056 256) tOdd.basis = P1Life.oddWord (Y / 2)),
    ∃ old, Paired false x (pullState phaseHost (run divHeadNC m tOdd))
      (pullState phaseHost (run OddStockLockstep.stockOddDivHeadCutNC old tOdd)) (StockRowVector.rows x p)

end ECDSAAdd.Entrant.StairPacket.WindowKernelReplay

end

section

namespace ECDSAAdd.Entrant.StairPacket.ExteriorDivReady
open Arithmetic MappedCompressed Secp256k1 StairConcreteAssembly Rolling1588Lifetime
open StockArchiveBanks WindowStartStates ExteriorPorts ExteriorDivPieces WindowFieldMask WindowFieldJourney
set_option maxHeartbeats 2000000
set_option maxRecDepth 15000
attribute [local irreducible] run measurementCount wires

theorem stockOddShapeCutNC : OddStockLockstep.stockOddDivHeadCutNC =
    prefixROdd ++ WindowReturningTail.program preOddCut betweenOddNC post StairSchedule.paritySetup := by
  simp only [OddStockLockstep.stockOddDivHeadCutNC, OddStockLockstep.stockOddDivBeforeGroup,
    OddStockLockstep.stockOddDivPreCut, OddStockLockstep.stockOddDivRawTailCut,
    OddStockLockstep.stockOddDivBetweenNC, OddStockLockstep.stockOddDivPost,
    prefixROdd, refBegin, beforeGroupOdd, preOddCut, rawTailOddCut, betweenOddNC, post,
    JointOdd1588.hostedFirstPacketOdd, StairConcreteAssembly.hostPlan, WindowReturningTail.program, List.append_assoc]

theorem newShapeOddCutNC : WindowMiddleContract.divHeadNC =
    prefixWOdd ++ WindowReturningTail.program preOddCut betweenOddNC post WindowFieldParity.setup := by
  simp only [WindowMiddleContract.divHeadNC, WindowKernelPrograms.divBeforeNC, correctedCutNC, fieldOddCutNC,
    prefixWOdd, beginW, opening, pack, post, WindowReturningTail.program, Six505.rename_append, List.append_assoc]

theorem entryOddNC : WindowKernelReplay.OddEntryContractNC := by
  intro hn hl ho hf x Y hx0 hx s tOdd m input hg hs phase eq val
  let tStd := OddStockLockstep.stdOfOdd tOdd Y
  have hag : OddStockLockstep.AgreeOutsideR tOdd tStd :=
    ⟨rfl, fun q hq => by simp only [tStd, OddStockLockstep.stdOfOdd, dif_neg hq]⟩
  have hval_std : regValue OddStockLockstep.fieldR tStd.basis = BalancedField.centerWord (Y / 2) := by
    have hlt : BalancedField.centerWord (Y / 2) < 2 ^ 256 := (BalancedField.centerWord_valid (Y / 2)).1
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 256
    · have hlen : OddStockLockstep.fieldR.length = 256 := by simp [OddStockLockstep.fieldR, wireBlock_length]
      have hbit := Arithmetic.regValue_bit OddStockLockstep.fieldR i 0 tStd.basis (by omega)
      have hget : OddStockLockstep.fieldR.getD i 0 = base (2056 + i) := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [OddStockLockstep.fieldR, wireBlock]
      rw [hget] at hbit
      have hmem : base (2056 + i) ∈ OddStockLockstep.fieldR :=
        List.mem_map.mpr ⟨2056 + i, by simp only [List.mem_range'_1]; omega, rfl⟩
      have hsub : base (2056 + i) - 2072 = i := by change (2056 + i) + 16 - 2072 = i; omega
      have htb : tStd.basis (base (2056 + i)) = (BalancedField.centerWord (Y / 2)).testBit i := by
        simp only [tStd, OddStockLockstep.stdOfOdd, dif_pos hmem, hsub]
      rw [htb] at hbit
      rw [Nat.testBit_eq_decide_div_mod_eq, ← hbit]
      cases (BalancedField.centerWord (Y / 2)).testBit i <;> decide
    · have hlen : OddStockLockstep.fieldR.length = 256 := by simp [OddStockLockstep.fieldR, wireBlock_length]
      have hlt1 : regValue OddStockLockstep.fieldR tStd.basis < 2 ^ 256 := hlen ▸ Arithmetic.regValue_lt OddStockLockstep.fieldR tStd.basis
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  let FStd : EntryFrame tStd :=
    ⟨hn, hl, ho, hf, x, Y, hx0, hx, s, input, hg, hs, phase,
      fun q hq => (hag.2 q hq).symm.trans (eq q hq), hval_std⟩
  obtain ⟨old, ff⟩ := starts_odd FStd hag val m
  let mTail := m.drop (measurementCount prefixWOdd)
  let tape0 := joinTapes prefixROdd old []
  obtain ⟨nOld0, Yh0, hag0, -, -⟩ := OddStockLockstep.stockOddDivHeadCutNC_agree_oldDivHead FStd hag val tape0
  have native0 := WindowEndBytes.div_native FStd nOld0
  have known : ∀ b, nativeAt false b (StockRowVector.rows x p b)
      (run OddStockLockstep.stockOddDivHeadCutNC tape0 tOdd) := by
    intro b j
    exact (hag0.2 _ (OddStockLockstep.archives_not_fieldR b j)).trans
      (WindowReturningBytes.nativeUnpull native0.bytes b j)
  unfold tape0 at known
  rw [stockOddShapeCutNC, joined] at known
  have hkeep : WindowReturningBytes.Keeps (WindowReturningTail.program preOddCut betweenOddNC post StairSchedule.paritySetup) :=
    WindowReturningBytes.both (WindowReturningBytes.both (WindowReturningBytes.both
      (WindowReturningBytes.both (WindowReturningBytes.untouched preOddCutFree) WindowReturningBytes.parity)
      (WindowReturningBytes.untouched betweenOddNCFree)) WindowReturningBytes.parity) (WindowReturningBytes.untouched postFree)
  have here := WindowReturningBytes.nativeBack hkeep known
  have source : Paired false x (run prefixWOdd m tOdd)
      (run prefixROdd old tOdd) (StockRowVector.rows x p) :=
    pairFinished ff native0.ids here
  obtain ⟨nTail, pairTail⟩ := WindowReturningTail.carry preOddCutFree betweenOddNCFree postFree _ _ source mTail
  refine ⟨joinTapes prefixROdd old nTail, ?_⟩
  rw [newShapeOddCutNC, stockOddShapeCutNC, run_append, run_take, joined]
  exact pairPull phaseHost phaseHost.injective phaseFix pairTail

end ECDSAAdd.Entrant.StairPacket.ExteriorDivReady

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowKernelReplay
open Arithmetic MappedCompressed Secp256k1 Rolling1588Lifetime FlagEntry StairConcreteAssembly StockArchiveBanks
open WindowMiddleContract WindowStockHead
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount wires renameProgram

theorem division_oddNC (geometry : OddEntryContractNC) :
    SqOddContract.EntryCorrectOddNC WindowKernelPrograms.divisionNC := by
  intro hn hl ho hf x Y hx0 hx s tOdd m input hg hs phase eq val
  let tStd := OddStockLockstep.stdOfOdd tOdd Y
  have hag := stdOfOdd_agree tOdd Y
  let FStd : EntryFrame tStd :=
    ⟨hn, hl, ho, hf, x, Y, hx0, hx, s, input, hg, hs, phase,
      fun q hq => (hag.2 q hq).symm.trans (eq q hq), stdOfOdd_val tOdd Y⟩
  obtain ⟨head, v⟩ := geometry hn hl ho hf x Y hx0 hx s tOdd m input hg hs phase eq val
  obtain ⟨nOld, Yh, hAgHead, hValOdd, hValOld⟩ :=
    OddStockLockstep.stockOddDivHeadCutNC_agree_oldDivHead FStd hag val head
  have hEndOdd : Endpoint false x 505 (pullState phaseHost (run OddStockLockstep.stockOddDivHeadCutNC head tOdd)) := by
    obtain ⟨s0, enc, st, hpool⟩ := div_endpoint FStd nOld
    refine ⟨s0, enc, st, fun q hq => ?_⟩
    have hq_notR : phaseHost q ∉ OddStockLockstep.fieldR :=
      OddStockLockstep.fieldR_disjoint_pool (phaseHost q) (Stair44DivTerm.host_pool q (List.mem_toFinset.mp hq))
    rw [pullState_basis_tail]
    have hhp := hpool q hq
    rw [pullState_basis_tail] at hhp
    exact (hAgHead.2 (phaseHost q) hq_notR).trans hhp
  obtain ⟨post, htail⟩ := tail false 85 x hx0 hx (by decide)
    (run divHeadNC m tOdd) (run OddStockLockstep.stockOddDivHeadCutNC head tOdd)
    (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))
    (m.drop (measurementCount divHeadNC)) v hEndOdd
  have hdiv_eq : run WindowKernelPrograms.divisionNC m tOdd =
      run (renameProgram phaseHost (Stair44WalkRun.backward false 490 ++
        renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)))
        post (run OddStockLockstep.stockOddDivHeadCutNC head tOdd) := by
    rw [div_head_splitNC, run_append divHeadNC, run_take]
    exact htail
  let mFull := WindowFieldJourney.joinTapes oldDivHead nOld post
  have hold_eq : run Stair44Kernel.division mFull tStd =
      run (renameProgram phaseHost (Stair44WalkRun.backward false 490 ++
        renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)))
        post (run oldDivHead nOld tStd) := by
    rw [old_div_head_split, WindowFieldJourney.joined]
  have hout := OddStockLockstep.divNCOut_run _ OddStockLockstep.divRawTail_notFieldR
    ⟨Yh, hAgHead, hValOdd, hValOld⟩ post
  rw [← hdiv_eq, ← hold_eq] at hout
  obtain ⟨Yh', hAg, hRo, hRs⟩ := hout
  have old := Stair44Kernel.division_correct hn hl ho hf x Y hx0 hx s tStd mFull input hg hs phase
    (fun q hq => (hag.2 q hq).symm.trans (eq q hq)) (stdOfOdd_val tOdd Y)
  have h2 : 2 * Yh' = skywalkArithmeticResult true x Y := ZMod.val_injective _ (hRs.symm.trans old.2.1)
  have hY : Yh' = skywalkArithmeticResult true x Y / 2 := by
    rw [← h2, mul_div_cancel_left₀ _ (by decide : (2 : Fp) ≠ 0)]
  dsimp only
  refine ⟨hAg.1.trans old.1, ?_, fun q hq => (hAg.2 q hq).trans (old.2.2 q hq)⟩
  rw [hRo, hY]
  rfl

end ECDSAAdd.Entrant.StairPacket.WindowKernelReplay

end

section

namespace ECDSAAdd.Entrant.SqOddContract
open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout

/-- A state that equals a `PointDialogValues` state off `point.y` and holds `oddWord (Y' / 2)` on it
    satisfies `PointDialogValuesOdd`. -/
theorem PointDialogValuesOdd.ofValues {L : ControlledPointLayout} {X Y Y' : Fp} {G : Bool}
    {origin s t : BasisState} (hn : L.wires.Nodup) (v : PointDialogValues L X Y G origin s)
    (hy : regValue L.point.y t = EntryFuseOdd.oddWord (Y' / 2)) (hf : ∀ q, q ∉ L.point.y → t q = s q) :
    PointDialogValuesOdd L X Y' G origin t := by
  have away (q : Wire) (hq : q ∈ L.point.x ++ [L.core.generic] ++ L.dialogPool) : q ∉ L.point.y := by
    intro hh
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    have h1 := List.count_pos_iff.mpr hq
    have h2 := List.count_pos_iff.mpr hh
    simp only [dialogUsedWires, inPlaceFlags, PointAddLayout.pointWires,
      List.count_append, List.count_cons, List.count_nil] at h h1
    omega
  refine ⟨?_, hy, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.x
  · exact (hf _ (away _ (by simp))).trans v.generic
  · exact (regValue_congr _ _ _ (fun q hq => hf q (away q (by simp [hq])))).trans v.clean
  · intro q hq; exact (hf q (fun h => hq (List.mem_append_right _ h))).trans (v.rest q hq)

end ECDSAAdd.Entrant.SqOddContract

namespace ECDSAAdd.Entrant.OddOuterBridge
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open ControlledPointLayout CompressedPointDialog CompressedAllocation CompressedFieldSupport
open DirectSkywalk EntryFuse EntryFuseFinite ExitFusionResearch
open ParityUniform FlagEntry FlagExit ParityEven ParityXEntry Stair44PointMap
open EntryFuseOdd
open MappedCompressed.LaneA FrontierEntry1591Callers StairSemanticFinal

attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical

private theorem mapped_regNC (f : Wire → Wire) (r : List Wire)
    (logical physical : BasisState) (h : ∀ q ∈ r, logical q = physical (f q)) :
    regValue r logical = regValue (r.map f) physical := by
  induction r generalizing logical physical with
  | nil => rfl
  | cons a rs ih =>
    change (if logical a then 1 else 0) + 2 * regValue rs logical =
      (if physical (f a) then 1 else 0) + 2 * regValue (rs.map f) physical
    rw [h a (by simp), ih logical physical (fun q hq => h q (List.mem_cons_of_mem a hq))]

theorem entryTransferOddNC (K : Program) (correct : SqOddContract.EntryCorrectOddNC K)
    (L : ControlledPointLayout) (f : Wire → Wire) (domain : Finset Wire)
    (injective : ∀ a ∈ domain, ∀ b ∈ domain, f a = f b → a = b)
    (divisorMap : (wireBlock base 770 256).map f = L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f = L.point.y)
    (sharedWork : ∀ q ∈ skywalkSharedWires base, q ∈ domain → q ∉ wireBlock base 770 256 →
      q ∉ wireBlock base 2056 256 → f q ∈ L.dialogPool)
    (selectorG : f (base 2409) ∈ L.dialogPool) (selectorS : f (base 2410) ∈ L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset ⊆ domain)
    (dySites : (wireBlock base 2056 256).toFinset ⊆ domain)
    (sites : wires K ⊆ domain)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (ho : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (hf : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410) (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (hX0 : 0 < X) (hX : X < p)
    (s t : State) (m : List Bool)
    (hx : regValue L.point.x s.basis = X) (hy : regValue L.point.y s.basis = Y.val)
    (clean : regValue L.dialogPool s.basis = 0)
    (phase : t.phase = s.phase) (same : ∀ q, q ∉ L.point.y → t.basis q = s.basis q)
    (half : regValue L.point.y t.basis = oddWord (Y / 2)) :
    let out := run (renameProgram f K) m t
    out.phase = s.phase ∧
      regValue L.point.y out.basis = oddWord (skywalkArithmeticResult true X Y / 2) ∧
      ∀ q, q ∉ L.point.y → out.basis q = s.basis q := by
  let a := laneLogicalInput domain f s
  let b := laneLogicalInput domain f t
  have aBits (q : Wire) (hq : q ∈ domain) : a.basis q = s.basis (f q) := by
    simp only [a, laneLogicalInput, if_pos hq]
  have bBits (q : Wire) (hq : q ∈ domain) : b.basis q = t.basis (f q) := by
    simp only [b, laneLogicalInput, if_pos hq]
  have zero (q : Wire) (hq : f q ∈ L.dialogPool) : a.basis q = false := by
    change (if q ∈ domain then s.basis (f q) else false) = false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_, ?_, ?_⟩
    · change regValue (wireBlock base 770 256) a.basis = X
      rw [mapped_regNC f _ a.basis s.basis (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))), divisorMap]
      exact hx
    · change regValue (wireBlock base 2056 256) a.basis = Y.val
      rw [mapped_regNC f _ a.basis s.basis (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))), numeratorMap]
      exact hy
    · intro q hq hdx hdy
      by_cases used : q ∈ domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a, laneLogicalInput, if_neg used]
  have outside (q : Wire) (hq : q ∈ domain) (haway : q ∉ wireBlock base 2056 256) : f q ∉ L.point.y := by
    rw [← numeratorMap]
    intro bad
    obtain ⟨r, hr, he⟩ := List.mem_map.mp bad
    have eq : q = r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀ q, q ∉ wireBlock base 2056 256 → b.basis q = a.basis q := by
    intro q hq
    by_cases used : q ∈ domain
    · rw [bBits q used, aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a, b, laneLogicalInput, if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis = oddWord (Y / 2) := by
    rw [mapped_regNC f _ b.basis t.basis (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))), numeratorMap]
    exact half
  have phases : b.phase = a.phase := phase
  have strong := correct hn hlo ho hf X Y hX0 hX a b m input
    (zero _ selectorG) (zero _ selectorS) phases paired halfLogical
  have transfer := run_rename_pool f domain injective K sites m b t rfl bBits
  refine ⟨transfer.1.trans strong.1, ?_, ?_⟩
  · rw [← numeratorMap]
    exact (mapped_regNC f _ (run K m b).basis (run (renameProgram f K) m t).basis
      (fun q hq => (transfer.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans strong.2.1
  · intro q hq
    by_cases image : q ∈ domain.image f
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp image
      have away : r ∉ skywalkArithmeticNumerator base := by
        intro mem
        apply hq
        rw [← numeratorMap]
        exact List.mem_map.mpr ⟨r, mem, rfl⟩
      exact (transfer.2 r hr).trans ((strong.2.2 r away).trans (aBits r hr))
    · exact (run_rename_pool_outside f domain K sites m t q image).trans (same q hq)

theorem entry_correctD_oddNC (K : Program) (kernelSupport : wires K ⊆ callerDomain)
    (correct : SqOddContract.EntryCorrectOddNC K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X : Nat) (Y : Fp) (hX0 : 0 < X) (hX : X < p)
    (s t : State) (m : List Bool)
    (hx : regValue L.point.x s.basis = X) (hy : regValue L.point.y s.basis = Y.val)
    (clean : regValue L.dialogPool s.basis = 0) (phase : t.phase = s.phase)
    (same : ∀ q, q ∉ L.point.y → t.basis q = s.basis q)
    (half : regValue L.point.y t.basis = oddWord (Y / 2)) :
    let out := run (FrontierEntry1591Callers.entry K L) m t
    out.phase = s.phase ∧
      regValue L.point.y out.basis = oddWord (skywalkArithmeticResult true X Y / 2) ∧
      ∀ q, q ∉ L.point.y → out.basis q = s.basis q := by
  rcases placement2 L hw hn with ⟨_, divisor, numerator, _, _, selG, selS, _⟩
  exact entryTransferOddNC K correct L (wireFn2 L) callerDomain (wireFn2_injOn_caller L hw hn)
    divisor numerator (sharedWork_caller L hw) selG selS
    divisor_caller numerator_caller kernelSupport
    logicalND hlo logicalAway logicalReplay X Y hX0 hX s t m hx hy clean phase same half

/-- The NC division step: from canonical `PointDialogValues`, the odd `Y` entry and the NC division
    kernel leave `λ = (Y + k) / X` on `point.y` in odd-word form, everything else as the stock step. -/
theorem division_stepD_oddNC (K : Program) (kernelSupport : wires K ⊆ callerDomain)
    (correct : SqOddContract.EntryCorrectOddNC K)
    (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀ q ∈ [base 2400, base 2409, base 2410], q ∉ skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base))
    (X Y k : Fp) (G : Bool) (origin : BasisState) (hX : X ≠ 0) :
    Triple (PointDialogValues L X Y G origin)
      (entryYAllOdd L k ++ FrontierEntry1591Callers.entry K L)
      (SqOddContract.PointDialogValuesOdd L X ((Y + (if G then k else 0)) / X) G origin) := by
  intro s m v
  let Z : Fp := Y + (if G then k else 0)
  let n := measurementCount (entryYAllOdd L k)
  let a := run (entryYAllOdd L k) (m.take n) s
  let c := run (fastConstAdd L L.point.y k) [] s
  have oldAdd := fastConstAdd_correct L hw hn L.point.y (Or.inr rfl) k Y.val G Y.isLt s []
    v.generic v.y v.clean
  have oldStep := fastStep_addY L hw hn X Y G origin k s [] v
  have canonical : PointDialogValues L X Z G origin c.basis := oldStep.2
  have fused := entryYAllOdd_correct L hw hn Y k s (m.take n) v.y v.clean
  change a.phase = s.phase ∧ regValue L.point.y a.basis =
    oddWord ((Y + (if s.basis L.core.generic then k else 0)) / 2) ∧
    ∀ q, q ∉ L.point.y → a.basis q = s.basis q at fused
  change c.phase = s.phase ∧ regValue L.point.y c.basis = (Y.val + (if G then k.val else 0)) % p ∧
    ∀ q, q ∉ L.point.y → c.basis q = s.basis q at oldAdd
  have phase : a.phase = c.phase := fused.1.trans oldAdd.1.symm
  have same (q : Wire) (hq : q ∉ L.point.y) : a.basis q = c.basis q :=
    (fused.2.2 q hq).trans (oldAdd.2.2 q hq).symm
  have half : regValue L.point.y a.basis = oddWord (Z / 2) := by
    simpa only [v.generic, Z] using fused.2.1
  have hp : 0 < X.val := Nat.pos_of_ne_zero (fun hz => hX ((ZMod.val_eq_zero X).mp hz))
  have res := entry_correctD_oddNC K kernelSupport correct L hw hn logicalND hlo logicalAway
    logicalReplay X.val Z hp X.isLt c a (m.drop n)
    canonical.x canonical.y canonical.clean phase same half
  dsimp only at res
  have hq : skywalkArithmeticResult true X.val Z = Z / X := by
    simp only [skywalkArithmeticResult, if_true, ZMod.natCast_zmod_val]
  rw [hq] at res
  have eqProgram : run (entryYAllOdd L k ++ FrontierEntry1591Callers.entry K L) m s =
      run (FrontierEntry1591Callers.entry K L) (m.drop n) a := run_append _ _ _ _
  rw [eqProgram]
  exact ⟨res.1.trans oldAdd.1,
    SqOddContract.PointDialogValuesOdd.ofValues hn canonical res.2.1 res.2.2⟩

end ECDSAAdd.Entrant.OddOuterBridge

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowReleaseProof
open Arithmetic MappedCompressed Secp256k1 StairSemanticFinal StairConcreteAssembly Rolling1588Lifetime
attribute [local irreducible] wires renameProgram

theorem entryLowSuffixOddNC_sub (h : StairHostsSchedule.HostPlan) :
    (WindowParityCaller.entryLowSuffixOddNC h).Sublist (OddFullPass.P1LifeLoan.entryLowSuffixOdd h) := by
  rw [OddFullPass.P1LifeLoan.entryLowSuffixOdd, WindowParityCaller.entryLowSuffixOddNC,
    WindowParityCaller.entryTailSuffixOdd_eqNC]
  exact ((List.Sublist.refl _).append (PackCutSub.rename_sub _ (List.sublist_append_left _ _))).append
    (List.Sublist.refl _)

theorem entryFieldHostedCutNC_sub :
    WindowParityCaller.entryFieldHostedCutNC.Sublist WindowParityCaller.entryFieldHostedCut := by
  unfold WindowParityCaller.entryFieldHostedCutNC WindowParityCaller.entryFieldHostedCut
  have f : (StairSchedule.fieldRename (WindowParityCaller.entryLowSuffixOddNC OddFullPass.P1LifeLoan.hostPlan1542)).Sublist
      (StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542)) := by
    unfold StairSchedule.fieldRename StairSchedule.parityRename
    exact PackCutSub.rename_sub _ (PackCutSub.rename_sub _ (entryLowSuffixOddNC_sub _))
  exact (((List.Sublist.refl _).append f).append (List.Sublist.refl _)).append (List.Sublist.refl _)

theorem divisionNC_sub : WindowKernelPrograms.divisionNC.Sublist WindowKernelPrograms.division := by
  unfold WindowKernelPrograms.divisionNC WindowKernelPrograms.division WindowKernelPrograms.divBeforeNC
    WindowKernelPrograms.divBefore
  exact ((List.Sublist.refl _).append entryFieldHostedCutNC_sub).append (List.Sublist.refl _)

/-- Kernel support of the NC division (the `divSites` field for the switch). -/
theorem divisionNC_sites : wires WindowKernelPrograms.divisionNC ⊆ callerDomain :=
  fun q hq => division ExteriorCaller.entryFieldHostedCut_corrected (PackCutSub.wires_sub divisionNC_sub q hq)

end ECDSAAdd.Entrant.StairPacket.WindowReleaseProof

end

section

namespace ECDSAAdd.Entrant.SqOddContract
open ECDSAAdd Arithmetic Secp256k1

/-- After the NC division the actual state agrees with the stock state off `point.y` (this is the
    `t`/`s` premise of `SquareOddNC`). -/
theorem agree_of_valuesOdd {L : ControlledPointLayout} {X Y : Fp} {G : Bool}
    {origin : BasisState} {s a b : State}
    (ha : a.phase = s.phase ∧ PointDialogValuesOdd L X Y G origin a.basis)
    (hb : b.phase = s.phase ∧ PointDialogValues L X Y G origin b.basis) :
    a.phase = b.phase ∧ (∀ q, q ∉ L.point.y → a.basis q = b.basis q) ∧
      regValue L.point.y a.basis = EntryFuseOdd.oddWord (Y / 2) := by
  refine ⟨ha.1.trans hb.1.symm, fun q hy => ?_, ha.2.y⟩
  by_cases hx : q ∈ L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ha.2.x.trans hb.2.x.symm) q hx
  have hq : q ∉ L.point.x ++ L.point.y := by simp [hx, hy]
  exact (ha.2.rest q hq).trans (hb.2.rest q hq).symm

end ECDSAAdd.Entrant.SqOddContract

namespace ECDSAAdd.Entrant.StairPacket.WindowPointDivision
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXEntry FrontierEntry1591Callers Stair44PlacedHead
set_option maxHeartbeats 3500000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount fastConstAdd fusedY

/-- `part` with the NC division. -/
def partNC (cx cy : Fp) := Stair44PlacedHead.routed (-cx) (-cy) ++ WindowParityCaller.divideNC

open Stair44PointDivision
/-- `stage` for the NC division: `λ` ends on `point.y` as `oddWord (λ / 2)`. -/
theorem stageNC (enter : SqOddContract.EntryCorrectOddNC WindowKernelPrograms.divisionNC)
    (cx cy X Y : Fp) (G : Bool) (s : State) (m : List Bool)
    (v : PointDialogValues layout X Y G s.basis s.basis) (hx : X+(if G then -cx else 0)≠0) :
    let e := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+(-cx).val) else false
    let u := run (partNC cx cy) m (pullState Stair44PointMap.outer.symm (put s (pkW layout) e))
    u.phase=s.phase ∧ SqOddContract.PointDialogValuesOdd layout (X+(if G then -cx else 0))
      ((Y+(if G then -cy else 0))/(X+(if G then -cx else 0))) G s.basis u.basis := by
  intro e u
  let P := fastConstAdd layout layout.point.x (-cx) ++ EntryFuseOdd.entryYAllOdd layout (-cy)
  let F := E1QubitPlacement.tickF layout
  let K := FrontierEntry1591Callers.entry WindowKernelPrograms.divisionNC layout
  let H := Stair44PlacedHead.routed (-cx) (-cy)
  let r := m.drop (measurementCount H)
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have add := fastStep_addX layout layout_widths layout_nodup X Y G s.basis (-cx)
  have div := OddOuterBridge.division_stepD_oddNC WindowKernelPrograms.divisionNC
    WindowReleaseProof.divisionNC_sites enter layout layout_widths layout_nodup config.1 above config.2.1 config.2.2
    (X+(if G then -cx else 0)) Y (-cy) G s.basis hx
  have joint := add.seq div
  have equiv : (fastConstAdd layout layout.point.x (-cx) ++ (EntryFuseOdd.entryYAllOdd layout (-cy) ++ K))=P++K :=
    List.append_assoc _ _ _ |>.symm
  rw [equiv] at joint
  have ans := joint s (pfx (measurementCount P) [] ++ (pfx (measurementCount Stair44Splits.tick) [] ++ r)) v
  rw [run_pre,show K=Stair44Splits.tick++WindowParityCaller.divideNC from WindowKernelPrograms.div_splitNC,run_pre,
    show Stair44Splits.tick=renameProgram Stair44PointMap.integerFirst F from rfl,
    encodedTick _ _ (OddOuterBridge.prepClean_odd layout layout_widths layout_nodup (-cx) (-cy) X Y G s v)] at ans
  have tr := encoded_head X Y (-cx) (-cy) s (m.take (measurementCount H)) v.x v.y v.clean
  dsimp only at tr
  rw [show plain (-cx) (-cy) = EntryFuseOdd.entryYAllOdd layout (-cy) ++ entryXNew layout (pkW layout) (-cx) from rfl,
    OddOuterBridge.head_eq_odd layout layout_widths layout_nodup cx cy X Y G s _ v.x v.y v.generic v.clean (by decide +kernel)] at tr
  have replay : u=run WindowParityCaller.divideNC r (pullState Stair44PointMap.integerFirst.symm (run F [] (run P [] s))) := by
    change run (H++WindowParityCaller.divideNC) m _=_
    rw [run_append]
    exact congrArg (run WindowParityCaller.divideNC r) tr
  rw [replay]
  exact ans

end ECDSAAdd.Entrant.StairPacket.WindowPointDivision

end

-- ==== end: division ====

section






end
end
-- ==== end Main ====

end
-- ==== end MainTail ====

-- ==== begin: outer chain ====
section

namespace ECDSAAdd.Entrant.OddOuterBridge
open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open ControlledPointLayout CompressedPointDialog CompressedAllocation CompressedFieldSupport
open DirectSkywalk EntryFuse EntryFuseFinite ExitFusionResearch
open ParityUniform FlagEntry FlagExit ParityEven ParityXEntry Stair44PointMap
open EntryFuseOdd
open MappedCompressed.LaneA FrontierEntry1591Callers StairSemanticFinal
open ParityXExitInverse23Kernel
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots GatePhysical

/-- `wordTransferOdd` for a kernel that reads its numerator in odd-word form: the physical input `t`
agrees with the canonical source `s` off `L.point.y` and holds `oddWord (Y / 2)` there. -/
theorem wordTransferOddNC (L : ControlledPointLayout) (f : Wire → Wire) (k : Nat)
    (domain : Finset Wire)
    (injective : ∀ a ∈ domain, ∀ b ∈ domain, f a = f b → a = b)
    (divisorMap : (wireBlock base 770 256).map f = L.point.x)
    (numeratorMap : (wireBlock base 2056 256).map f = L.point.y)
    (controlMap : f (base 2400) = L.core.generic)
    (sharedWork : ∀ q ∈ skywalkSharedWires base, q ∈ domain → q ∉ wireBlock base 770 256 →
      q ∉ wireBlock base 2056 256 → f q ∈ L.dialogPool)
    (selectorG : f (base 2409) ∈ L.dialogPool)
    (selectorS : f (base 2410) ∈ L.dialogPool)
    (dxSites : (wireBlock base 770 256).toFinset ⊆ domain)
    (dySites : (wireBlock base 2056 256).toFinset ⊆ domain)
    (gSite : base 2400 ∈ domain) (pkD : pkP ∈ domain)
    (X : Nat) (Y : Fp)
    (s t : State) (m : List Bool)
    (hX : regValue L.point.x s.basis = X) (hY : regValue L.point.y s.basis = Y.val)
    (clean : regValue L.dialogPool s.basis = 0)
    (phase : t.phase = s.phase) (same : ∀ q, q ∉ L.point.y → t.basis q = s.basis q)
    (half : regValue L.point.y t.basis = oddWord (Y / 2))
    (PN PO : Program) (supN : wires PN ⊆ domain) (supO : wires PO ⊆ domain)
    (P_spec : ∀ (a b : State) (records : List Bool),
      SkywalkArithmeticInput base X Y.val a.basis →
      a.basis (base 2409) = false → a.basis (base 2410) = false →
      b.phase = a.phase → (∀ q, q ∉ wireBlock base 2056 256 → b.basis q = a.basis q) →
      regValue (wireBlock base 2056 256) b.basis = oddWord (Y / 2) →
      let out := run PN records b
      let ref := put (run PO records a) pkP (a.basis (base 2400) && decide (k < X))
      out.phase = ref.phase ∧
        regValue (wireBlock base 2056 256) out.basis = oddWord (Y * (X : Fp) / 2) ∧
        ∀ q, q ∉ wireBlock base 2056 256 → out.basis q = ref.basis q) :
    let out := run (renameProgram f PN) m t
    let ref := put (run (renameProgram f PO) m s) (f pkP) (s.basis L.core.generic && decide (k < X))
    out.phase = ref.phase ∧
      regValue L.point.y out.basis = oddWord (Y * (X : Fp) / 2) ∧
      ∀ q, q ∉ L.point.y → out.basis q = ref.basis q := by
  let a := ECDSAAdd.Entrant.selInput domain f s
  let b := ECDSAAdd.Entrant.selInput domain f t
  have aBits (q : Wire) (hq : q ∈ domain) : a.basis q = s.basis (f q) := by
    simp only [a, ECDSAAdd.Entrant.selInput, if_pos hq]
  have bBits (q : Wire) (hq : q ∈ domain) : b.basis q = t.basis (f q) := by
    simp only [b, ECDSAAdd.Entrant.selInput, if_pos hq]
  have zero (q : Wire) (hq : f q ∈ L.dialogPool) : a.basis q = false := by
    change (if q ∈ domain then s.basis (f q) else false) = false
    split
    · exact (regValue_zero _ _).mp clean _ hq
    · rfl
  have input : SkywalkArithmeticInput base X Y.val a.basis := by
    refine ⟨?_, ?_, ?_⟩
    · change regValue (wireBlock base 770 256) a.basis = X
      rw [ECDSAAdd.Entrant.selRegMap f _ a.basis s.basis
        (fun q hq => aBits q (dxSites (List.mem_toFinset.mpr hq))), divisorMap]
      exact hX
    · change regValue (wireBlock base 2056 256) a.basis = Y.val
      rw [ECDSAAdd.Entrant.selRegMap f _ a.basis s.basis
        (fun q hq => aBits q (dySites (List.mem_toFinset.mpr hq))), numeratorMap]
      exact hY
    · intro q hq hdx hdy
      by_cases used : q ∈ domain
      · exact zero q (sharedWork q hq used hdx hdy)
      · simp only [a, ECDSAAdd.Entrant.selInput, if_neg used]
  have outside (q : Wire) (hq : q ∈ domain) (haway : q ∉ wireBlock base 2056 256) : f q ∉ L.point.y := by
    rw [← numeratorMap]
    intro bad
    obtain ⟨r, hr, he⟩ := List.mem_map.mp bad
    have eq : q = r := injective q hq r (dySites (List.mem_toFinset.mpr hr)) he.symm
    exact haway (eq ▸ hr)
  have paired : ∀ q, q ∉ wireBlock base 2056 256 → b.basis q = a.basis q := by
    intro q hq
    by_cases used : q ∈ domain
    · rw [bBits q used, aBits q used]
      exact same (f q) (outside q used hq)
    · simp only [a, b, ECDSAAdd.Entrant.selInput, if_neg used]
  have halfLogical : regValue (wireBlock base 2056 256) b.basis = oddWord (Y / 2) := by
    rw [ECDSAAdd.Entrant.selRegMap f _ b.basis t.basis
      (fun q hq => bBits q (dySites (List.mem_toFinset.mpr hq))), numeratorMap]
    exact half
  have pw := P_spec a b m input (zero _ selectorG) (zero _ selectorS) phase paired halfLogical
  have trN := run_rename_pool f domain injective PN supN m b t rfl bBits
  have trO := run_rename_pool f domain injective PO supO m a s rfl aBits
  have tg : a.basis (base 2400) = s.basis L.core.generic := by rw [aBits _ gSite, controlMap]
  dsimp only at pw ⊢
  rw [tg] at pw
  refine ⟨trN.1.trans (pw.1.trans trO.1.symm), ?_, ?_⟩
  · rw [← numeratorMap]
    exact (ECDSAAdd.Entrant.selRegMap f _ (run PN m b).basis (run (renameProgram f PN) m t).basis
      (fun q hq => (trN.2 q (dySites (List.mem_toFinset.mpr hq))).symm)).symm.trans pw.2.1
  · intro q hq
    by_cases image : q ∈ domain.image f
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp image
      have away : r ∉ wireBlock base 2056 256 := by
        intro mem
        apply hq
        rw [← numeratorMap]
        exact List.mem_map.mpr ⟨r, mem, rfl⟩
      rw [trN.2 r hr, pw.2.2 r away]
      by_cases e : r = pkP
      · subst e; simp [put, writeBit]
      · have ne : f r ≠ f pkP := fun h => e (injective r hr pkP pkD h)
        simp only [put, writeBit, Function.update_apply, if_neg e, if_neg ne]
        exact (trO.2 r hr).symm
    · have ne : q ≠ f pkP := fun h => image (h ▸ Finset.mem_image_of_mem _ pkD)
      rw [run_rename_pool_outside f domain PN supN m t q image]
      simp only [put, writeBit, Function.update_apply, if_neg ne]
      rw [run_rename_pool_outside f domain PO supO m s q image]
      exact same q hq
end ECDSAAdd.Entrant.OddOuterBridge

namespace ECDSAAdd.Entrant.StairPacket.WindowPointWord
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 Rolling1588Lifetime BalancedField
  ControlledPointLayout CompressedPointDialog ParityEven ParityXExitInverse23Kernel StairSemanticFinal
  Stair44Kernel Stair44PointMap Baselines StairConcreteAssembly
set_option maxRecDepth 18000
set_option maxHeartbeats 2500000
attribute [local irreducible] run wires measurementCount

def normalizedNC (k : Nat) := renameProgram outMap.symm (WindowKernelPrograms.multiplicationNC k)

theorem normSupportNC (mulSites : ∀ k, wires (WindowKernelPrograms.multiplicationNC k) ⊆ callerDomain) (k : Nat) :
    wires (normalizedNC k) ⊆ callerDomain :=
  rename_caller outMap.symm keep (WindowKernelPrograms.multiplicationNC k) (mulSites k)

theorem fullWordNC (mulSites : ∀ k, wires (WindowKernelPrograms.multiplicationNC k) ⊆ callerDomain)
    (exit : ∀ k, k < p → SqOddContract.ExitMatchesOddNC (normalizedNC k) k)
    (k X : Nat) (Y : Fp) (hk : k<p) (hp : 0<X) (hx : X<p) (s t : State) (m : List Bool)
    (sx : regValue layout.point.x s.basis=X) (sy : regValue layout.point.y s.basis=Y.val)
    (sc : regValue layout.dialogPool s.basis=0)
    (phase : t.phase = s.phase) (same : ∀ q, q ∉ layout.point.y → t.basis q = s.basis q)
    (half : regValue layout.point.y t.basis = EntryFuseOdd.oddWord (Y / 2)) :
    let C := FrontierEntry1591Callers.exit (WindowKernelPrograms.multiplicationNC k) layout
    let out := pullState outer (run C m t)
    let ref := put (run (FrontierEntry1591Callers.exit (kernelX k) layout) m s)
      (wireFn2 layout pkP) (s.basis layout.core.generic && decide (k<X))
    out.phase = ref.phase ∧ regValue layout.point.y out.basis = EntryFuseOdd.oddWord (Y * (X:Fp) / 2) ∧
      ∀ q, q ∉ layout.point.y → out.basis q = ref.basis q := by
  intro C
  rcases placement2 layout layout_widths layout_nodup with ⟨_,dx,dy,g,_,sg,ss,_⟩
  have pk : pkP∈callerDomain := by
    have a := E1QubitPlacement.sw_logical 724 (by unfold E1QubitPlacement.Rng; omega)
    exact logical_sub_caller (by simpa [E1QubitPlacement.sw,pkP] using a)
  have config := MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj; simp [base]
  have W := OddOuterBridge.wordTransferOddNC layout (wireFn2 layout) k callerDomain
    (wireFn2_injOn_caller layout layout_widths layout_nodup) dx dy g (sharedWork_caller layout layout_widths)
    sg ss divisor_caller numerator_caller generic_caller pk X Y s t m sx sy sc phase same half
    (normalizedNC k) (kernelX k) (normSupportNC mulSites k) ((kernelX_support k).trans logical_sub_caller)
    (fun a b records input hg hs hph hsame hval =>
      exit k hk config.1 above config.2.1 config.2.2 X Y hp hx a b records input hg hs hph hsame hval)
  have place : renameProgram (wireFn2 layout) (normalizedNC k)=renameProgram outer.symm C :=
    transport (wireFn2 layout) outMap.symm outer.symm (WindowKernelPrograms.multiplicationNC k) physInv
  have tc : regValue layout.dialogPool t.basis = 0 :=
    (regValue_congr _ _ _ (fun q hq => same q
      ((E1QubitPlacement.lay layout layout_widths layout_nodup q).2.1 hq).2)).trans sc
  have o : pullState outer.symm t=t := by
    have members : ∀ab∈earlyPairs,ab.1∈layout.dialogPool ∧ ab.2∈layout.dialogPool := by decide +kernel
    have f : pullState outer t=t := (clean_chain earlyPairs id t t (fun ab h =>
      ⟨(regValue_zero _ _).mp tc _ (members ab h).1,(regValue_zero _ _).mp tc _ (members ab h).2⟩)).mpr rfl
    have u := congrArg (pullState outer.symm) f
    rw [Stair44PlacedHead.unpull] at u; exact u.symm
  rw [place] at W
  have e := run_rename outer.symm outer.symm.injective C m t
  rw [o] at e
  have e2 := congrArg (pullState outer) (e.symm)
  have unp : ∀ st, pullState outer (pullState outer.symm st) = st := fun st =>
    State.extensionality _ _ rfl (funext fun q => by
      change st.basis (outer.symm (outer q)) = st.basis q
      rw [outer.symm_apply_apply])
  rw [unp] at e2
  simpa only [← e2] using W
end ECDSAAdd.Entrant.StairPacket.WindowPointWord

namespace ECDSAAdd.Entrant.StairPacket.WindowPointSecond
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic
  Stair44PointMap Stair44PlacedHead
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount fastConstAdd renameProgram wires
open Stair44PointSecond StairSemanticFinal

/-- Runs of a program that avoids register `r` on two states that agree off `r` agree off `r`. -/
theorem agreeOff_run (r : List Wire) (P : Program) (hP : ∀ q ∈ wires P, q ∉ r) {a b : State}
    (hph : a.phase = b.phase) (h : ∀ q, q ∉ r → a.basis q = b.basis q) (m : List Bool) :
    (run P m a).phase = (run P m b).phase ∧ ∀ q, q ∉ r → (run P m a).basis q = (run P m b).basis q := by
  have inc := Arithmetic.run_local_increment P a b m (fun q hq => h q (hP q hq))
  have hp : (run P m a).phase = (run P m b).phase := by
    have h1 := inc.1; rw [hph] at h1
    revert h1
    generalize (run P m a).phase = x
    generalize (run P m b).phase = y
    generalize b.phase = z
    cases x <;> cases y <;> cases z <;> decide
  refine ⟨hp, fun q hq => ?_⟩
  by_cases hp' : q ∈ wires P
  · exact inc.2 q hp'
  · rw [run_preserves_outside P m a q hp', run_preserves_outside P m b q hp']
    exact h q hq

theorem walkFirst_fix_numerator : ∀ q ∈ wireBlock base 2056 256, Stair44WalkMap.first q = q := by
  have h : (wireBlock base 2056 256).all (fun q => decide (Stair44WalkMap.first q = q)) = true := by decide +kernel
  intro q hq; exact of_decide_eq_true (List.all_eq_true.mp h q hq)

theorem phaseHost_fix_numerator : ∀ q ∈ wireBlock base 2056 256, Rolling1588Lifetime.phaseHost q = q :=
  OddStockLockstep.phaseHost_fix_fieldR

private theorem perm_away (e : Equiv.Perm Wire) (fix : ∀ q ∈ wireBlock base 2056 256, e q = q)
    (r : Wire) (hr : r ∉ wireBlock base 2056 256) : e r ∉ wireBlock base 2056 256 := by
  intro h
  have h2 := fix _ h
  rw [e.injective h2] at h
  exact hr h

/-- The placed first tick never touches `layout.point.y`. -/
theorem tick_notY (mulSites : wires (WindowKernelPrograms.multiplication 0) ⊆ callerDomain) :
    ∀ q ∈ wires Stair44Splits.tick, q ∉ layout.point.y := by
  intro q hq hy
  have hq' : q ∈ wires (renameProgram (wireFn2 layout)
      (renameProgram Rolling1588Lifetime.phaseHost Stair44Kernel.firstR)) := by
    rw [← Stair44Splits.tick_eq] at hq; exact hq
  rw [renameProgram_support] at hq'
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq'
  have hdom : r ∈ callerDomain := by
    apply mulSites
    simp only [WindowKernelPrograms.multiplication, WindowKernelPrograms.mulBefore, WindowKernelPrograms.openWalk,
      Six505.rename_append, wires_append, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hr))))
  have hnum : r ∉ wireBlock base 2056 256 := by
    rw [renameProgram_support] at hr
    obtain ⟨r1, hr1, rfl⟩ := Finset.mem_image.mp hr
    rw [Stair44Kernel.firstR, renameProgram_support] at hr1
    obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.mp hr1
    have hpool : r0 ∈ skywalkPoolWires base := by
      apply List.mem_toFinset.mp
      apply ParityXExitInverse23Kernel.first_pool false
      simp only [Rolling1588.firstPhase, wires_append, Finset.mem_union]
      exact Or.inl (Or.inl hr0)
    exact perm_away _ phaseHost_fix_numerator _
      (perm_away _ walkFirst_fix_numerator _ (FrontierEntry1591Kernel.pool_away_numerator r0 hpool))
  rcases placement2 layout layout_widths layout_nodup with ⟨_, _, dy, _⟩
  rw [← dy] at hy
  obtain ⟨n, hn, he⟩ := List.mem_map.mp hy
  have := wireFn2_injOn_caller layout layout_widths layout_nodup n (numerator_caller (List.mem_toFinset.mpr hn)) r hdom he
  exact hnum (this ▸ hn)


theorem productCutNC (mulSites0 : wires (WindowKernelPrograms.multiplication 0) ⊆ callerDomain)
    (mulSites : ∀ k, wires (WindowKernelPrograms.multiplicationNC k) ⊆ callerDomain)
    (exit : ∀ k, k < p → SqOddContract.ExitMatchesOddNC (WindowPointWord.normalizedNC k) k)
    (cx X Y : Fp) (G : Bool) (origin : BasisState) (w v v' : State) (rm : List Bool)
    (values : PointDialogValues layout X Y G origin w.basis) (hp : 0<X.val)
    (eq : v=pullState integerFirst.symm (run (E1QubitPlacement.tickF layout) [] w))
    (hph : v'.phase = v.phase) (hout : ∀ q, q ∉ layout.point.y → v'.basis q = v.basis q)
    (hy : regValue layout.point.y v'.basis = EntryFuseOdd.oddWord (Y / 2)) :
    let F := E1QubitPlacement.tickF layout
    let d := pfx (measurementCount F) [] ++ rm
    let a := run (FrontierEntry1591Callers.exit (kernelX cx.val) layout) d w
    let out := pullState outer (run (WindowParityCaller.multiplyNC cx.val) rm v')
    out.phase = a.phase ∧ regValue layout.point.y out.basis = EntryFuseOdd.oddWord (Y * X / 2) ∧
      ∀ q, q ∉ layout.point.y → out.basis q = (put a (pkW layout) (G && decide (cx.val < X.val))).basis q := by
  intro F d a out
  let w' : State := ⟨w.phase, fun q => if q ∈ layout.point.y then v'.basis q else w.basis q⟩
  have w'same : ∀ q, q ∉ layout.point.y → w'.basis q = w.basis q := by
    intro q hq; simp only [w', if_neg hq]
  have w'y : regValue layout.point.y w'.basis = EntryFuseOdd.oddWord (Y / 2) :=
    (regValue_congr _ _ v'.basis (fun q hq => by simp only [w', if_pos hq])).trans hy
  have ww := WindowPointWord.fullWordNC mulSites exit cx.val X.val Y cx.isLt hp X.isLt w w' d
    values.x values.y values.clean rfl w'same w'y
  have dt : d = pfx (measurementCount Stair44Splits.tick) [] ++ rm :=
    congrArg (fun z => pfx z [] ++ rm) (renameProgram_counts _ _).2.symm
  have tickv : run Stair44Splits.tick [] w = v := by
    rw [show Stair44Splits.tick = renameProgram integerFirst F from rfl, eq]
    exact encodedTick w [] values.clean
  have tickv' : run Stair44Splits.tick [] w' = v' := by
    have ag := agreeOff_run layout.point.y Stair44Splits.tick (tick_notY mulSites0) (a := w') (b := w) rfl w'same []
    apply State.extensionality
    · rw [ag.1, tickv]; exact hph.symm
    · funext q
      by_cases hq : q ∈ layout.point.y
      · rw [run_preserves_outside _ [] w' q (fun hw => tick_notY mulSites0 q hw hq)]
        simp only [w', if_pos hq]
      · rw [ag.2 q hq, tickv, hout q hq]
  have hrun : run (FrontierEntry1591Callers.exit (WindowKernelPrograms.multiplicationNC cx.val) layout) d w' =
      run (WindowParityCaller.multiplyNC cx.val) rm v' := by
    rw [WindowKernelPrograms.mul_splitNC, dt, run_pre, tickv']
  have hX : ((X.val : Nat) : Fp) = X := ZMod.natCast_zmod_val X
  have hput_ph : ∀ (st : State) (q : Wire) (b : Bool), (put st q b).phase = st.phase := fun _ _ _ => rfl
  rcases ww with ⟨h1, h2, h3⟩
  have ha_eq : a = run (FrontierEntry1591Callers.exit (kernelX cx.val) layout) d w := rfl
  have hout_eq : out = pullState outer (run (WindowParityCaller.multiplyNC cx.val) rm v') := rfl
  rw [hrun, hput_ph, ← ha_eq, ← hout_eq] at h1
  rw [hrun, hX, ← hout_eq] at h2
  rw [hrun, values.generic, pk_wire, ← ha_eq, ← hout_eq] at h3
  exact ⟨h1, h2, h3⟩
end ECDSAAdd.Entrant.StairPacket.WindowPointSecond

namespace ECDSAAdd.Entrant.StairPacket.WindowPointSecond
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic
  Stair44PointMap Stair44PlacedHead
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount fastConstAdd
open Stair44PointSecond StairSemanticFinal

def secondNC (P : Program) (cy cx : Fp) := P ++ WindowParityCaller.multiplyNC cx.val ++
  encodeY (EntryFuseOdd.exitYAllOdd layout cy)

theorem actualNC (mulSites0 : wires (WindowKernelPrograms.multiplication 0) ⊆ callerDomain)
    (mulSites : ∀ k, wires (WindowKernelPrograms.multiplicationNC k) ⊆ callerDomain)
    (exit : ∀ k, k < p → SqOddContract.ExitMatchesOddNC (WindowPointWord.normalizedNC k) k)
    (P : Program) (k : Fp) (sq : SqOddContract.SquareOddNC P k)
    (cy cx X Y : Fp) (G : Bool) (origin : BasisState) (s s' : State)
    (v : PointDialogValues layout X Y G origin s.basis)
    (hph : s'.phase = s.phase) (hout : ∀ q, q ∉ layout.point.y → s'.basis q = s.basis q)
    (hy : regValue layout.point.y s'.basis = EntryFuseOdd.oddWord (Y / 2))
    (hx : X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)+(if G then k else 0)≠0)
    (m : List Bool) : ∃ n,run (secondNC P cy cx) m s'=pullState outer.symm (run (secondStageN layout k cy cx) n s) := by
  let square := Stair44Square.program k
  let mul := WindowParityCaller.multiplyNC cx.val
  let A := SquareCarryLoan719BF.program layout ++ fastConstAdd layout layout.point.x k
  let Z := X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)
  let X' := Z+(if G then k else 0)
  obtain ⟨w,ew⟩ : ∃z : State, run A [] s=z := ⟨_,rfl⟩
  let F := E1QubitPlacement.tickF layout
  let u := run F [] w
  let sm := m.take (measurementCount P)
  let tail := m.drop (measurementCount P)
  let rm := tail.take (measurementCount mul)
  let ym := tail.drop (measurementCount mul)
  let d := pfx (measurementCount F) [] ++ rm
  obtain ⟨plainOut,ep⟩ : ∃z : State,run (FrontierEntry1591Callers.exit (kernelX cx.val) layout) d w=z := ⟨_,rfl⟩
  let flag := G && decide (cx.val<X'.val)
  let oldSq := squareEntry layout k
  let oldMul := restXXN layout cx.val
  have sqA := SquareCarryLoan719BF.step layout layout_widths layout_nodup X Y G origin
  have add := fastStep_addX layout layout_widths layout_nodup Z Y G origin k
  have vw : PointDialogValues layout X' Y G origin w.basis := by
    rw [←ew];exact ((sqA.seq add) s [] v).2
  have hp : 0<X'.val := Nat.pos_of_ne_zero (fun eq => hx ((ZMod.val_eq_zero X').mp eq))
  have core : run oldSq [] s=u := stockCut k X Y G origin s w v ew
  have realSquare : run square sm s=pullState integerFirst.symm u := squareCut k X Y G origin s w sm v ew X'.val vw.x X'.isLt vw.clean
  have sqo := sq X Y G origin s s' sm v hph hout hy
  have nw : (pullState outer (run mul rm (run P sm s'))).phase = plainOut.phase ∧
      regValue layout.point.y (pullState outer (run mul rm (run P sm s'))).basis = EntryFuseOdd.oddWord (Y * X' / 2) ∧
      ∀ q, q ∉ layout.point.y → (pullState outer (run mul rm (run P sm s'))).basis q = (put plainOut (pkW layout) flag).basis q := by
    rw [←ep]
    exact productCutNC mulSites0 mulSites exit cx X' Y G origin w (run square sm s) (run P sm s') rm vw hp realSquare
      sqo.1 sqo.2.2 sqo.2.1
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
  let actual := run mul rm (run P sm s')
  have final := OddOuterBridge.pointSecond_rejoin_odd ((Y*X')/2) cy plainOut actual ym flag oy oc nw.1 nw.2.1 nw.2.2
  refine ⟨pfx (measurementCount oldSq) [] ++ (pfx (measurementCount oldMul) rm ++ ym),?_⟩
  change run ((P++mul)++_) m s'=pullState outer.symm (run ((oldSq++oldMul)++_) _ s)
  rw [tripleRun P mul,chosenRun oldSq oldMul,stock]
  exact final
end ECDSAAdd.Entrant.StairPacket.WindowPointSecond

namespace ECDSAAdd.Entrant.StairPacket.WindowReleaseProof
open Arithmetic MappedCompressed Secp256k1 StairSemanticFinal StairConcreteAssembly Rolling1588Lifetime
set_option maxRecDepth 17000
set_option maxHeartbeats 3500000
attribute [local irreducible] wires renameProgram

private theorem rename_wires_mono (f : Wire → Wire) {P Q : Program} (h : wires P ⊆ wires Q) :
    wires (renameProgram f P) ⊆ wires (renameProgram f Q) := by
  rw [renameProgram_support, renameProgram_support]
  exact Finset.image_subset_image h

theorem exitFieldHostedNC_sub :
    wires (WindowParityCaller.exitFieldHostedNC checkpointPrimitives) ⊆
      wires (WindowParityCaller.exitFieldHosted checkpointPrimitives) := by
  have hHead : wires (WindowParityCaller.exitHeadPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ⊆
      wires (OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    have e : OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542 =
        OddFullPass.HalfConvertOdd.center760OddLoan ++
          WindowParityCaller.exitHeadPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542 := by
      simp only [OddFullPass.P1LifeLoan.exitHeadPrefixOdd, WindowParityCaller.exitHeadPrefixOddNC, List.append_assoc]
    rw [e, wires_append]
    exact Finset.subset_union_right
  have hLow : wires (WindowParityCaller.exitLowPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ⊆
      wires (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    simp only [WindowParityCaller.exitLowPrefixOddNC, OddFullPass.P1LifeLoan.exitLowPrefixOdd, wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
      (rename_wires_mono _ hHead)) (Finset.Subset.refl _)
  have hF : wires (StairSchedule.fieldRename (WindowParityCaller.exitLowPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542)) ⊆
      wires (StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542)) := by
    rw [StairField13V3.fieldRename_eq, StairField13V3.fieldRename_eq]
    exact rename_wires_mono _ hLow
  simp only [WindowParityCaller.exitFieldHostedNC, WindowParityCaller.exitFieldHosted, wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) hF) (Finset.Subset.refl _)) (Finset.Subset.refl _))
    (Finset.Subset.refl _)

theorem multiplicationNC_sites (k : Nat) : wires (WindowKernelPrograms.multiplicationNC k) ⊆ callerDomain := by
  refine Finset.Subset.trans ?_ (multiplication k ExteriorCaller.exitFieldHosted_corrected)
  simp only [WindowKernelPrograms.multiplicationNC, WindowKernelPrograms.multiplication,
    WindowKernelPrograms.mulBeforeNC, WindowKernelPrograms.mulBefore, wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _)
    exitFieldHostedNC_sub) (Finset.Subset.refl _)) (Finset.Subset.refl _)
end ECDSAAdd.Entrant.StairPacket.WindowReleaseProof

namespace ECDSAAdd.Entrant.StairPacket.WindowGeneric
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines ControlledPointLayout
  CompressedPointDialog CompressedAllocation CompressedFieldSupport EntryFuse EntryFuseFinite FlagEntry FlagExit
  DirectSkywalk ParityUniform ParityEven ParityXExitInverse23Kernel ParityStageBothInverse23 A161Generic
  Stair44PointMap Stair44PlacedHead
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000
attribute [local irreducible] run measurementCount
open StairSemanticFinal

/-- Kernel and square contracts of the circuit without the two field converters. -/
structure ContractsNC : Prop where
  mulSites0 : wires (WindowKernelPrograms.multiplication 0) ⊆ callerDomain
  mulSites : ∀ k, wires (WindowKernelPrograms.multiplicationNC k) ⊆ callerDomain
  enter : SqOddContract.EntryCorrectOddNC WindowKernelPrograms.divisionNC
  exit : ∀ k, k < p → SqOddContract.ExitMatchesOddNC
    (renameProgram Stair44Kernel.outMap.symm (WindowKernelPrograms.multiplicationNC k)) k
  square : ∀ k, SqOddContract.SquareOddNC (WindowParityCaller.squareNC k) k

theorem generic_eqDNC (K : ContractsNC) (cx cy X Y : Fp) (G : Bool) (s : State) (e : Bool)
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
  let H := WindowPointDivision.partNC cx cy
  let H0 := (entryYAll layout (-cy) ++ entryXNew layout (pkW layout) (-cx)) ++ restEntry layout
  let flag := if s.basis layout.core.generic then decide (EntryFuseArithmetic.prime ≤ X.val+(-cx).val) else false
  let s0 := put s (pkW layout) flag
  let s1 := run H0 [] s0
  have hv0 := entryStageAll_step layout layout_widths layout_nodup X Y (-cx) (-cy) G s.basis hx1
    s (padE layout cy cx []) hv
  rw [←(head_pad layout layout_widths layout_nodup cx cy X Y s hv.x hv.y hv.clean hg).run_eq []] at hv0
  have hv1 := WindowPointDivision.stageNC K.enter cx cy X Y G s (m.take (measurementCount H)) hv hx1
  have ag := SqOddContract.agree_of_valuesOdd hv1 hv0
  obtain ⟨n,hn⟩ := WindowPointSecond.actualNC K.mulSites0 K.mulSites K.exit
    (WindowParityCaller.squareNC (ReflectionE1.correction cx)) (ReflectionE1.correction cx) (K.square _)
    cy cx _ _ G s.basis s1 _ hv0.2 ag.1 ag.2.1 ag.2.2 hx2 (m.drop (measurementCount H))
  refine ⟨pfx (measurementCount H0) []++n,?_⟩
  have structureEq : WindowParityCaller.generic cx cy=H++WindowPointSecond.secondNC
      (WindowParityCaller.squareNC (ReflectionE1.correction cx)) cy cx := by
    simp only [H,WindowPointDivision.partNC,WindowPointSecond.secondNC,WindowParityCaller.generic,WindowParityCaller.genericNC,
      Stair44PlacedHead.routed,OddOuterBridge.routedOdd,List.append_assoc]
  rw [structureEq,run_append,genericN,run_pre]
  exact hn

theorem certificateNC (K : ContractsNC) :
    Challenge.Certificate WindowParityRelease.entryNC WindowParityRelease.boundsNC :=
  WindowPointCertificate.certificate (generic_eqDNC K)
end ECDSAAdd.Entrant.StairPacket.WindowGeneric

end
-- ==== end: outer chain ====

section

namespace ECDSAAdd.Entrant

def entry : Challenge.Entry := StairPacket.WindowParityRelease.entryNC
def bounds : Challenge.Bounds := StairPacket.WindowParityRelease.boundsNC
theorem certificate : Challenge.Certificate entry bounds :=
  StairPacket.WindowGeneric.certificateNC
    ⟨StairPacket.WindowReleaseProof.multiplication 0 StairPacket.ExteriorCaller.exitFieldHosted_corrected,
     StairPacket.WindowReleaseProof.multiplicationNC_sites,
     StairPacket.WindowKernelReplay.division_oddNC StairPacket.ExteriorDivReady.entryOddNC,
     StairPacket.WindowKernelReplay.multiplication_oddNC StairPacket.WindowExitReady.exitOddNC,
     StairPacket.WindowParityCaller.squareNC_correct⟩

end ECDSAAdd.Entrant

end
