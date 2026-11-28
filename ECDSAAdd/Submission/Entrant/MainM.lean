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

section

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed



section

namespace ECDSAAdd.Arithmetic.BoundaryCommute

/-- Basis write targets. Corrections read wires and change phase. -/
def basisWrites : Program → Finset Wire
  | [] => ∅
  | .X t :: p | .CX _ t :: p | .CCX _ _ t :: p
  | .measureX t _ _ :: p => insert t (basisWrites p)

theorem run_preserves_outside_basisWrites (p : Program) (m : List Bool)
    (s : State) (a : Wire) (outside : a ∉ basisWrites p) :
    (run p m s).basis a = s.basis a := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [basisWrites, Finset.mem_insert, not_or] at outside
    all_goals rw [run, ih _ _ outside.2]
    case measureX =>
      simp only [measureAndCorrect, correct_basis, writeBit, Function.update_of_ne outside.1]
    all_goals simp only [writeBit, Function.update_of_ne outside.1]

/-- Commute two blocks that preserve each other's read wires. Each block keeps
its own measurement records, including records used by phase corrections. -/
theorem run_commute_of_read_only (p q : Program) (mp mq : List Bool) (s : State)
    (pRead : ∀ u a, a ∈ wires p → (run q mq u).basis a = u.basis a)
    (qRead : ∀ u a, a ∈ wires q → (run p mp u).basis a = u.basis a) :
    run p mp (run q mq s) = run q mq (run p mp s) := by
  have hp := run_local_increment p (run q mq s) s mp (pRead s)
  have hq := run_local_increment q (run p mp s) s mq (qRead s)
  apply State.extensionality
  · have phase (a b c d e : Bool) (h1 : (a ^^ b) = (c ^^ d))
        (h2 : (e ^^ c) = (b ^^ d)) : a = e := by
      cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all
    exact phase _ _ _ _ _ hp.1 hq.1
  · funext a
    by_cases ha : a ∈ wires p
    · exact (hp.2 a ha).trans (pRead (run p mp s) a ha).symm
    · rw [run_preserves_outside p mp (run q mq s) a ha]
      by_cases hb : a ∈ wires q
      · exact (hq.2 a hb).symm
      · rw [run_preserves_outside q mq (run p mp s) a hb,
          run_preserves_outside q mq s a hb,
          run_preserves_outside p mp s a ha]

/-- Move the record-free exchange past the measured block on the same tape. -/
theorem run_append_commute_zero (p q : Program) (tape : List Bool) (s : State)
    (zero : measurementCount p = 0)
    (pRead : ∀ u a, a ∈ wires p → (run q tape u).basis a = u.basis a)
    (qRead : ∀ u a, a ∈ wires q → (run p [] u).basis a = u.basis a) :
    run (p ++ q) tape s = run (q ++ p) tape s := by
  calc
    run (p ++ q) tape s = run q tape (run p [] s) := by
      rw [run_append, zero, List.take_zero, List.drop_zero]
    _ = run p [] (run q tape s) := (run_commute_of_read_only p q [] tape s pRead qRead).symm
    _ = run (q ++ p) tape s := by
      rw [run_append, run_take]
      simpa only [zero, List.take_zero] using
        run_take p (tape.drop (measurementCount q)) (run q tape s)

theorem run_append_commute_of_writes (p q : Program) (tape : List Bool) (s : State)
    (zero : measurementCount p = 0)
    (pRead : Disjoint (wires p) (basisWrites q))
    (qRead : Disjoint (wires q) (basisWrites p)) :
    run (p ++ q) tape s = run (q ++ p) tape s :=
  run_append_commute_zero p q tape s zero
    (fun u a ha => run_preserves_outside_basisWrites q tape u a
      (fun h => Finset.disjoint_left.mp pRead ha h))
    (fun u a ha => run_preserves_outside_basisWrites p [] u a
      (fun h => Finset.disjoint_left.mp qRead ha h))

end ECDSAAdd.Arithmetic.BoundaryCommute

namespace ECDSAAdd.Entrant.StairPacket.Shadow20.MergeCut
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
open ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket ECDSAAdd.Entrant.StairPacket.Shadow20

set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

/-! ### Local programs

Wires `0..8` stand for: `0` the enter's swap control (`s+15`), `1` the first routed tick's route
control (`a0`), `2,3` and `4,5` the two top rail pairs the enter exchanges, `6` the enter's parity
cell and `7,8` the enter's last exchanged pair. The enter ends with a Fredkin on `(2,3)` and a
controlled move on `(4,5)`, both under `0`; the first tick's route then exchanges the same two pairs
under `1`. Composing the two exchanges is one exchange under `0 ⊕ 1`. -/

def tailF : Program :=
  [.CX 2 3, .CCX 0 3 2, .CX 2 3, .CCX 0 5 4, .CX 4 5, .CX 4 6, .CX 5 6, .CX 7 8, .CX 8 7]
def routeT : Program :=
  [.CX 3 2, .CX 5 4, .CCX 1 2 3, .CCX 1 4 5, .CX 3 2, .CX 5 4]
def newF : Program :=
  [.CX 0 1, .CX 2 3, .CCX 1 3 2, .CX 2 3, .CCX 1 5 4, .CX 4 5, .CX 0 1,
   .CX 4 6, .CX 5 6, .CX 7 8, .CX 8 7]
def tailR : Program :=
  [.CX 8 7, .CX 7 8, .CX 5 6, .CX 4 6, .CX 4 5, .measureX 4 [] [.CZ 0 5],
   .CX 2 3, .CCX 0 3 2, .CX 2 3]
def newR : Program :=
  [.CX 0 1, .CX 8 7, .CX 7 8, .CX 5 6, .CX 4 6, .CX 4 5, .measureX 4 [] [.CZ 1 5],
   .CX 2 3, .CCX 1 3 2, .CX 2 3, .CX 0 1]

def tapes : List (List Bool) := [[], [false], [true]]

theorem fwd_sim : ∀ (x : Fin 512) (ph : Bool),
    MeasuredCodec5.sim newF [] ph x.val = MeasuredCodec5.sim (tailF ++ routeT) [] ph x.val := by
  decide +kernel

theorem rev_sim : ∀ (x : Fin 512) (ph : Bool) (k : Fin 3),
    MeasuredCodec5.sim newR (tapes.getD k.val []) ph x.val =
      MeasuredCodec5.sim (routeT ++ tailR) (tapes.getD k.val []) ph x.val := by
  decide +kernel

theorem mc_newF : measurementCount newF = 0 := by decide
theorem mc_tailF : measurementCount tailF = 0 := by decide
theorem mc_routeT : measurementCount routeT = 0 := by decide
theorem mc_newR : measurementCount newR = 1 := by decide
theorem mc_tailR : measurementCount tailR = 1 := by decide
theorem tc_newF : toffoliCount newF = 2 := by decide
theorem tc_tailF : toffoliCount tailF = 2 := by decide
theorem tc_routeT : toffoliCount routeT = 2 := by decide
theorem tc_newR : toffoliCount newR = 1 := by decide
theorem tc_tailR : toffoliCount tailR = 1 := by decide
theorem gs_F : gateSlots newF ≤ gateSlots tailF + gateSlots routeT := by decide
theorem gs_R : gateSlots newR ≤ gateSlots routeT + gateSlots tailR := by decide
theorem w_newF : wires newF = Finset.range 9 := by decide
theorem w_oldF : wires (tailF ++ routeT) = Finset.range 9 := by decide
theorem w_newR : wires newR = Finset.range 9 := by decide
theorem w_oldR : wires (routeT ++ tailR) = Finset.range 9 := by decide

/-! ### Lifting a local equality to renamed programs -/

theorem packBits_lt : ∀ bs : List Bool, CodecBitSliceVerify.packBits bs < 2 ^ bs.length
  | [] => by simp [CodecBitSliceVerify.packBits]
  | b :: bs => by
    have ih := packBits_lt bs
    simp only [CodecBitSliceVerify.packBits, List.length_cons, pow_succ]
    cases b <;> simp [Nat.bit] <;> omega

def pk (u : State) (f : Wire → Wire) : Nat :=
  CodecBitSliceVerify.packBits ((List.range 9).map fun i => u.basis (f i))

theorem pk_lt (u : State) (f : Wire → Wire) : pk u f < 512 := by
  have h := packBits_lt ((List.range 9).map fun i => u.basis (f i))
  simpa [pk] using h

theorem pk_bit (u : State) (f : Wire → Wire) (i : Nat) (hi : i < 9) :
    (pk u f).testBit i = u.basis (f i) := by
  rw [pk, CodecBitSliceVerify.pack_testBit]
  simp [List.getElem?_map, List.getElem?_range hi]

theorem rename_eq (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (p q : Program) (hp : wires p ⊆ S) (hq : wires q ⊆ S)
    (mp mq : List Bool) (t s : State) (hph : t.phase = s.phase)
    (hb : ∀ a ∈ S, t.basis a = s.basis (f a))
    (heq : run p mp t = run q mq t) :
    run (renameProgram f p) mp s = run (renameProgram f q) mq s := by
  have rp := run_rename_pool f S hf p hp mp t s hph hb
  have rq := run_rename_pool f S hf q hq mq t s hph hb
  have hph_eq : (run (renameProgram f p) mp s).phase = (run (renameProgram f q) mq s).phase := by
    rw [rp.1, rq.1, heq]
  have hb_eq : (run (renameProgram f p) mp s).basis = (run (renameProgram f q) mq s).basis := by
    funext w
    by_cases hw : w ∈ S.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      rw [rp.2 a ha, rq.2 a ha, heq]
    · rw [run_rename_pool_outside f S p hp mp s w hw, run_rename_pool_outside f S q hq mq s w hw]
  cases h1 : run (renameProgram f p) mp s
  cases h2 : run (renameProgram f q) mq s
  rw [h1, h2] at hph_eq hb_eq
  simp only at hph_eq hb_eq
  rw [hph_eq, hb_eq]

def Inj9 (f : Wire → Wire) : Prop := ∀ a b : Fin 9, f a.val = f b.val → a = b

theorem inj9 {f : Wire → Wire} (h : Inj9 f) :
    ∀ a ∈ Finset.range 9, ∀ b ∈ Finset.range 9, f a = f b → a = b := fun a ha b hb e =>
  congrArg Fin.val (h ⟨a, Finset.mem_range.mp ha⟩ ⟨b, Finset.mem_range.mp hb⟩ e)

/-- Run a local program from the `bitsOf` image of the ported bits. -/
theorem local_run (f : Wire → Wire) (u : State) (p q : Program) (mp mq : List Bool)
    (hf : Inj9 f) (hp : wires p ⊆ Finset.range 9) (hq : wires q ⊆ Finset.range 9)
    (hsim : MeasuredCodec5.sim p mp u.phase (pk u f) = MeasuredCodec5.sim q mq u.phase (pk u f)) :
    run (renameProgram f p) mp u = run (renameProgram f q) mq u := by
  let t : State := ⟨u.phase, MeasuredCodec5.bitsOf (pk u f)⟩
  have hreads : ∀ a ∈ Finset.range 9, t.basis a = u.basis (f a) := fun a ha =>
    pk_bit u f a (Finset.mem_range.mp ha)
  have hloc : run p mp t = run q mq t := by
    simp only [t, MeasuredCodec5.run_sim, hsim]
  exact rename_eq f (Finset.range 9) (inj9 hf) p q hp hq mp mq t u rfl hreads hloc

theorem fwd_local (f : Wire → Wire) (hf : Inj9 f) (m : List Bool) (u : State) :
    run (renameProgram f newF) m u = run (renameProgram f (tailF ++ routeT)) m u := by
  have hm1 : measurementCount (renameProgram f newF) = 0 := by
    rw [(renameProgram_counts _ _).2]; exact mc_newF
  have hm2 : measurementCount (renameProgram f (tailF ++ routeT)) = 0 := by
    rw [(renameProgram_counts _ _).2, measurementCount_append, mc_tailF, mc_routeT]
  rw [← run_take _ m u, hm1, ← run_take (renameProgram f (tailF ++ routeT)) m u, hm2, List.take_zero]
  exact local_run f u _ _ [] [] hf w_newF.le w_oldF.le (fwd_sim ⟨pk u f, pk_lt u f⟩ u.phase)

theorem rev_local (f : Wire → Wire) (hf : Inj9 f) (m : List Bool) (u : State) :
    run (renameProgram f newR) m u = run (renameProgram f (routeT ++ tailR)) m u := by
  have hm1 : measurementCount (renameProgram f newR) = 1 := by
    rw [(renameProgram_counts _ _).2]; exact mc_newR
  have hm2 : measurementCount (renameProgram f (routeT ++ tailR)) = 1 := by
    rw [(renameProgram_counts _ _).2, measurementCount_append, mc_routeT, mc_tailR]
  rw [← run_take _ m u, hm1, ← run_take (renameProgram f (routeT ++ tailR)) m u, hm2]
  have hk : ∃ k : Fin 3, m.take 1 = tapes.getD k.val [] := by
    rcases m with _ | ⟨b, m⟩
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · cases b
      · exact ⟨⟨1, by decide⟩, rfl⟩
      · exact ⟨⟨2, by decide⟩, rfl⟩
  obtain ⟨k, hk⟩ := hk
  rw [hk]
  exact local_run f u _ _ _ _ hf w_newR.le w_oldR.le (rev_sim ⟨pk u f, pk_lt u f⟩ u.phase k)

/-! ### Splicing the merged exchange into a block boundary -/

theorem mfa (p q : Program) (hp : measurementCount p = 0) (m : List Bool) (s : State) :
    run (p ++ q) m s = run q m (run p [] s) := by
  rw [run_append, hp, List.take_zero, List.drop_zero]

theorem seg {α : Type} (l : List α) (a k b : Nat) (h : a + k = b) :
    (l.drop a).take k ++ l.drop b = l.drop a := by
  have e := List.take_append_drop k (l.drop a)
  rw [List.drop_drop] at e
  rw [← h]; exact e

theorem comm (p q : Program) (hd : Disjoint (wires p) (wires q)) (s : State) :
    run q [] (run p [] s) = run p [] (run q [] s) :=
  (run_disjoint_commute q p hd.symm [] [] s)

/-- Forward boundary: the enter's last nine gates `Tl` and the first tick's route exchanges `T1,T2,T3`
of the two top pairs fold into `N`. -/
theorem fwd_core (A Tl C1 T1 C2 T2 C3 T3 Rest N : Program)
    (mTl : measurementCount Tl = 0) (mC1 : measurementCount C1 = 0) (mT1 : measurementCount T1 = 0)
    (mC2 : measurementCount C2 = 0) (mT2 : measurementCount T2 = 0) (mC3 : measurementCount C3 = 0)
    (mT3 : measurementCount T3 = 0) (mN : measurementCount N = 0)
    (d1 : Disjoint (wires T1) (wires C2)) (d2 : Disjoint (wires (T1 ++ T2)) (wires C3))
    (d3 : Disjoint (wires Tl) (wires (C1 ++ C2 ++ C3)))
    (loc : ∀ m u, run N m u = run (Tl ++ (T1 ++ T2 ++ T3)) m u) (m : List Bool) (s : State) :
    run (A ++ (C1 ++ C2 ++ C3 ++ N ++ Rest)) m s =
      run ((A ++ Tl) ++ (C1 ++ (T1 ++ (C2 ++ (T2 ++ (C3 ++ (T3 ++ Rest))))))) m s := by
  rw [List.append_assoc A Tl]
  rw [run_append A, run_append A]
  generalize run A (m.take (measurementCount A)) s = t
  generalize m.drop (measurementCount A) = m'
  have m12 : measurementCount (T1 ++ T2) = 0 := by rw [measurementCount_append, mT1, mT2]
  have mT : measurementCount (T1 ++ T2 ++ T3) = 0 := by rw [measurementCount_append, m12, mT3]
  have mC : measurementCount (C1 ++ C2 ++ C3) = 0 := by
    rw [measurementCount_append, measurementCount_append, mC1, mC2, mC3]
  -- left side
  have hl : run (C1 ++ C2 ++ C3 ++ N ++ Rest) m' t = run Rest m' (run N [] (run (C1 ++ C2 ++ C3) [] t)) := by
    rw [mfa _ _ (by rw [measurementCount_append, mC, mN]), mfa _ _ mC]
  -- right side
  have hr : run (Tl ++ (C1 ++ (T1 ++ (C2 ++ (T2 ++ (C3 ++ (T3 ++ Rest))))))) m' t =
      run Rest m' (run T3 [] (run C3 [] (run T2 [] (run C2 [] (run T1 [] (run C1 [] (run Tl [] t))))))) := by
    rw [mfa _ _ mTl, mfa _ _ mC1, mfa _ _ mT1, mfa _ _ mC2, mfa _ _ mT2, mfa _ _ mC3, mfa _ _ mT3]
  rw [hl, hr]
  congr 1
  -- commute T1 past C2
  rw [comm T1 C2 d1]
  -- commute (T1 ++ T2) past C3
  have e2 : run C3 [] (run T2 [] (run T1 [] (run C2 [] (run C1 [] (run Tl [] t))))) =
      run T2 [] (run T1 [] (run C3 [] (run C2 [] (run C1 [] (run Tl [] t))))) := by
    have h := comm (T1 ++ T2) C3 d2 (run C2 [] (run C1 [] (run Tl [] t)))
    rw [mfa _ _ mT1] at h
    rw [h]
    rw [show run T1 [] (run C3 [] (run C2 [] (run C1 [] (run Tl [] t)))) =
        run T1 [] (run C3 [] (run C2 [] (run C1 [] (run Tl [] t)))) from rfl]
    have h2 := mfa T1 (T2 ++ []) mT1 [] (run C3 [] (run C2 [] (run C1 [] (run Tl [] t))))
    simp only [List.append_nil] at h2
    rw [← h2]
  rw [e2]
  -- commute Tl past C1 ++ C2 ++ C3
  have e3 : run C3 [] (run C2 [] (run C1 [] (run Tl [] t))) = run Tl [] (run (C1 ++ C2 ++ C3) [] t) := by
    have h := comm Tl (C1 ++ C2 ++ C3) d3 t
    rw [mfa _ _ (by rw [measurementCount_append, mC1, mC2]), mfa _ _ mC1] at h
    exact h
  rw [e3]
  have e4 : run T3 [] (run T2 [] (run T1 [] (run Tl [] (run (C1 ++ C2 ++ C3) [] t)))) =
      run (Tl ++ (T1 ++ T2 ++ T3)) [] (run (C1 ++ C2 ++ C3) [] t) := by
    rw [mfa _ _ mTl, mfa _ _ m12, mfa _ _ mT1]
  rw [e4, loc]

/-- Reverse boundary: the first untick's route exchanges `T1,T2,T3` and the inverse enter's first nine
gates `Tl` fold into `N`. -/
theorem rev_core (P C1 T1 C2 T2 C3 T3 Tl B N : Program)
    (mC1 : measurementCount C1 = 0) (mT1 : measurementCount T1 = 0)
    (mC2 : measurementCount C2 = 0) (mT2 : measurementCount T2 = 0) (mC3 : measurementCount C3 = 0)
    (mT3 : measurementCount T3 = 0) (mN : measurementCount N = measurementCount Tl)
    (d1 : Disjoint (wires T1) (wires C2)) (d2 : Disjoint (wires (T1 ++ T2)) (wires C3))
    (loc : ∀ m u, run N m u = run ((T1 ++ T2 ++ T3) ++ Tl) m u) (m : List Bool) (s : State) :
    run ((P ++ (C1 ++ C2 ++ C3)) ++ (N ++ B)) m s =
      run ((P ++ (C1 ++ (T1 ++ (C2 ++ (T2 ++ (C3 ++ T3)))))) ++ (Tl ++ B)) m s := by
  rw [List.append_assoc P, List.append_assoc P]
  rw [run_append P, run_append P]
  generalize run P (m.take (measurementCount P)) s = t
  generalize m.drop (measurementCount P) = m'
  have m12 : measurementCount (T1 ++ T2) = 0 := by rw [measurementCount_append, mT1, mT2]
  have mT : measurementCount (T1 ++ T2 ++ T3) = 0 := by rw [measurementCount_append, m12, mT3]
  have mC : measurementCount (C1 ++ C2 ++ C3) = 0 := by
    rw [measurementCount_append, measurementCount_append, mC1, mC2, mC3]
  have hl : run ((C1 ++ C2 ++ C3) ++ (N ++ B)) m' t = run (N ++ B) m' (run (C1 ++ C2 ++ C3) [] t) :=
    mfa _ _ mC m' t
  have hr : run ((C1 ++ (T1 ++ (C2 ++ (T2 ++ (C3 ++ T3))))) ++ (Tl ++ B)) m' t =
      run (Tl ++ B) m' (run T3 [] (run C3 [] (run T2 [] (run C2 [] (run T1 [] (run C1 [] t)))))) := by
    simp only [List.append_assoc]
    rw [mfa _ _ mC1, mfa _ _ mT1, mfa _ _ mC2, mfa _ _ mT2, mfa _ _ mC3, mfa _ _ mT3]
  rw [hl, hr]
  rw [comm T1 C2 d1]
  have e2 : run C3 [] (run T2 [] (run T1 [] (run C2 [] (run C1 [] t)))) =
      run T2 [] (run T1 [] (run C3 [] (run C2 [] (run C1 [] t)))) := by
    have h := comm (T1 ++ T2) C3 d2 (run C2 [] (run C1 [] t))
    rw [mfa _ _ mT1] at h
    rw [h]
    have h2 := mfa T1 (T2 ++ []) mT1 [] (run C3 [] (run C2 [] (run C1 [] t)))
    simp only [List.append_nil] at h2
    rw [← h2]
  rw [e2]
  have e3 : run C3 [] (run C2 [] (run C1 [] t)) = run (C1 ++ C2 ++ C3) [] t := by
    rw [mfa _ _ (by rw [measurementCount_append, mC1, mC2]), mfa _ _ mC1]
  rw [e3]
  generalize run (C1 ++ C2 ++ C3) [] t = z
  have e4 : run T3 [] (run T2 [] (run T1 [] z)) = run (T1 ++ T2 ++ T3) [] z := by
    rw [mfa _ _ m12, mfa _ _ mT1]
  rw [e4, ← mfa _ _ mT m' z, ← List.append_assoc, run_append N B, run_append (T1 ++ T2 ++ T3 ++ Tl) B,
    measurementCount_append, mT, Nat.zero_add, mN, loc]

/-! ### A resource-tracking equivalence -/

structure Rel (k : Nat) (P Q : Program) : Prop where
  run_eq : ∀ m s, run P m s = run Q m s
  mc_eq : measurementCount P = measurementCount Q
  tc_eq : toffoliCount P + k = toffoliCount Q
  wires_sub : wires P ⊆ wires Q
  slots_le : gateSlots P ≤ gateSlots Q
  phys : GatePhysical Q → GatePhysical P

theorem Rel.refl (P : Program) : Rel 0 P P :=
  ⟨fun _ _ => rfl, rfl, rfl, Finset.Subset.refl _, le_refl _, id⟩

theorem Rel.app {a b : Nat} {P Q P' Q' : Program} (h1 : Rel a P Q) (h2 : Rel b P' Q') :
    Rel (a + b) (P ++ P') (Q ++ Q') where
  run_eq m s := by rw [run_append, run_append, h1.mc_eq, h1.run_eq, h2.run_eq]
  mc_eq := by rw [measurementCount_append, measurementCount_append, h1.mc_eq, h2.mc_eq]
  tc_eq := by
    have := h1.tc_eq; have := h2.tc_eq
    rw [toffoliCount_append, toffoliCount_append]; omega
  wires_sub := by
    rw [wires_append, wires_append]; exact Finset.union_subset_union h1.wires_sub h2.wires_sub
  slots_le := by
    rw [gateSlots_append, gateSlots_append]; exact Nat.add_le_add h1.slots_le h2.slots_le
  phys h := by
    rw [gatePhysical_append] at h ⊢; exact ⟨h1.phys h.1, h2.phys h.2⟩

def avoidB (E M : Program) : Bool :=
  (MixedFredCut.wl E).all (fun q => !((MixedFredCut.wl M).contains q))

theorem disj_of (E M : Program) (h : avoidB E M = true) : Disjoint (wires E) (wires M) :=
  Finset.disjoint_left.mpr (MixedFredCut.avoid_of_check E M h)

instance (f : Wire → Wire) : Decidable (Inj9 f) := by unfold Inj9; infer_instance

theorem phys_of_all (p : Program) (h : p.all physicalGateCheck = true) : GatePhysical p :=
  physicalGateCheck_correct p h

theorem phys_sub {P Q : Program} (h : ∀ i ∈ P, i ∈ Q) (hq : GatePhysical Q) : GatePhysical P :=
  fun i hi => hq i (h i hi)

theorem mem_take {α : Type} {l : List α} {k : Nat} {x : α} (h : x ∈ l.take k) : x ∈ l :=
  List.mem_of_mem_take h
theorem mem_drop {α : Type} {l : List α} {k : Nat} {x : α} (h : x ∈ l.drop k) : x ∈ l :=
  List.mem_of_mem_drop h

theorem wires_mem_sub {P Q : Program} (h : ∀ i ∈ P, i ∈ Q) : wires P ⊆ wires Q := by
  intro q hq
  induction P with
  | nil => simp [wires] at hq
  | cons i p ih =>
    simp only [wires, Finset.mem_union] at hq
    rcases hq with hq | hq
    · have hi := h i (by simp)
      clear ih h
      induction Q with
      | nil => simp at hi
      | cons j Q ihQ =>
        simp only [wires, Finset.mem_union]
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Or.inl hq
        · exact Or.inr (ihQ hi)
    · exact ih (fun j hj => h j (by simp [hj])) hq

/-! ### Forward boundary on concrete pieces -/

def topF (R : Program) (n : Nat) : Program :=
  (R.drop (n - 2)).take 2 ++ (R.drop (2 * n - 2)).take 2 ++ (R.drop (3 * n - 2)).take 2

def restF (R : Program) (n : Nat) : Program :=
  R.take (n - 2) ++ (R.drop n).take (n - 2) ++ (R.drop (2 * n)).take (n - 2)

def goodF (E R : Program) (n : Nat) (f : Wire → Wire) : Bool :=
  decide (2 ≤ n) && decide (Inj9 f) &&
  (E.drop (E.length - 9) == renameProgram f tailF) && (topF R n == renameProgram f routeT) &&
  avoidB ((R.drop (n - 2)).take 2) ((R.drop n).take (n - 2)) &&
  avoidB ((R.drop (n - 2)).take 2 ++ (R.drop (2 * n - 2)).take 2) ((R.drop (2 * n)).take (n - 2)) &&
  avoidB (renameProgram f tailF) (restF R n) &&
  (measurementCount (restF R n) == 0) && (renameProgram f newF).all physicalGateCheck

def enterM (E : Program) : Program := E.take (E.length - 9)
def routedM (R : Program) (n : Nat) (f : Wire → Wire) : Program :=
  restF R n ++ renameProgram f newF ++ R.drop (3 * n)

theorem rename_app (f : Wire → Wire) (p q : Program) :
    renameProgram f (p ++ q) = renameProgram f p ++ renameProgram f q := List.map_append

theorem fwd_pair (E R : Program) (n : Nat) (f : Wire → Wire) (h : goodF E R n f = true) :
    Rel 2 (enterM E ++ routedM R n f) (E ++ R) := by
  simp only [goodF, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hn, hf⟩, hE⟩, hT⟩, a1⟩, a2⟩, a3⟩, mR⟩, ph⟩ := h
  -- parts
  set C1 := R.take (n - 2)
  set T1 := (R.drop (n - 2)).take 2
  set C2 := (R.drop n).take (n - 2)
  set T2 := (R.drop (2 * n - 2)).take 2
  set C3 := (R.drop (2 * n)).take (n - 2)
  set T3 := (R.drop (3 * n - 2)).take 2
  set Rest := R.drop (3 * n)
  set A := E.take (E.length - 9)
  set Tl := E.drop (E.length - 9)
  set N := renameProgram f newF
  have dR : R = C1 ++ (T1 ++ (C2 ++ (T2 ++ (C3 ++ (T3 ++ Rest))))) := by
    have s6 := seg R (3 * n - 2) 2 (3 * n) (by omega)
    have s5 := seg R (2 * n) (n - 2) (3 * n - 2) (by omega)
    have s4 := seg R (2 * n - 2) 2 (2 * n) (by omega)
    have s3 := seg R n (n - 2) (2 * n - 2) (by omega)
    have s2 := seg R (n - 2) 2 n (by omega)
    rw [s6, s5, s4, s3, s2]
    exact (List.take_append_drop _ _).symm
  have dE : E = A ++ Tl := (List.take_append_drop _ _).symm
  have hTop : T1 ++ T2 ++ T3 = renameProgram f routeT := hT
  have hRest : restF R n = C1 ++ C2 ++ C3 := rfl
  have mTop : measurementCount (T1 ++ T2 ++ T3) = 0 := by
    rw [hTop, (renameProgram_counts _ _).2]; exact mc_routeT
  have mRest : measurementCount (C1 ++ C2 ++ C3) = 0 := by rw [← hRest]; exact mR
  simp only [measurementCount_append] at mTop mRest
  have mTl : measurementCount Tl = 0 := by rw [hE, (renameProgram_counts _ _).2]; exact mc_tailF
  have mN : measurementCount N = 0 := by rw [(renameProgram_counts _ _).2]; exact mc_newF
  have loc : ∀ m u, run N m u = run (Tl ++ (T1 ++ T2 ++ T3)) m u := by
    intro m u; rw [hE, hTop, ← rename_app]; exact fwd_local f hf m u
  have d3 : Disjoint (wires Tl) (wires (C1 ++ C2 ++ C3)) := by
    rw [hE, ← hRest]; exact disj_of _ _ a3
  have tTl : toffoliCount Tl = 2 := by rw [hE, (renameProgram_counts _ _).1]; exact tc_tailF
  have tTop : toffoliCount (T1 ++ T2 ++ T3) = 2 := by
    rw [hTop, (renameProgram_counts _ _).1]; exact tc_routeT
  have tN : toffoliCount N = 2 := by rw [(renameProgram_counts _ _).1]; exact tc_newF
  have new_eq : enterM E ++ routedM R n f = A ++ (C1 ++ C2 ++ C3 ++ N ++ Rest) := by
    simp only [enterM, routedM, hRest]; rfl
  rw [new_eq]
  conv => rhs; rw [dE, dR]
  constructor
  · intro m s
    exact fwd_core A Tl C1 T1 C2 T2 C3 T3 Rest N mTl (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) mN (disj_of _ _ a1) (disj_of _ _ a2) d3 loc m s
  · simp only [measurementCount_append]; omega
  · simp only [toffoliCount_append] at tTop ⊢; omega
  · have wN : wires N ⊆ wires Tl ∪ wires (T1 ++ T2 ++ T3) := by
      rw [← wires_append, hE, hTop, ← rename_app, renameProgram_support, renameProgram_support,
        w_newF, w_oldF]
    intro q hq
    have wN' : q ∈ wires N → q ∈ wires Tl ∨ q ∈ wires T1 ∨ q ∈ wires T2 ∨ q ∈ wires T3 := by
      intro h; have := wN h; simp only [wires_append, Finset.mem_union] at this; tauto
    simp only [wires_append, Finset.mem_union] at hq ⊢
    tauto
  · have gN : gateSlots N ≤ gateSlots Tl + gateSlots (T1 ++ T2 ++ T3) := by
      rw [hE, hTop, Baselines.rename_gateSlots, Baselines.rename_gateSlots, Baselines.rename_gateSlots]; exact gs_F
    simp only [gateSlots_append] at gN ⊢; omega
  · intro hold
    have pN : GatePhysical N := phys_of_all _ ph
    simp only [gatePhysical_append] at hold ⊢
    tauto

/-! ### Reverse boundary on concrete pieces -/

def topR (U : Program) (n : Nat) : Program :=
  (U.drop (U.length - 2 * n - 2)).take 2 ++ (U.drop (U.length - n - 2)).take 2 ++ U.drop (U.length - 2)

def restR (U : Program) (n : Nat) : Program :=
  (U.drop (U.length - 3 * n)).take (n - 2) ++ (U.drop (U.length - 2 * n)).take (n - 2) ++
    (U.drop (U.length - n)).take (n - 2)

def goodR (U Ei : Program) (n : Nat) (f : Wire → Wire) : Bool :=
  decide (2 ≤ n) && decide (3 * n ≤ U.length) && decide (Inj9 f) &&
  (Ei.take 9 == renameProgram f tailR) && (topR U n == renameProgram f routeT) &&
  avoidB ((U.drop (U.length - 2 * n - 2)).take 2) ((U.drop (U.length - 2 * n)).take (n - 2)) &&
  avoidB ((U.drop (U.length - 2 * n - 2)).take 2 ++ (U.drop (U.length - n - 2)).take 2)
    ((U.drop (U.length - n)).take (n - 2)) &&
  (measurementCount (restR U n) == 0) && (renameProgram f newR).all physicalGateCheck

def unroutedM (U : Program) (n : Nat) : Program := U.take (U.length - 3 * n) ++ restR U n
def enterInvM (Ei : Program) (f : Wire → Wire) : Program := renameProgram f newR ++ Ei.drop 9

theorem rev_pair (U Ei : Program) (n : Nat) (f : Wire → Wire) (h : goodR U Ei n f = true) :
    Rel 2 (unroutedM U n ++ enterInvM Ei f) (U ++ Ei) := by
  simp only [goodR, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hn, hL⟩, hf⟩, hE⟩, hT⟩, a1⟩, a2⟩, mR⟩, ph⟩ := h
  set L := U.length
  set P := U.take (L - 3 * n)
  set C1 := (U.drop (L - 3 * n)).take (n - 2)
  set T1 := (U.drop (L - 2 * n - 2)).take 2
  set C2 := (U.drop (L - 2 * n)).take (n - 2)
  set T2 := (U.drop (L - n - 2)).take 2
  set C3 := (U.drop (L - n)).take (n - 2)
  set T3 := U.drop (L - 2)
  set Tl := Ei.take 9
  set B := Ei.drop 9
  set N := renameProgram f newR
  have dU : U = P ++ (C1 ++ (T1 ++ (C2 ++ (T2 ++ (C3 ++ T3))))) := by
    have s5 := seg U (L - n) (n - 2) (L - 2) (by omega)
    have s4 := seg U (L - n - 2) 2 (L - n) (by omega)
    have s3 := seg U (L - 2 * n) (n - 2) (L - n - 2) (by omega)
    have s2 := seg U (L - 2 * n - 2) 2 (L - 2 * n) (by omega)
    have s1 := seg U (L - 3 * n) (n - 2) (L - 2 * n - 2) (by omega)
    rw [s5, s4, s3, s2, s1]
    exact (List.take_append_drop _ _).symm
  have dE : Ei = Tl ++ B := (List.take_append_drop _ _).symm
  have hTop : T1 ++ T2 ++ T3 = renameProgram f routeT := hT
  have hRest : restR U n = C1 ++ C2 ++ C3 := rfl
  have mTop : measurementCount (T1 ++ T2 ++ T3) = 0 := by
    rw [hTop, (renameProgram_counts _ _).2]; exact mc_routeT
  have mRest : measurementCount (C1 ++ C2 ++ C3) = 0 := by rw [← hRest]; exact mR
  simp only [measurementCount_append] at mTop mRest
  have mTl : measurementCount Tl = 1 := by rw [hE, (renameProgram_counts _ _).2]; exact mc_tailR
  have mN : measurementCount N = 1 := by rw [(renameProgram_counts _ _).2]; exact mc_newR
  have loc : ∀ m u, run N m u = run ((T1 ++ T2 ++ T3) ++ Tl) m u := by
    intro m u; rw [hE, hTop, ← rename_app]; exact rev_local f hf m u
  have tTl : toffoliCount Tl = 1 := by rw [hE, (renameProgram_counts _ _).1]; exact tc_tailR
  have tTop : toffoliCount (T1 ++ T2 ++ T3) = 2 := by
    rw [hTop, (renameProgram_counts _ _).1]; exact tc_routeT
  have tN : toffoliCount N = 1 := by rw [(renameProgram_counts _ _).1]; exact tc_newR
  have new_eq : unroutedM U n ++ enterInvM Ei f = (P ++ (C1 ++ C2 ++ C3)) ++ (N ++ B) := by
    simp only [unroutedM, enterInvM, hRest]; rfl
  rw [new_eq]
  conv => rhs; rw [dU, dE]
  constructor
  · intro m s
    exact rev_core P C1 T1 C2 T2 C3 T3 Tl B N (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by rw [mN, mTl]) (disj_of _ _ a1) (disj_of _ _ a2) loc m s
  · simp only [measurementCount_append]; omega
  · simp only [toffoliCount_append] at tTop ⊢; omega
  · have wN : wires N ⊆ wires (T1 ++ T2 ++ T3) ∪ wires Tl := by
      rw [← wires_append, hE, hTop, ← rename_app, renameProgram_support, renameProgram_support,
        w_newR, w_oldR]
    intro q hq
    have wN' : q ∈ wires N → q ∈ wires Tl ∨ q ∈ wires T1 ∨ q ∈ wires T2 ∨ q ∈ wires T3 := by
      intro h; have := wN h; simp only [wires_append, Finset.mem_union] at this; tauto
    simp only [wires_append, Finset.mem_union] at hq ⊢
    tauto
  · have gN : gateSlots N ≤ gateSlots (T1 ++ T2 ++ T3) + gateSlots Tl := by
      rw [hE, hTop, Baselines.rename_gateSlots, Baselines.rename_gateSlots, Baselines.rename_gateSlots]; exact gs_R
    simp only [gateSlots_append] at gN ⊢; omega
  · intro hold
    have pN : GatePhysical N := phys_of_all _ ph
    simp only [gatePhysical_append] at hold ⊢
    tauto

/-! ### Block data -/

def port15 (j : Fin 26) (q : Wire) : Wire :=
  let s := start j
  let h := Shadow7.sbP s
  [s + 15, s + 16, s + h + 31, h + 801, s + h + 32, h + 802, h + 1579, h + 803, h + 1576].getD q 0

def nP15 (j : Fin 26) : Nat := Shadow7.sbP (start j) + 16

def port20 (j : Fin 9) (q : Wire) : Wire :=
  let s := start20 j
  let h := sbP20 s + 5
  [s + 15, s + 16, s + h + 31, h + 801, s + h + 32, h + 802, h + 1579, h + 803, h + 1576].getD q 0

def nP20 (j : Fin 9) : Nat := sbP20 (start20 j) + 21

theorem drop_suf {α : Type} (P S : List α) (i : Nat) : (P ++ S).drop (P.length + i) = S.drop i := by
  have h : (P ++ S).drop P.length = S := List.drop_left' rfl
  rw [← List.drop_drop, h]

theorem dt_pre {α : Type} (S X : List α) (a k : Nat) (h : a + k ≤ S.length) :
    ((S ++ X).drop a).take k = (S.drop a).take k := by
  have h1 : a ≤ S.length := by omega
  have e1 : (S ++ X).drop a = S.drop a ++ X := List.drop_append_of_le_length h1
  have h2 : k ≤ (S.drop a).length := by rw [List.length_drop]; omega
  have e2 : (S.drop a ++ X).take k = (S.drop a).take k := List.take_append_of_le_length h2
  rw [e1, e2]

/-- The reverse check reads only the last `3 * n` gates of the untick. -/
theorem goodR_suffix (P S Ei : Program) (n : Nat) (f : Wire → Wire) (hn : 2 ≤ n) (hS : S.length = 3 * n) :
    goodR (P ++ S) Ei n f = goodR S Ei n f := by
  have e0 : (P ++ S).length = P.length + S.length := by simp only [List.length_append]
  have h1 : (P ++ S).drop ((P ++ S).length - 2 * n - 2) = S.drop (S.length - 2 * n - 2) := by
    rw [e0, show P.length + S.length - 2 * n - 2 = P.length + (S.length - 2 * n - 2) by omega, drop_suf]
  have h2 : (P ++ S).drop ((P ++ S).length - n - 2) = S.drop (S.length - n - 2) := by
    rw [e0, show P.length + S.length - n - 2 = P.length + (S.length - n - 2) by omega, drop_suf]
  have h3 : (P ++ S).drop ((P ++ S).length - 2) = S.drop (S.length - 2) := by
    rw [e0, show P.length + S.length - 2 = P.length + (S.length - 2) by omega, drop_suf]
  have h4 : (P ++ S).drop ((P ++ S).length - 3 * n) = S.drop (S.length - 3 * n) := by
    rw [e0, show P.length + S.length - 3 * n = P.length + (S.length - 3 * n) by omega, drop_suf]
  have h5 : (P ++ S).drop ((P ++ S).length - 2 * n) = S.drop (S.length - 2 * n) := by
    rw [e0, show P.length + S.length - 2 * n = P.length + (S.length - 2 * n) by omega, drop_suf]
  have h6 : (P ++ S).drop ((P ++ S).length - n) = S.drop (S.length - n) := by
    rw [e0, show P.length + S.length - n = P.length + (S.length - n) by omega, drop_suf]
  have dP : decide (3 * n ≤ (P ++ S).length) = true := decide_eq_true (by rw [e0]; omega)
  have dS : decide (3 * n ≤ S.length) = true := decide_eq_true (by omega)
  unfold goodR topR restR
  rw [dP, dS, h1, h2, h3, h4, h5, h6]

/-- The forward check reads only the first `3 * n` gates of the tick. -/
theorem goodF_prefix (E S X : Program) (n : Nat) (f : Wire → Wire) (hn : 2 ≤ n) (hS : S.length = 3 * n) :
    goodF E (S ++ X) n f = goodF E S n f := by
  have t1 := dt_pre S X (n - 2) 2 (by omega)
  have t2 := dt_pre S X (2 * n - 2) 2 (by omega)
  have t3 := dt_pre S X (3 * n - 2) 2 (by omega)
  have t4 := dt_pre S X n (n - 2) (by omega)
  have t5 := dt_pre S X (2 * n) (n - 2) (by omega)
  have t6 : (S ++ X).take (n - 2) = S.take (n - 2) :=
    List.take_append_of_le_length (show n - 2 ≤ S.length by omega)
  unfold goodF topF restF
  rw [t1, t2, t3, t4, t5, t6]

/-- The route exchange of the first tick of a 15-tick block: `3 * nP15 j` gates. -/
def sw15 (j : Fin 26) : Program :=
  renameProgram (ECDSAAdd.Entrant.StairPacket.net j 0)
    (swapRegisters (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0).a0
      (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0).ah
      (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0).bh)

def sw20 (j : Fin 9) : Program :=
  renameProgram (net20 j 0)
    (swapRegisters (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0).a0
      (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0).ah
      (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0).bh)

theorem untick_split (L : SkywalkIntegerLayout) (k : Nat) :
    ∃ X : Program, ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick L k = X ++ swapRegisters L.a0 L.ah L.bh :=
  ⟨_, rfl⟩

theorem tick_split (L : SkywalkIntegerLayout) :
    skywalkIntegerTick L = swapRegisters L.a0 L.ah L.bh ++
      ([Instr.CX L.a0 L.b0] ++ (skywalkSignedHalf L.aSign L.ext ++
        (signedRecord L.ext L.bSign L.history L.half L.b L.carry ++ [Instr.CX L.previous L.a0]))) := by
  simp only [skywalkIntegerTick, skywalkRoute, List.append_assoc]

theorem unrouted15_split (j : Fin 26) : ∃ P : Program, Shadow7.unrouted j 0 1 = P ++ sw15 j := by
  obtain ⟨X, hX⟩ := untick_split (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0)
    (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0).half.length
  have h : Shadow7.unrouted j 0 1 = renameProgram (ECDSAAdd.Entrant.StairPacket.net j 0)
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0)
        (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0).half.length) := rfl
  exact ⟨renameProgram (ECDSAAdd.Entrant.StairPacket.net j 0) X,
    h.trans ((congrArg (renameProgram (ECDSAAdd.Entrant.StairPacket.net j 0)) hX).trans (rename_app _ _ _))⟩

theorem unrouted20_split (j : Fin 9) : ∃ P : Program, unrouted20 j 0 1 = P ++ sw20 j := by
  obtain ⟨X, hX⟩ := untick_split (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0)
    (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0).half.length
  have h : unrouted20 j 0 1 = renameProgram (net20 j 0)
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0)
        (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0).half.length) := rfl
  exact ⟨renameProgram (net20 j 0) X,
    h.trans ((congrArg (renameProgram (net20 j 0)) hX).trans (rename_app _ _ _))⟩

theorem routed15_split (j : Fin 26) : ∃ Q : Program, Shadow7.routed j 0 1 = sw15 j ++ Q := by
  have h : Shadow7.routed j 0 1 = renameProgram (ECDSAAdd.Entrant.StairPacket.net j 0)
      (skywalkIntegerTick (ECDSAAdd.Entrant.IntegerPacket.ports (Shadow7.shape j) 0)) ++ [] := rfl
  exact ⟨_, h.trans ((List.append_nil _).trans
    ((congrArg (renameProgram (ECDSAAdd.Entrant.StairPacket.net j 0)) (tick_split _)).trans (rename_app _ _ _)))⟩

theorem routed20_split (j : Fin 9) : ∃ Q : Program, routed20 j 0 1 = sw20 j ++ Q := by
  have h : routed20 j 0 1 = renameProgram (net20 j 0)
      (skywalkIntegerTick (ECDSAAdd.Entrant.IntegerPacket.ports (shape20 j) 0)) ++ [] := rfl
  exact ⟨_, h.trans ((List.append_nil _).trans
    ((congrArg (renameProgram (net20 j 0)) (tick_split _)).trans (rename_app _ _ _)))⟩

def good15 (j : Fin 26) : Bool :=
  goodF (MixedFredCut.enter15C j) (sw15 j) (nP15 j) (port15 j) &&
  goodR (sw15 j) (MixedFredCut.enterInv15C j) (nP15 j) (port15 j) && ((sw15 j).length == 3 * nP15 j)

def good20 (j : Fin 9) : Bool :=
  goodF (MixedFredCut.enter20C j) (sw20 j) (nP20 j) (port20 j) &&
  goodR (sw20 j) (MixedFredCut.enterInv20C j) (nP20 j) (port20 j) && ((sw20 j).length == 3 * nP20 j)

theorem g15_0 : good15 ⟨0, by decide⟩ = true := by decide +kernel
theorem g15_1 : good15 ⟨1, by decide⟩ = true := by decide +kernel
theorem g15_2 : good15 ⟨2, by decide⟩ = true := by decide +kernel
theorem g15_3 : good15 ⟨3, by decide⟩ = true := by decide +kernel
theorem g15_4 : good15 ⟨4, by decide⟩ = true := by decide +kernel
theorem g15_5 : good15 ⟨5, by decide⟩ = true := by decide +kernel
theorem g15_6 : good15 ⟨6, by decide⟩ = true := by decide +kernel
theorem g15_7 : good15 ⟨7, by decide⟩ = true := by decide +kernel
theorem g15_20 : good15 ⟨20, by decide⟩ = true := by decide +kernel
theorem g15_21 : good15 ⟨21, by decide⟩ = true := by decide +kernel
theorem g15_22 : good15 ⟨22, by decide⟩ = true := by decide +kernel
theorem g15_23 : good15 ⟨23, by decide⟩ = true := by decide +kernel
theorem g15_24 : good15 ⟨24, by decide⟩ = true := by decide +kernel
theorem g20_0 : good20 ⟨0, by decide⟩ = true := by decide +kernel
theorem g20_1 : good20 ⟨1, by decide⟩ = true := by decide +kernel
theorem g20_2 : good20 ⟨2, by decide⟩ = true := by decide +kernel
theorem g20_3 : good20 ⟨3, by decide⟩ = true := by decide +kernel
theorem g20_4 : good20 ⟨4, by decide⟩ = true := by decide +kernel
theorem g20_5 : good20 ⟨5, by decide⟩ = true := by decide +kernel
theorem g20_6 : good20 ⟨6, by decide⟩ = true := by decide +kernel
theorem g20_7 : good20 ⟨7, by decide⟩ = true := by decide +kernel
theorem g20_8 : good20 ⟨8, by decide⟩ = true := by decide +kernel

theorem g15 (j : Fin 26) (h : j.val ≤ 7 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) : good15 j = true := by
  obtain ⟨v, hv⟩ := j
  simp only at h
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 20 ∨ v = 21 ∨
      v = 22 ∨ v = 23 ∨ v = 24 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [g15_0, g15_1, g15_2, g15_3, g15_4, g15_5, g15_6, g15_7, g15_20, g15_21, g15_22, g15_23, g15_24]

theorem g20 (j : Fin 9) : good20 j = true := by
  obtain ⟨v, hv⟩ := j
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [g20_0, g20_1, g20_2, g20_3, g20_4, g20_5, g20_6, g20_7, g20_8]

/-! ### Lists of pieces -/

def LRel (k : Nat) (ps qs : List Program) : Prop := Rel k ps.flatten qs.flatten

theorem LRel.cast {a b : Nat} {ps qs : List Program} (h : LRel a ps qs) (e : a = b) : LRel b ps qs :=
  e ▸ h

theorem LRel.refl (ps : List Program) : LRel 0 ps ps := Rel.refl _

theorem LRel.keep {k : Nat} (p : Program) {ps qs : List Program} (h : LRel k ps qs) :
    LRel k (p :: ps) (p :: qs) := by
  have := Rel.app (Rel.refl p) h
  unfold LRel; simp only [List.flatten_cons]; simpa using this

theorem LRel.pair {k k' : Nat} (a b c e : Program) {ps qs : List Program} (hp : Rel k' (a ++ b) (c ++ e))
    (h : LRel k ps qs) : LRel (k' + k) (a :: b :: ps) (c :: e :: qs) := by
  have := Rel.app hp h
  unfold LRel; simp only [List.flatten_cons, ← List.append_assoc]; exact this

theorem LRel.app {a b : Nat} {ps qs ps' qs' : List Program} (h1 : LRel a ps qs) (h2 : LRel b ps' qs') :
    LRel (a + b) (ps ++ ps') (qs ++ qs') := by
  unfold LRel; rw [List.flatten_append, List.flatten_append]; exact Rel.app h1 h2

theorem LRel.flatMap {α : Type} (xs : List α) (f g : α → List Program) (k : Nat)
    (h : ∀ x ∈ xs, LRel k (f x) (g x)) : LRel (k * xs.length) (xs.flatMap f) (xs.flatMap g) := by
  induction xs with
  | nil => exact (LRel.refl []).cast (by simp)
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    exact (LRel.app (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))).cast
      (by simp only [List.length_cons]; rw [Nat.mul_succ]; omega)

theorem pairF15 (j : Fin 26) (h : j.val ≤ 7 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) :
    Rel 2 (enterM (MixedFredCut.enter15C j) ++ routedM (Shadow7.routed j 0 1) (nP15 j) (port15 j))
      (MixedFredCut.enter15C j ++ Shadow7.routed j 0 1) := by
  have g := g15 j h
  simp only [good15, Bool.and_eq_true, beq_iff_eq] at g
  obtain ⟨Q, hQ⟩ := routed15_split j
  have hn : 2 ≤ nP15 j := by unfold nP15; omega
  have gf : goodF (MixedFredCut.enter15C j) (Shadow7.routed j 0 1) (nP15 j) (port15 j) = true := by
    rw [hQ, goodF_prefix _ _ Q _ _ hn g.2]; exact g.1.1
  exact fwd_pair _ _ _ _ gf

theorem pairR15 (j : Fin 26) (h : j.val ≤ 7 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) :
    Rel 2 (unroutedM (Shadow7.unrouted j 0 1) (nP15 j) ++ enterInvM (MixedFredCut.enterInv15C j) (port15 j))
      (Shadow7.unrouted j 0 1 ++ MixedFredCut.enterInv15C j) := by
  have g := g15 j h
  simp only [good15, Bool.and_eq_true, beq_iff_eq] at g
  obtain ⟨P, hP⟩ := unrouted15_split j
  have hn : 2 ≤ nP15 j := by unfold nP15; omega
  have gr : goodR (Shadow7.unrouted j 0 1) (MixedFredCut.enterInv15C j) (nP15 j) (port15 j) = true := by
    rw [hP, goodR_suffix P _ _ _ _ hn g.2]; exact g.1.2
  exact rev_pair _ _ _ _ gr

theorem pairF20 (j : Fin 9) :
    Rel 2 (enterM (MixedFredCut.enter20C j) ++ routedM (routed20 j 0 1) (nP20 j) (port20 j))
      (MixedFredCut.enter20C j ++ routed20 j 0 1) := by
  have g := g20 j
  simp only [good20, Bool.and_eq_true, beq_iff_eq] at g
  obtain ⟨Q, hQ⟩ := routed20_split j
  have hn : 2 ≤ nP20 j := by unfold nP20; omega
  have gf : goodF (MixedFredCut.enter20C j) (routed20 j 0 1) (nP20 j) (port20 j) = true := by
    rw [hQ, goodF_prefix _ _ Q _ _ hn g.2]; exact g.1.1
  exact fwd_pair _ _ _ _ gf

theorem pairR20 (j : Fin 9) :
    Rel 2 (unroutedM (unrouted20 j 0 1) (nP20 j) ++ enterInvM (MixedFredCut.enterInv20C j) (port20 j))
      (unrouted20 j 0 1 ++ MixedFredCut.enterInv20C j) := by
  have g := g20 j
  simp only [good20, Bool.and_eq_true, beq_iff_eq] at g
  obtain ⟨P, hP⟩ := unrouted20_split j
  have hn : 2 ≤ nP20 j := by unfold nP20; omega
  have gr : goodR (unrouted20 j 0 1) (MixedFredCut.enterInv20C j) (nP20 j) (port20 j) = true := by
    rw [hP, goodR_suffix P _ _ _ _ hn g.2]; exact g.1.2
  exact rev_pair _ _ _ _ gr


/-! ### Gate commutation and controlled exchanges -/

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

def tgt : Instr → Wire
  | .X t => t
  | .CX _ t => t
  | .CCX _ _ t => t
  | .measureX t _ _ => t

def isGate : Instr → Bool
  | .measureX _ _ _ => false
  | _ => true

def NonInt (i j : Instr) : Prop :=
  isGate i = true ∧ isGate j = true ∧ tgt i ∉ j.wires ∧ tgt j ∉ i.wires

theorem swap2 (i j : Instr) (h : NonInt i j) (m : List Bool) (s : State) :
    run [i, j] m s = run [j, i] m s := by
  obtain ⟨gi, gj, hij, hji⟩ := h
  cases i <;> cases j <;> simp_all [isGate, tgt, Instr.wires, run, writeBit] <;>
  · funext q
    simp only [Function.update_apply]
    split_ifs <;> simp_all

def Eqv (P Q : Program) : Prop := ∀ m s, run P m s = run Q m s

theorem Eqv.refl (P : Program) : Eqv P P := fun _ _ => rfl
theorem Eqv.symm {P Q : Program} (h : Eqv P Q) : Eqv Q P := fun m s => (h m s).symm
theorem Eqv.trans {P Q R : Program} (h1 : Eqv P Q) (h2 : Eqv Q R) : Eqv P R :=
  fun m s => (h1 m s).trans (h2 m s)

def GateOnly (P : Program) : Prop := ∀ i ∈ P, isGate i = true

theorem gate_mc {P : Program} (h : GateOnly P) : measurementCount P = 0 := by
  induction P with
  | nil => rfl
  | cons i p ih =>
    have hi := h i (by simp)
    have hp : GateOnly p := fun j hj => h j (by simp [hj])
    cases i <;> simp_all [isGate, measurementCount]

theorem run_gates (P Q : Program) (g : GateOnly P) (m : List Bool) (s : State) :
    run (P ++ Q) m s = run Q m (run P [] s) := by
  rw [run_append, gate_mc g, List.take_zero, List.drop_zero]

theorem gate_cons {i : Instr} {p : Program} (h : GateOnly (i :: p)) : isGate i = true ∧ GateOnly p :=
  ⟨h i (by simp), fun j hj => h j (by simp [hj])⟩

theorem gate_app {P Q : Program} : GateOnly (P ++ Q) ↔ GateOnly P ∧ GateOnly Q := by
  simp only [GateOnly, List.mem_append]
  constructor
  · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · intro h i hi; rcases hi with hi | hi; exacts [h.1 i hi, h.2 i hi]

theorem Eqv.app {P P' Q Q' : Program} (hP : Eqv P P') (hQ : Eqv Q Q')
    (gP : GateOnly P) (gP' : GateOnly P') : Eqv (P ++ Q) (P' ++ Q') := by
  intro m s
  rw [run_gates _ _ gP, run_gates _ _ gP', hP, hQ]

theorem Eqv.appR {P Q Q' : Program} (hQ : Eqv Q Q') : Eqv (P ++ Q) (P ++ Q') := by
  intro m s; rw [run_append, run_append, hQ]

theorem Eqv.appL {P P' Q : Program} (hP : Eqv P P') (gP : GateOnly P) (gP' : GateOnly P') :
    Eqv (P ++ Q) (P' ++ Q) := Eqv.app hP (Eqv.refl Q) gP gP'

theorem commP1 (i : Instr) (q : Program) (h : ∀ j ∈ q, NonInt i j) : Eqv (i :: q) (q ++ [i]) := by
  induction q with
  | nil => exact Eqv.refl _
  | cons j q ih =>
    have hij := h j (by simp)
    have rest := ih (fun k hk => h k (by simp [hk]))
    have gi : GateOnly [i] := by intro k hk; simp at hk; subst hk; exact hij.1
    have gj : GateOnly [j] := by intro k hk; simp at hk; subst hk; exact hij.2.1
    have gij : GateOnly [i, j] := by intro k hk; simp at hk; rcases hk with rfl | rfl; exacts [hij.1, hij.2.1]
    have gji : GateOnly [j, i] := by intro k hk; simp at hk; rcases hk with rfl | rfl; exacts [hij.2.1, hij.1]
    intro m s
    have e1 := run_gates [i, j] q gij m s
    have e2 := run_gates [j, i] q gji m s
    have e3 := run_gates [j] (i :: q) gj m s
    have e4 := run_gates [j] (q ++ [i]) gj m s
    simp only [List.cons_append, List.nil_append] at e1 e2 e3 e4
    rw [e1, swap2 i j hij, ← e2, e3, rest m, ← e4]
    rfl

theorem commP (p q : Program) (gp : GateOnly p) (gq : GateOnly q)
    (h : ∀ i ∈ p, ∀ j ∈ q, NonInt i j) : Eqv (p ++ q) (q ++ p) := by
  induction p with
  | nil => simp only [List.nil_append, List.append_nil]; exact Eqv.refl _
  | cons i p ih =>
    obtain ⟨gi, gp'⟩ := gate_cons gp
    have hi : ∀ j ∈ q, NonInt i j := h i (by simp)
    have rest := ih gp' (fun k hk j hj => h k (by simp [hk]) j hj)
    have gI : GateOnly [i] := by intro k hk; simp at hk; subst hk; exact gi
    have step1 : Eqv ([i] ++ (p ++ q)) ([i] ++ (q ++ p)) := Eqv.appR rest
    have step2 : Eqv ((i :: q) ++ p) ((q ++ [i]) ++ p) :=
      Eqv.appL (commP1 i q hi) (by intro k hk; simp at hk; rcases hk with rfl | hk; exacts [gi, gq k hk])
        (by intro k hk; simp at hk; rcases hk with hk | rfl; exacts [gq k hk, gi])
    have e1 : (i :: p) ++ q = [i] ++ (p ++ q) := rfl
    have e2 : [i] ++ (q ++ p) = (i :: q) ++ p := rfl
    have e3 : (q ++ [i]) ++ p = q ++ (i :: p) := by simp
    rw [e1]
    exact step1.trans (e2 ▸ (e3 ▸ step2))


def fE (c : Wire) (ps : List (Wire × Wire)) : Program :=
  ps.flatMap fun p => [.CX p.1 p.2, .CCX c p.2 p.1, .CX p.1 p.2]

def fR (c : Wire) (p : Wire × Wire) : Program := [.CX p.2 p.1, .CCX c p.1 p.2, .CX p.2 p.1]

set_option maxHeartbeats 1000000 in
theorem local4 (c1 c2 a b : Wire) (h12 : c1 ≠ c2) (h1a : c1 ≠ a) (h1b : c1 ≠ b) (h2a : c2 ≠ a)
    (h2b : c2 ≠ b) (hab : a ≠ b) :
    Eqv (fE c1 [(a, b)] ++ fR c2 (a, b)) ([.CX c1 c2] ++ fE c2 [(a, b)] ++ [.CX c1 c2]) := by
  intro m s
  simp only [fE, fR, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, run, writeBit]
  congr 1
  funext q
  simp only [Function.update_apply, h12, h1a, h1b, h2a, h2b, hab, h12.symm, h1a.symm, h1b.symm,
    h2a.symm, h2b.symm, hab.symm, if_true, if_false]
  by_cases e2 : q = c2
  · subst e2; simp [h12.symm, h2a, h2b]
  by_cases ea : q = a
  · subst ea; simp [e2, h1a.symm, h2a.symm, hab]; cases s.basis c1 <;> cases s.basis q <;> cases s.basis b <;> cases s.basis c2 <;> simp
  by_cases eb : q = b
  · subst eb; simp [e2, ea, h1b.symm, h2b.symm, hab.symm]; cases s.basis c1 <;> cases s.basis q <;> cases s.basis a <;> cases s.basis c2 <;> simp
  simp [e2, ea, eb]


/-! ### Pair lists -/

def pw (ps : List (Wire × Wire)) : List Wire := ps.flatMap fun p => [p.1, p.2]

/-- Controls `cs` and pair wires all distinct. -/
def Good (cs : List Wire) (ps : List (Wire × Wire)) : Prop := (cs ++ pw ps).Nodup

def passT (c : Wire) (ps : List (Wire × Wire)) : Program :=
  ps.map (fun p => Instr.CX p.2 p.1) ++ ps.map (fun p => Instr.CCX c p.1 p.2) ++
    ps.map (fun p => Instr.CX p.2 p.1)

theorem good_tail {cs : List Wire} {p : Wire × Wire} {ps : List (Wire × Wire)}
    (h : Good cs (p :: ps)) : Good cs ps := by
  unfold Good pw at *
  simp only [List.flatMap_cons] at h
  exact h.sublist (List.Sublist.append_left (List.sublist_append_right _ _) cs)

theorem good_head {cs : List Wire} {p : Wire × Wire} {ps : List (Wire × Wire)}
    (h : Good cs (p :: ps)) :
    p.1 ≠ p.2 ∧ p.1 ∉ cs ∧ p.2 ∉ cs ∧ p.1 ∉ pw ps ∧ p.2 ∉ pw ps := by
  unfold Good pw at h
  simp only [List.flatMap_cons, List.cons_append, List.nil_append] at h
  rw [List.nodup_append] at h
  obtain ⟨_, h2, hd⟩ := h
  rw [List.nodup_cons, List.nodup_cons] at h2
  obtain ⟨n1, n2, _⟩ := h2
  simp only [List.mem_cons, not_or] at n1
  refine ⟨n1.1, ?_, ?_, n1.2, n2⟩
  · intro hm; exact hd _ hm _ (by simp) rfl
  · intro hm; exact hd _ hm _ (by simp) rfl

theorem mem_pw {q : Wire × Wire} {ps : List (Wire × Wire)} (h : q ∈ ps) :
    q.1 ∈ pw ps ∧ q.2 ∈ pw ps := by
  unfold pw; constructor <;> exact List.mem_flatMap.mpr ⟨q, h, by simp⟩

theorem gate_map {α : Type} (f : α → Instr) (xs : List α) (h : ∀ x, isGate (f x) = true) :
    GateOnly (xs.map f) := by
  intro i hi; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hi; exact h x

theorem gate_cs (c : Wire) (p : Wire × Wire) : GateOnly (fR c p) := by
  intro i hi; simp [fR] at hi; rcases hi with rfl | rfl | rfl <;> rfl
theorem gate_ce (c : Wire) (ps : List (Wire × Wire)) : GateOnly (fE c ps) := by
  intro i hi; simp only [fE, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨p, _, hi⟩ := hi; rcases hi with rfl | rfl | rfl <;> rfl
theorem gate_csl (c : Wire) (ps : List (Wire × Wire)) : GateOnly (ps.flatMap (fR c)) := by
  intro i hi; simp only [List.mem_flatMap] at hi
  obtain ⟨p, _, hi⟩ := hi; exact gate_cs c p i hi

theorem gate_passT (c : Wire) (ps : List (Wire × Wire)) : GateOnly (passT c ps) := by
  unfold passT
  rw [gate_app, gate_app]
  exact ⟨⟨gate_map _ _ (fun _ => rfl), gate_map _ _ (fun _ => rfl)⟩, gate_map _ _ (fun _ => rfl)⟩

theorem passT_seq (c : Wire) (ps : List (Wire × Wire)) (h : Good [c] ps) :
    Eqv (passT c ps) (ps.flatMap (fR c)) := by
  induction ps with
  | nil => exact Eqv.refl _
  | cons p ps ih =>
    obtain ⟨h12, h1c, h2c, h1p, h2p⟩ := good_head h
    have ht := good_tail h
    have rest := ih ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1c h2c
    have hc : c ∉ pw ps := by
      unfold Good at ht; intro hm; simp only [List.singleton_append, List.nodup_cons] at ht; exact ht.1 hm
    set X := ps.map (fun p => Instr.CX p.2 p.1)
    set Y := ps.map (fun p => Instr.CCX c p.1 p.2)
    set Z := ps.map (fun p => Instr.CX p.2 p.1)
    have eP : passT c (p :: ps) = Instr.CX p.2 p.1 :: (X ++ (Instr.CCX c p.1 p.2 :: (Y ++ (Instr.CX p.2 p.1 :: Z)))) := by
      simp [passT, X, Y, Z]
    have gX : GateOnly X := gate_map _ _ (fun _ => rfl)
    have gY : GateOnly Y := gate_map _ _ (fun _ => rfl)
    have gZ : GateOnly Z := gate_map _ _ (fun _ => rfl)
    -- y past X
    have c1 : Eqv (X ++ [Instr.CCX c p.1 p.2]) ([Instr.CCX c p.1 p.2] ++ X) := by
      apply commP _ _ gX (by intro k hk; simp at hk; subst hk; rfl)
      intro i hi j hj
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
      simp only [List.mem_singleton] at hj; subst hj
      have mq := mem_pw hq
      refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [tgt, Instr.wires, Finset.mem_insert, Finset.mem_singleton, not_or]
      · exact ⟨fun e => hc (e ▸ mq.1), fun e => h1p (e ▸ mq.1), fun e => h2p (e ▸ mq.1)⟩
      · exact ⟨fun e => h2p (e ▸ mq.2), fun e => h2p (e ▸ mq.1)⟩
    -- z past X ++ Y
    have c2 : Eqv ((X ++ Y) ++ [Instr.CX p.2 p.1]) ([Instr.CX p.2 p.1] ++ (X ++ Y)) := by
      apply commP _ _ (gate_app.mpr ⟨gX, gY⟩) (by intro k hk; simp at hk; subst hk; rfl)
      intro i hi j hj
      simp only [List.mem_singleton] at hj; subst hj
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        have mq := mem_pw hq
        refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [tgt, Instr.wires, Finset.mem_insert, Finset.mem_singleton, not_or]
        · exact ⟨fun e => h2p (e ▸ mq.1), fun e => h1p (e ▸ mq.1)⟩
        · exact ⟨fun e => h1p (e ▸ mq.2), fun e => h1p (e ▸ mq.1)⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
        have mq := mem_pw hq
        refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [tgt, Instr.wires, Finset.mem_insert, Finset.mem_singleton, not_or]
        · exact ⟨fun e => h2p (e ▸ mq.2), fun e => h1p (e ▸ mq.2)⟩
        · exact ⟨fun e => h1c (e ▸ rfl), fun e => h1p (e ▸ mq.1), fun e => h1p (e ▸ mq.2)⟩
    rw [eP]
    have target : (p :: ps).flatMap (fR c) =
        [Instr.CX p.2 p.1, Instr.CCX c p.1 p.2, Instr.CX p.2 p.1] ++ ps.flatMap (fR c) := by simp [fR]
    rw [target]
    have gy : GateOnly [Instr.CCX c p.1 p.2] := by intro k hk; simp at hk; subst hk; rfl
    have gz : GateOnly [Instr.CX p.2 p.1] := by intro k hk; simp at hk; subst hk; rfl
    refine Eqv.trans (Q := [Instr.CX p.2 p.1] ++ (([Instr.CCX c p.1 p.2] ++ X) ++ (Y ++ (Instr.CX p.2 p.1 :: Z)))) ?_ ?_
    · have h := Eqv.appR (P := [Instr.CX p.2 p.1]) (Eqv.appL (Q := Y ++ (Instr.CX p.2 p.1 :: Z)) c1
        (gate_app.mpr ⟨gX, gy⟩) (gate_app.mpr ⟨gy, gX⟩))
      have e : Instr.CX p.2 p.1 :: (X ++ (Instr.CCX c p.1 p.2 :: (Y ++ (Instr.CX p.2 p.1 :: Z)))) =
          [Instr.CX p.2 p.1] ++ ((X ++ [Instr.CCX c p.1 p.2]) ++ (Y ++ (Instr.CX p.2 p.1 :: Z))) := by simp
      rw [e]; exact h
    · refine Eqv.trans (Q := [Instr.CX p.2 p.1, Instr.CCX c p.1 p.2] ++ (([Instr.CX p.2 p.1] ++ (X ++ Y)) ++ Z)) ?_ ?_
      · have h := Eqv.appR (P := [Instr.CX p.2 p.1, Instr.CCX c p.1 p.2]) (Eqv.appL (Q := Z) c2
          (gate_app.mpr ⟨gate_app.mpr ⟨gX, gY⟩, gz⟩) (gate_app.mpr ⟨gz, gate_app.mpr ⟨gX, gY⟩⟩))
        have e1 : [Instr.CX p.2 p.1] ++ (([Instr.CCX c p.1 p.2] ++ X) ++ (Y ++ (Instr.CX p.2 p.1 :: Z))) =
            [Instr.CX p.2 p.1, Instr.CCX c p.1 p.2] ++ (((X ++ Y) ++ [Instr.CX p.2 p.1]) ++ Z) := by simp
        rw [e1]; exact h
      · have e2 : [Instr.CX p.2 p.1, Instr.CCX c p.1 p.2] ++ (([Instr.CX p.2 p.1] ++ (X ++ Y)) ++ Z) =
            [Instr.CX p.2 p.1, Instr.CCX c p.1 p.2, Instr.CX p.2 p.1] ++ passT c ps := by
          simp [passT, X, Y, Z]
        rw [e2]; exact Eqv.appR rest


set_option maxHeartbeats 1000000 in
theorem local4r (c1 c2 a b : Wire) (h12 : c1 ≠ c2) (h1a : c1 ≠ a) (h1b : c1 ≠ b) (h2a : c2 ≠ a)
    (h2b : c2 ≠ b) (hab : a ≠ b) :
    Eqv (fR c2 (a, b) ++ fE c1 [(a, b)]) ([.CX c1 c2] ++ fE c2 [(a, b)] ++ [.CX c1 c2]) := by
  intro m s
  simp only [fE, fR, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, run, writeBit]
  congr 1
  funext q
  simp only [Function.update_apply, h12, h1a, h1b, h2a, h2b, hab, h12.symm, h1a.symm, h1b.symm,
    h2a.symm, h2b.symm, hab.symm, if_true, if_false]
  by_cases e2 : q = c2
  · subst e2; simp [h12.symm, h2a, h2b]
  by_cases ea : q = a
  · subst ea; simp [e2, h1a.symm, h2a.symm, hab]; cases s.basis c1 <;> cases s.basis q <;> cases s.basis b <;> cases s.basis c2 <;> simp
  by_cases eb : q = b
  · subst eb; simp [e2, ea, h1b.symm, h2b.symm, hab.symm]; cases s.basis c1 <;> cases s.basis q <;> cases s.basis a <;> cases s.basis c2 <;> simp
  simp [e2, ea, eb]

set_option maxHeartbeats 1000000 in
theorem cxcx (a b : Wire) (hab : a ≠ b) : Eqv [.CX a b, .CX a b] [] := by
  intro m s
  simp only [run, writeBit]
  congr 1
  funext q
  simp only [Function.update_apply]
  by_cases e : q = b
  · subst e; simp [hab]
  · simp [e]

set_option maxHeartbeats 1000000 in
theorem wswap (c a b x : Wire) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) (hcx : c ≠ x) (hax : a ≠ x)
    (hbx : b ≠ x) : Eqv (fR c (a, b) ++ [.CX a x, .CX b x]) ([.CX a x, .CX b x] ++ fR c (a, b)) := by
  intro m s
  simp only [fR, List.cons_append, List.nil_append, run, writeBit]
  congr 1
  funext q
  simp only [Function.update_apply, hca, hcb, hab, hcx, hax, hbx, hca.symm, hcb.symm, hab.symm,
    hcx.symm, hax.symm, hbx.symm, if_true, if_false]
  by_cases ex : q = x
  · subst ex; simp [hax.symm, hbx.symm]; cases s.basis c <;> cases s.basis a <;> cases s.basis b <;> simp
  by_cases ea : q = a
  · subst ea; simp [ex, hab]
  by_cases eb : q = b
  · subst eb; simp [ex, ea]
  simp [ex, ea, eb]


theorem fE_cons (c : Wire) (p : Wire × Wire) (ps : List (Wire × Wire)) :
    fE c (p :: ps) = fE c [p] ++ fE c ps := by simp [fE]

/-- Facts about two controls and the pairs of a good list. -/
theorem good2 {c1 c2 : Wire} {p : Wire × Wire} {ps : List (Wire × Wire)} (h : Good [c1, c2] (p :: ps)) :
    c1 ≠ c2 ∧ c1 ≠ p.1 ∧ c1 ≠ p.2 ∧ c2 ≠ p.1 ∧ c2 ≠ p.2 ∧ p.1 ≠ p.2 ∧
    c1 ∉ pw ps ∧ c2 ∉ pw ps ∧ p.1 ∉ pw ps ∧ p.2 ∉ pw ps := by
  obtain ⟨h12, h1c, h2c, h1p, h2p⟩ := good_head h
  have ht := good_tail h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1c h2c
  unfold Good at ht h
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, not_or] at ht h
  exact ⟨h.1.1, fun e => h1c.1 e.symm, fun e => h2c.1 e.symm, fun e => h1c.2 e.symm,
    fun e => h2c.2 e.symm, h12, ht.1.2, ht.2.1, h1p, h2p⟩

theorem nonint_fE_fR {c1 c2 : Wire} {p : Wire × Wire} {ps : List (Wire × Wire)}
    (h : Good [c1, c2] (p :: ps)) : ∀ i ∈ fE c1 ps, ∀ j ∈ fR c2 p, NonInt i j := by
  obtain ⟨h12, h1a, h1b, h2a, h2b, hab, h1p, h2p, hap, hbp⟩ := good2 h
  intro i hi j hj
  simp only [fE, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨q, hq, hi⟩ := hi
  have mq := mem_pw hq
  simp only [fR, List.mem_cons, List.not_mem_nil, or_false] at hj
  have q1a : q.1 ≠ p.1 := fun e => hap (e ▸ mq.1)
  have q1b : q.1 ≠ p.2 := fun e => hbp (e ▸ mq.1)
  have q2a : q.2 ≠ p.1 := fun e => hap (e ▸ mq.2)
  have q2b : q.2 ≠ p.2 := fun e => hbp (e ▸ mq.2)
  have q1c : q.1 ≠ c2 := fun e => h2p (e ▸ mq.1)
  have q2c : q.2 ≠ c2 := fun e => h2p (e ▸ mq.2)
  have q1d : q.1 ≠ c1 := fun e => h1p (e ▸ mq.1)
  have q2d : q.2 ≠ c1 := fun e => h1p (e ▸ mq.2)
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    simp only [tgt, Instr.wires, Finset.mem_insert, Finset.mem_singleton, not_or] <;>
    first
    | exact ⟨q2b, q2a⟩ | exact ⟨q1b, q1a⟩ | exact ⟨q2c, q2a, q2b⟩ | exact ⟨q1c, q1a, q1b⟩
    | exact ⟨Ne.symm q1a, Ne.symm q2a⟩ | exact ⟨Ne.symm q1b, Ne.symm q2b⟩
    | exact ⟨h1a, Ne.symm q2a, Ne.symm q1a⟩ | exact ⟨h1b, Ne.symm q2b, Ne.symm q1b⟩
    | exact ⟨Ne.symm h1a, Ne.symm q2a, Ne.symm q1a⟩ | exact ⟨Ne.symm h1b, Ne.symm q2b, Ne.symm q1b⟩


theorem merge_fwd (c1 c2 : Wire) (ps : List (Wire × Wire)) (h : Good [c1, c2] ps) :
    Eqv (fE c1 ps ++ ps.flatMap (fR c2)) ([.CX c1 c2] ++ fE c2 ps ++ [.CX c1 c2]) := by
  induction ps with
  | nil =>
    have h12 : c1 ≠ c2 := by unfold Good at h; simp at h; exact h.1.1
    simp only [fE, List.flatMap_nil, List.append_nil, List.nil_append, List.singleton_append]
    exact (cxcx c1 c2 h12).symm
  | cons p ps ih =>
    obtain ⟨h12, h1a, h1b, h2a, h2b, hab, _, _, _, _⟩ := good2 h
    have rest := ih (good_tail h)
    have cm := commP (fE c1 ps) (fR c2 p) (gate_ce c1 ps) (gate_cs c2 p) (nonint_fE_fR h)
    have loc := local4 c1 c2 p.1 p.2 h12 h1a h1b h2a h2b hab
    have gC : GateOnly [Instr.CX c1 c2] := by intro k hk; simp at hk; subst hk; rfl
    -- reorder
    have s1 : Eqv (fE c1 (p :: ps) ++ (p :: ps).flatMap (fR c2))
        ((fE c1 [p] ++ fR c2 p) ++ (fE c1 ps ++ ps.flatMap (fR c2))) := by
      have e1 : fE c1 (p :: ps) ++ (p :: ps).flatMap (fR c2) =
          fE c1 [p] ++ ((fE c1 ps ++ fR c2 p) ++ ps.flatMap (fR c2)) := by simp [fE]
      have e2 : (fE c1 [p] ++ fR c2 p) ++ (fE c1 ps ++ ps.flatMap (fR c2)) =
          fE c1 [p] ++ ((fR c2 p ++ fE c1 ps) ++ ps.flatMap (fR c2)) := by simp
      rw [e1, e2]
      exact Eqv.appR (Eqv.appL cm (gate_app.mpr ⟨gate_ce _ _, gate_cs _ _⟩)
        (gate_app.mpr ⟨gate_cs _ _, gate_ce _ _⟩))
    refine s1.trans ?_
    have hp : (p.1, p.2) = p := rfl
    rw [hp] at loc
    have s2 := Eqv.app loc rest (gate_app.mpr ⟨gate_ce _ _, gate_cs _ _⟩)
      (gate_app.mpr ⟨gate_app.mpr ⟨gC, gate_ce _ _⟩, gC⟩)
    refine s2.trans ?_
    have e3 : [Instr.CX c1 c2] ++ fE c2 [p] ++ [Instr.CX c1 c2] ++ ([Instr.CX c1 c2] ++ fE c2 ps ++ [Instr.CX c1 c2]) =
        ([Instr.CX c1 c2] ++ fE c2 [p]) ++ ([Instr.CX c1 c2, Instr.CX c1 c2] ++ (fE c2 ps ++ [Instr.CX c1 c2])) := by simp
    have e4 : [Instr.CX c1 c2] ++ fE c2 (p :: ps) ++ [Instr.CX c1 c2] =
        ([Instr.CX c1 c2] ++ fE c2 [p]) ++ ([] ++ (fE c2 ps ++ [Instr.CX c1 c2])) := by simp [fE]
    rw [e3, e4]
    exact Eqv.appR (Eqv.appL (cxcx c1 c2 h12) (by intro k hk; simp at hk; rcases hk with rfl | rfl <;> rfl)
      (by intro k hk; simp at hk))


theorem nonint_fR_fE {c1 c2 : Wire} {p : Wire × Wire} {ps : List (Wire × Wire)}
    (h : Good [c1, c2] (p :: ps)) : ∀ i ∈ ps.flatMap (fR c2), ∀ j ∈ fE c1 [p], NonInt i j := by
  obtain ⟨h12, h1a, h1b, h2a, h2b, hab, h1p, h2p, hap, hbp⟩ := good2 h
  intro i hi j hj
  simp only [List.mem_flatMap] at hi
  obtain ⟨q, hq, hi⟩ := hi
  have mq := mem_pw hq
  simp only [fR, List.mem_cons, List.not_mem_nil, or_false] at hi
  simp only [fE, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  have q1a : q.1 ≠ p.1 := fun e => hap (e ▸ mq.1)
  have q1b : q.1 ≠ p.2 := fun e => hbp (e ▸ mq.1)
  have q2a : q.2 ≠ p.1 := fun e => hap (e ▸ mq.2)
  have q2b : q.2 ≠ p.2 := fun e => hbp (e ▸ mq.2)
  have q1c : q.1 ≠ c2 := fun e => h2p (e ▸ mq.1)
  have q2c : q.2 ≠ c2 := fun e => h2p (e ▸ mq.2)
  have q1d : q.1 ≠ c1 := fun e => h1p (e ▸ mq.1)
  have q2d : q.2 ≠ c1 := fun e => h1p (e ▸ mq.2)
  have := q1a.symm; have := q1b.symm; have := q2a.symm; have := q2b.symm; have := q1c.symm
  have := q2c.symm; have := q1d.symm; have := q2d.symm; have := h12.symm; have := h1a.symm
  have := h1b.symm; have := h2a.symm; have := h2b.symm; have := hab.symm
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    simp only [tgt, Instr.wires, Finset.mem_insert, Finset.mem_singleton, not_or] <;>
    tauto


theorem merge_rev (c1 c2 : Wire) (ps : List (Wire × Wire)) (h : Good [c1, c2] ps) :
    Eqv (ps.flatMap (fR c2) ++ fE c1 ps) ([.CX c1 c2] ++ fE c2 ps ++ [.CX c1 c2]) := by
  induction ps with
  | nil =>
    have h12 : c1 ≠ c2 := by unfold Good at h; simp at h; exact h.1.1
    simp only [fE, List.flatMap_nil, List.append_nil, List.nil_append, List.singleton_append]
    exact (cxcx c1 c2 h12).symm
  | cons p ps ih =>
    obtain ⟨h12, h1a, h1b, h2a, h2b, hab, _, _, _, _⟩ := good2 h
    have rest := ih (good_tail h)
    have cm := commP (ps.flatMap (fR c2)) (fE c1 [p]) (gate_csl c2 ps) (gate_ce c1 [p]) (nonint_fR_fE h)
    have loc := local4r c1 c2 p.1 p.2 h12 h1a h1b h2a h2b hab
    have gC : GateOnly [Instr.CX c1 c2] := by intro k hk; simp at hk; subst hk; rfl
    have s1 : Eqv ((p :: ps).flatMap (fR c2) ++ fE c1 (p :: ps))
        ((fR c2 p ++ fE c1 [p]) ++ (ps.flatMap (fR c2) ++ fE c1 ps)) := by
      have e1 : (p :: ps).flatMap (fR c2) ++ fE c1 (p :: ps) =
          fR c2 p ++ ((ps.flatMap (fR c2) ++ fE c1 [p]) ++ fE c1 ps) := by simp [fE]
      have e2 : (fR c2 p ++ fE c1 [p]) ++ (ps.flatMap (fR c2) ++ fE c1 ps) =
          fR c2 p ++ ((fE c1 [p] ++ ps.flatMap (fR c2)) ++ fE c1 ps) := by simp
      rw [e1, e2]
      exact Eqv.appR (Eqv.appL cm (gate_app.mpr ⟨gate_csl _ _, gate_ce _ _⟩)
        (gate_app.mpr ⟨gate_ce _ _, gate_csl _ _⟩))
    refine s1.trans ?_
    have hp : (p.1, p.2) = p := rfl
    rw [hp] at loc
    have s2 := Eqv.app loc rest (gate_app.mpr ⟨gate_cs _ _, gate_ce _ _⟩)
      (gate_app.mpr ⟨gate_app.mpr ⟨gC, gate_ce _ _⟩, gC⟩)
    refine s2.trans ?_
    have e3 : [Instr.CX c1 c2] ++ fE c2 [p] ++ [Instr.CX c1 c2] ++ ([Instr.CX c1 c2] ++ fE c2 ps ++ [Instr.CX c1 c2]) =
        ([Instr.CX c1 c2] ++ fE c2 [p]) ++ ([Instr.CX c1 c2, Instr.CX c1 c2] ++ (fE c2 ps ++ [Instr.CX c1 c2])) := by simp
    have e4 : [Instr.CX c1 c2] ++ fE c2 (p :: ps) ++ [Instr.CX c1 c2] =
        ([Instr.CX c1 c2] ++ fE c2 [p]) ++ ([] ++ (fE c2 ps ++ [Instr.CX c1 c2])) := by simp [fE]
    rw [e3, e4]
    exact Eqv.appR (Eqv.appL (cxcx c1 c2 h12) (by intro k hk; simp at hk; rcases hk with rfl | rfl <;> rfl)
      (by intro k hk; simp at hk))


theorem good1 {c : Wire} {p : Wire × Wire} {ps : List (Wire × Wire)} (h : Good [c] (p :: ps)) :
    c ≠ p.1 ∧ c ≠ p.2 ∧ p.1 ≠ p.2 ∧ c ∉ pw ps ∧ p.1 ∉ pw ps ∧ p.2 ∉ pw ps := by
  obtain ⟨h12, h1c, h2c, h1p, h2p⟩ := good_head h
  have ht := good_tail h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1c h2c
  unfold Good at ht
  simp only [List.cons_append, List.nil_append, List.nodup_cons] at ht
  exact ⟨fun e => h1c e.symm, fun e => h2c e.symm, h12, ht.1, h1p, h2p⟩

theorem nonint_fE_fE {c : Wire} {p : Wire × Wire} {ps : List (Wire × Wire)}
    (h : Good [c] (p :: ps)) : ∀ i ∈ fE c ps, ∀ j ∈ fE c [p], NonInt i j := by
  obtain ⟨h1a, h1b, hab, h1p, hap, hbp⟩ := good1 h
  intro i hi j hj
  simp only [fE, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨q, hq, hi⟩ := hi
  have mq := mem_pw hq
  simp only [fE, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hj
  have q1a : q.1 ≠ p.1 := fun e => hap (e ▸ mq.1)
  have q1b : q.1 ≠ p.2 := fun e => hbp (e ▸ mq.1)
  have q2a : q.2 ≠ p.1 := fun e => hap (e ▸ mq.2)
  have q2b : q.2 ≠ p.2 := fun e => hbp (e ▸ mq.2)
  have q1d : q.1 ≠ c := fun e => h1p (e ▸ mq.1)
  have q2d : q.2 ≠ c := fun e => h1p (e ▸ mq.2)
  have := q1a.symm; have := q1b.symm; have := q2a.symm; have := q2b.symm
  have := q1d.symm; have := q2d.symm; have := h1a.symm; have := h1b.symm; have := hab.symm
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    refine ⟨rfl, rfl, ?_, ?_⟩ <;>
    simp only [tgt, Instr.wires, Finset.mem_insert, Finset.mem_singleton, not_or] <;>
    tauto

theorem fE_rev (c : Wire) (ps : List (Wire × Wire)) (h : Good [c] ps) :
    Eqv (fE c ps.reverse) (fE c ps) := by
  induction ps with
  | nil => exact Eqv.refl _
  | cons p ps ih =>
    have rest := ih (good_tail h)
    have e1 : fE c (p :: ps).reverse = fE c ps.reverse ++ fE c [p] := by simp [fE]
    have e2 : fE c (p :: ps) = fE c [p] ++ fE c ps := by simp [fE]
    rw [e1, e2]
    exact (Eqv.appL rest (gate_ce _ _) (gate_ce _ _)).trans
      (commP _ _ (gate_ce _ _) (gate_ce _ _) (nonint_fE_fE h))


/-! ### The window exit portal and the stock tick at 420 -/

def nonIntB (i j : Instr) : Bool :=
  isGate i && isGate j && !((MixedFredCut.iwl j).contains (tgt i)) && !((MixedFredCut.iwl i).contains (tgt j))

theorem mem_iwl_gate (i : Instr) (hi : isGate i = true) (q : Wire) : q ∈ i.wires ↔ q ∈ MixedFredCut.iwl i := by
  cases i <;> simp_all [isGate, Instr.wires, MixedFredCut.iwl]

theorem nonIntB_sound (i j : Instr) (h : nonIntB i j = true) : NonInt i j := by
  simp only [nonIntB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨gi, gj⟩, h1⟩, h2⟩ := h
  refine ⟨gi, gj, ?_, ?_⟩
  · rw [mem_iwl_gate j gj]; intro hm; simp at h1; exact h1 hm
  · rw [mem_iwl_gate i gi]; intro hm; simp at h2; exact h2 hm

def allNI (p q : Program) : Bool := p.all fun i => q.all fun j => nonIntB i j

theorem allNI_sound (p q : Program) (h : allNI p q = true) : ∀ i ∈ p, ∀ j ∈ q, NonInt i j := by
  intro i hi j hj
  exact nonIntB_sound i j (List.all_eq_true.mp (List.all_eq_true.mp h i hi) j hj)

def sharedF : List (Wire × Wire) := (List.range 38).map fun k => (490 + k, 840 + k)
def otherF : List (Wire × Wire) := (List.range 53).map fun k => (437 + k, 787 + k)
def topP : Wire × Wire := (528, 878)
def Wx : Program := [.CX 878 1618, .CX 528 1618]
def Wr : Program := [.CX 528 1618, .CX 878 1618]

def tlF : Program := fE 435 (topP :: sharedF.reverse) ++ Wx
def rtF : Program := passT 436 (otherF ++ sharedF)
def nmF : Program :=
  otherF.flatMap (fR 436) ++ (fE 435 [topP] ++ (([.CX 435 436] ++ fE 436 sharedF ++ [.CX 435 436]) ++ Wx))

def rtR : Program := passT 436 (otherF ++ sharedF ++ [topP])
def tlR : Program := Wr ++ fE 435 (sharedF ++ [topP])
def nmR : Program :=
  otherF.flatMap (fR 436) ++ (Wr ++ ([.CX 435 436] ++ fE 436 (sharedF ++ [topP]) ++ [.CX 435 436]))

theorem pf1 : (MixedFredCut.portalInvC 420).drop ((MixedFredCut.portalInvC 420).length - 119) = tlF := by
  decide +kernel
theorem pf2 : (MixedWindow.tickW 420).take (3 * 91) = rtF := by decide +kernel
theorem pr1 : (MixedWindow.recvW 420).drop ((MixedWindow.recvW 420).length - 3 * 92) = rtR := by
  decide +kernel
theorem pr2 : (MixedFredCut.portalC 420).take 119 = tlR := by decide +kernel

theorem goods : Good [436] (otherF ++ sharedF) ∧ Good [435] sharedF ∧ Good [435, 436] sharedF ∧
    Good [436] (otherF ++ sharedF ++ [topP]) ∧ Good [435, 436] (sharedF ++ [topP]) := by
  unfold Good; decide +kernel

theorem mid_fwd : Eqv (tlF ++ rtF) nmF := by
  obtain ⟨g1, g2, g3, _, _⟩ := goods
  have hs := passT_seq 436 _ g1
  rw [List.flatMap_append] at hs
  set O := otherF.flatMap (fR 436)
  set S := sharedF.flatMap (fR 436)
  have gO : GateOnly O := gate_csl _ _
  have gS : GateOnly S := gate_csl _ _
  have gW : GateOnly Wx := by intro k hk; simp [Wx] at hk; rcases hk with rfl | rfl <;> rfl
  have gT : GateOnly tlF := gate_app.mpr ⟨gate_ce _ _, gW⟩
  have cTO : Eqv (tlF ++ O) (O ++ tlF) := commP _ _ gT gO (allNI_sound _ _ (by decide +kernel))
  have cWS : Eqv (Wx ++ S) (S ++ Wx) := commP _ _ gW gS (allNI_sound _ _ (by decide +kernel))
  have rv := fE_rev 435 sharedF g2
  have mg := merge_fwd 435 436 sharedF g3
  -- assemble
  refine (Eqv.appR (P := tlF) hs).trans ?_
  have e1 : tlF ++ (O ++ S) = (tlF ++ O) ++ S := by simp
  rw [e1]
  refine (Eqv.appL cTO (gate_app.mpr ⟨gT, gO⟩) (gate_app.mpr ⟨gO, gT⟩)).trans ?_
  have e2 : (O ++ tlF) ++ S = O ++ (fE 435 [topP] ++ (fE 435 sharedF.reverse ++ (Wx ++ S))) := by
    simp [tlF, fE]
  rw [e2]
  refine (Eqv.appR (Eqv.appR (Eqv.appR cWS))).trans ?_
  have e3 : O ++ (fE 435 [topP] ++ (fE 435 sharedF.reverse ++ (S ++ Wx))) =
      O ++ (fE 435 [topP] ++ ((fE 435 sharedF.reverse ++ S) ++ Wx)) := by simp
  rw [e3]
  refine (Eqv.appR (Eqv.appR (Eqv.appL (Eqv.appL rv (gate_ce _ _) (gate_ce _ _))
    (gate_app.mpr ⟨gate_ce _ _, gS⟩) (gate_app.mpr ⟨gate_ce _ _, gS⟩)))).trans ?_
  have gC : GateOnly [Instr.CX 435 436] := by intro k hk; simp at hk; subst hk; rfl
  exact Eqv.appR (Eqv.appR (Eqv.appL mg (gate_app.mpr ⟨gate_ce _ _, gS⟩)
    (gate_app.mpr ⟨gate_app.mpr ⟨gC, gate_ce _ _⟩, gC⟩)))

theorem mid_rev : Eqv (rtR ++ tlR) nmR := by
  obtain ⟨_, _, _, g4, g5⟩ := goods
  have hs := passT_seq 436 _ g4
  rw [List.flatMap_append, List.flatMap_append] at hs
  set O := otherF.flatMap (fR 436)
  set S := sharedF.flatMap (fR 436)
  have gO : GateOnly O := gate_csl _ _
  have gS : GateOnly S := gate_csl _ _
  have gW : GateOnly Wr := by intro k hk; simp [Wr] at hk; rcases hk with rfl | rfl <;> rfl
  have gtop : GateOnly ([topP].flatMap (fR 436)) := gate_csl _ _
  have cSW : Eqv (S ++ Wr) (Wr ++ S) := commP _ _ gS gW (allNI_sound _ _ (by decide +kernel))
  have wt : Eqv ([topP].flatMap (fR 436) ++ Wr) (Wr ++ [topP].flatMap (fR 436)) := by
    have := wswap 436 528 878 1618 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [topP, Wr, List.flatMap] using this
  have mg := merge_rev 435 436 (sharedF ++ [topP]) g5
  rw [List.flatMap_append] at mg
  refine (Eqv.appL hs (gate_passT _ _) (gate_app.mpr ⟨gate_app.mpr ⟨gO, gS⟩, gtop⟩)).trans ?_
  have e1 : (O ++ S ++ [topP].flatMap (fR 436)) ++ tlR =
      O ++ (S ++ (([topP].flatMap (fR 436) ++ Wr) ++ fE 435 (sharedF ++ [topP]))) := by simp [tlR]
  rw [e1]
  refine (Eqv.appR (Eqv.appR (Eqv.appL wt (gate_app.mpr ⟨gtop, gW⟩) (gate_app.mpr ⟨gW, gtop⟩)))).trans ?_
  have e2 : O ++ (S ++ ((Wr ++ [topP].flatMap (fR 436)) ++ fE 435 (sharedF ++ [topP]))) =
      O ++ ((S ++ Wr) ++ ([topP].flatMap (fR 436) ++ fE 435 (sharedF ++ [topP]))) := by simp
  rw [e2]
  refine (Eqv.appR (Eqv.appL cSW (gate_app.mpr ⟨gS, gW⟩) (gate_app.mpr ⟨gW, gS⟩))).trans ?_
  have e3 : O ++ ((Wr ++ S) ++ ([topP].flatMap (fR 436) ++ fE 435 (sharedF ++ [topP]))) =
      O ++ (Wr ++ ((S ++ [topP].flatMap (fR 436)) ++ fE 435 (sharedF ++ [topP]))) := by simp
  rw [e3]
  exact Eqv.appR (Eqv.appR mg)

def portalInvM : Program :=
  (MixedFredCut.portalInvC 420).take ((MixedFredCut.portalInvC 420).length - 119)
def tickWM : Program := nmF ++ (MixedWindow.tickW 420).drop (3 * 91)
def recvWM : Program :=
  (MixedWindow.recvW 420).take ((MixedWindow.recvW 420).length - 3 * 92) ++ otherF.flatMap (fR 436)
def portalCM : Program :=
  (Wr ++ ([.CX 435 436] ++ fE 436 (sharedF ++ [topP]) ++ [.CX 435 436])) ++ (MixedFredCut.portalC 420).drop 119

theorem midF_rel : Rel 38 nmF (tlF ++ rtF) where
  run_eq m s := (mid_fwd m s).symm
  mc_eq := by decide +kernel
  tc_eq := by decide +kernel
  wires_sub := MixedFredCut.sub_of_check _ _ (by decide +kernel)
  slots_le := by decide +kernel
  phys _ := physicalGateCheck_correct _ (by decide +kernel)

theorem midR_rel : Rel 39 nmR (rtR ++ tlR) where
  run_eq m s := (mid_rev m s).symm
  mc_eq := by decide +kernel
  tc_eq := by decide +kernel
  wires_sub := MixedFredCut.sub_of_check _ _ (by decide +kernel)
  slots_le := by decide +kernel
  phys _ := physicalGateCheck_correct _ (by decide +kernel)

theorem portalF_rel :
    Rel 38 (portalInvM ++ tickWM) (MixedFredCut.portalInvC 420 ++ MixedWindow.tickW 420) := by
  have dP : MixedFredCut.portalInvC 420 = portalInvM ++ tlF := by
    rw [← pf1]; exact (List.take_append_drop _ _).symm
  have dR : MixedWindow.tickW 420 = rtF ++ (MixedWindow.tickW 420).drop (3 * 91) := by
    rw [← pf2]; exact (List.take_append_drop _ _).symm
  have h := Rel.app (Rel.refl portalInvM) (Rel.app midF_rel (Rel.refl ((MixedWindow.tickW 420).drop (3 * 91))))
  have e1 : portalInvM ++ tickWM = portalInvM ++ (nmF ++ (MixedWindow.tickW 420).drop (3 * 91)) := rfl
  rw [e1]
  conv => rhs; rw [dP, dR]
  simpa only [List.append_assoc, Nat.zero_add, Nat.add_zero] using h

theorem portalR_rel :
    Rel 39 (recvWM ++ portalCM) (MixedWindow.recvW 420 ++ MixedFredCut.portalC 420) := by
  have dU : MixedWindow.recvW 420 =
      (MixedWindow.recvW 420).take ((MixedWindow.recvW 420).length - 3 * 92) ++ rtR := by
    rw [← pr1]; exact (List.take_append_drop _ _).symm
  have dC : MixedFredCut.portalC 420 = tlR ++ (MixedFredCut.portalC 420).drop 119 := by
    rw [← pr2]; exact (List.take_append_drop _ _).symm
  have h := Rel.app (Rel.refl ((MixedWindow.recvW 420).take ((MixedWindow.recvW 420).length - 3 * 92)))
    (Rel.app midR_rel (Rel.refl ((MixedFredCut.portalC 420).drop 119)))
  have e1 : recvWM ++ portalCM =
      (MixedWindow.recvW 420).take ((MixedWindow.recvW 420).length - 3 * 92) ++
        (nmR ++ (MixedFredCut.portalC 420).drop 119) := by
    simp only [recvWM, portalCM, nmR, List.append_assoc]
  rw [e1]
  conv => rhs; rw [dU, dC]
  simpa only [List.append_assoc, Nat.zero_add, Nat.add_zero] using h

/-! Forward window list with merged enter/first-tick boundaries. -/

def e15 (j : Fin 26) : Program := enterM (MixedFredCut.enter15C j)
def r15 (j : Fin 26) : Program := routedM (Shadow7.routed j 0 1) (nP15 j) (port15 j)
def e20 (j : Fin 9) : Program := enterM (MixedFredCut.enter20C j)
def r20 (j : Fin 9) : Program := routedM (routed20 j 0 1) (nP20 j) (port20 j)
def u15 (j : Fin 26) : Program := unroutedM (Shadow7.unrouted j 0 1) (nP15 j)
def i15 (j : Fin 26) : Program := enterInvM (MixedFredCut.enterInv15C j) (port15 j)
def u20 (j : Fin 9) : Program := unroutedM (unrouted20 j 0 1) (nP20 j)
def i20 (j : Fin 9) : Program := enterInvM (MixedFredCut.enterInv20C j) (port20 j)

def block15FM (d : Bool) (i j : Fin 26) : List Program :=
  [e15 j, r15 j, MixedWindow.packW d (start j) (start j - 10),
   Shadow7.archiveLoadP i d, Shadow7.routed j 1 14, MixedFredCut.leave15C j]

def block20FM (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if h : j.val = 0 then
    [e20 j, r20 j, MixedWindow.packW d 165 155, archiveLoad150To20 d, routed20 j 1 19, MixedFredCut.leave20C j]
  else
    [e20 j, r20 j, MixedWindow.packW d s (s - 15), MixedWindow.packW d s (s - 10),
     archiveLoadP20 ⟨j.val - 1, by omega⟩ d, routed20 j 1 19, MixedFredCut.leave20C j]

def forwardLCM (d : Bool) : List Program :=
  [MixedFredCut.portalC 45, e15 MixedWindow.j0, r15 MixedWindow.j0, MixedWindow.packW d 45 45,
   Shadow7.routed MixedWindow.j0 1 14, MixedFredCut.leave15C MixedWindow.j0] ++
  (MixedWindow.prefixPairs.flatMap fun p => block15FM d p.1 p.2) ++
  [e15 MixedWindow.j7, r15 MixedWindow.j7, MixedWindow.packW d 150 140,
   Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, MixedFredCut.leave150C] ++
  ((List.finRange 9).flatMap (block20FM d)) ++
  [e15 MixedWindow.j20, r15 MixedWindow.j20, MixedWindow.packW d 345 330, MixedWindow.packW d 345 335,
   archiveLoadP20 MixedWindow.k8 d, Shadow7.routed MixedWindow.j20 1 14, MixedFredCut.leave15C MixedWindow.j20] ++
  (MixedWindow.suffixPairs.flatMap fun p => block15FM d p.1 p.2) ++
  [Shadow7.parkP 420, portalInvM, tickWM, MixedWindow.packW d 420 410, Shadow7.exitLoadP 420 d]

theorem block15F_rel (d : Bool) (i j : Fin 26) (h : j.val ≤ 7 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) :
    LRel 2 (block15FM d i j) (MixedFredCut.block15FC d i j) :=
  (LRel.pair _ _ _ _ (pairF15 j h) (LRel.refl _)).cast rfl

theorem block20F_rel (d : Bool) (j : Fin 9) : LRel 2 (block20FM d j) (MixedFredCut.block20FC d j) := by
  by_cases h : j.val = 0
  · simp only [block20FM, MixedFredCut.block20FC, h, ↓reduceDIte]
    exact (LRel.pair _ _ _ _ (pairF20 j) (LRel.refl _)).cast rfl
  · simp only [block20FM, MixedFredCut.block20FC, h, ↓reduceDIte]
    exact (LRel.pair _ _ _ _ (pairF20 j) (LRel.refl _)).cast rfl

theorem forward_rel (d : Bool) : LRel 82 (forwardLCM d) (MixedFredCut.forwardLC d) := by
  unfold forwardLCM MixedFredCut.forwardLC
  have h0 := LRel.keep (MixedFredCut.portalC 45)
    (LRel.pair _ _ _ _ (pairF15 MixedWindow.j0 (by decide)) (LRel.refl [MixedWindow.packW d 45 45,
      Shadow7.routed MixedWindow.j0 1 14, MixedFredCut.leave15C MixedWindow.j0]))
  have h1 := LRel.flatMap MixedWindow.prefixPairs (fun p => block15FM d p.1 p.2)
    (fun p => MixedFredCut.block15FC d p.1 p.2) 2 (fun x hx => block15F_rel d x.1 x.2 (by
      simp only [MixedWindow.prefixPairs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  have h7 := LRel.pair _ _ _ _ (pairF15 MixedWindow.j7 (by decide)) (LRel.refl [MixedWindow.packW d 150 140,
      Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, MixedFredCut.leave150C])
  have h2 := LRel.flatMap (List.finRange 9) (block20FM d) (MixedFredCut.block20FC d) 2
    (fun x _ => block20F_rel d x)
  have h20 := LRel.pair _ _ _ _ (pairF15 MixedWindow.j20 (by decide)) (LRel.refl [MixedWindow.packW d 345 330,
      MixedWindow.packW d 345 335, archiveLoadP20 MixedWindow.k8 d, Shadow7.routed MixedWindow.j20 1 14,
      MixedFredCut.leave15C MixedWindow.j20])
  have h3 := LRel.flatMap MixedWindow.suffixPairs (fun p => block15FM d p.1 p.2)
    (fun p => MixedFredCut.block15FC d p.1 p.2) 2 (fun x hx => block15F_rel d x.1 x.2 (by
      simp only [MixedWindow.suffixPairs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide))
  have he := LRel.keep (Shadow7.parkP 420) (LRel.pair _ _ _ _ portalF_rel
    (LRel.refl [MixedWindow.packW d 420 410, Shadow7.exitLoadP 420 d]))
  exact ((((((h0.app h1).app h7).app h2).app h20).app h3).app he).cast (by
    simp [MixedWindow.prefixPairs, MixedWindow.suffixPairs])

/-! Reverse window list with merged first-untick/inverse-enter boundaries. -/

def block15RM (d : Bool) (i j : Fin 26) : List Program :=
  [MixedFredCut.unleave15C j, TickCut.Hosted.unroutedHigh j 1 14, Shadow7.archiveRestoreP i d,
   MixedWindow.unpackW d (start j) (start j - 10), u15 j, i15 j]

def block20RM (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if h : j.val = 0 then
    [MixedFredCut.unleave20C j, TickCut.Wide.unroutedHigh j 1 19, archiveRestore150To20 d,
     MixedWindow.unpackW d 165 155, u20 j, i20 j]
  else
    [MixedFredCut.unleave20C j, TickCut.Wide.unroutedHigh j 1 19, archiveRestoreP20 ⟨j.val - 1, by omega⟩ d,
     MixedWindow.unpackW d s (s - 10), MixedWindow.unpackW d s (s - 15), u20 j, i20 j]

def reverseLCM (d : Bool) : List Program :=
  [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, recvWM, portalCM, Shadow7.parkInvP 420] ++
  (MixedWindow.suffixPairs.reverse.flatMap fun p => block15RM d p.1 p.2) ++
  [MixedFredCut.unleave15C MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
   archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
   u15 MixedWindow.j20, i15 MixedWindow.j20] ++
  ((List.finRange 9).reverse.flatMap (block20RM d)) ++
  [MixedFredCut.unleave150C, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14,
   Shadow7.archiveRestoreP MixedWindow.j6 d, MixedWindow.unpackW d 150 140,
   u15 MixedWindow.j7, i15 MixedWindow.j7] ++
  (MixedWindow.prefixPairs.reverse.flatMap fun p => block15RM d p.1 p.2) ++
  [MixedFredCut.unleave15C MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
   MixedWindow.unpackW d 45 45, u15 MixedWindow.j0, i15 MixedWindow.j0, MixedFredCut.portalInvC 45]

theorem block15R_rel (d : Bool) (i j : Fin 26) (h : j.val ≤ 7 ∨ (20 ≤ j.val ∧ j.val ≤ 24)) :
    LRel 2 (block15RM d i j) (TickCut.Mixed.block15RC d i j) :=
  LRel.keep _ (LRel.keep _ (LRel.keep _ (LRel.keep _
    ((LRel.pair _ _ _ _ (pairR15 j h) (LRel.refl [])).cast rfl))))

theorem block20R_rel (d : Bool) (j : Fin 9) : LRel 2 (block20RM d j) (TickCut.Mixed.block20RC d j) := by
  by_cases h : j.val = 0
  · simp only [block20RM, TickCut.Mixed.block20RC, h, ↓reduceDIte]
    exact LRel.keep _ (LRel.keep _ (LRel.keep _ (LRel.keep _
      ((LRel.pair _ _ _ _ (pairR20 j) (LRel.refl [])).cast rfl))))
  · simp only [block20RM, TickCut.Mixed.block20RC, h, ↓reduceDIte]
    exact LRel.keep _ (LRel.keep _ (LRel.keep _ (LRel.keep _ (LRel.keep _
      ((LRel.pair _ _ _ _ (pairR20 j) (LRel.refl [])).cast rfl)))))

theorem reverse_rel (d : Bool) : LRel 83 (reverseLCM d) (TickCut.Mixed.reverseLC d) := by
  unfold reverseLCM TickCut.Mixed.reverseLC
  have he := LRel.keep (Shadow7.exitRestoreP 420 d) (LRel.keep (MixedWindow.unpackW d 420 410)
    (LRel.pair _ _ _ _ portalR_rel (LRel.refl [Shadow7.parkInvP 420])))
  have h3 := LRel.flatMap MixedWindow.suffixPairs.reverse (fun p => block15RM d p.1 p.2)
    (fun p => TickCut.Mixed.block15RC d p.1 p.2) 2 (fun x hx => block15R_rel d x.1 x.2 (by
      simp only [MixedWindow.suffixPairs, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> decide))
  have h20 := LRel.keep (MixedFredCut.unleave15C MixedWindow.j20)
    (LRel.keep (TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14)
    (LRel.keep (archiveRestoreP20 MixedWindow.k8 d) (LRel.keep (MixedWindow.unpackW d 345 335)
    (LRel.keep (MixedWindow.unpackW d 345 330)
    ((LRel.pair _ _ _ _ (pairR15 MixedWindow.j20 (by decide)) (LRel.refl [])).cast rfl)))))
  have h2 := LRel.flatMap (List.finRange 9).reverse (block20RM d) (TickCut.Mixed.block20RC d) 2
    (fun x _ => block20R_rel d x)
  have h7 := LRel.keep MixedFredCut.unleave150C (LRel.keep (TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14)
    (LRel.keep (Shadow7.archiveRestoreP MixedWindow.j6 d) (LRel.keep (MixedWindow.unpackW d 150 140)
    ((LRel.pair _ _ _ _ (pairR15 MixedWindow.j7 (by decide)) (LRel.refl [])).cast rfl))))
  have h1 := LRel.flatMap MixedWindow.prefixPairs.reverse (fun p => block15RM d p.1 p.2)
    (fun p => TickCut.Mixed.block15RC d p.1 p.2) 2 (fun x hx => block15R_rel d x.1 x.2 (by
      simp only [MixedWindow.prefixPairs, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
  have h0 := LRel.keep (MixedFredCut.unleave15C MixedWindow.j0)
    (LRel.keep (TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14) (LRel.keep (MixedWindow.unpackW d 45 45)
    (LRel.pair _ _ _ _ (pairR15 MixedWindow.j0 (by decide)) (LRel.refl [MixedFredCut.portalInvC 45]))))
  exact ((((((he.app h3).app h20).app h2).app h7).app h1).app h0).cast (by
    simp [MixedWindow.prefixPairs, MixedWindow.suffixPairs])

/-! ### Exit merge

The last 15-tick block (`j = 24`) leaves through `fE 435 ps8`, a Fredkin under the leave control
`435` on the eight rail pairs `482..489 ↔ 832..839`; nothing after it in the leave, the park, the
inverse portal or the first 45 routed pairs of tick 420 touches those sixteen wires or `435`.
Tick 420 then exchanges the same eight pairs under its route control `436`. The two exchanges
compose to one exchange under `435 ⊕ 436`, which saves eight Toffolis per forward walk. -/

def ps8 : List (Wire × Wire) := (List.range 8).map fun k => (482 + k, 832 + k)
def other45 : List (Wire × Wire) := (List.range 45).map fun k => (437 + k, 787 + k)
def jL : Fin 26 := ⟨24, by decide⟩
def leaveA : Program := (MixedFredCut.leave15C jL).take 4471
def leaveB : Program := (MixedFredCut.leave15C jL).drop 4495
def leaveX : Program := leaveA ++ leaveB
def nmX : Program :=
  other45.flatMap (fR 436) ++ (([.CX 435 436] ++ fE 436 ps8 ++ [.CX 435 436]) ++
    (fE 435 [topP] ++ (([.CX 435 436] ++ fE 436 sharedF ++ [.CX 435 436]) ++ Wx)))
def tickWX : Program := nmX ++ (MixedWindow.tickW 420).drop (3 * 91)

theorem leave_split_of (h : ((MixedFredCut.leave15C jL).drop 4471).take 24 = fE 435 ps8) :
    MixedFredCut.leave15C jL = leaveA ++ (fE 435 ps8 ++ leaveB) := by
  unfold leaveA leaveB
  have h3 : ((MixedFredCut.leave15C jL).drop 4471).drop 24 = (MixedFredCut.leave15C jL).drop 4495 := by
    rw [List.drop_drop]
  have e : (MixedFredCut.leave15C jL).drop 4471 = fE 435 ps8 ++ (MixedFredCut.leave15C jL).drop 4495 := by
    rw [← List.take_append_drop 24 ((MixedFredCut.leave15C jL).drop 4471), h, h3]
  conv_lhs => rw [← List.take_append_drop 4471 (MixedFredCut.leave15C jL)]
  rw [e]

theorem other_split : otherF = other45 ++ ps8 := by decide

theorem eqv_comm_disj (p q : Program) (hp : measurementCount p = 0)
    (hd : Disjoint (wires p) (wires q)) : Eqv (p ++ q) (q ++ p) := by
  intro m s
  have hp0 : ∀ (t : List Bool) (u : State), run p t u = run p [] u := by
    intro t u
    rw [← run_take p t u, hp, List.take_zero]
  rw [run_append, run_append, hp, List.take_zero, List.drop_zero, hp0 (m.drop _),
    ← run_take q m (run p [] s)]
  exact run_disjoint_commute q p hd.symm _ [] s

theorem Eqv.appLm {P P' Q : Program} (hP : Eqv P P') (hm : measurementCount P = measurementCount P') :
    Eqv (P ++ Q) (P' ++ Q) := by
  intro m s
  rw [run_append, run_append, hm, hP]

theorem Rel.trans {a b : Nat} {P Q R : Program} (h1 : Rel a P Q) (h2 : Rel b Q R) : Rel (a + b) P R where
  run_eq m s := (h1.run_eq m s).trans (h2.run_eq m s)
  mc_eq := h1.mc_eq.trans h2.mc_eq
  tc_eq := by have := h1.tc_eq; have := h2.tc_eq; omega
  wires_sub := h1.wires_sub.trans h2.wires_sub
  slots_le := h1.slots_le.trans h2.slots_le
  phys h := h1.phys (h2.phys h)

/-- Everything between the leave's exchange and tick 420's exchange of the same pairs. -/
def midY : Program := leaveB ++ (Shadow7.parkP 420 ++ (portalInvM ++ other45.flatMap (fR 436)))

theorem disj_mask (E M : Program)
    (h : (MixedFredCut.wl E).all (fun q => !(StairLoan.maskOf (MixedFredCut.wl M)).testBit q) = true) :
    Disjoint (wires E) (wires M) := by
  refine Finset.disjoint_left.mpr (MixedFredCut.avoid_of_check E M ?_)
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have h1 := h q hq
  rw [StairLoan.testBit_maskOf] at h1
  simpa using h1

theorem sub_mask (D E : Program)
    (h : (MixedFredCut.wl D).all (fun q => (StairLoan.maskOf (MixedFredCut.wl E)).testBit q) = true) :
    wires D ⊆ wires E := by
  refine MixedFredCut.sub_of_check D E ?_
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have h1 := h q hq
  rw [StairLoan.testBit_maskOf] at h1
  simpa using h1

theorem leave_facts : ((MixedFredCut.leave15C jL).drop 4471).take 24 = fE 435 ps8 ∧
    (MixedFredCut.wl (fE 435 ps8)).all (fun q => !(StairLoan.maskOf (MixedFredCut.wl midY)).testBit q) = true := by
  decide +kernel

theorem leave_split : MixedFredCut.leave15C jL = leaveA ++ (fE 435 ps8 ++ leaveB) :=
  leave_split_of leave_facts.1

theorem midY_disj : Disjoint (wires (fE 435 ps8)) (wires midY) := disj_mask _ _ leave_facts.2

theorem mc_L8 : measurementCount (fE 435 ps8) = 0 := by decide
theorem tc_L8 : toffoliCount (fE 435 ps8) = 8 := by decide
theorem good8 : Good [435, 436] ps8 := by unfold Good; decide

def tailX : Program :=
  fE 435 [topP] ++ (([.CX 435 436] ++ fE 436 sharedF ++ [.CX 435 436]) ++ Wx)

theorem nmF_split : nmF = other45.flatMap (fR 436) ++ (ps8.flatMap (fR 436) ++ tailX) := by
  simp only [nmF, other_split, List.flatMap_append, List.append_assoc, tailX]

theorem nmX_eq : nmX = other45.flatMap (fR 436) ++ (([.CX 435 436] ++ fE 436 ps8 ++ [.CX 435 436]) ++ tailX) := by
  simp only [nmX, tailX]

theorem exit_eqv (R : Program) :
    Eqv (leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmX ++ R))))
      (MixedFredCut.leave15C jL ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmF ++ R)))) := by
  rw [leave_split, nmF_split, nmX_eq]
  have gL : GateOnly (fE 435 ps8) := gate_ce _ _
  have gO : GateOnly (ps8.flatMap (fR 436)) := gate_csl _ _
  have gC : GateOnly ([.CX 435 436] ++ fE 436 ps8 ++ [.CX 435 436]) := by
    have g1 : GateOnly [Instr.CX 435 436] := by intro k hk; simp at hk; subst hk; rfl
    exact gate_app.mpr ⟨gate_app.mpr ⟨g1, gate_ce _ _⟩, g1⟩
  have mg := merge_fwd 435 436 ps8 good8
  have cm := eqv_comm_disj (fE 435 ps8) midY mc_L8 midY_disj
  -- new side: A ++ (Y ++ ((C ++ F8 ++ C) ++ (tailX ++ R)))
  -- old side: A ++ ((L8 ++ Y) ++ (O8 ++ (tailX ++ R)))
  have eNew : leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++
      ((other45.flatMap (fR 436) ++ (([.CX 435 436] ++ fE 436 ps8 ++ [.CX 435 436]) ++ tailX)) ++ R))) =
      leaveA ++ (midY ++ (([.CX 435 436] ++ fE 436 ps8 ++ [.CX 435 436]) ++ (tailX ++ R))) := by
    simp only [leaveX, midY, List.append_assoc]
  have eOld : leaveA ++ (fE 435 ps8 ++ leaveB) ++ (Shadow7.parkP 420 ++ (portalInvM ++
      ((other45.flatMap (fR 436) ++ (ps8.flatMap (fR 436) ++ tailX)) ++ R))) =
      leaveA ++ ((fE 435 ps8 ++ midY) ++ (ps8.flatMap (fR 436) ++ (tailX ++ R))) := by
    simp only [midY, List.append_assoc]
  rw [eNew, eOld]
  refine Eqv.appR ?_
  have m1 : measurementCount (fE 435 ps8 ++ midY) = measurementCount (midY ++ fE 435 ps8) := by
    simp only [measurementCount_append]; omega
  refine Eqv.trans ?_ (Eqv.symm (Eqv.appLm cm m1))
  have e3 : midY ++ fE 435 ps8 ++ (ps8.flatMap (fR 436) ++ (tailX ++ R)) =
      midY ++ ((fE 435 ps8 ++ ps8.flatMap (fR 436)) ++ (tailX ++ R)) := by
    simp only [List.append_assoc]
  rw [e3]
  refine Eqv.appR ?_
  exact Eqv.symm (Eqv.appL mg (gate_app.mpr ⟨gL, gO⟩) gC)

theorem nm_facts : toffoliCount nmX = toffoliCount nmF ∧ measurementCount nmX = 0 ∧
    measurementCount nmF = 0 ∧ gateSlots nmX ≤ gateSlots nmF + gateSlots (fE 435 ps8) ∧
    (MixedFredCut.wl nmX).all (fun q => (StairLoan.maskOf (MixedFredCut.wl nmF)).testBit q) = true ∧
    nmX.all physicalGateCheck = true := by
  decide +kernel
theorem tc_nm : toffoliCount nmX = toffoliCount nmF := nm_facts.1
theorem mc_nmX : measurementCount nmX = 0 := nm_facts.2.1
theorem mc_nmF : measurementCount nmF = 0 := nm_facts.2.2.1
theorem gs_nm : gateSlots nmX ≤ gateSlots nmF + gateSlots (fE 435 ps8) := nm_facts.2.2.2.1
theorem w_nm : wires nmX ⊆ wires nmF := sub_mask _ _ nm_facts.2.2.2.2.1
theorem phys_nmX : GatePhysical nmX := physicalGateCheck_correct _ nm_facts.2.2.2.2.2

theorem leave_mc : measurementCount (MixedFredCut.leave15C jL) = measurementCount leaveX := by
  rw [leave_split]; simp only [leaveX, measurementCount_append, mc_L8]; omega

theorem leave_tc : toffoliCount (MixedFredCut.leave15C jL) = toffoliCount leaveX + 8 := by
  rw [leave_split]; simp only [leaveX, toffoliCount_append, tc_L8]; omega

theorem leave_gs : gateSlots leaveX + gateSlots (fE 435 ps8) = gateSlots (MixedFredCut.leave15C jL) := by
  rw [leave_split]; simp only [leaveX, gateSlots_append]; omega

theorem leave_w : wires leaveX ⊆ wires (MixedFredCut.leave15C jL) := by
  rw [leave_split, leaveX, wires_append, wires_append, wires_append]
  exact Finset.union_subset_union (Finset.Subset.refl _) Finset.subset_union_right

theorem leave_phys (h : GatePhysical (MixedFredCut.leave15C jL)) : GatePhysical leaveX := by
  rw [leave_split] at h
  simp only [leaveX, gatePhysical_append] at h ⊢
  exact ⟨h.1, h.2.2⟩

theorem exit_mc (R : Program) :
    measurementCount (leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmX ++ R)))) =
      measurementCount (MixedFredCut.leave15C jL ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmF ++ R)))) := by
  simp only [measurementCount_append, leave_mc, mc_nmX, mc_nmF]

theorem exit_tc (R : Program) :
    toffoliCount (leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmX ++ R)))) + 8 =
      toffoliCount (MixedFredCut.leave15C jL ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmF ++ R)))) := by
  simp only [toffoliCount_append, leave_tc, tc_nm]
  omega

theorem exit_w (R : Program) :
    wires (leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmX ++ R)))) ⊆
      wires (MixedFredCut.leave15C jL ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmF ++ R)))) := by
  simp only [wires_append]
  exact Finset.union_subset_union leave_w (Finset.union_subset_union (Finset.Subset.refl _)
    (Finset.union_subset_union (Finset.Subset.refl _) (Finset.union_subset_union w_nm (Finset.Subset.refl _))))

theorem exit_gs (R : Program) :
    gateSlots (leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmX ++ R)))) ≤
      gateSlots (MixedFredCut.leave15C jL ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmF ++ R)))) := by
  simp only [gateSlots_append]
  have h1 := leave_gs
  have h2 := gs_nm
  omega

theorem exit_phys (R : Program)
    (h : GatePhysical (MixedFredCut.leave15C jL ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmF ++ R))))) :
    GatePhysical (leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmX ++ R)))) := by
  simp only [gatePhysical_append] at h ⊢
  exact ⟨leave_phys h.1, h.2.1, h.2.2.1, phys_nmX, h.2.2.2.2⟩

theorem exit_rel (R : Program) :
    Rel 8 (leaveX ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmX ++ R))))
      (MixedFredCut.leave15C jL ++ (Shadow7.parkP 420 ++ (portalInvM ++ (nmF ++ R)))) :=
  ⟨exit_eqv R, exit_mc R, exit_tc R, exit_w R, exit_gs R, exit_phys R⟩

def jL' : Fin 26 := ⟨23, by decide⟩

def forwardPreX (d : Bool) : List Program :=
  [MixedFredCut.portalC 45, e15 MixedWindow.j0, r15 MixedWindow.j0, MixedWindow.packW d 45 45,
   Shadow7.routed MixedWindow.j0 1 14, MixedFredCut.leave15C MixedWindow.j0] ++
  (MixedWindow.prefixPairs.flatMap fun p => block15FM d p.1 p.2) ++
  [e15 MixedWindow.j7, r15 MixedWindow.j7, MixedWindow.packW d 150 140,
   Shadow7.archiveLoadP MixedWindow.j6 d, Shadow7.routed MixedWindow.j7 1 14, MixedFredCut.leave150C] ++
  ((List.finRange 9).flatMap (block20FM d)) ++
  [e15 MixedWindow.j20, r15 MixedWindow.j20, MixedWindow.packW d 345 330, MixedWindow.packW d 345 335,
   archiveLoadP20 MixedWindow.k8 d, Shadow7.routed MixedWindow.j20 1 14, MixedFredCut.leave15C MixedWindow.j20] ++
  ([(⟨20, by decide⟩, ⟨21, by decide⟩), (⟨21, by decide⟩, ⟨22, by decide⟩), (⟨22, by decide⟩, ⟨23, by decide⟩)].flatMap
    fun (p : Fin 26 × Fin 26) => block15FM d p.1 p.2) ++
  [e15 jL, r15 jL, MixedWindow.packW d (start jL) (start jL - 10), Shadow7.archiveLoadP jL' d, Shadow7.routed jL 1 14]

def forwardLCX (d : Bool) : List Program :=
  forwardPreX d ++ [leaveX, Shadow7.parkP 420, portalInvM, tickWX, MixedWindow.packW d 420 410, Shadow7.exitLoadP 420 d]

theorem forwardLCM_eq (d : Bool) : forwardLCM d = forwardPreX d ++
    [MixedFredCut.leave15C jL, Shadow7.parkP 420, portalInvM, tickWM, MixedWindow.packW d 420 410,
     Shadow7.exitLoadP 420 d] := by
  simp only [forwardLCM, forwardPreX, MixedWindow.suffixPairs, List.flatMap_cons, List.flatMap_nil,
    block15FM, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  rfl

theorem tail_rel (d : Bool) :
    LRel 8 [leaveX, Shadow7.parkP 420, portalInvM, tickWX, MixedWindow.packW d 420 410, Shadow7.exitLoadP 420 d]
      [MixedFredCut.leave15C jL, Shadow7.parkP 420, portalInvM, tickWM, MixedWindow.packW d 420 410,
       Shadow7.exitLoadP 420 d] := by
  unfold LRel
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, tickWX, tickWM, List.append_assoc]
  exact exit_rel _

theorem forward_relX (d : Bool) : LRel 90 (forwardLCX d) (MixedFredCut.forwardLC d) := by
  have h1 : LRel 8 (forwardLCX d) (forwardLCM d) := by
    rw [forwardLCM_eq]
    exact (LRel.app (LRel.refl (forwardPreX d)) (tail_rel d)).cast (by omega)
  exact Rel.trans h1 (forward_rel d)

/-! ### Reverse exit merge

The mirror of the exit merge in the reverse walks. The merged receiver untick of tick 420 (`recvWM`) ends
with the exchange of the eight pairs `ps8` under `436` (`ps8.flatMap (fR 436)`, its last 24 gates). The reverse
portal `portalCM`, the inverse park and the first 142 gates of block 24's unleave never write those sixteen
wires, `435` or `436` (the portal brackets its own exchanges by `CX 435 436` and is measurement-free on that
stretch), and the unleave then exchanges the same pairs under `435` (`fE 435 ps8.reverse`). Moving the second
exchange back next to the first and composing the two gives one exchange under `435 ⊕ 436`, which saves eight
Toffolis per reverse walk. -/

def recvA : Program := recvWM.take 1329
def mergedX : Program := [.CX 435 436] ++ fE 436 ps8 ++ [.CX 435 436]
def recvX : Program := recvA ++ mergedX
def unA : Program := (MixedFredCut.unleave15C jL).take 142
def unB : Program := (MixedFredCut.unleave15C jL).drop 166
def unleaveX : Program := unA ++ unB
def portA : Program := portalCM.take 121
def portB : Program := portalCM.drop 121
/-- Everything between the moved exchange's new and old positions, after the portal's gate-only head. -/
def midR : Program := portB ++ (Shadow7.parkInvP 420 ++ unA)

theorem rexit_facts :
    recvWM.drop 1329 = ps8.flatMap (fR 436) ∧
    ((MixedFredCut.unleave15C jL).drop 142).take 24 = fE 435 ps8.reverse ∧
    (MixedFredCut.wl (fE 435 ps8.reverse)).all
      (fun q => !(StairLoan.maskOf (MixedFredCut.wl midR)).testBit q) = true ∧
    portA.all isGate = true := by
  decide +kernel

theorem rexit_small :
    toffoliCount (ps8.flatMap (fR 436)) = 8 ∧ toffoliCount (fE 435 ps8.reverse) = 8 ∧
    toffoliCount mergedX = 8 ∧ measurementCount (ps8.flatMap (fR 436)) = 0 ∧
    measurementCount (fE 435 ps8.reverse) = 0 ∧ measurementCount mergedX = 0 ∧
    gateSlots mergedX ≤ gateSlots (ps8.flatMap (fR 436)) + gateSlots (fE 435 ps8.reverse) ∧
    (MixedFredCut.wl mergedX).all
      (fun q => (StairLoan.maskOf (MixedFredCut.wl (ps8.flatMap (fR 436) ++ fE 435 ps8.reverse))).testBit q) = true ∧
    mergedX.all physicalGateCheck = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem portA_nonint : ∀ i ∈ portA, ∀ j ∈ fE 435 ps8.reverse, NonInt i j := by
  unfold NonInt
  decide +kernel

theorem good8a : Good [435] ps8 := by unfold Good; decide

theorem recv_split : recvWM = recvA ++ ps8.flatMap (fR 436) := by
  rw [← rexit_facts.1]; exact (List.take_append_drop 1329 recvWM).symm

theorem unleave_split : MixedFredCut.unleave15C jL = unA ++ (fE 435 ps8.reverse ++ unB) := by
  unfold unA unB
  have h3 : ((MixedFredCut.unleave15C jL).drop 142).drop 24 = (MixedFredCut.unleave15C jL).drop 166 := by
    rw [List.drop_drop]
  have e : (MixedFredCut.unleave15C jL).drop 142 = fE 435 ps8.reverse ++ (MixedFredCut.unleave15C jL).drop 166 := by
    rw [← List.take_append_drop 24 ((MixedFredCut.unleave15C jL).drop 142), rexit_facts.2.1, h3]
  conv_lhs => rw [← List.take_append_drop 142 (MixedFredCut.unleave15C jL)]
  rw [e]

theorem portal_split : portalCM = portA ++ portB := (List.take_append_drop 121 portalCM).symm

theorem rexit_eqv (R : Program) :
    Eqv (recvX ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R))))
      (recvWM ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (MixedFredCut.unleave15C jL ++ R)))) := by
  rw [recv_split, unleave_split, portal_split]
  have gA : GateOnly portA := fun i hi => List.all_eq_true.mp rexit_facts.2.2.2 i hi
  have gE : GateOnly (fE 435 ps8.reverse) := gate_ce _ _
  have gF : GateOnly (ps8.flatMap (fR 436)) := gate_csl _ _
  have gM : GateOnly mergedX := by
    have g1 : GateOnly [Instr.CX 435 436] := by intro k hk; simp at hk; subst hk; rfl
    exact gate_app.mpr ⟨gate_app.mpr ⟨g1, gate_ce _ _⟩, g1⟩
  have dj : Disjoint (wires (fE 435 ps8.reverse)) (wires midR) := disj_mask _ _ rexit_facts.2.2.1
  have eNew : recvX ++ ((portA ++ portB) ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R))) =
      recvA ++ (mergedX ++ (portA ++ (midR ++ (unB ++ R)))) := by
    simp only [recvX, unleaveX, midR, List.append_assoc]
  have eOld : recvA ++ ps8.flatMap (fR 436) ++ ((portA ++ portB) ++ (Shadow7.parkInvP 420 ++
      (unA ++ (fE 435 ps8.reverse ++ unB) ++ R))) =
      recvA ++ (ps8.flatMap (fR 436) ++ (portA ++ (midR ++ (fE 435 ps8.reverse ++ (unB ++ R))))) := by
    simp only [midR, List.append_assoc]
  rw [eNew, eOld]
  refine Eqv.appR ?_
  -- 1. the unleave's exchange moves back over `midR` (disjoint wires)
  have s1 : Eqv (midR ++ (fE 435 ps8.reverse ++ (unB ++ R))) (fE 435 ps8.reverse ++ (midR ++ (unB ++ R))) := by
    have cm := eqv_comm_disj (fE 435 ps8.reverse) midR rexit_small.2.2.2.2.1 dj
    have m1 : measurementCount (midR ++ fE 435 ps8.reverse) = measurementCount (fE 435 ps8.reverse ++ midR) := by
      simp only [measurementCount_append]; omega
    have := Eqv.appLm (Q := unB ++ R) (Eqv.symm cm) m1
    simpa only [List.append_assoc] using this
  -- 2. and over the portal's gate-only head (only read-only sharing of `435`)
  have s2 : Eqv (portA ++ (fE 435 ps8.reverse ++ (midR ++ (unB ++ R))))
      (fE 435 ps8.reverse ++ (portA ++ (midR ++ (unB ++ R)))) := by
    have cm := commP portA (fE 435 ps8.reverse) gA gE portA_nonint
    have := Eqv.appL (Q := midR ++ (unB ++ R)) cm (gate_app.mpr ⟨gA, gE⟩) (gate_app.mpr ⟨gE, gA⟩)
    simpa only [List.append_assoc] using this
  -- 3. the two adjacent exchanges compose into one under `435 ⊕ 436`
  have s3 : Eqv (ps8.flatMap (fR 436) ++ (fE 435 ps8.reverse ++ (portA ++ (midR ++ (unB ++ R)))))
      (mergedX ++ (portA ++ (midR ++ (unB ++ R)))) := by
    have t1 : Eqv (ps8.flatMap (fR 436) ++ fE 435 ps8.reverse) (ps8.flatMap (fR 436) ++ fE 435 ps8) :=
      Eqv.appR (fE_rev 435 ps8 good8a)
    have t2 : Eqv (ps8.flatMap (fR 436) ++ fE 435 ps8) mergedX := merge_rev 435 436 ps8 good8
    have := Eqv.appL (Q := portA ++ (midR ++ (unB ++ R))) (t1.trans t2) (gate_app.mpr ⟨gF, gE⟩) gM
    simpa only [List.append_assoc] using this
  refine Eqv.symm ?_
  exact (Eqv.appR (Eqv.appR s1)).trans ((Eqv.appR s2).trans s3)

theorem rexit_mc (R : Program) :
    measurementCount (recvX ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R)))) =
      measurementCount (recvWM ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (MixedFredCut.unleave15C jL ++ R)))) := by
  rw [recv_split, unleave_split]
  have h := rexit_small
  simp only [recvX, unleaveX, measurementCount_append]
  omega

theorem rexit_tc (R : Program) :
    toffoliCount (recvX ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R)))) + 8 =
      toffoliCount (recvWM ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (MixedFredCut.unleave15C jL ++ R)))) := by
  rw [recv_split, unleave_split]
  have h := rexit_small
  simp only [recvX, unleaveX, toffoliCount_append]
  omega

theorem rexit_gs (R : Program) :
    gateSlots (recvX ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R)))) ≤
      gateSlots (recvWM ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (MixedFredCut.unleave15C jL ++ R)))) := by
  rw [recv_split, unleave_split]
  have h := rexit_small.2.2.2.2.2.2.1
  simp only [recvX, unleaveX, gateSlots_append]
  omega

theorem rexit_w (R : Program) :
    wires (recvX ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R)))) ⊆
      wires (recvWM ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (MixedFredCut.unleave15C jL ++ R)))) := by
  rw [recv_split, unleave_split]
  have hm := sub_mask _ _ rexit_small.2.2.2.2.2.2.2.1
  intro q hq
  simp only [recvX, unleaveX, wires_append, Finset.mem_union] at hq hm ⊢
  rcases hq with (h | h) | h | h | (h | h) | h
  · exact Or.inl (Or.inl h)
  · rcases Finset.mem_union.mp (hm h) with h' | h'
    · exact Or.inl (Or.inr h')
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h')))))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem rexit_phys (R : Program)
    (h : GatePhysical (recvWM ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (MixedFredCut.unleave15C jL ++ R))))) :
    GatePhysical (recvX ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R)))) := by
  rw [recv_split, unleave_split] at h
  have pm := physicalGateCheck_correct _ rexit_small.2.2.2.2.2.2.2.2
  simp only [recvX, unleaveX, gatePhysical_append] at h ⊢
  exact ⟨⟨h.1.1, pm⟩, h.2.1, h.2.2.1, ⟨h.2.2.2.1.1, h.2.2.2.1.2.2⟩, h.2.2.2.2⟩

theorem rexit_rel (R : Program) :
    Rel 8 (recvX ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (unleaveX ++ R))))
      (recvWM ++ (portalCM ++ (Shadow7.parkInvP 420 ++ (MixedFredCut.unleave15C jL ++ R)))) :=
  ⟨rexit_eqv R, rexit_mc R, rexit_tc R, rexit_w R, rexit_gs R, rexit_phys R⟩

/-- The reverse window list after block 24's unleave. -/
def reversePostX (d : Bool) : List Program :=
  [TickCut.Hosted.unroutedHigh jL 1 14, Shadow7.archiveRestoreP jL' d,
   MixedWindow.unpackW d (start jL) (start jL - 10), u15 jL, i15 jL] ++
  ([(⟨22, by decide⟩, ⟨23, by decide⟩), (⟨21, by decide⟩, ⟨22, by decide⟩), (⟨20, by decide⟩, ⟨21, by decide⟩)].flatMap
    fun (p : Fin 26 × Fin 26) => block15RM d p.1 p.2) ++
  [MixedFredCut.unleave15C MixedWindow.j20, TickCut.Hosted.unroutedHigh MixedWindow.j20 1 14,
   archiveRestoreP20 MixedWindow.k8 d, MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330,
   u15 MixedWindow.j20, i15 MixedWindow.j20] ++
  ((List.finRange 9).reverse.flatMap (block20RM d)) ++
  [MixedFredCut.unleave150C, TickCut.Hosted.unroutedHigh MixedWindow.j7 1 14,
   Shadow7.archiveRestoreP MixedWindow.j6 d, MixedWindow.unpackW d 150 140,
   u15 MixedWindow.j7, i15 MixedWindow.j7] ++
  (MixedWindow.prefixPairs.reverse.flatMap fun p => block15RM d p.1 p.2) ++
  [MixedFredCut.unleave15C MixedWindow.j0, TickCut.Hosted.unroutedHigh MixedWindow.j0 1 14,
   MixedWindow.unpackW d 45 45, u15 MixedWindow.j0, i15 MixedWindow.j0, MixedFredCut.portalInvC 45]

def reverseLCX (d : Bool) : List Program :=
  [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410] ++
    ([recvX, portalCM, Shadow7.parkInvP 420, unleaveX] ++ reversePostX d)

theorem reverseLCM_eq (d : Bool) : reverseLCM d = [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410] ++
    ([recvWM, portalCM, Shadow7.parkInvP 420, MixedFredCut.unleave15C jL] ++ reversePostX d) := by
  simp only [reverseLCM, reversePostX, MixedWindow.suffixPairs, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.flatMap_cons, List.flatMap_nil, block15RM,
    List.cons_append, List.append_nil]
  rfl

theorem rtail_rel (d : Bool) :
    LRel 8 ([recvX, portalCM, Shadow7.parkInvP 420, unleaveX] ++ reversePostX d)
      ([recvWM, portalCM, Shadow7.parkInvP 420, MixedFredCut.unleave15C jL] ++ reversePostX d) := by
  unfold LRel
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  exact rexit_rel _

theorem reverse_relX (d : Bool) : LRel 91 (reverseLCX d) (TickCut.Mixed.reverseLC d) := by
  have h1 : LRel 8 (reverseLCX d) (reverseLCM d) := by
    rw [reverseLCM_eq]
    exact (LRel.app (LRel.refl [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410]) (rtail_rel d)).cast
      (by omega)
  exact Rel.trans h1 (reverse_rel d)

/-! The interior leave and first-route exchanges share the lower pairs. -/

inductive InteriorWindow where
  | short (j : Fin 26)
  | wide (j : Fin 9)
  deriving DecidableEq

def InteriorWindow.s : InteriorWindow → Nat
  | .short j => start j
  | .wide j => start20 j

def InteriorWindow.n : InteriorWindow → Nat
  | .short j => nP15 j
  | .wide j => nP20 j

def InteriorWindow.port : InteriorWindow → Wire → Wire
  | .short j => port15 j
  | .wide j => port20 j

def InteriorWindow.leaveF : InteriorWindow → Program
  | .short j => if j.val = 7 then MixedFredCut.leave150C else MixedFredCut.leave15C j
  | .wide j => MixedFredCut.leave20C j

def InteriorWindow.leaveR : InteriorWindow → Program
  | .short j => if j.val = 7 then MixedFredCut.unleave150C else MixedFredCut.unleave15C j
  | .wide j => MixedFredCut.unleave20C j

def InteriorWindow.enterF : InteriorWindow → Program
  | .short j => e15 j
  | .wide j => e20 j

def InteriorWindow.enterR : InteriorWindow → Program
  | .short j => i15 j
  | .wide j => i20 j

def InteriorWindow.baseF : InteriorWindow → Program
  | .short j => Shadow7.routed j 0 1
  | .wide j => routed20 j 0 1

def InteriorWindow.baseR : InteriorWindow → Program
  | .short j => Shadow7.unrouted j 0 1
  | .wide j => unrouted20 j 0 1

def InteriorWindow.routeF : InteriorWindow → Program
  | .short j => r15 j
  | .wide j => r20 j

def InteriorWindow.routeR : InteriorWindow → Program
  | .short j => u15 j
  | .wide j => u20 j

def InteriorWindow.close : InteriorWindow → List GateMirror.Gate
  | .short j => if j.val = 7 then leaveClose150To20 else Shadow7.leaveClose (start j)
  | .wide j => leaveClose20 (start20 j)

structure InteriorEdge where
  left : InteriorWindow
  right : InteriorWindow
  first : Nat
  count : Nat
  deriving DecidableEq

def InteriorEdge.c (e : InteriorEdge) : Wire := e.right.s + 15
def InteriorEdge.r (e : InteriorEdge) : Wire := e.right.s + 16

def InteriorEdge.loPairs (e : InteriorEdge) : List (Wire × Wire) :=
  (List.range' e.first e.count).map fun i => (e.right.s + 17 + i, 787 + i)

def InteriorEdge.allPairs (e : InteriorEdge) : List (Wire × Wire) :=
  (List.range (e.right.n - 2)).map fun i => (e.right.s + 17 + i, 787 + i)

def InteriorEdge.otherPairs (e : InteriorEdge) : List (Wire × Wire) :=
  e.allPairs.take e.first ++ e.allPairs.drop (e.first + e.count)

def InteriorEdge.oldF (e : InteriorEdge) : List Program := [e.left.leaveF, e.right.enterF, e.right.routeF]

def InteriorEdge.oldR (e : InteriorEdge) : List Program := [e.right.routeR, e.right.enterR, e.left.leaveR]

def interiorEdges : List InteriorEdge :=
  [⟨.short 0, .short 1, 225, 7⟩, ⟨.short 1, .short 2, 217, 8⟩,
   ⟨.short 2, .short 3, 210, 7⟩, ⟨.short 3, .short 4, 202, 8⟩,
   ⟨.short 4, .short 5, 195, 7⟩, ⟨.short 5, .short 6, 187, 8⟩,
   ⟨.short 6, .short 7, 180, 7⟩, ⟨.short 7, .wide 0, 172, 10⟩,
   ⟨.wide 0, .wide 1, 162, 10⟩, ⟨.wide 1, .wide 2, 152, 10⟩,
   ⟨.wide 2, .wide 3, 142, 10⟩, ⟨.wide 3, .wide 4, 132, 10⟩,
   ⟨.wide 4, .wide 5, 122, 10⟩, ⟨.wide 5, .wide 6, 112, 10⟩,
   ⟨.wide 6, .wide 7, 102, 10⟩, ⟨.wide 7, .wide 8, 92, 10⟩,
   ⟨.wide 8, .short 20, 82, 8⟩, ⟨.short 20, .short 21, 75, 7⟩,
   ⟨.short 21, .short 22, 67, 8⟩, ⟨.short 22, .short 23, 60, 7⟩,
   ⟨.short 23, .short 24, 52, 8⟩]

theorem interior_sum : (interiorEdges.map InteriorEdge.count).sum = 180 := by decide

theorem interior_sum_reverse : (interiorEdges.reverse.map InteriorEdge.count).sum = 180 := by decide

theorem interior_list_rel {α : Type} (xs : List α) (p q : α → List Program) (price : α → Nat)
    (h : ∀ x ∈ xs, LRel (price x) (p x) (q x)) :
    LRel (xs.map price).sum (xs.flatMap p) (xs.flatMap q) := by
  induction xs with
  | nil => exact LRel.refl []
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    exact LRel.app (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))


/-! The forward local rewrite keeps the old leave and route tails. -/

private def fClose (e : InteriorEdge) : Program := GateMirror.forward e.left.close
private def fBefore (e : InteriorEdge) : List (Wire × Wire) := e.allPairs.take e.first
private def fAfter (e : InteriorEdge) : List (Wire × Wire) := e.allPairs.drop (e.first + e.count)
private def fCut (e : InteriorEdge) : Nat := e.left.leaveF.length - (fClose e).length - 3 * e.count
private def fHead (e : InteriorEdge) : Program := e.left.leaveF.take (fCut e)
private def fTail (e : InteriorEdge) : Program := e.right.routeF.drop (3 * e.allPairs.length)
private def fMiddle (e : InteriorEdge) : Program := fClose e ++ e.right.enterF
private def fShared (e : InteriorEdge) : Program := e.loPairs.flatMap (fR e.r)
private def fOther (e : InteriorEdge) : Program := passT e.r e.otherPairs
private def fFused (e : InteriorEdge) : Program := [.CX e.c e.r] ++ fE e.r e.loPairs ++ [.CX e.c e.r]

def InteriorEdge.newF (e : InteriorEdge) : List Program :=
  [fHead e ++ (fFused e ++ fClose e), e.right.enterF, fOther e ++ fTail e]

private def fOldCore (e : InteriorEdge) : Program := fE e.c e.loPairs ++ passT e.r e.allPairs
private def fNewCore (e : InteriorEdge) : Program := fFused e ++ fOther e

private def fTargets (p : Program) : Program := p.map fun i => Instr.X (tgt i)

private theorem fTargets_wires (p : Program) :
    wires (fTargets p) = ECDSAAdd.Arithmetic.BoundaryCommute.basisWrites p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    change wires (Instr.X (tgt i) :: fTargets p) = _
    cases i <;>
      simp [wires, Instr.wires, ECDSAAdd.Arithmetic.BoundaryCommute.basisWrites, tgt, ih]

private def fAvoid (p q : Program) : Prop :=
  (MixedFredCut.wl p).all (fun x => !(StairLoan.maskOf (MixedFredCut.wl q)).testBit x) = true

private instance (p q : Program) : Decidable (fAvoid p q) := by
  unfold fAvoid
  infer_instance

private def fStable (p q : Program) : Prop := fAvoid p (fTargets q) ∧ fAvoid q (fTargets p)

private instance (p q : Program) : Decidable (fStable p q) := by
  unfold fStable
  infer_instance

private theorem fStable_swap (p q : Program) (hp : GateOnly p) (h : fStable p q) :
    Eqv (p ++ q) (q ++ p) := by
  have pRead := disj_mask p (fTargets q) h.1
  have qRead := disj_mask q (fTargets p) h.2
  rw [fTargets_wires] at pRead qRead
  exact fun m s => ECDSAAdd.Arithmetic.BoundaryCommute.run_append_commute_of_writes
    p q m s (gate_mc hp) pRead qRead

private def fRouteFacts (e : InteriorEdge) : Prop :=
  e.allPairs = fBefore e ++ (e.loPairs ++ fAfter e) ∧
  StairLoan.nodupMask ([e.r] ++ pw e.allPairs) 0 = true ∧
  StairLoan.nodupMask ([e.r] ++ pw e.otherPairs) 0 = true ∧
  fStable (fShared e) ((fAfter e).flatMap (fR e.r)) ∧
  fStable (fShared e) (fOther e)

private instance (e : InteriorEdge) : Decidable (fRouteFacts e) := by
  unfold fRouteFacts
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fRouteChecked : interiorEdges.all (fun e => decide (fRouteFacts e)) = true := by
  decide +kernel

private theorem fRouteFacts_of (e : InteriorEdge) (he : e ∈ interiorEdges) : fRouteFacts e :=
  of_decide_eq_true (List.all_eq_true.mp fRouteChecked e he)

private theorem fGateShared (e : InteriorEdge) : GateOnly (fShared e) := gate_csl _ _
private theorem fGateOther (e : InteriorEdge) : GateOnly (fOther e) := gate_passT _ _

theorem interior_route_partition (e : InteriorEdge) (he : e ∈ interiorEdges) :
    Eqv (passT e.r e.allPairs) (passT e.r e.otherPairs ++ e.loPairs.flatMap (fR e.r)) := by
  obtain ⟨hsplit, hall, hother, hstable, _⟩ := fRouteFacts_of e he
  have hAllSeq : Eqv (passT e.r e.allPairs)
      ((fBefore e).flatMap (fR e.r) ++ (fShared e ++ (fAfter e).flatMap (fR e.r))) := by
    have h := passT_seq e.r e.allPairs (StairLoan.nodup_of_mask _ hall)
    have h' : e.allPairs.flatMap (fR e.r) =
        (fBefore e).flatMap (fR e.r) ++ (fShared e ++ (fAfter e).flatMap (fR e.r)) := by
      conv_lhs => rw [hsplit]
      simp only [List.flatMap_append, fShared]
    rw [h'] at h
    exact h
  have hOtherSeq : Eqv (fOther e)
      ((fBefore e).flatMap (fR e.r) ++ (fAfter e).flatMap (fR e.r)) := by
    simpa only [fOther, InteriorEdge.otherPairs, List.flatMap_append, fBefore, fAfter] using
      passT_seq e.r e.otherPairs (StairLoan.nodup_of_mask _ hother)
  have hMove := fStable_swap _ _ (fGateShared e) hstable
  have hStep : Eqv ((fBefore e).flatMap (fR e.r) ++ ((fAfter e).flatMap (fR e.r) ++ fShared e))
      (fOther e ++ fShared e) := by
    simpa only [List.append_assoc] using Eqv.appL (Q := fShared e) hOtherSeq.symm
      (gate_app.mpr ⟨gate_csl _ _, gate_csl _ _⟩) (fGateOther e)
  exact hAllSeq.trans ((Eqv.appR hMove).trans hStep)

private theorem fRoute_first (e : InteriorEdge) (he : e ∈ interiorEdges) :
    Eqv (passT e.r e.allPairs) (fShared e ++ fOther e) :=
  (interior_route_partition e he).trans (fStable_swap _ _ (fGateShared e) (fRouteFacts_of e he).2.2.2.2).symm

private def fShapeFacts (e : InteriorEdge) : Prop :=
  ((e.left.leaveF.drop (fCut e)).take (3 * e.count) = fE e.c e.loPairs) ∧
  e.left.leaveF.drop (fCut e + 3 * e.count) = fClose e ∧
  e.right.routeF.take (3 * e.allPairs.length) = passT e.r e.allPairs ∧
  StairLoan.nodupMask ([e.c, e.r] ++ pw e.loPairs) 0 = true ∧
  fAvoid (fShared e) (fMiddle e)

private def fPreCRT : InteriorWindow → Program
  | .short j => if j.val = 7 then GateMirror.forward (CRTBarrel.before 150) ++ CRTBarrel.barrel 150 false
      else GateMirror.forward (CRTBarrel.before (start j)) ++ CRTBarrel.barrel (start j) false
  | .wide j => GateMirror.forward (WideSelectorNormalized.beforeRow (start20 j)) ++ barrel20 (start20 j) false

private def fPostCRT : InteriorWindow → Program
  | .short j => if j.val = 7 then GateMirror.forward afterRow150
      else GateMirror.forward (CRTBarrel.afterPart (start j))
  | .wide j => GateMirror.forward (WideSelectorNormalized.afterRow (start20 j))

private def fDiscard : InteriorWindow → Program
  | .short j => if j.val = 7 then MixedFredCut.Eblk150 else MixedFredCut.Eblk15 (start j)
  | .wide j => MixedFredCut.Eblk20 (start20 j)

private def fLeftOK : InteriorWindow → Prop
  | .short j => j.val ≤ 24
  | .wide _ => True

private instance (w : InteriorWindow) : Decidable (fLeftOK w) := by cases w <;> unfold fLeftOK <;> infer_instance

private def fRawLeave : InteriorWindow → Program
  | .short j => if j.val = 7 then leave150To20Red else CRTBarrel.leave j
  | .wide j => leaveP20Red j

attribute [local irreducible] GateMirror.forward CRTBarrel.barrel barrel20 in
private theorem fRawMatches (w : InteriorWindow) (ok : fLeftOK w) :
    fPreCRT w ++ fPostCRT w = fRawLeave w := by
  cases w with
  | short j =>
    change j.val ≤ 24 at ok
    by_cases h : j.val = 7
    · rw [fRawLeave, if_pos h, fPreCRT, fPostCRT, if_pos h, if_pos h, leave150To20Red]
    · simp only [fRawLeave, fPreCRT, fPostCRT, if_neg h, CRTBarrel.leave, if_pos ok, List.append_assoc]
  | wide j =>
    rw [fRawLeave, fPreCRT, fPostCRT, leaveP20Red]

open private leave15C_eq leave150C_eq leave20C_eq from ECDSAAdd.Submission.Entrant.Mixed20D

attribute [local irreducible] CRTBarrel.leave leave150To20Red leaveP20Red GateMirror.forward
  Shadow7.leaveClose leaveClose150To20 leaveClose20 in
private theorem fApplyCut (w : InteriorWindow) (ok : fLeftOK w) (p : Program)
    (h : fRawLeave w = p ++ (fDiscard w ++ GateMirror.forward w.close)) :
    w.leaveF = p ++ GateMirror.forward w.close := by
  cases w with
  | short j =>
    change j.val ≤ 24 at ok
    by_cases hit : j.val = 7
    · have raw : leave150To20Red = p ++ (MixedFredCut.Eblk150 ++ GateMirror.forward leaveClose150To20) := by
        simpa only [fRawLeave, fDiscard, InteriorWindow.close, if_pos hit] using h
      simpa only [InteriorWindow.leaveF, InteriorWindow.close, if_pos hit] using leave150C_eq p raw
    · have raw : CRTBarrel.leave j = p ++ (MixedFredCut.Eblk15 (start j) ++ GateMirror.forward (Shadow7.leaveClose (start j))) := by
        simpa only [fRawLeave, fDiscard, InteriorWindow.close, if_neg hit] using h
      simpa only [InteriorWindow.leaveF, InteriorWindow.close, if_neg hit] using leave15C_eq j ok p raw
  | wide j =>
    have raw : leaveP20Red j = p ++ (MixedFredCut.Eblk20 (start20 j) ++ GateMirror.forward (leaveClose20 (start20 j))) := by
      simpa only [fRawLeave, fDiscard, InteriorWindow.close] using h
    simpa only [InteriorWindow.leaveF, InteriorWindow.close] using leave20C_eq j p raw

private def fLowProgram : InteriorWindow → Program
  | .short j => if j.val = 7 then GateMirror.forward leaveLowClose150
      else GateMirror.forward (Shadow7.leaveLowClose (start j))
  | .wide j => GateMirror.forward (leaveLowClose20 (start20 j))

set_option linter.unusedSimpArgs false in
/-- Expose the low and closing programs without evaluating the earlier arithmetic. -/
private theorem fPostHasLow (w : InteriorWindow) :
    ∃ p, fPostCRT w = p ++ (fLowProgram w ++ GateMirror.forward w.close) := by
  cases w with
  | short j =>
    by_cases hit : j.val = 7
    · let top := Shadow7.a0P 150 + lows150 - 2
      refine ⟨GateMirror.forward (tailD0_150 ++ tailD1S150 ++ [.cx (Shadow7.e0P 150 + 4) 1559] ++
        tailE0_150 ++ [.cx top 1559] ++ chainMid150S ++ [.cx top 1559] ++
        (lowPre150 ++ (lowNew150 ++ lowPost150))), ?_⟩
      simp only [fPostCRT, fLowProgram, InteriorWindow.close, if_pos hit, afterRow150, tailE1_150S, top,
        GateMirror.forward, List.map_append, List.append_assoc]
    · let s := start j
      refine ⟨GateMirror.forward (DeadJoin.lowPreAll7 s ++ (DeadJoin.lowNew7 s ++ DeadJoin.lowPost7 s)), ?_⟩
      simp only [fPostCRT, fLowProgram, InteriorWindow.close, if_neg hit, CRTBarrel.afterPart, DeadJoin.after7S_low,
        DeadJoin.lowEnd7, s, GateMirror.forward, List.map_append, List.append_assoc]
  | wide j =>
    let s := start20 j
    let top := a0P20 s + lowsP20 s - 2
    refine ⟨GateMirror.forward (WideSelectorNormalized.tailD0 s ++ WideSelectorNormalized.tailD1 s ++
      [.cx (e0P20 s + 4) 1559] ++ tailE0_20 s ++ [.cx top 1559] ++ WideSelectorNormalized.chainMidS s ++
      [.cx top 1559] ++ (lowPre20 s ++ (lowNew20 s ++ lowPost20 s))), ?_⟩
    simp only [fPostCRT, fLowProgram, InteriorWindow.close, WideSelectorNormalized.afterRow, tailE1_20S,
      s, top, GateMirror.forward, List.map_append, List.append_assoc]

private def fLowCut (e : InteriorEdge) : Nat :=
  (fLowProgram e.left).length - 6 - 3 * e.count

private def fLowFacts (e : InteriorEdge) : Prop :=
  fLeftOK e.left ∧ (fE e.c e.loPairs).length = 3 * e.count ∧ (fDiscard e.left).length = 6 ∧
  (fLowProgram e.left).drop (fLowCut e) = fE e.c e.loPairs ++ fDiscard e.left

private instance (e : InteriorEdge) : Decidable (fLowFacts e) := by unfold fLowFacts; infer_instance

set_option maxRecDepth 100000 in
/-- The deciding expression has neither a CRT program nor a closing program. -/
private theorem fLowChecked : interiorEdges.all (fun e => decide (fLowFacts e)) = true := by
  decide +kernel

private theorem fLowTransfer (e : InteriorEdge) (h : fLowFacts e) :
    ∃ p : Program, e.left.leaveF = p ++ (fE e.c e.loPairs ++ fClose e) := by
  obtain ⟨ok, _, _, low⟩ := h
  obtain ⟨postPrefix, post⟩ := fPostHasLow e.left
  let p := fPreCRT e.left ++ (postPrefix ++ (fLowProgram e.left).take (fLowCut e))
  have lowSplit : fLowProgram e.left =
      (fLowProgram e.left).take (fLowCut e) ++ (fE e.c e.loPairs ++ fDiscard e.left) := by
    have cut := List.take_append_drop (fLowCut e) (fLowProgram e.left)
    rw [low] at cut
    exact cut.symm
  have before : fPreCRT e.left ++ fPostCRT e.left =
      (p ++ fE e.c e.loPairs) ++ (fDiscard e.left ++ fClose e) := by
    rw [post, lowSplit]
    simp only [p, fClose, List.append_assoc]
  have hRaw := (fRawMatches e.left ok).symm.trans before
  refine ⟨p, (fApplyCut e.left ok (p ++ fE e.c e.loPairs) hRaw).trans ?_⟩
  exact List.append_assoc p (fE e.c e.loPairs) (fClose e)

/-- These are the first two fields of the original forward shape certificate. -/
theorem forward_leave_body (e : InteriorEdge) (he : e ∈ interiorEdges) :
    ((e.left.leaveF.drop (fCut e)).take (3 * e.count) = fE e.c e.loPairs) ∧
    e.left.leaveF.drop (fCut e + 3 * e.count) = fClose e := by
  have facts : fLowFacts e := of_decide_eq_true (List.all_eq_true.mp fLowChecked e he)
  obtain ⟨p, shape⟩ := fLowTransfer e facts
  have keptLen := facts.2.1
  have cut : fCut e = p.length := by
    simp only [fCut, shape, List.length_append, keptLen]
    omega
  constructor
  · rw [cut, shape, List.drop_left' rfl, ← keptLen]
    exact List.take_left' rfl
  · rw [cut, shape, ← List.append_assoc, ← keptLen, ← List.length_append, List.drop_left' rfl]

private def fNextFacts (e : InteriorEdge) : Prop :=
  e.right.routeF.take (3 * e.allPairs.length) = passT e.r e.allPairs ∧
  StairLoan.nodupMask ([e.c, e.r] ++ pw e.loPairs) 0 = true ∧
  fAvoid (fShared e) (fMiddle e)

private instance (e : InteriorEdge) : Decidable (fNextFacts e) := by unfold fNextFacts; infer_instance

set_option maxRecDepth 100000 in
private theorem fNextChecked : interiorEdges.all (fun e => decide (fNextFacts e)) = true := by
  decide +kernel

theorem forward_route_frame (e : InteriorEdge) (he : e ∈ interiorEdges) : fNextFacts e :=
  of_decide_eq_true (List.all_eq_true.mp fNextChecked e he)

private theorem fShapeFacts_of (e : InteriorEdge) (he : e ∈ interiorEdges) : fShapeFacts e := by
  obtain ⟨kept, close⟩ := forward_leave_body e he
  obtain ⟨route, distinct, frame⟩ := forward_route_frame e he
  exact ⟨kept, close, route, distinct, frame⟩

private theorem fOld_flat (e : InteriorEdge) (he : e ∈ interiorEdges) :
    e.oldF.flatten = fHead e ++ (fE e.c e.loPairs ++ (fMiddle e ++ (passT e.r e.allPairs ++ fTail e))) := by
  obtain ⟨hex, hclose, hroute, _, _⟩ := fShapeFacts_of e he
  have hLeave : e.left.leaveF = fHead e ++ (fE e.c e.loPairs ++ fClose e) := by
    have h := List.take_append_drop (3 * e.count) (e.left.leaveF.drop (fCut e))
    rw [hex, List.drop_drop, hclose] at h
    exact (List.take_append_drop (fCut e) e.left.leaveF).symm.trans
      (congrArg (fun p => fHead e ++ p) h.symm)
  have hRoute : e.right.routeF = passT e.r e.allPairs ++ fTail e := by
    have h := List.take_append_drop (3 * e.allPairs.length) e.right.routeF
    rw [hroute] at h
    exact h.symm
  simp only [InteriorEdge.oldF, List.flatten_cons, List.flatten_nil, List.append_nil,
    hLeave, hRoute, fMiddle, List.append_assoc]

private theorem fNew_flat (e : InteriorEdge) :
    e.newF.flatten = fHead e ++ (fFused e ++ (fMiddle e ++ (fOther e ++ fTail e))) := by
  simp only [InteriorEdge.newF, List.flatten_cons, List.flatten_nil, List.append_nil,
    fMiddle, List.append_assoc]

private theorem fGateFused (e : InteriorEdge) : GateOnly (fFused e) := by
  have hc : GateOnly [.CX e.c e.r] := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    rfl
  exact gate_app.mpr ⟨gate_app.mpr ⟨hc, gate_ce _ _⟩, hc⟩

private theorem fRun (e : InteriorEdge) (he : e ∈ interiorEdges) : Eqv e.newF.flatten e.oldF.flatten := by
  rw [fOld_flat e he, fNew_flat]
  have hr : Eqv (passT e.r e.allPairs ++ fTail e) (fShared e ++ (fOther e ++ fTail e)) := by
    simpa only [List.append_assoc] using Eqv.appL (Q := fTail e) (fRoute_first e he)
      (gate_passT _ _) (gate_app.mpr ⟨fGateShared e, fGateOther e⟩)
  have hm : Eqv (fMiddle e ++ (fShared e ++ (fOther e ++ fTail e)))
      (fShared e ++ (fMiddle e ++ (fOther e ++ fTail e))) := by
    have h := eqv_comm_disj (fShared e) (fMiddle e) (gate_mc (fGateShared e))
      (disj_mask _ _ (fShapeFacts_of e he).2.2.2.2)
    have hc : measurementCount (fMiddle e ++ fShared e) = measurementCount (fShared e ++ fMiddle e) := by
      simp only [measurementCount_append, Nat.add_comm]
    simpa only [List.append_assoc] using Eqv.appLm (Q := fOther e ++ fTail e) h.symm hc
  have hf : Eqv (fE e.c e.loPairs ++ (fShared e ++ (fMiddle e ++ (fOther e ++ fTail e))))
      (fFused e ++ (fMiddle e ++ (fOther e ++ fTail e))) := by
    have hg := merge_fwd e.c e.r e.loPairs
      (StairLoan.nodup_of_mask _ (fShapeFacts_of e he).2.2.2.1)
    simpa only [List.append_assoc] using
      Eqv.appL (P := fE e.c e.loPairs ++ fShared e) (P' := fFused e)
        (Q := fMiddle e ++ (fOther e ++ fTail e)) hg
        (gate_app.mpr ⟨gate_ce _ _, fGateShared e⟩) (fGateFused e)
  exact (Eqv.appR ((Eqv.appR (Eqv.appR hr)).trans ((Eqv.appR hm).trans hf))).symm

private def fCostFacts (e : InteriorEdge) : Prop :=
  toffoliCount (fNewCore e) + e.count = toffoliCount (fOldCore e) ∧
  gateSlots (fNewCore e) + (3 * e.count - 2) = gateSlots (fOldCore e) ∧
  (MixedFredCut.wl (fNewCore e)).all
    (fun q => (StairLoan.maskOf (MixedFredCut.wl (fOldCore e))).testBit q) = true ∧
  (fNewCore e).all physicalGateCheck = true

private instance (e : InteriorEdge) : Decidable (fCostFacts e) := by
  unfold fCostFacts
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem fCostChecked : interiorEdges.all (fun e => decide (fCostFacts e)) = true := by
  decide +kernel

private theorem fCostFacts_of (e : InteriorEdge) (he : e ∈ interiorEdges) : fCostFacts e :=
  of_decide_eq_true (List.all_eq_true.mp fCostChecked e he)

theorem interior_localF_slots (e : InteriorEdge) (he : e ∈ interiorEdges) :
    gateSlots e.newF.flatten + (3 * e.count - 2) = gateSlots e.oldF.flatten := by
  rw [fNew_flat, fOld_flat e he]
  have h := (fCostFacts_of e he).2.1
  simp only [fOldCore, fNewCore, gateSlots_append] at h
  simp only [gateSlots_append]
  omega

theorem interior_localF (e : InteriorEdge) (he : e ∈ interiorEdges) :
    LRel e.count e.newF e.oldF := by
  refine ⟨fRun e he, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fNew_flat, fOld_flat e he]
    simp only [measurementCount_append, gate_mc (fGateFused e), gate_mc (fGateOther e),
      gate_mc (gate_ce e.c e.loPairs), gate_mc (gate_passT e.r e.allPairs)]
  · rw [fNew_flat, fOld_flat e he]
    have h := (fCostFacts_of e he).1
    simp only [fOldCore, fNewCore, toffoliCount_append] at h
    simp only [toffoliCount_append]
    omega
  · rw [fNew_flat, fOld_flat e he]
    have hs := sub_mask _ _ (fCostFacts_of e he).2.2.1
    have newEq :
        wires (fHead e ++ (fFused e ++ (fMiddle e ++ (fOther e ++ fTail e)))) =
        (wires (fHead e) ∪ wires (fMiddle e) ∪ wires (fTail e)) ∪ wires (fNewCore e) := by
      simp only [fNewCore, wires_append]
      ac_rfl
    have oldEq :
        wires (fHead e ++ (fE e.c e.loPairs ++ (fMiddle e ++ (passT e.r e.allPairs ++ fTail e)))) =
        (wires (fHead e) ∪ wires (fMiddle e) ∪ wires (fTail e)) ∪ wires (fOldCore e) := by
      simp only [fOldCore, wires_append]
      ac_rfl
    rw [newEq, oldEq]
    exact Finset.union_subset_union (Finset.Subset.refl _) hs
  · have h := interior_localF_slots e he
    omega
  · rw [fNew_flat, fOld_flat e he]
    intro h
    have hp := phys_of_all _ (fCostFacts_of e he).2.2.2
    simp only [fNewCore, gatePhysical_append] at hp
    simp only [gatePhysical_append] at h ⊢
    exact ⟨h.1, hp.1, h.2.2.1, hp.2, h.2.2.2.2⟩


def interiorPrefixF (d : Bool) : List Program :=
  [MixedFredCut.portalC 45, e15 MixedWindow.j0, r15 MixedWindow.j0, MixedWindow.packW d 45 45,
   Shadow7.routed MixedWindow.j0 1 14]

def interiorSuffixF (d : Bool) : List Program :=
  [leaveX, Shadow7.parkP 420, portalInvM, tickWX, MixedWindow.packW d 420 410, Shadow7.exitLoadP 420 d]

def interiorBodyF (d : Bool) : InteriorWindow → List Program
  | .short j =>
    if j.val = 20 then
      [MixedWindow.packW d 345 330, MixedWindow.packW d 345 335,
       archiveLoadP20 MixedWindow.k8 d, Shadow7.routed j 1 14]
    else
      [MixedWindow.packW d (start j) (start j - 10),
       Shadow7.archiveLoadP ⟨j.val - 1, by have := j.isLt; omega⟩ d, Shadow7.routed j 1 14]
  | .wide j =>
    let s := start20 j
    if j.val = 0 then
      [MixedWindow.packW d 165 155, archiveLoad150To20 d, routed20 j 1 19]
    else
      [MixedWindow.packW d s (s - 15), MixedWindow.packW d s (s - 10),
       archiveLoadP20 ⟨j.val - 1, by have := j.isLt; omega⟩ d, routed20 j 1 19]

def interiorFC (d : Bool) : List Program :=
  interiorPrefixF d ++
    (interiorEdges.flatMap (fun e => e.newF ++ interiorBodyF d e.right) ++ interiorSuffixF d)

theorem interiorF_old (d : Bool) : forwardLCX d =
    interiorPrefixF d ++
      (interiorEdges.flatMap (fun e => e.oldF ++ interiorBodyF d e.right) ++ interiorSuffixF d) := by
  rfl

theorem interiorF_rel (d : Bool) : LRel 180 (interiorFC d) (forwardLCX d) := by
  rw [interiorF_old d]
  unfold interiorFC
  have mid := interior_list_rel interiorEdges
    (fun e => e.newF ++ interiorBodyF d e.right)
    (fun e => e.oldF ++ interiorBodyF d e.right) InteriorEdge.count
    (fun e he => (interior_localF e he).app (LRel.refl (interiorBodyF d e.right)))
  rw [interior_sum] at mid
  exact (LRel.refl (interiorPrefixF d)).app (mid.app (LRel.refl (interiorSuffixF d)))

theorem forward_relInterior (d : Bool) :
    Rel 270 (interiorFC d).flatten (MixedWindow.forwardMixedCut d) :=
  Rel.trans (interiorF_rel d) (forward_relX d)


def forward (d : Bool) : Program := (interiorFC d).flatten
/-! The lower exchanges at the reverse boundary from wide window 8 to wide window 7. -/

private def reverseLowerEdge : InteriorEdge := ⟨.wide 7, .wide 8, 92, 10⟩

private theorem reverseLowerEdge_mem : reverseLowerEdge ∈ interiorEdges := by decide

private def InteriorEdge.closeR (e : InteriorEdge) : Program := GateMirror.inverse e.left.close
private def InteriorEdge.swapR (e : InteriorEdge) : Program := fE e.c e.loPairs.reverse
private def InteriorEdge.leaveTailR (e : InteriorEdge) : Program :=
  e.left.leaveR.drop (e.closeR.length + 3 * e.count)
private def InteriorEdge.routeHeadR (e : InteriorEdge) : Program :=
  e.right.baseR.take (e.right.baseR.length - 3 * e.right.n)
private def InteriorEdge.interiorMidR (e : InteriorEdge) : Program := e.right.enterR ++ e.closeR
private def InteriorEdge.mergeR (e : InteriorEdge) : Program :=
  [.CX e.c e.r] ++ fE e.r e.loPairs ++ [.CX e.c e.r]
private def InteriorEdge.replacedR (e : InteriorEdge) : Program := passT e.r e.otherPairs ++ e.mergeR
private def InteriorEdge.newR (e : InteriorEdge) : List Program :=
  [e.routeHeadR ++ e.replacedR, e.right.enterR, e.closeR ++ e.leaveTailR]
private def reverseSlotSaving (e : InteriorEdge) : Nat := 3 * e.count - 2

private structure ReverseLowerFacts (e : InteriorEdge) : Prop where
  leavePrefix : e.left.leaveR.take (e.closeR.length + 3 * e.count) = e.closeR ++ e.swapR
  routeSuffix : restR e.right.baseR e.right.n = passT e.r e.allPairs
  leaveDistinct : StairLoan.nodupMask ([e.c] ++ pw e.loPairs) 0 = true
  bothDistinct : StairLoan.nodupMask ([e.c, e.r] ++ pw e.loPairs) 0 = true
  stable : fStable e.swapR e.interiorMidR
  measurements : measurementCount e.replacedR = 0
  toffolis : toffoliCount e.replacedR + e.count = toffoliCount (passT e.r e.allPairs ++ e.swapR)
  slots : gateSlots e.replacedR + reverseSlotSaving e = gateSlots (passT e.r e.allPairs ++ e.swapR)
  support : (MixedFredCut.wl e.replacedR).all
    (fun q => (StairLoan.maskOf (MixedFredCut.wl (passT e.r e.allPairs ++ e.swapR))).testBit q) = true
  physical : e.replacedR.all physicalGateCheck = true

/-! ### Structural shapes of the reverse boundary pieces

The inverse leave and the inverse route of each interior edge are exposed from their definitions, so the kernel
checks facts about the small exchange pieces only and never evaluates a whole unleave or inverse route. The shape
lemmas below (`rRawShape`, `rLeaveShape`, `rSwapTail`, `rBaseShape`, `rRestR_append`) are taken from yukonautominer's
reverse-interior entries (60521eb7 / 04aeede4). -/

open private unleave15C_eq unleave150C_eq unleave20C_eq suffix_after150 suffix_after20
  from ECDSAAdd.Submission.Entrant.Mixed20D

/-- The raw (uncut) unleave programs of the left windows. -/
private def rRawUnleave : InteriorWindow → Program
  | .short j => if j.val = 7 then leaveInv150To20Red else CRTBarrel.unleave j
  | .wide j => leaveInvP20Red j

/-- The low-close gate lists (small, no CRT program). -/
private def rLowG : InteriorWindow → List GateMirror.Gate
  | .short j => if j.val = 7 then leaveLowClose150 else Shadow7.leaveLowClose (start j)
  | .wide j => leaveLowClose20 (start20 j)

private def rDblk : InteriorWindow → Program
  | .short j => if j.val = 7 then MixedFredCut.Dblk150 else MixedFredCut.Dblk15 (start j)
  | .wide j => MixedFredCut.Dblk20 (start20 j)

attribute [local irreducible] CRTBarrel.barrel barrel20 GateMirror.inverse CRTBarrel.before
  WideSelectorNormalized.beforeRow CRTBarrel.afterPart WideSelectorNormalized.afterRow afterRow150
  Shadow7.leaveLowClose leaveLowClose150 leaveLowClose20 Shadow7.leaveClose leaveClose150To20 leaveClose20 in
/-- Expose the inverse close and the inverse low close at the head of each raw unleave,
without evaluating any CRT program. -/
private theorem rRawShape (w : InteriorWindow) (ok : fLeftOK w) :
    ∃ T, rRawUnleave w = GateMirror.inverse (w.close) ++ (GateMirror.inverse (rLowG w) ++ T) := by
  cases w with
  | short j =>
    change j.val ≤ 24 at ok
    by_cases h : j.val = 7
    · obtain ⟨Z, hZ⟩ := suffix_after150
      refine ⟨GateMirror.inverse Z ++ (CRTBarrel.barrel 150 true ++ GateMirror.inverse (CRTBarrel.before 150)), ?_⟩
      simp only [rRawUnleave, rLowG, InteriorWindow.close, if_pos h]
      unfold leaveInv150To20Red
      rw [← hZ]
      simp only [FredCut.inv_app, List.append_assoc]
    · obtain ⟨Z, hZ⟩ := FredCut.suffix_after (start j)
      refine ⟨GateMirror.inverse Z ++
        (CRTBarrel.barrel (start j) true ++ GateMirror.inverse (CRTBarrel.before (start j))), ?_⟩
      simp only [rRawUnleave, rLowG, InteriorWindow.close, if_neg h]
      unfold CRTBarrel.unleave
      simp only [if_pos ok]
      rw [← hZ]
      simp only [FredCut.inv_app, List.append_assoc]
  | wide j =>
    obtain ⟨Z, hZ⟩ := suffix_after20 (start20 j)
    refine ⟨GateMirror.inverse Z ++
      (barrel20 (start20 j) true ++ GateMirror.inverse (WideSelectorNormalized.beforeRow (start20 j))), ?_⟩
    simp only [rRawUnleave, rLowG, InteriorWindow.close]
    unfold leaveInvP20Red
    dsimp only
    rw [← hZ]
    simp only [FredCut.inv_app, List.append_assoc]

attribute [local irreducible] CRTBarrel.unleave leaveInv150To20Red leaveInvP20Red GateMirror.inverse
  Shadow7.leaveLowClose leaveLowClose150 leaveLowClose20 Shadow7.leaveClose leaveClose150To20 leaveClose20 in
private theorem rLeaveShape (w : InteriorWindow) (ok : fLeftOK w)
    (hD : (GateMirror.inverse (rLowG w)).take 6 = rDblk w) :
    ∃ T, w.leaveR = GateMirror.inverse (w.close) ++ ((GateMirror.inverse (rLowG w)).drop 6 ++ T) := by
  obtain ⟨T, hT⟩ := rRawShape w ok
  have split : GateMirror.inverse (rLowG w) = rDblk w ++ (GateMirror.inverse (rLowG w)).drop 6 := by
    rw [← hD]; exact (List.take_append_drop 6 _).symm
  rw [split, List.append_assoc] at hT
  refine ⟨T, ?_⟩
  cases w with
  | short j =>
    change j.val ≤ 24 at ok
    by_cases h : j.val = 7
    · simp only [rRawUnleave, rDblk, InteriorWindow.close, if_pos h] at hT
      simp only [InteriorWindow.leaveR, InteriorWindow.close, if_pos h]
      exact unleave150C_eq _ hT
    · simp only [rRawUnleave, rDblk, InteriorWindow.close, if_neg h] at hT
      simp only [InteriorWindow.leaveR, InteriorWindow.close, if_neg h]
      exact unleave15C_eq j ok _ hT
  | wide j =>
    simp only [rRawUnleave, rDblk, InteriorWindow.close] at hT
    simp only [InteriorWindow.leaveR, InteriorWindow.close]
    exact unleave20C_eq j _ hT

/-- The last piece of each first inverse route: the renamed register swap of its first untick. -/
private def rSwapTail : InteriorWindow → Program
  | .short j => renameProgram (StairPacket.net j 0)
      (swapRegisters (IntegerPacket.ports (Shadow7.shape j) 0).a0 (IntegerPacket.ports (Shadow7.shape j) 0).ah
        (IntegerPacket.ports (Shadow7.shape j) 0).bh)
  | .wide j => renameProgram (net20 j 0)
      (swapRegisters (IntegerPacket.ports (shape20 j) 0).a0 (IntegerPacket.ports (shape20 j) 0).ah
        (IntegerPacket.ports (shape20 j) 0).bh)

private def rBaseU : InteriorWindow → Program
  | .short j => Shadow7.unrouted j 0 1
  | .wide j => unrouted20 j 0 1

private theorem rBaseShape (w : InteriorWindow) : ∃ A, rBaseU w = A ++ rSwapTail w := by
  cases w with
  | short j =>
    obtain ⟨P, hP⟩ : ∃ P, ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (IntegerPacket.ports (Shadow7.shape j) 0)
        (IntegerPacket.ports (Shadow7.shape j) 0).half.length =
        P ++ swapRegisters (IntegerPacket.ports (Shadow7.shape j) 0).a0 (IntegerPacket.ports (Shadow7.shape j) 0).ah
          (IntegerPacket.ports (Shadow7.shape j) 0).bh := ⟨_, rfl⟩
    refine ⟨renameProgram (StairPacket.net j 0) P, ?_⟩
    simp only [rBaseU, rSwapTail, Shadow7.unrouted, List.nil_append]
    rw [hP, rename_app]
  | wide j =>
    obtain ⟨P, hP⟩ : ∃ P, ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick (IntegerPacket.ports (shape20 j) 0)
        (IntegerPacket.ports (shape20 j) 0).half.length =
        P ++ swapRegisters (IntegerPacket.ports (shape20 j) 0).a0 (IntegerPacket.ports (shape20 j) 0).ah
          (IntegerPacket.ports (shape20 j) 0).bh := ⟨_, rfl⟩
    refine ⟨renameProgram (net20 j 0) P, ?_⟩
    simp only [rBaseU, rSwapTail, unrouted20, List.nil_append]
    rw [hP, rename_app]

private theorem rRestR_append (A S : Program) (n : Nat) (hS : S.length = 3 * n) :
    restR (A ++ S) n = restR S n := by
  have h1 : ∀ k, k ≤ S.length → (A ++ S).drop ((A ++ S).length - k) = S.drop (S.length - k) := by
    intro k hk
    rw [List.length_append, show A.length + S.length - k = A.length + (S.length - k) by omega,
      List.drop_append]
    simp
  unfold restR
  rw [h1 (3 * n) (by omega), h1 (2 * n) (by omega), h1 n (by omega)]


private def rSmall (e : InteriorEdge) : Prop :=
  fLeftOK e.left ∧
  (GateMirror.inverse (rLowG e.left)).take 6 = rDblk e.left ∧
  ((GateMirror.inverse (rLowG e.left)).drop 6).take (3 * e.count) = e.swapR ∧
  e.swapR.length = 3 * e.count ∧
  (rSwapTail e.right).length = 3 * e.right.n ∧
  restR (rSwapTail e.right) e.right.n = passT e.r e.allPairs ∧
  StairLoan.nodupMask ([e.c] ++ pw e.loPairs) 0 = true ∧
  StairLoan.nodupMask ([e.c, e.r] ++ pw e.loPairs) 0 = true ∧
  fStable e.swapR e.interiorMidR ∧
  measurementCount e.replacedR = 0 ∧
  toffoliCount e.replacedR + e.count = toffoliCount (passT e.r e.allPairs ++ e.swapR) ∧
  gateSlots e.replacedR + reverseSlotSaving e = gateSlots (passT e.r e.allPairs ++ e.swapR) ∧
  (MixedFredCut.wl e.replacedR).all
    (fun q => (StairLoan.maskOf (MixedFredCut.wl (passT e.r e.allPairs ++ e.swapR))).testBit q) = true ∧
  e.replacedR.all physicalGateCheck = true

private instance (e : InteriorEdge) : Decidable (rSmall e) := by unfold rSmall; infer_instance

private theorem rBase_eq : ∀ w : InteriorWindow, w.baseR = rBaseU w := by
  intro w; cases w <;> rfl

private theorem revFacts_of (e : InteriorEdge) (h : rSmall e) : ReverseLowerFacts e := by
  obtain ⟨ok, hD, hex, hlen, hSl, hRest, d1, d2, st, mc, tc, sl, sp, ph⟩ := h
  refine ⟨?_, ?_, d1, d2, st, mc, tc, sl, sp, ph⟩
  · obtain ⟨T, hT⟩ := rLeaveShape e.left ok hD
    have hB : (GateMirror.inverse (rLowG e.left)).drop 6 =
        e.swapR ++ ((GateMirror.inverse (rLowG e.left)).drop 6).drop (3 * e.count) := by
      rw [← hex]; exact (List.take_append_drop _ _).symm
    rw [hB, List.append_assoc] at hT
    simp only [InteriorEdge.closeR]
    rw [hT, ← List.append_assoc]
    exact List.take_left' (by simp only [List.length_append, hlen])
  · obtain ⟨A, hA⟩ := rBaseShape e.right
    rw [rBase_eq e.right, hA, rRestR_append A _ _ hSl, hRest]

set_option maxRecDepth 100000 in
private theorem reverseLowerChecked : ReverseLowerFacts reverseLowerEdge :=
  revFacts_of _ (by decide +kernel)

private theorem reverseLowerOld (e : InteriorEdge) (h : ReverseLowerFacts e) :
    e.oldR.flatten =
      e.routeHeadR ++ (passT e.r e.allPairs ++ (e.interiorMidR ++ (e.swapR ++ e.leaveTailR))) := by
  have route : e.right.routeR = e.routeHeadR ++ restR e.right.baseR e.right.n := by
    unfold InteriorEdge.routeHeadR
    cases e.right <;> rfl
  rw [h.routeSuffix] at route
  have leave : e.left.leaveR = (e.closeR ++ e.swapR) ++ e.leaveTailR := by
    rw [← h.leavePrefix]
    exact (List.take_append_drop _ _).symm
  simp only [InteriorEdge.oldR, InteriorEdge.interiorMidR, List.flatten_cons, List.flatten_nil,
    List.append_nil, route, leave, List.append_assoc]

private theorem reverseLowerNew (e : InteriorEdge) :
    e.newR.flatten = e.routeHeadR ++ (e.replacedR ++ (e.interiorMidR ++ e.leaveTailR)) := by
  simp only [InteriorEdge.newR, InteriorEdge.interiorMidR, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

private theorem reverseLowerRun (e : InteriorEdge) (he : e ∈ interiorEdges) (h : ReverseLowerFacts e) :
    Eqv e.newR.flatten e.oldR.flatten := by
  rw [reverseLowerNew, reverseLowerOld e h]
  have route : Eqv (passT e.r e.allPairs ++ (e.interiorMidR ++ (e.swapR ++ e.leaveTailR)))
      (passT e.r e.otherPairs ++ (fShared e ++ (e.interiorMidR ++ (e.swapR ++ e.leaveTailR)))) := by
    have step := Eqv.appLm (Q := e.interiorMidR ++ (e.swapR ++ e.leaveTailR))
      (interior_route_partition e he)
      ((gate_mc (gate_passT _ _)).trans
        (gate_mc (gate_app.mpr ⟨gate_passT _ _, gate_csl _ _⟩)).symm)
    simpa only [fShared, List.append_assoc] using step
  have move : Eqv (e.interiorMidR ++ (e.swapR ++ e.leaveTailR))
      (e.swapR ++ (e.interiorMidR ++ e.leaveTailR)) := by
    have step := Eqv.appLm (Q := e.leaveTailR)
      (fStable_swap _ _ (gate_ce e.c e.loPairs.reverse) h.stable).symm (by
        simp only [measurementCount_append, Nat.add_comm])
    simpa only [List.append_assoc] using step
  have fuse : Eqv (fShared e ++ (e.swapR ++ (e.interiorMidR ++ e.leaveTailR)))
      (e.mergeR ++ (e.interiorMidR ++ e.leaveTailR)) := by
    have confluent : Eqv (fShared e ++ e.swapR) e.mergeR := by
      have flip : Eqv (fShared e ++ e.swapR) (fShared e ++ fE e.c e.loPairs) :=
        Eqv.appR (fE_rev e.c e.loPairs (StairLoan.nodup_of_mask _ h.leaveDistinct))
      exact flip.trans (merge_rev e.c e.r e.loPairs (StairLoan.nodup_of_mask _ h.bothDistinct))
    have bracket : GateOnly [Instr.CX e.c e.r] := by
      intro instr hi
      simp only [List.mem_singleton] at hi
      subst instr
      rfl
    have pure : GateOnly e.mergeR := gate_app.mpr ⟨gate_app.mpr ⟨bracket, gate_ce _ _⟩, bracket⟩
    have step := Eqv.appLm (Q := e.interiorMidR ++ e.leaveTailR) confluent
      ((gate_mc (gate_app.mpr ⟨fGateShared e, gate_ce _ _⟩)).trans (gate_mc pure).symm)
    simpa only [List.append_assoc] using step
  have whole := route.trans ((Eqv.appR (Eqv.appR move)).trans (Eqv.appR fuse))
  exact Eqv.appR (by simpa only [InteriorEdge.replacedR, List.append_assoc] using whole.symm)

private def reverseTapeOps : Program → Program
  | [] => []
  | .measureX t z o :: rest => .measureX t z o :: reverseTapeOps rest
  | _ :: rest => reverseTapeOps rest

private theorem reverseTapeOps_append (p q : Program) :
    reverseTapeOps (p ++ q) = reverseTapeOps p ++ reverseTapeOps q := by
  induction p with
  | nil => rfl
  | cons i p ih => cases i <;> simp [reverseTapeOps, ih]

private theorem reverseTapeOps_nil (p : Program) (h : measurementCount p = 0) :
    reverseTapeOps p = [] := by
  induction p with
  | nil => rfl
  | cons i p ih => cases i <;> simp_all [measurementCount, reverseTapeOps]

private theorem reverseLowerTape (e : InteriorEdge) (h : ReverseLowerFacts e) :
    reverseTapeOps e.newR.flatten = reverseTapeOps e.oldR.flatten := by
  rw [reverseLowerNew, reverseLowerOld e h]
  have swapZero : reverseTapeOps e.swapR = [] := reverseTapeOps_nil _ (gate_mc (gate_ce _ _))
  have routeZero := reverseTapeOps_nil _ (gate_mc (gate_passT e.r e.allPairs))
  have newZero := reverseTapeOps_nil _ h.measurements
  simp only [reverseTapeOps_append, swapZero, routeZero, newZero, List.nil_append]

private theorem reverseLowerSlots (e : InteriorEdge) (h : ReverseLowerFacts e) :
    gateSlots e.newR.flatten + reverseSlotSaving e = gateSlots e.oldR.flatten := by
  rw [reverseLowerNew, reverseLowerOld e h]
  have slots := h.slots
  simp only [gateSlots_append] at slots ⊢
  omega

private theorem reverseLowerRel (e : InteriorEdge) (he : e ∈ interiorEdges) (h : ReverseLowerFacts e) :
    LRel e.count e.newR e.oldR := by
  have hs := reverseLowerSlots e h
  have hr := reverseLowerRun e he h
  unfold LRel
  rw [reverseLowerNew, reverseLowerOld e h] at hr hs ⊢
  have swapZero : measurementCount e.swapR = 0 := gate_mc (gate_ce _ _)
  have routeZero : measurementCount (passT e.r e.allPairs) = 0 := gate_mc (gate_passT _ _)
  have supported := sub_mask _ _ h.support
  have proper := phys_of_all _ h.physical
  refine ⟨hr, ?_, ?_, ?_, by omega, ?_⟩
  · simp only [measurementCount_append, swapZero, routeZero, h.measurements, Nat.zero_add]
  · have t := h.toffolis
    simp only [toffoliCount_append] at t ⊢
    omega
  · intro q hq
    have sub : q ∈ wires e.replacedR → q ∈ wires (passT e.r e.allPairs) ∨ q ∈ wires e.swapR := by
      intro uses
      rw [← Finset.mem_union, ← wires_append]
      exact supported uses
    simp only [wires_append, Finset.mem_union] at hq ⊢
    tauto
  · intro original
    simp only [gatePhysical_append] at original ⊢
    exact ⟨original.1, proper, original.2.2.1, original.2.2.2.2⟩

private def reverseLowerWalk (d : Bool) : List Program :=
  (reverseLCX d).take 41 ++ (reverseLowerEdge.newR ++ (reverseLCX d).drop 44)

/-- This reduces the list of programs. The runtime contents of its programs are unchanged terms. -/
private theorem reverseLowerAt (d : Bool) :
    ((reverseLCX d).drop 41).take 3 = reverseLowerEdge.oldR := by
  rfl

private theorem reverseLowerSplit (d : Bool) :
    reverseLCX d = (reverseLCX d).take 41 ++ (reverseLowerEdge.oldR ++ (reverseLCX d).drop 44) := by
  have rest := (List.take_append_drop 3 ((reverseLCX d).drop 41)).symm
  rw [reverseLowerAt, List.drop_drop] at rest
  calc
    reverseLCX d = (reverseLCX d).take 41 ++ (reverseLCX d).drop 41 :=
      (List.take_append_drop _ _).symm
    _ = _ := congrArg ((reverseLCX d).take 41 ++ ·) rest

private theorem reverseLowerDeploy (d : Bool) : LRel 10 (reverseLowerWalk d) (reverseLCX d) := by
  have localRel := reverseLowerRel reverseLowerEdge reverseLowerEdge_mem reverseLowerChecked
  have lifted := (LRel.refl ((reverseLCX d).take 41)).app
    (localRel.app (LRel.refl ((reverseLCX d).drop 44)))
  rw [← reverseLowerSplit d] at lifted
  exact lifted

private theorem reverseLowerTapeDeploy (d : Bool) :
    reverseTapeOps (reverseLowerWalk d).flatten = reverseTapeOps (reverseLCX d).flatten := by
  have h := reverseLowerTape reverseLowerEdge reverseLowerChecked
  have lifted : reverseTapeOps (reverseLowerWalk d).flatten =
      reverseTapeOps ((reverseLCX d).take 41 ++ (reverseLowerEdge.oldR ++ (reverseLCX d).drop 44)).flatten := by
    simp only [reverseLowerWalk, List.flatten_append, reverseTapeOps_append, h]
  rwa [← reverseLowerSplit d] at lifted

private theorem reverseLowerSlotsDeploy (d : Bool) :
    gateSlots (reverseLowerWalk d).flatten + 28 = gateSlots (reverseLCX d).flatten := by
  have h := reverseLowerSlots reverseLowerEdge reverseLowerChecked
  change gateSlots reverseLowerEdge.newR.flatten + 28 = gateSlots reverseLowerEdge.oldR.flatten at h
  have lifted : gateSlots (reverseLowerWalk d).flatten + 28 =
      gateSlots ((reverseLCX d).take 41 ++ (reverseLowerEdge.oldR ++ (reverseLCX d).drop 44)).flatten := by
    simp only [reverseLowerWalk, List.flatten_append, gateSlots_append]
    omega
  rwa [← reverseLowerSplit d] at lifted


/-! ### The same reverse lower-pair merge at the other twenty interior edges

`ReverseLowerFacts` holds at every edge of `interiorEdges`, so `reverseLowerRel` applies at each of the twenty
edges not yet merged above. Each edge's old pieces `[routeR right, enterR right, leaveR left]` sit at a fixed
position of the deployed reverse list `reverseLowerWalk d`. The twenty 3-piece windows are replaced from the
highest position down; a replacement at `k1` leaves every window ending at or before `k1` unchanged
(`revKeep`), so each window is read off `reverseLowerWalk d` itself. -/

private def revStepL (L : List Program) (k : Nat) (e : InteriorEdge) : List Program :=
  L.take k ++ (e.newR ++ (L.drop k).drop 3)

private theorem revStep (L : List Program) (k : Nat) (e : InteriorEdge) (he : e ∈ interiorEdges)
    (h : ReverseLowerFacts e) (hat : (L.drop k).take 3 = e.oldR) :
    LRel e.count (revStepL L k e) L := by
  have split : L = L.take k ++ (e.oldR ++ (L.drop k).drop 3) := by
    have rest := (List.take_append_drop 3 (L.drop k)).symm
    rw [hat] at rest
    calc
      L = L.take k ++ L.drop k := (List.take_append_drop _ _).symm
      _ = _ := congrArg (L.take k ++ ·) rest
  have lifted := (LRel.refl (L.take k)).app ((reverseLowerRel e he h).app (LRel.refl ((L.drop k).drop 3)))
  rw [← split] at lifted
  exact lifted.cast (by omega)

private theorem revKeep (L : List Program) (k1 k2 : Nat) (e : InteriorEdge)
    (hd : k2 + 3 ≤ k1) (hl : ((L.drop k2).take 3).length = 3) :
    ((revStepL L k1 e).drop k2).take 3 = (L.drop k2).take 3 := by
  have h1 : k2 + 3 ≤ L.length := by
    simp only [List.length_take, List.length_drop] at hl
    omega
  have hk : k2 ≤ (L.take k1).length := by simp only [List.length_take]; omega
  unfold revStepL
  rw [List.drop_append_of_le_length hk]
  have hk2 : 3 ≤ ((L.take k1).drop k2).length := by
    simp only [List.length_drop, List.length_take]; omega
  rw [List.take_append_of_le_length hk2, List.drop_take, List.take_take]
  congr 1
  omega

private def revE1 : InteriorEdge := ⟨.short 0, .short 1, 225, 7⟩
private def revW1 (d : Bool) : List Program := revStepL (reverseLowerWalk d) 138 revE1
private theorem revE1_mem : revE1 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE1_facts : ReverseLowerFacts revE1 :=
  revFacts_of _ (by decide +kernel)
private theorem revE1_at0 (d : Bool) : ((reverseLowerWalk d).drop 138).take 3 = revE1.oldR := by
  rfl
private theorem revE1_at (d : Bool) : ((reverseLowerWalk d).drop 138).take 3 = revE1.oldR := by
  have p0 := revE1_at0 d
  exact p0
private theorem revE1_rel (d : Bool) : LRel 7 (revW1 d) (reverseLowerWalk d) :=
  revStep _ 138 revE1 revE1_mem revE1_facts (revE1_at d)

private def revE2 : InteriorEdge := ⟨.short 1, .short 2, 217, 8⟩
private def revW2 (d : Bool) : List Program := revStepL (revW1 d) 132 revE2
private theorem revE2_mem : revE2 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE2_facts : ReverseLowerFacts revE2 :=
  revFacts_of _ (by decide +kernel)
private theorem revE2_at0 (d : Bool) : ((reverseLowerWalk d).drop 132).take 3 = revE2.oldR := by
  rfl
private theorem revE2_at (d : Bool) : ((revW1 d).drop 132).take 3 = revE2.oldR := by
  have p0 := revE2_at0 d
  have p1 : ((revW1 d).drop 132).take 3 = revE2.oldR :=
    (revKeep _ 138 132 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  exact p1
private theorem revE2_rel (d : Bool) : LRel 8 (revW2 d) (revW1 d) :=
  revStep _ 132 revE2 revE2_mem revE2_facts (revE2_at d)

private def revE3 : InteriorEdge := ⟨.short 2, .short 3, 210, 7⟩
private def revW3 (d : Bool) : List Program := revStepL (revW2 d) 126 revE3
private theorem revE3_mem : revE3 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE3_facts : ReverseLowerFacts revE3 :=
  revFacts_of _ (by decide +kernel)
private theorem revE3_at0 (d : Bool) : ((reverseLowerWalk d).drop 126).take 3 = revE3.oldR := by
  rfl
private theorem revE3_at (d : Bool) : ((revW2 d).drop 126).take 3 = revE3.oldR := by
  have p0 := revE3_at0 d
  have p1 : ((revW1 d).drop 126).take 3 = revE3.oldR :=
    (revKeep _ 138 126 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 126).take 3 = revE3.oldR :=
    (revKeep _ 132 126 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  exact p2
private theorem revE3_rel (d : Bool) : LRel 7 (revW3 d) (revW2 d) :=
  revStep _ 126 revE3 revE3_mem revE3_facts (revE3_at d)

private def revE4 : InteriorEdge := ⟨.short 3, .short 4, 202, 8⟩
private def revW4 (d : Bool) : List Program := revStepL (revW3 d) 120 revE4
private theorem revE4_mem : revE4 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE4_facts : ReverseLowerFacts revE4 :=
  revFacts_of _ (by decide +kernel)
private theorem revE4_at0 (d : Bool) : ((reverseLowerWalk d).drop 120).take 3 = revE4.oldR := by
  rfl
private theorem revE4_at (d : Bool) : ((revW3 d).drop 120).take 3 = revE4.oldR := by
  have p0 := revE4_at0 d
  have p1 : ((revW1 d).drop 120).take 3 = revE4.oldR :=
    (revKeep _ 138 120 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 120).take 3 = revE4.oldR :=
    (revKeep _ 132 120 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 120).take 3 = revE4.oldR :=
    (revKeep _ 126 120 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  exact p3
private theorem revE4_rel (d : Bool) : LRel 8 (revW4 d) (revW3 d) :=
  revStep _ 120 revE4 revE4_mem revE4_facts (revE4_at d)

private def revE5 : InteriorEdge := ⟨.short 4, .short 5, 195, 7⟩
private def revW5 (d : Bool) : List Program := revStepL (revW4 d) 114 revE5
private theorem revE5_mem : revE5 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE5_facts : ReverseLowerFacts revE5 :=
  revFacts_of _ (by decide +kernel)
private theorem revE5_at0 (d : Bool) : ((reverseLowerWalk d).drop 114).take 3 = revE5.oldR := by
  rfl
private theorem revE5_at (d : Bool) : ((revW4 d).drop 114).take 3 = revE5.oldR := by
  have p0 := revE5_at0 d
  have p1 : ((revW1 d).drop 114).take 3 = revE5.oldR :=
    (revKeep _ 138 114 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 114).take 3 = revE5.oldR :=
    (revKeep _ 132 114 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 114).take 3 = revE5.oldR :=
    (revKeep _ 126 114 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 114).take 3 = revE5.oldR :=
    (revKeep _ 120 114 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  exact p4
private theorem revE5_rel (d : Bool) : LRel 7 (revW5 d) (revW4 d) :=
  revStep _ 114 revE5 revE5_mem revE5_facts (revE5_at d)

private def revE6 : InteriorEdge := ⟨.short 5, .short 6, 187, 8⟩
private def revW6 (d : Bool) : List Program := revStepL (revW5 d) 108 revE6
private theorem revE6_mem : revE6 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE6_facts : ReverseLowerFacts revE6 :=
  revFacts_of _ (by decide +kernel)
private theorem revE6_at0 (d : Bool) : ((reverseLowerWalk d).drop 108).take 3 = revE6.oldR := by
  rfl
private theorem revE6_at (d : Bool) : ((revW5 d).drop 108).take 3 = revE6.oldR := by
  have p0 := revE6_at0 d
  have p1 : ((revW1 d).drop 108).take 3 = revE6.oldR :=
    (revKeep _ 138 108 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 108).take 3 = revE6.oldR :=
    (revKeep _ 132 108 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 108).take 3 = revE6.oldR :=
    (revKeep _ 126 108 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 108).take 3 = revE6.oldR :=
    (revKeep _ 120 108 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 108).take 3 = revE6.oldR :=
    (revKeep _ 114 108 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  exact p5
private theorem revE6_rel (d : Bool) : LRel 8 (revW6 d) (revW5 d) :=
  revStep _ 108 revE6 revE6_mem revE6_facts (revE6_at d)

private def revE7 : InteriorEdge := ⟨.short 6, .short 7, 180, 7⟩
private def revW7 (d : Bool) : List Program := revStepL (revW6 d) 102 revE7
private theorem revE7_mem : revE7 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE7_facts : ReverseLowerFacts revE7 :=
  revFacts_of _ (by decide +kernel)
private theorem revE7_at0 (d : Bool) : ((reverseLowerWalk d).drop 102).take 3 = revE7.oldR := by
  rfl
private theorem revE7_at (d : Bool) : ((revW6 d).drop 102).take 3 = revE7.oldR := by
  have p0 := revE7_at0 d
  have p1 : ((revW1 d).drop 102).take 3 = revE7.oldR :=
    (revKeep _ 138 102 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 102).take 3 = revE7.oldR :=
    (revKeep _ 132 102 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 102).take 3 = revE7.oldR :=
    (revKeep _ 126 102 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 102).take 3 = revE7.oldR :=
    (revKeep _ 120 102 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 102).take 3 = revE7.oldR :=
    (revKeep _ 114 102 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 102).take 3 = revE7.oldR :=
    (revKeep _ 108 102 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  exact p6
private theorem revE7_rel (d : Bool) : LRel 7 (revW7 d) (revW6 d) :=
  revStep _ 102 revE7 revE7_mem revE7_facts (revE7_at d)

private def revE8 : InteriorEdge := ⟨.short 7, .wide 0, 172, 10⟩
private def revW8 (d : Bool) : List Program := revStepL (revW7 d) 96 revE8
private theorem revE8_mem : revE8 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE8_facts : ReverseLowerFacts revE8 :=
  revFacts_of _ (by decide +kernel)
private theorem revE8_at0 (d : Bool) : ((reverseLowerWalk d).drop 96).take 3 = revE8.oldR := by
  rfl
private theorem revE8_at (d : Bool) : ((revW7 d).drop 96).take 3 = revE8.oldR := by
  have p0 := revE8_at0 d
  have p1 : ((revW1 d).drop 96).take 3 = revE8.oldR :=
    (revKeep _ 138 96 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 96).take 3 = revE8.oldR :=
    (revKeep _ 132 96 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 96).take 3 = revE8.oldR :=
    (revKeep _ 126 96 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 96).take 3 = revE8.oldR :=
    (revKeep _ 120 96 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 96).take 3 = revE8.oldR :=
    (revKeep _ 114 96 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 96).take 3 = revE8.oldR :=
    (revKeep _ 108 96 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 96).take 3 = revE8.oldR :=
    (revKeep _ 102 96 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  exact p7
private theorem revE8_rel (d : Bool) : LRel 10 (revW8 d) (revW7 d) :=
  revStep _ 96 revE8 revE8_mem revE8_facts (revE8_at d)

private def revE9 : InteriorEdge := ⟨.wide 0, .wide 1, 162, 10⟩
private def revW9 (d : Bool) : List Program := revStepL (revW8 d) 90 revE9
private theorem revE9_mem : revE9 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE9_facts : ReverseLowerFacts revE9 :=
  revFacts_of _ (by decide +kernel)
private theorem revE9_at0 (d : Bool) : ((reverseLowerWalk d).drop 90).take 3 = revE9.oldR := by
  rfl
private theorem revE9_at (d : Bool) : ((revW8 d).drop 90).take 3 = revE9.oldR := by
  have p0 := revE9_at0 d
  have p1 : ((revW1 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 138 90 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 132 90 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 126 90 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 120 90 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 114 90 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 108 90 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 102 90 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 90).take 3 = revE9.oldR :=
    (revKeep _ 96 90 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  exact p8
private theorem revE9_rel (d : Bool) : LRel 10 (revW9 d) (revW8 d) :=
  revStep _ 90 revE9 revE9_mem revE9_facts (revE9_at d)

private def revE10 : InteriorEdge := ⟨.wide 1, .wide 2, 152, 10⟩
private def revW10 (d : Bool) : List Program := revStepL (revW9 d) 83 revE10
private theorem revE10_mem : revE10 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE10_facts : ReverseLowerFacts revE10 :=
  revFacts_of _ (by decide +kernel)
private theorem revE10_at0 (d : Bool) : ((reverseLowerWalk d).drop 83).take 3 = revE10.oldR := by
  rfl
private theorem revE10_at (d : Bool) : ((revW9 d).drop 83).take 3 = revE10.oldR := by
  have p0 := revE10_at0 d
  have p1 : ((revW1 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 138 83 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 132 83 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 126 83 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 120 83 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 114 83 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 108 83 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 102 83 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 96 83 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 83).take 3 = revE10.oldR :=
    (revKeep _ 90 83 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  exact p9
private theorem revE10_rel (d : Bool) : LRel 10 (revW10 d) (revW9 d) :=
  revStep _ 83 revE10 revE10_mem revE10_facts (revE10_at d)

private def revE11 : InteriorEdge := ⟨.wide 2, .wide 3, 142, 10⟩
private def revW11 (d : Bool) : List Program := revStepL (revW10 d) 76 revE11
private theorem revE11_mem : revE11 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE11_facts : ReverseLowerFacts revE11 :=
  revFacts_of _ (by decide +kernel)
private theorem revE11_at0 (d : Bool) : ((reverseLowerWalk d).drop 76).take 3 = revE11.oldR := by
  rfl
private theorem revE11_at (d : Bool) : ((revW10 d).drop 76).take 3 = revE11.oldR := by
  have p0 := revE11_at0 d
  have p1 : ((revW1 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 138 76 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 132 76 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 126 76 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 120 76 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 114 76 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 108 76 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 102 76 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 96 76 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 90 76 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 76).take 3 = revE11.oldR :=
    (revKeep _ 83 76 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  exact p10
private theorem revE11_rel (d : Bool) : LRel 10 (revW11 d) (revW10 d) :=
  revStep _ 76 revE11 revE11_mem revE11_facts (revE11_at d)

private def revE12 : InteriorEdge := ⟨.wide 3, .wide 4, 132, 10⟩
private def revW12 (d : Bool) : List Program := revStepL (revW11 d) 69 revE12
private theorem revE12_mem : revE12 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE12_facts : ReverseLowerFacts revE12 :=
  revFacts_of _ (by decide +kernel)
private theorem revE12_at0 (d : Bool) : ((reverseLowerWalk d).drop 69).take 3 = revE12.oldR := by
  rfl
private theorem revE12_at (d : Bool) : ((revW11 d).drop 69).take 3 = revE12.oldR := by
  have p0 := revE12_at0 d
  have p1 : ((revW1 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 138 69 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 132 69 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 126 69 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 120 69 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 114 69 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 108 69 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 102 69 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 96 69 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 90 69 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 83 69 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 69).take 3 = revE12.oldR :=
    (revKeep _ 76 69 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  exact p11
private theorem revE12_rel (d : Bool) : LRel 10 (revW12 d) (revW11 d) :=
  revStep _ 69 revE12 revE12_mem revE12_facts (revE12_at d)

private def revE13 : InteriorEdge := ⟨.wide 4, .wide 5, 122, 10⟩
private def revW13 (d : Bool) : List Program := revStepL (revW12 d) 62 revE13
private theorem revE13_mem : revE13 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE13_facts : ReverseLowerFacts revE13 :=
  revFacts_of _ (by decide +kernel)
private theorem revE13_at0 (d : Bool) : ((reverseLowerWalk d).drop 62).take 3 = revE13.oldR := by
  rfl
private theorem revE13_at (d : Bool) : ((revW12 d).drop 62).take 3 = revE13.oldR := by
  have p0 := revE13_at0 d
  have p1 : ((revW1 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 138 62 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 132 62 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 126 62 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 120 62 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 114 62 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 108 62 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 102 62 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 96 62 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 90 62 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 83 62 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 76 62 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 62).take 3 = revE13.oldR :=
    (revKeep _ 69 62 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  exact p12
private theorem revE13_rel (d : Bool) : LRel 10 (revW13 d) (revW12 d) :=
  revStep _ 62 revE13 revE13_mem revE13_facts (revE13_at d)

private def revE14 : InteriorEdge := ⟨.wide 5, .wide 6, 112, 10⟩
private def revW14 (d : Bool) : List Program := revStepL (revW13 d) 55 revE14
private theorem revE14_mem : revE14 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE14_facts : ReverseLowerFacts revE14 :=
  revFacts_of _ (by decide +kernel)
private theorem revE14_at0 (d : Bool) : ((reverseLowerWalk d).drop 55).take 3 = revE14.oldR := by
  rfl
private theorem revE14_at (d : Bool) : ((revW13 d).drop 55).take 3 = revE14.oldR := by
  have p0 := revE14_at0 d
  have p1 : ((revW1 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 138 55 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 132 55 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 126 55 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 120 55 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 114 55 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 108 55 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 102 55 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 96 55 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 90 55 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 83 55 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 76 55 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 69 55 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  have p13 : ((revW13 d).drop 55).take 3 = revE14.oldR :=
    (revKeep _ 62 55 revE13 (by decide) (by rw [p12]; rfl)).trans p12
  exact p13
private theorem revE14_rel (d : Bool) : LRel 10 (revW14 d) (revW13 d) :=
  revStep _ 55 revE14 revE14_mem revE14_facts (revE14_at d)

private def revE15 : InteriorEdge := ⟨.wide 6, .wide 7, 102, 10⟩
private def revW15 (d : Bool) : List Program := revStepL (revW14 d) 48 revE15
private theorem revE15_mem : revE15 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE15_facts : ReverseLowerFacts revE15 :=
  revFacts_of _ (by decide +kernel)
private theorem revE15_at0 (d : Bool) : ((reverseLowerWalk d).drop 48).take 3 = revE15.oldR := by
  rfl
private theorem revE15_at (d : Bool) : ((revW14 d).drop 48).take 3 = revE15.oldR := by
  have p0 := revE15_at0 d
  have p1 : ((revW1 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 138 48 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 132 48 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 126 48 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 120 48 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 114 48 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 108 48 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 102 48 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 96 48 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 90 48 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 83 48 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 76 48 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 69 48 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  have p13 : ((revW13 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 62 48 revE13 (by decide) (by rw [p12]; rfl)).trans p12
  have p14 : ((revW14 d).drop 48).take 3 = revE15.oldR :=
    (revKeep _ 55 48 revE14 (by decide) (by rw [p13]; rfl)).trans p13
  exact p14
private theorem revE15_rel (d : Bool) : LRel 10 (revW15 d) (revW14 d) :=
  revStep _ 48 revE15 revE15_mem revE15_facts (revE15_at d)

private def revE16 : InteriorEdge := ⟨.wide 8, .short 20, 82, 8⟩
private def revW16 (d : Bool) : List Program := revStepL (revW15 d) 34 revE16
private theorem revE16_mem : revE16 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE16_facts : ReverseLowerFacts revE16 :=
  revFacts_of _ (by decide +kernel)
private theorem revE16_at0 (d : Bool) : ((reverseLowerWalk d).drop 34).take 3 = revE16.oldR := by
  rfl
private theorem revE16_at (d : Bool) : ((revW15 d).drop 34).take 3 = revE16.oldR := by
  have p0 := revE16_at0 d
  have p1 : ((revW1 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 138 34 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 132 34 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 126 34 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 120 34 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 114 34 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 108 34 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 102 34 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 96 34 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 90 34 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 83 34 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 76 34 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 69 34 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  have p13 : ((revW13 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 62 34 revE13 (by decide) (by rw [p12]; rfl)).trans p12
  have p14 : ((revW14 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 55 34 revE14 (by decide) (by rw [p13]; rfl)).trans p13
  have p15 : ((revW15 d).drop 34).take 3 = revE16.oldR :=
    (revKeep _ 48 34 revE15 (by decide) (by rw [p14]; rfl)).trans p14
  exact p15
private theorem revE16_rel (d : Bool) : LRel 8 (revW16 d) (revW15 d) :=
  revStep _ 34 revE16 revE16_mem revE16_facts (revE16_at d)

private def revE17 : InteriorEdge := ⟨.short 20, .short 21, 75, 7⟩
private def revW17 (d : Bool) : List Program := revStepL (revW16 d) 27 revE17
private theorem revE17_mem : revE17 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE17_facts : ReverseLowerFacts revE17 :=
  revFacts_of _ (by decide +kernel)
private theorem revE17_at0 (d : Bool) : ((reverseLowerWalk d).drop 27).take 3 = revE17.oldR := by
  rfl
private theorem revE17_at (d : Bool) : ((revW16 d).drop 27).take 3 = revE17.oldR := by
  have p0 := revE17_at0 d
  have p1 : ((revW1 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 138 27 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 132 27 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 126 27 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 120 27 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 114 27 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 108 27 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 102 27 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 96 27 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 90 27 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 83 27 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 76 27 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 69 27 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  have p13 : ((revW13 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 62 27 revE13 (by decide) (by rw [p12]; rfl)).trans p12
  have p14 : ((revW14 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 55 27 revE14 (by decide) (by rw [p13]; rfl)).trans p13
  have p15 : ((revW15 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 48 27 revE15 (by decide) (by rw [p14]; rfl)).trans p14
  have p16 : ((revW16 d).drop 27).take 3 = revE17.oldR :=
    (revKeep _ 34 27 revE16 (by decide) (by rw [p15]; rfl)).trans p15
  exact p16
private theorem revE17_rel (d : Bool) : LRel 7 (revW17 d) (revW16 d) :=
  revStep _ 27 revE17 revE17_mem revE17_facts (revE17_at d)

private def revE18 : InteriorEdge := ⟨.short 21, .short 22, 67, 8⟩
private def revW18 (d : Bool) : List Program := revStepL (revW17 d) 21 revE18
private theorem revE18_mem : revE18 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE18_facts : ReverseLowerFacts revE18 :=
  revFacts_of _ (by decide +kernel)
private theorem revE18_at0 (d : Bool) : ((reverseLowerWalk d).drop 21).take 3 = revE18.oldR := by
  rfl
private theorem revE18_at (d : Bool) : ((revW17 d).drop 21).take 3 = revE18.oldR := by
  have p0 := revE18_at0 d
  have p1 : ((revW1 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 138 21 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 132 21 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 126 21 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 120 21 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 114 21 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 108 21 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 102 21 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 96 21 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 90 21 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 83 21 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 76 21 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 69 21 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  have p13 : ((revW13 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 62 21 revE13 (by decide) (by rw [p12]; rfl)).trans p12
  have p14 : ((revW14 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 55 21 revE14 (by decide) (by rw [p13]; rfl)).trans p13
  have p15 : ((revW15 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 48 21 revE15 (by decide) (by rw [p14]; rfl)).trans p14
  have p16 : ((revW16 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 34 21 revE16 (by decide) (by rw [p15]; rfl)).trans p15
  have p17 : ((revW17 d).drop 21).take 3 = revE18.oldR :=
    (revKeep _ 27 21 revE17 (by decide) (by rw [p16]; rfl)).trans p16
  exact p17
private theorem revE18_rel (d : Bool) : LRel 8 (revW18 d) (revW17 d) :=
  revStep _ 21 revE18 revE18_mem revE18_facts (revE18_at d)

private def revE19 : InteriorEdge := ⟨.short 22, .short 23, 60, 7⟩
private def revW19 (d : Bool) : List Program := revStepL (revW18 d) 15 revE19
private theorem revE19_mem : revE19 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE19_facts : ReverseLowerFacts revE19 :=
  revFacts_of _ (by decide +kernel)
private theorem revE19_at0 (d : Bool) : ((reverseLowerWalk d).drop 15).take 3 = revE19.oldR := by
  rfl
private theorem revE19_at (d : Bool) : ((revW18 d).drop 15).take 3 = revE19.oldR := by
  have p0 := revE19_at0 d
  have p1 : ((revW1 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 138 15 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 132 15 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 126 15 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 120 15 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 114 15 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 108 15 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 102 15 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 96 15 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 90 15 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 83 15 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 76 15 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 69 15 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  have p13 : ((revW13 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 62 15 revE13 (by decide) (by rw [p12]; rfl)).trans p12
  have p14 : ((revW14 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 55 15 revE14 (by decide) (by rw [p13]; rfl)).trans p13
  have p15 : ((revW15 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 48 15 revE15 (by decide) (by rw [p14]; rfl)).trans p14
  have p16 : ((revW16 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 34 15 revE16 (by decide) (by rw [p15]; rfl)).trans p15
  have p17 : ((revW17 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 27 15 revE17 (by decide) (by rw [p16]; rfl)).trans p16
  have p18 : ((revW18 d).drop 15).take 3 = revE19.oldR :=
    (revKeep _ 21 15 revE18 (by decide) (by rw [p17]; rfl)).trans p17
  exact p18
private theorem revE19_rel (d : Bool) : LRel 7 (revW19 d) (revW18 d) :=
  revStep _ 15 revE19 revE19_mem revE19_facts (revE19_at d)

private def revE20 : InteriorEdge := ⟨.short 23, .short 24, 52, 8⟩
private def revW20 (d : Bool) : List Program := revStepL (revW19 d) 9 revE20
private theorem revE20_mem : revE20 ∈ interiorEdges := by decide
set_option maxRecDepth 100000 in
private theorem revE20_facts : ReverseLowerFacts revE20 :=
  revFacts_of _ (by decide +kernel)
private theorem revE20_at0 (d : Bool) : ((reverseLowerWalk d).drop 9).take 3 = revE20.oldR := by
  rfl
private theorem revE20_at (d : Bool) : ((revW19 d).drop 9).take 3 = revE20.oldR := by
  have p0 := revE20_at0 d
  have p1 : ((revW1 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 138 9 revE1 (by decide) (by rw [p0]; rfl)).trans p0
  have p2 : ((revW2 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 132 9 revE2 (by decide) (by rw [p1]; rfl)).trans p1
  have p3 : ((revW3 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 126 9 revE3 (by decide) (by rw [p2]; rfl)).trans p2
  have p4 : ((revW4 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 120 9 revE4 (by decide) (by rw [p3]; rfl)).trans p3
  have p5 : ((revW5 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 114 9 revE5 (by decide) (by rw [p4]; rfl)).trans p4
  have p6 : ((revW6 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 108 9 revE6 (by decide) (by rw [p5]; rfl)).trans p5
  have p7 : ((revW7 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 102 9 revE7 (by decide) (by rw [p6]; rfl)).trans p6
  have p8 : ((revW8 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 96 9 revE8 (by decide) (by rw [p7]; rfl)).trans p7
  have p9 : ((revW9 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 90 9 revE9 (by decide) (by rw [p8]; rfl)).trans p8
  have p10 : ((revW10 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 83 9 revE10 (by decide) (by rw [p9]; rfl)).trans p9
  have p11 : ((revW11 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 76 9 revE11 (by decide) (by rw [p10]; rfl)).trans p10
  have p12 : ((revW12 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 69 9 revE12 (by decide) (by rw [p11]; rfl)).trans p11
  have p13 : ((revW13 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 62 9 revE13 (by decide) (by rw [p12]; rfl)).trans p12
  have p14 : ((revW14 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 55 9 revE14 (by decide) (by rw [p13]; rfl)).trans p13
  have p15 : ((revW15 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 48 9 revE15 (by decide) (by rw [p14]; rfl)).trans p14
  have p16 : ((revW16 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 34 9 revE16 (by decide) (by rw [p15]; rfl)).trans p15
  have p17 : ((revW17 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 27 9 revE17 (by decide) (by rw [p16]; rfl)).trans p16
  have p18 : ((revW18 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 21 9 revE18 (by decide) (by rw [p17]; rfl)).trans p17
  have p19 : ((revW19 d).drop 9).take 3 = revE20.oldR :=
    (revKeep _ 15 9 revE19 (by decide) (by rw [p18]; rfl)).trans p18
  exact p19
private theorem revE20_rel (d : Bool) : LRel 8 (revW20 d) (revW19 d) :=
  revStep _ 9 revE20 revE20_mem revE20_facts (revE20_at d)

private theorem revAllDeploy (d : Bool) : LRel 170 (revW20 d) (reverseLowerWalk d) := by
  have h : LRel 0 (reverseLowerWalk d) (reverseLowerWalk d) := LRel.refl _
  have h1 : LRel 7 (revW1 d) (reverseLowerWalk d) := Rel.trans (revE1_rel d) h
  have h2 : LRel 15 (revW2 d) (reverseLowerWalk d) := Rel.trans (revE2_rel d) h1
  have h3 : LRel 22 (revW3 d) (reverseLowerWalk d) := Rel.trans (revE3_rel d) h2
  have h4 : LRel 30 (revW4 d) (reverseLowerWalk d) := Rel.trans (revE4_rel d) h3
  have h5 : LRel 37 (revW5 d) (reverseLowerWalk d) := Rel.trans (revE5_rel d) h4
  have h6 : LRel 45 (revW6 d) (reverseLowerWalk d) := Rel.trans (revE6_rel d) h5
  have h7 : LRel 52 (revW7 d) (reverseLowerWalk d) := Rel.trans (revE7_rel d) h6
  have h8 : LRel 62 (revW8 d) (reverseLowerWalk d) := Rel.trans (revE8_rel d) h7
  have h9 : LRel 72 (revW9 d) (reverseLowerWalk d) := Rel.trans (revE9_rel d) h8
  have h10 : LRel 82 (revW10 d) (reverseLowerWalk d) := Rel.trans (revE10_rel d) h9
  have h11 : LRel 92 (revW11 d) (reverseLowerWalk d) := Rel.trans (revE11_rel d) h10
  have h12 : LRel 102 (revW12 d) (reverseLowerWalk d) := Rel.trans (revE12_rel d) h11
  have h13 : LRel 112 (revW13 d) (reverseLowerWalk d) := Rel.trans (revE13_rel d) h12
  have h14 : LRel 122 (revW14 d) (reverseLowerWalk d) := Rel.trans (revE14_rel d) h13
  have h15 : LRel 132 (revW15 d) (reverseLowerWalk d) := Rel.trans (revE15_rel d) h14
  have h16 : LRel 140 (revW16 d) (reverseLowerWalk d) := Rel.trans (revE16_rel d) h15
  have h17 : LRel 147 (revW17 d) (reverseLowerWalk d) := Rel.trans (revE17_rel d) h16
  have h18 : LRel 155 (revW18 d) (reverseLowerWalk d) := Rel.trans (revE18_rel d) h17
  have h19 : LRel 162 (revW19 d) (reverseLowerWalk d) := Rel.trans (revE19_rel d) h18
  have h20 : LRel 170 (revW20 d) (reverseLowerWalk d) := Rel.trans (revE20_rel d) h19
  exact h20

attribute [irreducible] revW20

def reverse (d : Bool) : Program := (revW20 d).flatten

theorem fwdRel (d : Bool) : Rel 270 (forward d) (MixedWindow.forwardMixedCut d) := forward_relInterior d
theorem revRel (d : Bool) : Rel 271 (reverse d) (TickCut.Mixed.reverse d) :=
  Rel.trans (revAllDeploy d) (Rel.trans (reverseLowerDeploy d) (reverse_relX d))

theorem run_eq (d : Bool) :
    run (forward d) = run (MixedWindow.forwardMixed d) ∧
    run (MixedWindow.reverseMixedCut d) = run (MixedWindow.reverseMixed d) := by
  refine ⟨?_, (MixedWindow.mixedCut_run_eq d).2⟩
  funext m s
  rw [(fwdRel d).run_eq m s, (MixedWindow.mixedCut_run_eq d).1]

theorem reverse_run_eq (d : Bool) : run (reverse d) = run (TickCut.Mixed.reverseUncut d) := by
  funext m s
  rw [(revRel d).run_eq m s, TickCut.Mixed.reverse_run_eq d]

theorem mixed_counts (d : Bool) :
    toffoliCount (forward d) = 126272 ∧
    toffoliCount (reverse d) = (if d then 126094 else 126116) ∧
    measurementCount (forward d) = (if d then 65251 else 65273) ∧
    measurementCount (reverse d) = (if d then 65162 else 65184) := by
  have old := TickCut.Mixed.mixed_counts d
  rw [TickCut.Mixed.forward_eq] at old
  have ft := (fwdRel d).tc_eq
  have fm := (fwdRel d).mc_eq
  have rt := (revRel d).tc_eq
  have rm := (revRel d).mc_eq
  cases d <;> simp only [Bool.false_eq_true, ↓reduceIte] at old ⊢ <;>
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem physical (d : Bool) :
    GatePhysical (forward d) ∧ GatePhysical (MixedWindow.reverseMixedCut d) :=
  ⟨(fwdRel d).phys (MixedWindow.mixedCut_physical d).1, (MixedWindow.mixedCut_physical d).2⟩

theorem covered (d : Bool) :
    WindowCovered.CoveredW (forward d) ∧ WindowCovered.CoveredW (MixedWindow.reverseMixedCut d) :=
  ⟨fun q h => (MixedWindow.mixedCut_covered d).1 q ((fwdRel d).wires_sub h),
   (MixedWindow.mixedCut_covered d).2⟩

theorem slots_le (d : Bool) :
    gateSlots (forward d) ≤ gateSlots (MixedWindow.forwardMixed d) ∧
    gateSlots (MixedWindow.reverseMixedCut d) ≤ gateSlots (MixedWindow.reverseMixed d) :=
  ⟨(fwdRel d).slots_le.trans (MixedWindow.mixedCut_slots_le d).1, (MixedWindow.mixedCut_slots_le d).2⟩

theorem rphysical (d : Bool) : GatePhysical (reverse d) := (revRel d).phys (TickCut.Mixed.physical d)

theorem rcovered (d : Bool) : WindowCovered.CoveredW (reverse d) :=
  fun q h => TickCut.Mixed.covered d q ((revRel d).wires_sub h)

theorem rslots_le (d : Bool) :
    gateSlots (reverse d) ≤ gateSlots (MixedWindow.reverseMixedCut d) + 1197 :=
  (revRel d).slots_le.trans (TickCut.Mixed.slots_le d)

end ECDSAAdd.Entrant.StairPacket.Shadow20.MergeCut

end

/-! ### Head of the former Main.lean (moved here unchanged to balance the replay) -/

section

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ECDSAAdd.Arithmetic.MappedCompressed

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts
open Arithmetic MappedCompressed Stair44Resources StairConcreteAssembly StairArchiveInactive
open StairArchiveRelease StairArchiveNativeCut StairArchiveTen StairArchiveGates
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount measurementCount StairGroups.packet
  StairArchiveInactive.packet fieldHook

/-- The smallest-rail sign relocated into the last B87 rest letter. -/
def signHost : Wire := base 510

def signPayload : List Wire := (List.range' 1 84).flatMap pkSitesOf

def prefixDataPorts : List Nat := [0, 1, 2, 3, 4, 6, 7, 8]
def prefixEncodedPorts : List Nat := prefixDataPorts.drop 1

def prefixExpand (n : Nat) : Nat :=
  prefixEncodedPorts.zipIdx.foldl
    (fun acc p => if n.testBit p.2 then acc + 2 ^ p.1 else acc) 0

def prefixParityValue (n : Nat) : Bool :=
  let d := MeasuredCodec5.bitRun FourScratchPrefix.invV (prefixExpand n)
  TraceParity5.parity (prefixDataPorts.map d.testBit)

def prefixLoanSites : List Wire :=
  [tagPort 86, tagPort 7, tagPort 8, tagPort 9, tagPort 10, tagPort 87,
    tagPort 11, tagPort 12, tagPort 13, tagPort 88, tagPort 89, tagPort 90]

def prefixLoanPort (i : Nat) : Wire := prefixLoanSites[i]?.getD i

def xorIntoSign (xs : List Wire) : Program := xs.map fun q => .CX q signHost

def prefixParity : Program :=
  renameProgram prefixLoanPort FourScratchPrefix.invV ++
    xorIntoSign (prefixDataPorts.map prefixLoanPort) ++
    renameProgram prefixLoanPort FourScratchPrefix.clearV

def signBracket : Program := prefixParity ++ xorIntoSign signPayload

def spk (d : Bool) (k : Nat) : Program :=
  renameProgram (Equiv.swap (base 720) signHost) (rpk d k)

def sfirst (j : Nat) (rev : Bool) := spk (!rev) (if rev then j + 1 else j)
def ssecond (j : Nat) (rev : Bool) := spk (!rev) (if rev then j else j + 1)

def sten (j : Nat) (rev : Bool) :=
  fieldHook j (enter rev) ++ (sfirst j rev ++ (fieldHook j (shift rev) ++
    (ssecond j rev ++ fieldHook j (leave rev))))


/-- Fully decoded packet `k`, hosted like `opk` with its half-window carry on the archive tag,
    for every packet of the field group. -/
def gpk (d : Bool) (k : Nat) : Program :=
  renameProgram rawSwap (StairLoan.rebindMany StairSchedule.exclusiveRoles (StairPhysicalLayout.hosts 87)
    (renameProgram (OB5.sig 511) (RouteA.Rolling1588.rawPacket d k)))

/-- The fully decoded packet with its carry on the relocated sign site. -/
def epk (d : Bool) (k : Nat) : Program :=
  renameProgram (Equiv.swap (base 720) signHost) (gpk d k)

/-- A native leg of fully decoded packets with the carry on the sign site. -/
def egroup (d : Bool) (j n : Nat) : Program := PacketSequence.program d (epk d) j n

theorem gpk_hosted (d : Bool) (k : Nat) :
    gpk d k=renameProgram (fun q => rawSwap (StairArchiveInactive.host (OB5.sig 511 q)))
      (RouteA.Rolling1588.rawPacket d k) := by
  rw [gpk,StairArchiveInactive.hosts_eq,renameProgram_comp,renameProgram_comp]
  rfl

section
attribute [local irreducible] wires renameProgram opk
theorem gpk_sub (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) :
    wires (gpk d k)⊆insert (base 720) (wires (opk d k)) := by
  rw [gpk_hosted d k,renameProgram_support]
  intro q hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  have sub := RouteA.Rolling1588.rawPacket_wires d k (by omega) hp
  rw [← oddPk_regular d k lo hi] at sub
  rcases Finset.mem_insert.mp sub with e|member
  · subst e
    apply Finset.mem_insert.mpr
    left
    simp only [host_760,rawSwap,Equiv.swap_apply_left]
  · apply Finset.mem_insert_of_mem
    have hw : StairArchiveInactive.host (OB5.sig 511 p)∈wires (opk d k) := by
      rw [opk_hosted,renameProgram_support]; exact Finset.mem_image_of_mem _ member
    have fix : rawSwap (StairArchiveInactive.host (OB5.sig 511 p))=StairArchiveInactive.host (OB5.sig 511 p) :=
      Equiv.swap_apply_of_ne_of_ne (fun e => opk_avoid760 d k lo hi (e ▸ hw))
        (fun e => opk_avoid720 d k lo hi (e ▸ hw))
    simpa only [fix] using hw

end

theorem gpk_measure (c : Cost) (d : Bool) (k : Nat) (h1 : 1≤k) (h2 : k≤84) :
    c.measure (gpk d k)+(c.measure Rolling1588.d3short+c.measure Rolling1588.e3short)=c.measure (opk d k) := by
  have raw := RouteA.Rolling1588.rawPacket_measure_regular c d k
  have o : c.measure (opk d k)=c.measure (oddPk d k) := by
    simp only [opk,StairArchiveInactive.hosts_eq,c.rename]
  rw [o,oddPk_regular d k h1 h2,c.rename]
  rw [gpk,c.rename,StairArchiveInactive.hosts_eq,c.rename,c.rename]
  omega

theorem epk_measure (c : Cost) (d : Bool) (k : Nat) (h1 : 1≤k) (h2 : k≤84) :
    c.measure (epk d k)+(c.measure Rolling1588.d3short+c.measure Rolling1588.e3short)=c.measure (opk d k) := by
  rw [epk,c.rename]
  exact gpk_measure c d k h1 h2

theorem egroup_measure (c : Cost) (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    c.measure (egroup d j n)+n*(c.measure Rolling1588.d3short+c.measure Rolling1588.e3short)=
      c.measure (ogroup d j n) := by
  unfold egroup ogroup
  induction n generalizing j with
  | zero => simp only [PacketSequence.program,Nat.zero_mul,Nat.add_zero]
  | succ n ih =>
    have head := epk_measure c d j lo (by omega)
    have tail := ih (j+1) (by omega) (by omega)
    rw [Nat.succ_mul]
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true,c.append] <;> omega


def group84SignBody (d : Bool) : Program :=
  ordered d (sten 10 (!d)) (ordered d (rgroup d 12 1) (ordered d (sten 13 (!d)) (ordered d (rgroup d 15 1) (ordered d (sten 16 (!d)) (ordered d (rgroup d 18 1) (ordered d (sten 19 (!d)) (ordered d (rgroup d 21 1) (ordered d (sten 22 (!d)) (ordered d (rgroup d 24 1) (ordered d (sten 25 (!d)) (ordered d (rgroup d 27 1) (ordered d (sten 28 (!d)) (ordered d (rgroup d 30 1) (ordered d (sten 31 (!d)) (ordered d (rgroup d 33 2) (ordered d (sten 35 (!d)) (ordered d (rgroup d 37 2) (ordered d (sten 39 (!d)) (ordered d (rgroup d 41 2) (ordered d (sten 43 (!d)) (ordered d (rgroup d 45 2) (ordered d (sten 47 (!d)) (ordered d (rgroup d 49 2) (ordered d (sten 51 (!d)) (ordered d (rgroup d 53 2) (ordered d (sten 55 (!d)) (ordered d (rgroup d 57 2) (ordered d (sten 59 (!d)) (ordered d (rgroup d 61 2) (ordered d (sten 63 (!d)) (ordered d (rgroup d 65 2) (ordered d (sten 67 (!d)) (ordered d (rgroup d 69 1) (ordered d (sten 70 (!d)) (ordered d (rgroup d 72 1) (ordered d (sten 73 (!d)) (ordered d (rgroup d 75 1) (ordered d (sten 76 (!d)) (ordered d (rgroup d 78 1) (ordered d (sten 79 (!d)) (ordered d (rgroup d 81 1) (ordered d (sten 82 (!d)) ((rgroup d 84 1))))))))))))))))))))))))))))))))))))))))))))

def group84Sign (d : Bool) : Program :=
  signBracket ++ ordered d (egroup d 1 9)
    (packTag ++ renameProgram tagSwap (group84SignBody d) ++ unpackTag) ++ signBracket


namespace SignCounts

attribute [local irreducible] opk

theorem signBracket_t : toffoliCount signBracket = 13 := by decide +kernel
theorem signBracket_m : measurementCount signBracket = 11 := by decide +kernel
theorem signBracket_slots : Challenge.gateSlots signBracket = 1447 := by decide +kernel

theorem sten_measure (c : Stair44Resources.Cost) (d : Bool) (j : Nat)
    (lo : 10 ≤ j) (hi : j ≤ 83) :
    c.measure (sten j (!d)) +
        2 * (c.measure Rolling1588.d3short + c.measure Rolling1588.e3short) =
      c.measure (oten j (!d)) := by
  have a := rpk_measure c d j lo (by omega)
  have b := rpk_measure c d (j + 1) (by omega) (by omega)
  cases d <;>
    simp only [sten, oten, sfirst, ssecond, ofirst, osecond, spk, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, c.append, c.rename] <;> omega

theorem signBody_measure (c : Stair44Resources.Cost) (d : Bool) :
    c.measure (group84SignBody d) +
        44 * (c.measure Rolling1588.d3short + c.measure Rolling1588.e3short) =
      c.measure (group84Body d) := by
  have h10 := sten_measure c d 10 (by decide) (by decide)
  have h13 := sten_measure c d 13 (by decide) (by decide)
  have h16 := sten_measure c d 16 (by decide) (by decide)
  have h19 := sten_measure c d 19 (by decide) (by decide)
  have h22 := sten_measure c d 22 (by decide) (by decide)
  have h25 := sten_measure c d 25 (by decide) (by decide)
  have h28 := sten_measure c d 28 (by decide) (by decide)
  have h31 := sten_measure c d 31 (by decide) (by decide)
  have h35 := sten_measure c d 35 (by decide) (by decide)
  have h39 := sten_measure c d 39 (by decide) (by decide)
  have h43 := sten_measure c d 43 (by decide) (by decide)
  have h47 := sten_measure c d 47 (by decide) (by decide)
  have h51 := sten_measure c d 51 (by decide) (by decide)
  have h55 := sten_measure c d 55 (by decide) (by decide)
  have h59 := sten_measure c d 59 (by decide) (by decide)
  have h63 := sten_measure c d 63 (by decide) (by decide)
  have h67 := sten_measure c d 67 (by decide) (by decide)
  have h70 := sten_measure c d 70 (by decide) (by decide)
  have h73 := sten_measure c d 73 (by decide) (by decide)
  have h76 := sten_measure c d 76 (by decide) (by decide)
  have h79 := sten_measure c d 79 (by decide) (by decide)
  have h82 := sten_measure c d 82 (by decide) (by decide)
  simp only [group84SignBody, group84Body, ord]
  omega

theorem group_delta (d : Bool) :
    toffoliCount (group84Sign d) + 239 = toffoliCount (group84 d) ∧
    measurementCount (group84Sign d) + 31 = measurementCount (group84 d) ∧
    Challenge.gateSlots (group84Sign d) + 8925 = Challenge.gateSlots (group84 d) := by
  have et := egroup_measure Stair44Resources.tc d 1 9 (by decide) (by decide)
  have em := egroup_measure Stair44Resources.mc d 1 9 (by decide) (by decide)
  have es := egroup_measure Stair44Resources.slots d 1 9 (by decide) (by decide)
  change toffoliCount _ + 9 * (toffoliCount _ + toffoliCount _) = toffoliCount _ at et
  change measurementCount _ + 9 * (measurementCount _ + measurementCount _) = measurementCount _ at em
  change Challenge.gateSlots _ + 9 * (Challenge.gateSlots _ + Challenge.gateSlots _) =
    Challenge.gateSlots _ at es
  have ht := signBody_measure Stair44Resources.tc d
  have hm := signBody_measure Stair44Resources.mc d
  have hs := signBody_measure Stair44Resources.slots d
  have hc := RouteA.Rolling1588.codec_short_counts
  change toffoliCount _ + 44 * (toffoliCount _ + toffoliCount _) = toffoliCount _ at ht
  change measurementCount _ + 44 * (measurementCount _ + measurementCount _) = measurementCount _ at hm
  change Challenge.gateSlots _ + 44 * (Challenge.gateSlots _ + Challenge.gateSlots _) =
    Challenge.gateSlots _ at hs
  cases d <;> simp only [group84Sign, group84, ordered, Bool.false_eq_true, if_false, if_true,
    toffoliCount_append, measurementCount_append, Challenge.gateSlots_append,
    Baselines.rename_gateSlots, (renameProgram_counts _ _).1, (renameProgram_counts _ _).2,
    signBracket_t, signBracket_m, signBracket_slots] <;> omega

end SignCounts


end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts





section

namespace ECDSAAdd.Entrant.StairPacket.WindowWalkCosts
open Arithmetic MappedCompressed Stair44Resources Partial PartialCosts
set_option maxHeartbeats 1250000
set_option maxRecDepth 16000

/-- The replacement occupies [45,406); the initial fifteen ticks use a distinct placement. -/
def forward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.first (Rolling1588TickGap.forward d 1 15) ++
  renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 16 29 ++
    Shadow20.MergeCut.forward d ++ Rolling1588TickGap.forward d 421 tail)

def backward (d : Bool) (tail : Nat) : Program :=
  renameProgram Stair44WalkMap.rest (Rolling1588.reverse d 421 tail ++
    Shadow20.MergeCut.reverse d ++ Rolling1588.reverse d 16 29) ++
  renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)

theorem walk (c : Cost) (d : Bool) (tail f r : Nat)
    (hf : c.measure (Shadow20.MergeCut.forward d)+f=c.measure (Rolling1588TickGap.forward d 45 376))
    (hr : c.measure (Shadow20.MergeCut.reverse d)+r=c.measure (Rolling1588.reverse d 45 376)) :
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

attribute [local irreducible] Shadow20.MergeCut.forward Shadow20.MergeCut.reverse Rolling1588TickGap.forward Rolling1588.reverse
  Stair44WalkRun.forward Stair44WalkRun.backward toffoliCount measurementCount forward backward

private theorem subEq {x y a b : Nat} (n : Nat) (hx : x=a) (hy : y=b) (h : a+n=b) : x+n=y := by omega

theorem exactWalks (d : Bool) (tail : Nat) :
    toffoliCount (forward d tail)+(if d then 39828 else 39828)=
      toffoliCount (Stair44WalkRun.forward d (405+tail)) ∧
    toffoliCount (backward d tail)+(if d then 39979 else 39957)=
      toffoliCount (Stair44WalkRun.backward d (405+tail)) ∧
    measurementCount (forward d tail)+(if d then 17960 else 17938)=measurementCount (Stair44WalkRun.forward d (405+tail)) ∧
    measurementCount (backward d tail)+(if d then 17730 else 17708)=measurementCount (Stair44WalkRun.backward d (405+tail)) := by
  have sf := StockWindowCosts420.stock420from45 d
  have mcw := Shadow20.MergeCut.mixed_counts d
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte] at mcw ⊢
    have t := walk tc false tail 39828 39957 (subEq 39828 mcw.1 sf.1 (by omega)) (subEq 39957 mcw.2.1 sf.2.2.1 (by omega))
    have mv := walk mc false tail 17938 17708 (subEq 17938 mcw.2.2.1 sf.2.1 (by omega)) (subEq 17708 mcw.2.2.2 sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,mv⟩
  · simp only [↓reduceIte] at mcw ⊢
    have t := walk tc true tail 39828 39979 (subEq 39828 mcw.1 sf.1 (by omega)) (subEq 39979 mcw.2.1 sf.2.2.1 (by omega))
    have mv := walk mc true tail 17960 17730 (subEq 17960 mcw.2.2.1 sf.2.1 (by omega)) (subEq 17730 mcw.2.2.2 sf.2.2.2 (by omega))
    exact ⟨t.1,t.2,mv⟩

/-- Rewrite small arithmetic arguments before instantiating either physical walk. -/
theorem inst (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 39828 else 39828)=f) (hr : (if d then 39979 else 39957)=r) :
    tc.measure (forward d tail)+f=tc.measure (Stair44WalkRun.forward d n) ∧
    tc.measure (backward d tail)+r=tc.measure (Stair44WalkRun.backward d n) ∧
    mc.measure (forward d tail)+(if d then 17960 else 17938)=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+(if d then 17730 else 17708)=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact exactWalks d tail

theorem instMeasurements (d : Bool) (tail n f r : Nat) (hn : 405+tail=n)
    (hf : (if d then 17960 else 17938)=f) (hr : (if d then 17730 else 17708)=r) :
    mc.measure (forward d tail)+f=mc.measure (Stair44WalkRun.forward d n) ∧
    mc.measure (backward d tail)+r=mc.measure (Stair44WalkRun.backward d n) := by
  subst n; subst f; subst r
  exact ⟨(exactWalks d tail).2.2.1, (exactWalks d tail).2.2.2⟩

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
  WindowFieldCosts.group84Sign true ++
    StairSchedule.forwardSegment p 87 62 425 450 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 5 ++
    StairSchedule.forwardSegment p 62 47 450 465 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 3 ++
    StairSchedule.forwardSegment p 47 32 465 480 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 3 ++
    StairSchedule.forwardSegment p 32 22 480 490 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 2 ++
    StairSchedule.forwardSegment p 22 12 490 500 ++
    OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 2 ++ StairSchedule.forwardLast p

def exitHeadSuffix (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.reverseLast p ++
    PackCutOddExit.cutRowOddPk 22 12 490 500 42 98 1 ++
    PackCutOddExit.cutRowOddPk 32 22 480 490 37 96 1 ++
    PackCutOddExit.cutRowOddPk 47 32 465 480 31 93 2 ++
    PackCutOddExit.cutRowOddPk 62 47 450 465 23 90 2 ++
    PackCutOddExit.cutRowOddPk 87 62 425 450 14 85 4 ++
    WindowFieldCosts.group84Sign false

/-- Odd-word half-cell on `base 760` used for cells 2, 3, 4 of `placedFirstPacketOdd`. -/
def oddFirstHalf (divide : Bool) : Program :=
  P1Life.half (base 760) divide base (base 2409)

theorem oddFirstHalf_physical (divide : Bool) : GatePhysical (oddFirstHalf divide) :=
  (P1Life.half_resources (base 760) divide base (base 2409)
    Rolling1588Lifetime.half_ports_nodup RouteA.Rolling1588.route_retired_member).1

theorem oddFirstHalf_support (divide : Bool) :
    JointOdd1588.OddHalfSupport (oddFirstHalf divide) := by
  intro q hq
  have hsub := (P1Life.half_resources (base 760) divide base (base 2409)
    Rolling1588Lifetime.half_ports_nodup RouteA.Rolling1588.route_retired_member).2 hq
  have hne := (Finset.mem_erase.mp hsub).1
  have hmem := Finset.mem_of_mem_erase hsub
  rw [P1Life.junction_footprint_ports, List.mem_toFinset] at hmem
  have hindices : q ∈ (2409 :: 768 :: 1797 :: 1027 ::
      (List.range' 2056 256 ++ List.range' 770 256 ++ (List.range' 512 253 ++ [1540]))).map base := by
    simpa only [List.map_cons, List.map_append, List.map_nil, wireBlock] using hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hindices
  have h760 : i ≠ 760 := fun e => hne (congrArg base e)
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1] at hi
  have inside : i = 2409 ∨ i ∈ Q6EndpointCell.ids := by
    simp only [Q6EndpointCell.ids, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_range'_1]
    omega
  refine ⟨?_, ?_⟩
  · rw [StairFirstPacketKernel.LT48T.env]
    rcases inside with rfl | hi
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · intro hit
    simp only [StairFirstPacketKernel.LT48T.bad, List.mem_cons, List.not_mem_nil, or_false,
      base_injective.eq_iff] at hit
    omega

theorem oddFirstHalf_slots_le (divide : Bool) :
    Challenge.gateSlots (oddFirstHalf divide) ≤ Challenge.gateSlots (R2Life760.half760 divide) := by
  have h1 := RouteA.slot_half (base 760) divide base (base 2409)
  have h2 := RouteA.slot_record_half divide
  cases divide <;> simp only [oddFirstHalf, Bool.false_eq_true, if_false, if_true] at h1 h2 ⊢ <;> omega

theorem fpSup_bounds (w : Wire) (h : StairWireCheck.fpSup w = true) :
    (16 ≤ w ∧ w < 2330) ∨ w = 2425 := by
  unfold StairWireCheck.fpSup at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Wire] at *
  omega

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
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowSuffix p)

/-- The division field's tail prefix with the five packet-cut odd rows. -/
def entryTailPrefixCut : Program :=
  WindowFieldCosts.group84Sign true ++
    (PackCutOdd.cutRowOdd 87 62 425 450 14 85 4 ++
    (PackCutOdd.cutRowOdd 62 47 450 465 23 90 2 ++
    (PackCutOdd.cutRowOdd 47 32 465 480 31 93 2 ++
    (PackCutOdd.cutRowOdd 32 22 480 490 37 96 1 ++
    (PackCutOdd.cutRowOdd 22 12 490 500 42 98 1 ++ StairSchedule.forwardLast checkpointPrimitives)))))

def entryLowPrefixCut : Program :=
  StairLoan.rebindMany StairSchedule.exclusiveRoles (hostPlan.firstPacket true)
      (JointOdd1588.placedFirstPacketOdd oddFirstHalf true) ++
    FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow entryTailPrefixCut ++
    FourScratchWindow.unprefix

def entryFieldHostedCut : Program :=
  StairSchedule.fieldRename entryLowPrefixCut ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ StairSchedule.paritySetup

theorem field_delta_tc_div (n : Nat)
    (h : tc.measure (WindowFieldCosts.group84Sign true)=tc.measure (WindowFieldCosts.group true 1 84)+n) :
    tc.measure (entryFieldHosted checkpointPrimitives)+617 =
      tc.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 13 85 5 (by decide) (by decide)).1
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 22 90 3 (by decide) (by decide)).1
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 30 93 3 (by decide) (by decide)).1
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 36 96 2 (by decide) (by decide)).1
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 41 98 2 (by decide) (by decide)).1
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 43 100 2 (by decide) (by decide)).1
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
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_tc_mul (n : Nat)
    (h : tc.measure (WindowFieldCosts.group84Sign false)=tc.measure (WindowFieldCosts.group false 1 84)+n) :
    tc.measure (exitFieldHosted checkpointPrimitives)+729 =
      tc.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 13 85 5 (by decide) (by decide)).1
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 22 90 3 (by decide) (by decide)).1
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 30 93 3 (by decide) (by decide)).1
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 36 96 2 (by decide) (by decide)).1
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 41 98 2 (by decide) (by decide)).1
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 43 100 2 (by decide) (by decide)).1
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
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_mc_div (n : Nat)
    (h : mc.measure (WindowFieldCosts.group84Sign true)=mc.measure (WindowFieldCosts.group true 1 84)+n) :
    mc.measure (entryFieldHosted checkpointPrimitives)+1381 =
      mc.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 13 85 5 (by decide) (by decide)).2
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 22 90 3 (by decide) (by decide)).2
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 30 93 3 (by decide) (by decide)).2
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 36 96 2 (by decide) (by decide)).2
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 41 98 2 (by decide) (by decide)).2
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift true 43 100 2 (by decide) (by decide)).2
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
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_mc_mul (n : Nat)
    (h : mc.measure (WindowFieldCosts.group84Sign false)=mc.measure (WindowFieldCosts.group false 1 84)+n) :
    mc.measure (exitFieldHosted checkpointPrimitives)+1707 =
      mc.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan)+n := by
  have g13 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 13 85 5 (by decide) (by decide)).2
  have g22 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 22 90 3 (by decide) (by decide)).2
  have g30 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 30 93 3 (by decide) (by decide)).2
  have g36 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 36 96 2 (by decide) (by decide)).2
  have g41 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 41 98 2 (by decide) (by decide)).2
  have g43 := (OddFullPass.P1LifeLoan.hostedGroup_counts_shift false 43 100 2 (by decide) (by decide)).2
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
  simp only [show FoldLoanTop.saving (13 + 1) = 1 from rfl,show FoldLoanTop.saving (22 + 1) = 1 from rfl,show FoldLoanTop.saving (30 + 1) = 1 from rfl,show FoldLoanTop.saving (36 + 1) = 1 from rfl,show FoldLoanTop.saving (41 + 1) = 1 from rfl,show FoldLoanTop.saving (43 + 1) = 1 from rfl] at g13 g22 g30 g36 g41 g43
  norm_num only at g13 g22 g30 g36 g41 g43
  omega

theorem field_delta_slots (d : Bool) (n : Nat)
    (h : slots.measure (WindowFieldCosts.group84Sign d)=slots.measure (WindowFieldCosts.group d 1 84)+n) :
    (if d then slots.measure (entryFieldHosted checkpointPrimitives)
     else slots.measure (exitFieldHosted checkpointPrimitives)) ≤
    (if d then slots.measure (StairHostsSchedule.entryFieldHosted checkpointPrimitives hostPlan)
     else slots.measure (StairHostsSchedule.exitFieldHosted checkpointPrimitives hostPlan))+n+
      (if d then 12660 else 12920) := by
  have g13 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 13 85 5 (by decide) (by decide)
  have g22 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 22 90 3 (by decide) (by decide)
  have g30 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 30 93 3 (by decide) (by decide)
  have g36 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 36 96 2 (by decide) (by decide)
  have g41 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 41 98 2 (by decide) (by decide)
  have g43 := OddFullPass.P1LifeLoan.hostedGroup_slots_shift d 43 100 2 (by decide) (by decide)
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
    Baselines.rename_gateSlots,Challenge.gateSlots_append] at * <;> (norm_num only at g13 g22 g30 g36 g41 g43; omega)

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

theorem tailPrefix_rows : entryTailPrefix checkpointPrimitives = WindowFieldCosts.group84Sign true ++
      ((StairSchedule.forwardSegment checkpointPrimitives 87 62 425 450 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 14 85 (4 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 62 47 450 465 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 23 90 (2 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 47 32 465 480 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 31 93 (2 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 32 22 480 490 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 37 96 (1 + 1)) ++
      ((StairSchedule.forwardSegment checkpointPrimitives 22 12 490 500 ++ OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true 42 98 (1 + 1)) ++
        StairSchedule.forwardLast checkpointPrimitives))))) := by
  simp only [entryTailPrefix, List.append_assoc]

theorem tail_sublist : entryTailPrefixCut.Sublist (entryTailPrefix checkpointPrimitives) := by
  rw [tailPrefix_rows]
  unfold entryTailPrefixCut
  exact (List.Sublist.refl _).append ((PackCutOdd.row_subOdd 87 62 425 450 14 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp1_1542).append
    ((PackCutOdd.row_subOdd 62 47 450 465 23 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp2_1542).append
    ((PackCutOdd.row_subOdd 47 32 465 480 31 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp3_1542).append
    ((PackCutOdd.row_subOdd 32 22 480 490 37 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp4_1542).append
    ((PackCutOdd.row_subOdd 22 12 490 500 42 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp5_1542).append
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
        (OddFullPass.P1LifeLoan.hostPlan1542.group true d first (cc + 1))
        (renameProgram (OB5.sig 511) (renameProgram (shifted (Placement5.pi first))
          (Rolling1588.onPacket first Rolling1588.dp))) =
      renameProgram (MeasuredCodec5.label (History5.historyMap
        (StairPhysicalPrimitives.midSegmentMap (StairPhysicalPrimitives.segmentOf (s + 1))) (5 * first)))
        Rolling1588.dp) :
    c.measure (StairSchedule.forwardSegment checkpointPrimitives B N s f ++
        OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 true d first (cc + 1)) =
      c.measure (PackCutOdd.cutRowOdd B N s f d first cc) + (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  obtain ⟨X, M, Y, ho, hc⟩ := PackCutOdd.row_shapeOdd B N s f d first cc h1 h2 h5 hdue hf0 hdp
  rw [ho, hc]
  simp only [c.append, c.rename]
  omega

theorem rows_cost (c : Cost) :
    c.measure (entryTailPrefix checkpointPrimitives) =
      c.measure entryTailPrefixCut + 5 * (c.measure Rolling1588.ep + c.measure Rolling1588.dp) := by
  have r1 := rowOdd_cost c 87 62 425 450 14 85 4 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp1_1542
  have r2 := rowOdd_cost c 62 47 450 465 23 90 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp2_1542
  have r3 := rowOdd_cost c 47 32 465 480 31 93 2 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp3_1542
  have r4 := rowOdd_cost c 32 22 480 490 37 96 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp4_1542
  have r5 := rowOdd_cost c 22 12 490 500 42 98 1 (by decide) (by decide) (by decide) (by decide) (by decide) PackCutOdd.hdp5_1542
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



section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Arithmetic MappedCompressed Secp256k1 BalancedField Baselines DirectSkywalk OB5
open StairConcreteAssembly Stair44Resources StairHostsSchedule
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

section
attribute [local irreducible] WindowFieldCosts.group84Sign WindowFieldCosts.group84
  WindowFieldCosts.group toffoliCount measurementCount

private theorem fieldCountScalar (stock signed field total saving extra : Nat)
    (before : stock = field + total) (after : signed + saving = stock)
    (offset : total = saving + extra) : signed = field + extra := by omega

private theorem fieldCountTransport (c : Cost) (f : Program → Nat) (measure_eq : c.measure = f)
    (stock signed field : Program) (total saving extra : Nat)
    (before : f stock = f field + total) (after : f signed + saving = f stock)
    (offset : total = saving + extra) : c.measure signed = c.measure field + extra :=
  Eq.mpr (congrArg (fun measure : Program → Nat => measure signed = measure field + extra) measure_eq)
    (fieldCountScalar (f stock) (f signed) (f field) total saving extra before after offset)

private theorem fieldTcDiv :
    tc.measure (WindowFieldCosts.group84Sign true)=tc.measure (WindowFieldCosts.group true 1 84)+827 :=
  fieldCountTransport tc toffoliCount rfl
    (WindowFieldCosts.group84 true) (WindowFieldCosts.group84Sign true) (WindowFieldCosts.group true 1 84)
    1066 239 827 WindowFieldCosts.group_cost_div.1
    (WindowFieldCosts.SignCounts.group_delta true).1 rfl
private theorem fieldMcDiv :
    mc.measure (WindowFieldCosts.group84Sign true)=mc.measure (WindowFieldCosts.group true 1 84)+657 :=
  fieldCountTransport mc measurementCount rfl
    (WindowFieldCosts.group84 true) (WindowFieldCosts.group84Sign true) (WindowFieldCosts.group true 1 84)
    688 31 657 WindowFieldCosts.group_cost_div.2
    (WindowFieldCosts.SignCounts.group_delta true).2.1 rfl
private theorem fieldTcMul :
    tc.measure (WindowFieldCosts.group84Sign false)=tc.measure (WindowFieldCosts.group false 1 84)+739 :=
  fieldCountTransport tc toffoliCount rfl
    (WindowFieldCosts.group84 false) (WindowFieldCosts.group84Sign false) (WindowFieldCosts.group false 1 84)
    978 239 739 WindowFieldCosts.group_cost_mul.1
    (WindowFieldCosts.SignCounts.group_delta false).1 rfl
private theorem fieldMcMul :
    mc.measure (WindowFieldCosts.group84Sign false)=mc.measure (WindowFieldCosts.group false 1 84)+547 :=
  fieldCountTransport mc measurementCount rfl
    (WindowFieldCosts.group84 false) (WindowFieldCosts.group84Sign false) (WindowFieldCosts.group false 1 84)
    578 31 547 WindowFieldCosts.group_cost_mul.2
    (WindowFieldCosts.SignCounts.group_delta false).2.1 rfl

end

private theorem pair_delta2 {a b x y g h i j t1 t2 f1 f2 r : Nat}
    (l : a+g+h+t1=x+f1) (rr : b+i+j+t2=y+f2) (v : g+h+t1+i+j+t2=r+f1+f2) : a+b+r=x+y := by omega
attribute [local irreducible] Stair44Outer.divide Stair44Outer.multiply divide multiply
  finite Stair44Outer.finite WindowWalkCosts.forward WindowWalkCosts.backward
  WindowFieldCosts.group84Sign WindowFieldCosts.group Stair44WalkRun.forward Stair44WalkRun.backward
  toffoliCount measurementCount

theorem tc_div : tc.measure divide+39828+39957+682=tc.measure Stair44Outer.divide+827 := by
  have k := kernels tc 39828 39957 617 827 (WindowWalkCosts.inst true 4 409 39828 39979 rfl rfl rfl).1
    (WindowWalkCosts.inst false 85 490 39828 39957 rfl rfl rfl).2.1 (field_delta_tc_div 827 fieldTcDiv)
  have e : tc.measure Rolling1588.ep + tc.measure Rolling1588.dp = 13 := by
    show toffoliCount Rolling1588.ep + toffoliCount Rolling1588.dp = 13
    rw [PackCutCounts.tc_ep, PackCutCounts.tc_dp]
  omega

theorem tc_mul (k : Nat) : tc.measure (multiply k)+39828+39979+729=tc.measure (Stair44Outer.multiply k)+739 :=
  kernelsM tc k 39828 39979 729 739 (WindowWalkCosts.inst false 84 489 39828 39957 rfl rfl rfl).1
    (WindowWalkCosts.inst true 4 409 39828 39979 rfl rfl rfl).2.1 (field_delta_tc_mul 739 fieldTcMul)

theorem mc_div : mc.measure divide+17960+17708+1406=mc.measure Stair44Outer.divide+657 := by
  have k := kernels mc 17960 17708 1381 657 (WindowWalkCosts.instMeasurements true 4 409 17960 17730 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements false 85 490 17938 17708 rfl rfl rfl).2 (field_delta_mc_div 657 fieldMcDiv)
  have e : mc.measure Rolling1588.ep + mc.measure Rolling1588.dp = 5 := by
    show measurementCount Rolling1588.ep + measurementCount Rolling1588.dp = 5
    exact PackCutCounts.mc_epdp
  omega

theorem mc_mul (k : Nat) : mc.measure (multiply k)+17938+17730+1707=mc.measure (Stair44Outer.multiply k)+547 :=
  kernelsM mc k 17938 17730 1707 547 (WindowWalkCosts.instMeasurements false 84 489 17938 17708 rfl rfl rfl).1
    (WindowWalkCosts.instMeasurements true 4 409 17960 17730 rfl rfl rfl).2 (field_delta_mc_mul 547 fieldMcMul)

theorem deltas (C : Point) (cx cy : Fp) :
    toffoliCount (finite C cx cy)+159437=toffoliCount (Stair44Outer.finite C cx cy) ∧
    measurementCount (finite C cx cy)+73245=measurementCount (Stair44Outer.finite C cx cy) :=
  ⟨finite_delta tc C cx cy 159437
      (OddOuterBridge.entryYAllOdd_tc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_tc_eq layout layout_widths cy)
      (pair_delta2 tc_div (tc_mul _) rfl),
    finite_delta mc C cx cy 73245
      (OddOuterBridge.entryYAllOdd_mc_eq layout layout_widths (-cy))
      (OddOuterBridge.exitYAllOdd_mc_eq layout layout_widths cy)
      (pair_delta2 mc_div (mc_mul _) rfl)⟩

theorem totals (C : Point) : toffoliCount (program C) ≤ 2008160 ∧
    measurementCount (program C) ≤ 1446339 := by
  have h := Stair44Resources.totals C
  cases C with
  | zero => change toffoliCount [] ≤ _ ∧ measurementCount [] ≤ _; simp [toffoliCount,measurementCount]
  | @some cx cy hc =>
    have d := deltas (.some hc) cx cy
    simp only [program,Stair44Outer.program,(renameProgram_counts _ _).1,
      (renameProgram_counts _ _).2] at h ⊢
    exact ⟨by omega,by omega⟩

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts


section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open ArchiveFieldScratch StairArchiveRelease StairArchiveNativeCut StairArchiveTen

def reserved : List Wire := StairPhysicalInventory.physicalHoles
theorem subset {q : Wire} (h : q∈reserved) : q∈StairPhysicalInventory.physicalHoles := h

theorem weaken {P : Program} {f : Wire → Wire} (h : PieceOK StairPhysicalInventory.physicalHoles f P) :
    PieceOK reserved f P := h

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
    4835∉Stair44FieldSites.holes := by
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

theorem hook43 (j : Nat) (hj : j∈List.range' 1 83) (op : Stage) :
    PieceOK Stair44FieldSites.holes TP (fieldHook j op) := by
  rw [fieldHook,ren]
  have cover (x : Wire) (hx : x∈wires (program op)) :
      TP (fieldPort j x)∈StairHoleSupport.recordArena ∧
      TP (fieldPort j x)∉StairHoleSupport.oldHoles ∧ TP (fieldPort j x)∉Stair44FieldSites.holes := by
    have lt := Finset.mem_range.mp (sub op hx)
    have sl := (layout_frame j hj).2
    have small : x < (layout j).length := sl ▸ lt
    have member : port j x ∈ layout j := by
      simp only [port,List.getElem?_eq_getElem small,Option.getD_some,List.getElem_mem]
    change StairOuterPlacement.outerPlace _ ∈ _ ∧ _ ∧ _
    simp only [show TP=StairOuterPlacement.outerPlace from rfl,StairPlaceFast.outerPlace_eqB,placed_port j hj x lt]
    rcases addresses j hj _ member with p|e
    · have sok := singleton_ok p
      exact ⟨sok.1, sok.2.1, fun h => sok.2.2 (Stair44FieldSites.hsub _ h)⟩
    · rw [e]; exact tagOK
  exact ⟨fun x hx => ⟨(cover x hx).1,(cover x hx).2.1⟩,fun x hx => (cover x hx).2.2⟩

theorem width {P : Program} (h : PieceOK reserved id P) : Challenge.qubits P ≤ 1542 := by
  have listOK := StairCertificate.holeList_of_physical_sub reserved
    (by rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat]; decide +kernel) (fun _ hx => subset hx)
  have hq := StairCertificate.qubits_le_holes reserved listOK P (holePlacement_of_ok h)
  have hlen : reserved.length = 44 := by rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat]; decide +kernel
  omega
end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.PartialSites
open Arithmetic MappedCompressed Partial StairSiteAvoidance
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

attribute [local irreducible] wires domain

theorem forwardMixed_domain (d : Bool) : Covered (Shadow20.MergeCut.forward d) := by
  intro q h
  rw [domain_eq]
  exact (Shadow20.MergeCut.covered d).1 q h
theorem reverseMixed_domain (d : Bool) : Covered (Shadow20.MergeCut.reverse d) := by
  intro q h
  rw [domain_eq]
  exact Shadow20.MergeCut.rcovered d q h

theorem forwardMixed_fits (d : Bool) : ∀ q ∈ wires (Shadow20.MergeCut.forward d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (forwardMixed_domain d q h)

theorem reverseMixed_fits (d : Bool) : ∀ q ∈ wires (Shadow20.MergeCut.reverse d), Stair44PhaseSites.valid (Stair44WalkMap.rest q) = true :=
  fun q h => valid (reverseMixed_domain d q h)

end ECDSAAdd.Entrant.StairPacket.PartialSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSlots
open Arithmetic MappedCompressed Secp256k1 Baselines Challenge Stair44Resources Stair44Outer
open StairConcreteAssembly WindowWalkCosts WindowFold Partial
set_option maxHeartbeats 1400000
set_option maxRecDepth 14000
set_option linter.unusedSimpArgs false
attribute [local irreducible] toffoliCount gateSlots measurementCount wires renameProgram
  Rolling1588TickGap.forward Rolling1588.reverse Shadow20.MergeCut.forward Shadow20.MergeCut.reverse

theorem walk (c : Cost) (d : Bool) (tail f r n : Nat) (hn : 405+tail=n)
    (hf : c.measure (Shadow20.MergeCut.forward d) ≤ f) (hr : c.measure (Shadow20.MergeCut.reverse d) ≤ r) :
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
    (g : slots.measure (WindowFieldCosts.group84Sign true)=slots.measure (WindowFieldCosts.group true 1 84)+fieldExtra) :
    slots.measure WindowCallerCosts.divide ≤ slots.measure Stair44Outer.divide+gainF+gainR+fieldExtra+12660 := by
  have h := WindowCallerCosts.field_delta_slots true _ g
  have hc := WindowCallerCosts.field_cut slots
  simp only [if_true] at h
  simp only [WindowCallerCosts.divide,Stair44Outer.divide,phasePlace,kernelPlace,
    Stair44Resources.slots.append,Stair44Resources.slots.rename]
  omega

private theorem kernelsM (k gainF gainR fieldExtra : Nat)
    (mF : slots.measure (WindowWalkCosts.forward false 84) ≤ slots.measure (Stair44WalkRun.forward false 489)+gainF)
    (mR : slots.measure (WindowWalkCosts.backward true 4) ≤ slots.measure (Stair44WalkRun.backward true 409)+gainR)
    (g : slots.measure (WindowFieldCosts.group84Sign false)=slots.measure (WindowFieldCosts.group false 1 84)+fieldExtra) :
    slots.measure (WindowCallerCosts.multiply k) ≤ slots.measure (Stair44Outer.multiply k)+gainF+gainR+fieldExtra+12920 := by
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



private theorem route20_slots (j : Fin 9) (i n : Nat) :
    gateSlots (Shadow20.routed20 j i n) ≤ 5000 * n ∧
    gateSlots (Shadow20.unrouted20 j i n) ≤ 5000 * n := by
  induction n generalizing i with
  | zero =>
    simp only [Shadow20.routed20, Shadow20.unrouted20, gateSlots_nil, Nat.mul_zero, Nat.le_refl, and_self]
  | succ n ih =>
    have tail := ih (i + 1)
    have t := WindowSlots.tick (Shadow20.shape20 j) i
    have u := WindowSlots7.untickR_slots (Shadow20.shape20 j) i
    simp only [Shadow20.routed20, Shadow20.unrouted20, gateSlots_append, rename_gateSlots, Nat.mul_succ]
    exact ⟨by omega, by omega⟩

private theorem sum_flatten_slots (ps : List Program) :
    gateSlots ps.flatten = (ps.map gateSlots).sum := by
  induction ps with
  | nil => simp only [List.flatten_nil, gateSlots_nil, List.map_nil, List.sum_nil]
  | cons p ps ih => simp only [List.flatten_cons, gateSlots_append, List.map_cons, List.sum_cons, ih]

private theorem sum_flatMap_slots_le {α : Type} (f : α → List Program) (b : α → Nat) (xs : List α)
    (h : ∀ x ∈ xs, ((f x).map gateSlots).sum ≤ b x) :
    ((xs.flatMap f).map gateSlots).sum ≤ (xs.map b).sum := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

private def b15SF (j : Fin 26) : Nat :=
  35 + 5000 + 168 + 15988 + 70000 +
  (6 * CRTBarrel.adjustWidth (start j) + 5 * Shadow7.liveW (start j) + 10 * Shadow7.lowsP (start j) + 646 +
    3 * Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) false)

private def b15SR (j : Fin 26) : Nat :=
  36 + 5000 + 166 + 12262 + 70098 +
  (6 * CRTBarrel.adjustWidth (start j) + 5 * Shadow7.liveW (start j) + 11 * Shadow7.lowsP (start j) + 616 +
    3 * Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) true)

private def b20SF (j : Fin 9) : Nat :=
  let s := Shadow20.start20 j
  35 + 5000 + (if j.val = 0 then 168 else 336) + 15988 + 95000 +
  (6 * Shadow20.TrimHigh.adjustWidth s + 5 * Shadow20.liveW20 s + 10 * Shadow20.lowsP20 s + 851 +
    3 * Shadow20.nextWp20 s + Shadow20.barrel20Slots s false)

private def b20SR (j : Fin 9) : Nat :=
  let s := Shadow20.start20 j
  36 + 5000 + (if j.val = 0 then 166 else 332) + 12262 + 95000 +
  (6 * Shadow20.TrimHigh.adjustWidth s + 5 * Shadow20.liveW20 s + 11 * Shadow20.lowsP20 s + 811 +
    3 * Shadow20.nextWp20 s + Shadow20.barrel20Slots s true)

private theorem packW_slots_le (d : Bool) (s t : Nat) (hd : WindowParams.dueTick t = true) :
    gateSlots (Shadow20.MixedWindow.packW d s t) ≤ 168 ∧
    gateSlots (Shadow20.MixedWindow.unpackW d s t) ≤ 166 := by
  have h1 := WindowParams7.slots_le.pack d s t
  have h2 := WindowParams7.slots_le.unpack d s t
  simp only [Pieces.map, Shadow7.params, ofParts, WindowParams7.slotsV, hd, ↓reduceIte] at h1 h2
  change gateSlots (Shadow20.MixedWindow.packW d s t) ≤ _ at h1
  change gateSlots (Shadow20.MixedWindow.unpackW d s t) ≤ _ at h2
  cases d <;> simp only [if_true, if_false, Bool.false_eq_true] at h1 h2 <;> exact ⟨by omega, by omega⟩

private theorem arch15_slots_le (j : Fin 26) (d : Bool) :
    gateSlots (Shadow7.archiveLoadP j d) ≤ 15988 ∧
    gateSlots (Shadow7.archiveRestoreP j d) ≤ 12262 := by
  have h1 := WindowParams7.slots_le.load j d
  have h2 := WindowParams7.slots_le.restore j d
  simp only [Pieces.map, Shadow7.params, ofParts, WindowParams7.slotsV] at h1 h2
  cases d <;> simp only [if_true, if_false, Bool.false_eq_true] at h1 h2 <;> exact ⟨by omega, by omega⟩

private theorem arch20_slots_le (j : Fin 9) (d : Bool) :
    gateSlots (Shadow20.archiveLoadP20 j d) ≤ 15988 ∧
    gateSlots (Shadow20.archiveRestoreP20 j d) ≤ 12262 := by
  have h := Shadow20.archive20_counts j d
  have h1 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.1
  have h2 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.2.2.2.1
  have a := arch15_slots_le WindowParams.first d
  exact ⟨by omega, by omega⟩

private theorem arch150_slots_le (d : Bool) :
    gateSlots (Shadow20.archiveLoad150To20 d) ≤ 15988 ∧
    gateSlots (Shadow20.archiveRestore150To20 d) ≤ 12262 := by
  obtain ⟨_, _, l3, _, _, l6⟩ := moves_counts 165 (Shadow20.e0P20 165 + 6)
  obtain ⟨_, _, m3, _, _, m6⟩ := moves240_counts
  have hL : gateSlots (Shadow20.archiveLoad150To20 d) = gateSlots (archiveLoad240 d) := by
    simp only [Shadow20.archiveLoad150To20, archiveLoad240, gateSlots_append, rename_gateSlots, l3, m3]
  have hR : gateSlots (Shadow20.archiveRestore150To20 d) = gateSlots (archiveRestore240 d) := by
    simp only [Shadow20.archiveRestore150To20, archiveRestore240, gateSlots_append, rename_gateSlots, l6, m6]
  have h1 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.1
  have h2 := (Shadow7.archive_counts WindowParams.first 0 d).2.2.2.2.2.1
  have a := arch15_slots_le WindowParams.first d
  exact ⟨by omega, by omega⟩

private theorem exit420_slots_le (d : Bool) :
    gateSlots (Shadow7.exitLoadP 420 d) ≤ 15988 ∧
    gateSlots (Shadow7.exitRestoreP 420 d) ≤ 12262 := by
  have h1 := WindowParams7.slots_le.exitLoad 420 d
  have h2 := WindowParams7.slots_le.exitRestore 420 d
  simp only [Pieces.map, Shadow7.params, ofParts, WindowParams7.slotsV] at h1 h2
  cases d <;> simp only [if_true, if_false, Bool.false_eq_true] at h1 h2 <;> exact ⟨by omega, by omega⟩

private theorem mixed_slot_sum_vals :
    ((22 * Shadow7.wpP 45 - 9) + (35 + (5000 + (168 + (70000 +
      ((6 * CRTBarrel.adjustWidth 45 + 5 * Shadow7.liveW 45 + 10 * Shadow7.lowsP 45 + 641 + 3 * Shadow7.wpP 60 + CRTBarrel.barrelSlots 45 false) + 0)))))) +
    (Shadow20.MixedWindow.prefixPairs.map fun p => b15SF p.2).sum +
    (35 + (5000 + (168 + (15988 + (70000 + (11679 + 0)))))) +
    ((List.finRange 9).map b20SF).sum +
    (35 + (5000 + (168 + (168 + (15988 + (70000 +
      ((6 * CRTBarrel.adjustWidth 345 + 5 * Shadow7.liveW 345 + 10 * Shadow7.lowsP 345 + 641 + 3 * Shadow7.wpP 360 + CRTBarrel.barrelSlots 345 false) + 0))))))) +
    (Shadow20.MixedWindow.suffixPairs.map fun p => b15SF p.2).sum +
    (9 + ((21 * Shadow7.wpP 420 - 7) + (6004 + (168 + (15988 + 0))))) ≤ 2698994 ∧
    (12262 + (166 + (6001 + ((22 * Shadow7.wpP 420 - 9) + (9 + 0))))) +
    (Shadow20.MixedWindow.suffixPairs.reverse.map fun p => b15SR p.2).sum +
    ((6 * CRTBarrel.adjustWidth 345 + 5 * Shadow7.liveW 345 + 11 * Shadow7.lowsP 345 + 611 + 3 * Shadow7.wpP 360 + CRTBarrel.barrelSlots 345 true) +
      (70098 + (12262 + (166 + (166 + (5000 + (36 + 0))))))) +
    ((List.finRange 9).reverse.map b20SR).sum +
    (11697 + (70098 + (12262 + (166 + (5000 + (36 + 0)))))) +
    (Shadow20.MixedWindow.prefixPairs.reverse.map fun p => b15SR p.2).sum +
    ((6 * CRTBarrel.adjustWidth 45 + 5 * Shadow7.liveW 45 + 11 * Shadow7.lowsP 45 + 611 + 3 * Shadow7.wpP 60 + CRTBarrel.barrelSlots 45 true) +
      (70098 + (166 + (5000 + (36 + ((21 * Shadow7.wpP 45 - 7) + 0)))))) ≤ 2598694 := by
  decide +kernel

private theorem tick420_slots_le :
    gateSlots (Shadow20.MixedWindow.tickW 420) ≤ 6004 ∧
    gateSlots (Shadow20.MixedWindow.recvW 420) ≤ 6001 := by
  unfold Shadow20.MixedWindow.tickW Shadow20.MixedWindow.recvW
  rw [rename_gateSlots, rename_gateSlots,
    StairSlotsLib.tick_slots_formula base 420 (by decide) (by decide) base_pool_nodup,
    StairSlotsLib.receiverTick_slots_formula base 420 (by decide) (by decide) base_pool_nodup]
  decide +kernel

private theorem b15F_slots_le (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24)
    (hd : WindowParams.dueTick (start j - 10) = true) :
    ((Shadow20.MixedWindow.block15F d i j).map gateSlots).sum ≤ b15SF j := by
  have e := (Shadow7.enter_counts j).2.2.2.2.1
  have r0 := (WindowSlots7.route j 0 1).1
  have r1 := (WindowSlots7.route j 1 14).1
  have pk := (packW_slots_le d (start j) (start j - 10) hd).1
  have ar := (arch15_slots_le i d).1
  have lv := (CRTWindow.leave_metrics j (Nat.zero_le _) hj).2.2.2.2.1
  simp only [Shadow20.MixedWindow.block15F, b15SF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem sel14_slots (j : Fin 26) : gateSlots (TickCut.Tail.selected j 1 14) ≤ 70098 := by
  have c := (TickCut.Tail.tail_counts j).2.2
  have r := (WindowSlots7.route j 1 14).2
  rw [TickCut.Tail.selected, if_pos (show (1:Nat) = 1 ∧ (14:Nat) = 14 from ⟨rfl, rfl⟩)]
  omega

private theorem b15R_slots_le (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24)
    (hd : WindowParams.dueTick (start j - 10) = true) :
    ((Shadow20.MixedWindow.block15R d i j).map gateSlots).sum ≤ b15SR j := by
  have e := (Shadow7.enter_counts j).2.2.2.2.2
  have r0 := (WindowSlots7.route j 0 1).2
  have r1 := sel14_slots j
  have pk := (packW_slots_le d (start j) (start j - 10) hd).2
  have ar := (arch15_slots_le i d).2
  have lv := (CRTWindow.leave_metrics j (Nat.zero_le _) hj).2.2.2.2.2
  simp only [Shadow20.MixedWindow.block15R, b15SR, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

private theorem b20F_slots_le (d : Bool) (j : Fin 9) :
    ((Shadow20.MixedWindow.block20F d j).map gateSlots).sum ≤ b20SF j := by
  have e := (Shadow20.enter20_counts j).2.2.2.2.1
  have r0 := (route20_slots j 0 1).1
  have r1 := (route20_slots j 1 19).1
  have lv := (Shadow20.leave20Red_counts j).2.2.2.2.1
  by_cases h0 : j.val = 0
  · have pk := (packW_slots_le d 165 155 (by decide)).1
    have ar := (arch150_slots_le d).1
    simp only [Shadow20.MixedWindow.block20F, b20SF, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · have hd1 : WindowParams.dueTick (Shadow20.start20 j - 15) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 15) = true := by decide +kernel
      exact h j h0
    have hd2 : WindowParams.dueTick (Shadow20.start20 j - 10) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 10) = true := by decide +kernel
      exact h j h0
    have pk1 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 15) hd1).1
    have pk2 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 10) hd2).1
    have ar := (arch20_slots_le ⟨j.val - 1, by omega⟩ d).1
    simp only [Shadow20.MixedWindow.block20F, b20SF, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

private theorem b20R_slots_le (d : Bool) (j : Fin 9) :
    ((Shadow20.MixedWindow.block20R d j).map gateSlots).sum ≤ b20SR j := by
  have e := (Shadow20.enter20_counts j).2.2.2.2.2
  have r0 := (route20_slots j 0 1).2
  have r1 := (route20_slots j 1 19).2
  have lv := (Shadow20.leave20Red_counts j).2.2.2.2.2
  by_cases h0 : j.val = 0
  · have pk := (packW_slots_le d 165 155 (by decide)).2
    have ar := (arch150_slots_le d).2
    simp only [Shadow20.MixedWindow.block20R, b20SR, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · have hd1 : WindowParams.dueTick (Shadow20.start20 j - 15) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 15) = true := by decide +kernel
      exact h j h0
    have hd2 : WindowParams.dueTick (Shadow20.start20 j - 10) = true := by
      have h : ∀ k : Fin 9, k.val ≠ 0 → WindowParams.dueTick (Shadow20.start20 k - 10) = true := by decide +kernel
      exact h j h0
    have pk1 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 15) hd1).2
    have pk2 := (packW_slots_le d (Shadow20.start20 j) (Shadow20.start20 j - 10) hd2).2
    have ar := (arch20_slots_le ⟨j.val - 1, by omega⟩ d).2
    simp only [Shadow20.MixedWindow.block20R, b20SR, h0, ↓reduceDIte, ↓reduceIte,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

private theorem sum_map_append7 (m : Program → Nat) (a b c d e f g : List Program) :
    ((a ++ b ++ c ++ d ++ e ++ f ++ g).map m).sum =
      (a.map m).sum + (b.map m).sum + (c.map m).sum + (d.map m).sum + (e.map m).sum + (f.map m).sum + (g.map m).sum := by
  simp only [List.map_append, List.sum_append]

private theorem sum_map5 (m : Program → Nat) (a b c d e : Program) :
    ([a, b, c, d, e].map m).sum = m a + (m b + (m c + (m d + (m e + 0)))) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

private theorem sum_map6 (m : Program → Nat) (a b c d e f : Program) :
    ([a, b, c, d, e, f].map m).sum = m a + (m b + (m c + (m d + (m e + (m f + 0))))) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

private theorem sum_map7 (m : Program → Nat) (a b c d e f g : Program) :
    ([a, b, c, d, e, f, g].map m).sum = m a + (m b + (m c + (m d + (m e + (m f + (m g + 0)))))) := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]

attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP
  Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP Shadow7.routed Shadow7.unrouted
  Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.exitLoadP Shadow7.exitRestoreP
  CRTBarrel.leave CRTBarrel.unleave Shadow20.enterP20 Shadow20.enterInvP20 Shadow20.leaveP20 Shadow20.leaveInvP20 Shadow20.leaveP20Red Shadow20.leaveInvP20Red
  Shadow20.routed20 Shadow20.unrouted20 Shadow20.archiveLoadP20 Shadow20.archiveRestoreP20
  Shadow20.leave150To20 Shadow20.leaveInv150To20 Shadow20.leave150To20Red Shadow20.leaveInv150To20Red Shadow20.archiveLoad150To20 Shadow20.archiveRestore150To20
  Shadow20.MixedWindow.packW Shadow20.MixedWindow.unpackW Shadow20.MixedWindow.tickW Shadow20.MixedWindow.recvW
  Shadow20.MixedWindow.block15F Shadow20.MixedWindow.block15R Shadow20.MixedWindow.block20F Shadow20.MixedWindow.block20R in
private theorem mixed_slots_F (d : Bool) :
    gateSlots (Shadow20.MixedWindow.forwardMixed d) ≤ 2698994 := by
  have hp15 : ∀ p ∈ Shadow20.MixedWindow.prefixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hs15 : ∀ p ∈ Shadow20.MixedWindow.suffixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hprF := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15F d p.1 p.2) (fun p => b15SF p.2) Shadow20.MixedWindow.prefixPairs (fun p hp => by have h := hp15 p hp; exact b15F_slots_le d p.1 p.2 h.1 h.2)
  have hsuF := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15F d p.1 p.2) (fun p => b15SF p.2) Shadow20.MixedWindow.suffixPairs (fun p hp => by have h := hs15 p hp; exact b15F_slots_le d p.1 p.2 h.1 h.2)
  have h20F := sum_flatMap_slots_le (Shadow20.MixedWindow.block20F d) b20SF (List.finRange 9) (fun j _ => b20F_slots_le d j)
  have p45 := (Shadow7.portal_counts 45 (by decide)).2.2.2.2.1
  have p420 := (Shadow7.portal_counts 420 (by decide)).2.2.2.2.2
  have pk420 := (Shadow7.park_counts 420).2.2.2.2.1
  have t420 := tick420_slots_le.1
  have exF := (exit420_slots_le d).1
  have e0 := (Shadow7.enter_counts Shadow20.MixedWindow.j0).2.2.2.2.1
  have r0a : gateSlots (Shadow7.routed Shadow20.MixedWindow.j0 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j0 0 1).1
  have r0b : gateSlots (Shadow7.routed Shadow20.MixedWindow.j0 1 14) ≤ 70000 := by
    simpa only [show 5000 * 14 = 70000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j0 1 14).1
  have l0 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j0 (by decide) (by decide)).2.2.2.2.1
  have e7 := (Shadow7.enter_counts Shadow20.MixedWindow.j7).2.2.2.2.1
  have r7a : gateSlots (Shadow7.routed Shadow20.MixedWindow.j7 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j7 0 1).1
  have r7b : gateSlots (Shadow7.routed Shadow20.MixedWindow.j7 1 14) ≤ 70000 := by
    simpa only [show 5000 * 14 = 70000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j7 1 14).1
  have a6 := (arch15_slots_le Shadow20.MixedWindow.j6 d).1
  have l7 := Shadow20.leave150To20Red_counts.2.2.2.2.1
  have e20 := (Shadow7.enter_counts Shadow20.MixedWindow.j20).2.2.2.2.1
  have r20a : gateSlots (Shadow7.routed Shadow20.MixedWindow.j20 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j20 0 1).1
  have r20b : gateSlots (Shadow7.routed Shadow20.MixedWindow.j20 1 14) ≤ 70000 := by
    simpa only [show 5000 * 14 = 70000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j20 1 14).1
  have a8 := (arch20_slots_le Shadow20.MixedWindow.k8 d).1
  have l20 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j20 (by decide) (by decide)).2.2.2.2.1
  have pk45 := (packW_slots_le d 45 45 (by decide)).1
  have pk140 := (packW_slots_le d 150 140 (by decide)).1
  have pk330 := (packW_slots_le d 345 330 (by decide)).1
  have pk335 := (packW_slots_le d 345 335 (by decide)).1
  have pk410 := (packW_slots_le d 420 410 (by decide)).1
  have mv := mixed_slot_sum_vals.1
  rw [show start Shadow20.MixedWindow.j0 = 45 from rfl, show (45 : Nat) + 15 = 60 from rfl] at l0
  rw [show start Shadow20.MixedWindow.j20 = 345 from rfl, show (345 : Nat) + 15 = 360 from rfl] at l20
  have hdef : Shadow20.MixedWindow.forwardMixed d = (Shadow20.MixedWindow.forwardL d).flatten := by
    unfold Shadow20.MixedWindow.forwardMixed; rfl
  rw [hdef, sum_flatten_slots, Shadow20.MixedWindow.forwardL, sum_map_append7, sum_map6, sum_map6, sum_map7, sum_map5]
  rw [p45, e0, l0, e7, l7, e20, l20, pk420, p420]
  refine Nat.le_trans ?_ mv
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add r0a (Nat.add_le_add pk45 (Nat.add_le_add r0b (Nat.le_refl _)))) _) _)
              hprF)
            (Nat.add_le_add_left (Nat.add_le_add r7a (Nat.add_le_add pk140 (Nat.add_le_add a6 (Nat.add_le_add r7b (Nat.le_refl _))))) _))
          h20F)
        (Nat.add_le_add_left (Nat.add_le_add r20a (Nat.add_le_add pk330 (Nat.add_le_add pk335 (Nat.add_le_add a8 (Nat.add_le_add r20b (Nat.le_refl _)))))) _))
      hsuF)
    (Nat.add_le_add_left (Nat.add_le_add_left (Nat.add_le_add t420 (Nat.add_le_add pk410 (Nat.add_le_add exF (Nat.le_refl _)))) _) _)

attribute [local irreducible] Shadow7.enterP Shadow7.enterInvP
  Shadow7.portalP Shadow7.portalInvP Shadow7.parkP Shadow7.parkInvP Shadow7.routed Shadow7.unrouted
  Shadow7.archiveLoadP Shadow7.archiveRestoreP Shadow7.exitLoadP Shadow7.exitRestoreP
  CRTBarrel.leave CRTBarrel.unleave Shadow20.enterP20 Shadow20.enterInvP20 Shadow20.leaveP20 Shadow20.leaveInvP20 Shadow20.leaveP20Red Shadow20.leaveInvP20Red
  Shadow20.routed20 Shadow20.unrouted20 Shadow20.archiveLoadP20 Shadow20.archiveRestoreP20
  Shadow20.leave150To20 Shadow20.leaveInv150To20 Shadow20.leave150To20Red Shadow20.leaveInv150To20Red Shadow20.archiveLoad150To20 Shadow20.archiveRestore150To20
  Shadow20.MixedWindow.packW Shadow20.MixedWindow.unpackW Shadow20.MixedWindow.tickW Shadow20.MixedWindow.recvW
  Shadow20.MixedWindow.block15F Shadow20.MixedWindow.block15R Shadow20.MixedWindow.block20F Shadow20.MixedWindow.block20R in
private theorem mixed_slots_R (d : Bool) :
    gateSlots (Shadow20.MixedWindow.reverseMixed d) ≤ 2598694 := by
  have hp15 : ∀ p ∈ Shadow20.MixedWindow.prefixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hs15 : ∀ p ∈ Shadow20.MixedWindow.suffixPairs, p.2.val ≤ 24 ∧ WindowParams.dueTick (start p.2 - 10) = true := by decide
  have hprR := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15R d p.1 p.2) (fun p => b15SR p.2) Shadow20.MixedWindow.prefixPairs.reverse (fun p hp => by have h := hp15 p (List.mem_reverse.mp hp); exact b15R_slots_le d p.1 p.2 h.1 h.2)
  have hsuR := sum_flatMap_slots_le (fun p : Fin 26 × Fin 26 => Shadow20.MixedWindow.block15R d p.1 p.2) (fun p => b15SR p.2) Shadow20.MixedWindow.suffixPairs.reverse (fun p hp => by have h := hs15 p (List.mem_reverse.mp hp); exact b15R_slots_le d p.1 p.2 h.1 h.2)
  have h20R := sum_flatMap_slots_le (Shadow20.MixedWindow.block20R d) b20SR (List.finRange 9).reverse (fun j _ => b20R_slots_le d j)
  have p45 := (Shadow7.portal_counts 45 (by decide)).2.2.2.2.2
  have p420 := (Shadow7.portal_counts 420 (by decide)).2.2.2.2.1
  have pk420 := (Shadow7.park_counts 420).2.2.2.2.2
  have t420 := tick420_slots_le.2
  have exR := (exit420_slots_le d).2
  have e0 := (Shadow7.enter_counts Shadow20.MixedWindow.j0).2.2.2.2.2
  have r0a : gateSlots (Shadow7.unrouted Shadow20.MixedWindow.j0 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j0 0 1).2
  have r0b : gateSlots (TickCut.Tail.selected Shadow20.MixedWindow.j0 1 14) ≤ 70098 := sel14_slots _
  have l0 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j0 (by decide) (by decide)).2.2.2.2.2
  have e7 := (Shadow7.enter_counts Shadow20.MixedWindow.j7).2.2.2.2.2
  have r7a : gateSlots (Shadow7.unrouted Shadow20.MixedWindow.j7 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j7 0 1).2
  have r7b : gateSlots (TickCut.Tail.selected Shadow20.MixedWindow.j7 1 14) ≤ 70098 := sel14_slots _
  have a6 := (arch15_slots_le Shadow20.MixedWindow.j6 d).2
  have l7 := Shadow20.leave150To20Red_counts.2.2.2.2.2
  have e20 := (Shadow7.enter_counts Shadow20.MixedWindow.j20).2.2.2.2.2
  have r20a : gateSlots (Shadow7.unrouted Shadow20.MixedWindow.j20 0 1) ≤ 5000 := by
    simpa only [show 5000 * 1 = 5000 from rfl] using (WindowSlots7.route Shadow20.MixedWindow.j20 0 1).2
  have r20b : gateSlots (TickCut.Tail.selected Shadow20.MixedWindow.j20 1 14) ≤ 70098 := sel14_slots _
  have a8 := (arch20_slots_le Shadow20.MixedWindow.k8 d).2
  have l20 := (CRTWindow.leave_metrics Shadow20.MixedWindow.j20 (by decide) (by decide)).2.2.2.2.2
  have pk45 := (packW_slots_le d 45 45 (by decide)).2
  have pk140 := (packW_slots_le d 150 140 (by decide)).2
  have pk330 := (packW_slots_le d 345 330 (by decide)).2
  have pk335 := (packW_slots_le d 345 335 (by decide)).2
  have pk410 := (packW_slots_le d 420 410 (by decide)).2
  have mv := mixed_slot_sum_vals.2
  rw [show start Shadow20.MixedWindow.j0 = 45 from rfl, show (45 : Nat) + 15 = 60 from rfl] at l0
  rw [show start Shadow20.MixedWindow.j20 = 345 from rfl, show (345 : Nat) + 15 = 360 from rfl] at l20
  have hdef : Shadow20.MixedWindow.reverseMixed d = (Shadow20.MixedWindow.reverseL d).flatten := by
    unfold Shadow20.MixedWindow.reverseMixed; rfl
  rw [hdef, sum_flatten_slots, Shadow20.MixedWindow.reverseL, sum_map_append7, sum_map5, sum_map7, sum_map6, sum_map6]
  rw [p45, e0, l0, e7, l7, e20, l20, pk420, p420]
  refine Nat.le_trans ?_ mv
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add exR (Nat.add_le_add pk410 (Nat.add_le_add t420 (Nat.le_refl _))))
              hsuR)
            (Nat.add_le_add_left (Nat.add_le_add r20b (Nat.add_le_add a8 (Nat.add_le_add pk335 (Nat.add_le_add pk330 (Nat.add_le_add r20a (Nat.le_refl _)))))) _))
          h20R)
        (Nat.add_le_add_left (Nat.add_le_add r7b (Nat.add_le_add a6 (Nat.add_le_add pk140 (Nat.add_le_add r7a (Nat.le_refl _))))) _))
      hprR)
    (Nat.add_le_add_left (Nat.add_le_add r0b (Nat.add_le_add pk45 (Nat.add_le_add r0a (Nat.le_refl _)))) _)

private theorem mixed_slots (d : Bool) :
    gateSlots (Shadow20.MixedWindow.forwardMixed d) ≤ 2698994 ∧
    gateSlots (Shadow20.MixedWindow.reverseMixed d) ≤ 2598694 :=
  ⟨mixed_slots_F d, mixed_slots_R d⟩

private theorem casts {P : Program} {n : Nat} (h : gateSlots P ≤ n) : slots.measure P ≤ n := h
private theorem groupCap (d : Bool) (n : Nat)
    (hn : 22*(if d then 5322 else 6122)+881=n+(if d then 30118 else 27598)) :
    slots.measure (WindowFieldCosts.group84Sign d)=slots.measure (WindowFieldCosts.group d 1 84)+n := by
  have offset : (if d then 21193 else 18673) + 8925 =
      (if d then 30118 else 27598) := by cases d <;> decide
  have transport (stock signed field : Nat)
      (before : stock + (if d then 21193 else 18673) =
        field + 22 * (if d then 5322 else 6122) + 881)
      (after : signed + 8925 = stock) : signed = field + n := by omega
  exact transport (slots.measure (WindowFieldCosts.group84 d))
    (slots.measure (WindowFieldCosts.group84Sign d))
    (slots.measure (WindowFieldCosts.group d 1 84)) (WindowFieldCosts.group_slots d)
    (WindowFieldCosts.SignCounts.group_delta d).2.2
theorem div : slots.measure WindowCallerCosts.divide ≤
    slots.measure Stair44Outer.divide+2698994+2599891+94760+12660 :=
  Nat.le_trans (kernels 2698994 2599891 87847
    (walk slots true 4 2698994 2599891 409 rfl (casts ((Shadow20.MergeCut.slots_le true).1.trans (mixed_slots true).1)) (casts ((Shadow20.MergeCut.rslots_le true).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le true).2.trans (mixed_slots true).2) 1197)))).1
    (walk slots false 85 2698994 2599891 490 rfl (casts ((Shadow20.MergeCut.slots_le false).1.trans (mixed_slots false).1)) (casts ((Shadow20.MergeCut.rslots_le false).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le false).2.trans (mixed_slots false).2) 1197)))).2
    (groupCap true 87847 rfl)) (by omega)

theorem mul (k : Nat) : slots.measure (WindowCallerCosts.multiply k) ≤
    slots.measure (Stair44Outer.multiply k)+2698994+2599891+114880+12920 :=
  Nat.le_trans (kernelsM k 2698994 2599891 107967
    (walk slots false 84 2698994 2599891 489 rfl (casts ((Shadow20.MergeCut.slots_le false).1.trans (mixed_slots false).1)) (casts ((Shadow20.MergeCut.rslots_le false).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le false).2.trans (mixed_slots false).2) 1197)))).1
    (walk slots true 4 2698994 2599891 409 rfl (casts ((Shadow20.MergeCut.slots_le true).1.trans (mixed_slots true).1)) (casts ((Shadow20.MergeCut.rslots_le true).trans (Nat.add_le_add_right ((Shadow20.MergeCut.slots_le true).2.trans (mixed_slots true).2) 1197)))).2
    (groupCap false 107967 rfl)) (by omega)

private theorem sum_caps {a b x y : Nat} (hd : a ≤ x+2698994+2599891+94760+12660)
    (hm : b ≤ y+2698994+2599891+114880+12920) : a+b+7144 ≤ x+y+10840134 := by omega

theorem cap (C : Point) (cx cy : Fp) :
    slots.measure (WindowCallerCosts.finite C cx cy) ≤
    slots.measure (Stair44Outer.finite C cx cy)+10840134 :=
  finite_upper C cx cy 10840134 (sum_caps div (mul _))

theorem slotBound (C : Point) : gateSlots (WindowCallerCosts.program C) ≤ 67191214 := by
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
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet


theorem app {p q : Program} : Sound (p++q) ↔ Sound p ∧ Sound q :=
  ⟨fun h => ⟨⟨gp_left h.physical,good_left h.good⟩,⟨gp_right h.physical,good_right h.good⟩⟩,
    fun h => sound_append h.1 h.2⟩

theorem emitted (op : Stage) : GatePhysical (StairArchiveRelease.program op) := by
  cases op
  exacts [ReducedWindowArchives.enter0_counts.1,ReducedWindowArchives.switch0_counts.1,ReducedWindowArchives.leave0_counts.1,
    ReducedWindowArchives.enter1_counts.1,ReducedWindowArchives.switch1_counts.1,ReducedWindowArchives.leave1_counts.1]

theorem hook (j : Nat) (hj : j∈[10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (op : Stage) :
    Sound (fieldHook j op) := by
  have span : j∈List.range' 1 83 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; apply List.mem_range'_1.mpr; omega
  have chk : (fieldSites j).all (fun q => decide (InDom q))=true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
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

theorem whole (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → Sound (packet d i) := by
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

/-- the fully decoded field-body packets are sound (regular footprint plus the archive tag). -/
private theorem ot_rpk_sound (d : Bool) (k : Nat) (lo : 1≤k) (hi : k≤84) : Sound (rpk d k) := by
  by_cases big : 10≤k
  · refine ⟨?_,?_⟩
    · rw [WindowFieldCosts.rpk_hosted d k big hi]
      exact gatePhysical_rename _ (rawSwap.injective.comp (StairArchiveInactive.host.injective.comp
        (OB5.sig_injective 511 (by decide)))) _ (RouteA.Rolling1588.rawPacket_physical d k (by omega))
    · intro q hq
      rcases Finset.mem_insert.mp (WindowFieldCosts.rpk_sub d k hq) with e|m
      · subst e
        decide
      · exact (ot_opk_sound d k lo hi).good q m
  · rw [WindowFieldCosts.rpk_low d k (by omega)]
    exact ot_opk_sound d k lo hi

private theorem ot_rgroup_sound (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) : Sound (rgroup d j n) := by
  unfold rgroup
  induction n generalizing j with
  | zero =>
    show Sound []
    exact ⟨by simp [GatePhysical],fun _ h => by simp [wires] at h⟩
  | succ n ih =>
    have head := ot_rpk_sound d j lo (by omega)
    have tail := ih (j+1) (by omega) (by omega)
    cases d <;> simp only [PacketSequence.program,Bool.false_eq_true,if_false,if_true]
    · exact sound_append tail head
    · exact sound_append head tail

private theorem ot_pair (d : Bool) (j : Nat) (pick : j∈[10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (lo : 1≤j) (hi : j≤83) :
    Sound (oten j (!d)) := by
  have here := ot_opk_sound d j lo (by omega)
  have next := ot_opk_sound d (j+1) (by omega) (by omega)
  have firstOK : Sound (ofirst j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : Sound (osecond j (!d)) := by cases d <;> first | exact here | exact next
  exact sound_append (hook j pick _) (sound_append firstOK (sound_append (hook j pick _) (sound_append lastOK (hook j pick _))))

private theorem tagSites_inDom : tagSites.all (fun q => decide (InDom q)) = true := by decide +kernel

theorem packTag_sound : Sound packTag := by
  refine ⟨gatePhysical_rename_support _ _
    (fun a ha b hb eq => tagPort_inj a (Finset.mem_range.mpr (TagPack1542.packTagProg_wires_lt a ha))
      b (Finset.mem_range.mpr (TagPack1542.packTagProg_wires_lt b hb)) eq)
    TagPack1542.packTagProg_physical, ?_⟩
  intro q hq
  rw [packTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.packTagProg_wires_lt x hx
  apply of_decide_eq_true (List.all_eq_true.mp tagSites_inDom _ ?_)
  simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]

theorem unpackTag_sound : Sound unpackTag := by
  refine ⟨gatePhysical_rename_support _ _
    (fun a ha b hb eq => tagPort_inj a (Finset.mem_range.mpr (TagPack1542.unpackTagProg_wires_lt a ha))
      b (Finset.mem_range.mpr (TagPack1542.unpackTagProg_wires_lt b hb)) eq)
    TagPack1542.unpackTagProg_physical, ?_⟩
  intro q hq
  rw [unpackTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.unpackTagProg_wires_lt x hx
  apply of_decide_eq_true (List.all_eq_true.mp tagSites_inDom _ ?_)
  simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]

theorem tagSwap_inDom (q : Wire) (hq : InDom q) : InDom (tagSwap q) :=
  indom_swap _ _ (by decide) (by decide) q hq

theorem group84Body_ok (d : Bool) : Sound (group84Body d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  have c43 := ord (ot_pair d 82 (by decide) (by decide) (by decide)) (ot_rgroup_sound d 84 1 (by decide) (by decide))
  have c42 := ord (ot_rgroup_sound d 81 1 (by decide) (by decide)) c43
  have c41 := ord (ot_pair d 79 (by decide) (by decide) (by decide)) c42
  have c40 := ord (ot_rgroup_sound d 78 1 (by decide) (by decide)) c41
  have c39 := ord (ot_pair d 76 (by decide) (by decide) (by decide)) c40
  have c38 := ord (ot_rgroup_sound d 75 1 (by decide) (by decide)) c39
  have c37 := ord (ot_pair d 73 (by decide) (by decide) (by decide)) c38
  have c36 := ord (ot_rgroup_sound d 72 1 (by decide) (by decide)) c37
  have c35 := ord (ot_pair d 70 (by decide) (by decide) (by decide)) c36
  have c34 := ord (ot_rgroup_sound d 69 1 (by decide) (by decide)) c35
  have c33 := ord (ot_pair d 67 (by decide) (by decide) (by decide)) c34
  have c32 := ord (ot_rgroup_sound d 65 2 (by decide) (by decide)) c33
  have c31 := ord (ot_pair d 63 (by decide) (by decide) (by decide)) c32
  have c30 := ord (ot_rgroup_sound d 61 2 (by decide) (by decide)) c31
  have c29 := ord (ot_pair d 59 (by decide) (by decide) (by decide)) c30
  have c28 := ord (ot_rgroup_sound d 57 2 (by decide) (by decide)) c29
  have c27 := ord (ot_pair d 55 (by decide) (by decide) (by decide)) c28
  have c26 := ord (ot_rgroup_sound d 53 2 (by decide) (by decide)) c27
  have c25 := ord (ot_pair d 51 (by decide) (by decide) (by decide)) c26
  have c24 := ord (ot_rgroup_sound d 49 2 (by decide) (by decide)) c25
  have c23 := ord (ot_pair d 47 (by decide) (by decide) (by decide)) c24
  have c22 := ord (ot_rgroup_sound d 45 2 (by decide) (by decide)) c23
  have c21 := ord (ot_pair d 43 (by decide) (by decide) (by decide)) c22
  have c20 := ord (ot_rgroup_sound d 41 2 (by decide) (by decide)) c21
  have c19 := ord (ot_pair d 39 (by decide) (by decide) (by decide)) c20
  have c18 := ord (ot_rgroup_sound d 37 2 (by decide) (by decide)) c19
  have c17 := ord (ot_pair d 35 (by decide) (by decide) (by decide)) c18
  have c16 := ord (ot_rgroup_sound d 33 2 (by decide) (by decide)) c17
  have c15 := ord (ot_pair d 31 (by decide) (by decide) (by decide)) c16
  have c14 := ord (ot_rgroup_sound d 30 1 (by decide) (by decide)) c15
  have c13 := ord (ot_pair d 28 (by decide) (by decide) (by decide)) c14
  have c12 := ord (ot_rgroup_sound d 27 1 (by decide) (by decide)) c13
  have c11 := ord (ot_pair d 25 (by decide) (by decide) (by decide)) c12
  have c10 := ord (ot_rgroup_sound d 24 1 (by decide) (by decide)) c11
  have c9 := ord (ot_pair d 22 (by decide) (by decide) (by decide)) c10
  have c8 := ord (ot_rgroup_sound d 21 1 (by decide) (by decide)) c9
  have c7 := ord (ot_pair d 19 (by decide) (by decide) (by decide)) c8
  have c6 := ord (ot_rgroup_sound d 18 1 (by decide) (by decide)) c7
  have c5 := ord (ot_pair d 16 (by decide) (by decide) (by decide)) c6
  have c4 := ord (ot_rgroup_sound d 15 1 (by decide) (by decide)) c5
  have c3 := ord (ot_pair d 13 (by decide) (by decide) (by decide)) c4
  have c2 := ord (ot_rgroup_sound d 12 1 (by decide) (by decide)) c3
  exact ord (ot_pair d 10 (by decide) (by decide) (by decide)) c2

theorem group84_ok (d : Bool) : Sound (group84 d) := by
  have ord {a b : Program} (ha : Sound a) (hb : Sound b) :
      Sound (ordered d a b) := by cases d <;> first | exact sound_append ha hb | exact sound_append hb ha
  have hbody : Sound (renameProgram tagSwap (group84Body d)) :=
    sound_rename tagSwap tagSwap.injective tagSwap_inDom (group84Body_ok d)
  exact ord (ot_ogroup_sound d 1 9 (by decide) (by decide))
    (sound_append (sound_append packTag_sound hbody) unpackTag_sound)

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowSites
open Arithmetic MappedCompressed StairSiteAvoidance StairSiteEasy StairConcreteAssembly
open StairArchiveInactive StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
attribute [local irreducible] wires renameProgram StairArchiveInactive.packet

private theorem distributed_ok43 (d : Bool) (j n : Nat) :
    PieceOK Stair44FieldSites.holes TP (distributed d j n) ↔
    ∀ (i : Nat), j ≤ i → i < j+n → PieceOK Stair44FieldSites.holes TP (packet d i) := by
  induction n generalizing j with
  | zero =>
    change PieceOK _ _ [] ↔ _
    exact ⟨fun _ i lo hi => False.elim (by omega),fun _ => pieceOK_nil _ _⟩
  | succ n ih =>
    change PieceOK _ _ (if d then packet d j ++ distributed d (j+1) n
      else distributed d (j+1) n ++ packet d j) ↔ _
    have both : (PieceOK Stair44FieldSites.holes TP (packet d j) ∧ PieceOK Stair44FieldSites.holes TP (distributed d (j+1) n)) ↔
        ∀ (i : Nat), j ≤ i → i < j+(n+1) → PieceOK Stair44FieldSites.holes TP (packet d i) := by
      rw [ih]
      refine ⟨fun h i l u => ?_,fun h => ⟨h j (by omega) (by omega),?_⟩⟩
      · by_cases e : j=i
        · exact e ▸ h.1
        · exact h.2 i (by omega) (by omega)
      · exact fun i l u => h i (by omega) (by omega)
    cases d <;> simp only [Bool.false_eq_true,if_false,if_true,app]
    · exact and_comm.trans both
    · exact both

theorem whole43 (d : Bool) : ∀ (i : Nat), 1 ≤ i → i < 85 → PieceOK Stair44FieldSites.holes TP (packet d i) := by
  apply (distributed_ok43 d 1 84).mp
  rw [←distribute]
  exact Stair44Groups.hostedGroup44 d 0 1 84 (by decide)

theorem ordinary43 (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK Stair44FieldSites.holes TP (group d j n) := by
  rw [group,distribute,distributed_ok43]
  exact fun i l u => whole43 d i (by omega) (by omega)

theorem pair43 (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) :
    PieceOK Stair44FieldSites.holes TP (ten j (!d)) := by
  have jmem : j∈List.range' 1 83 := List.mem_range'_1.mpr ⟨lo,by omega⟩
  have here := whole43 d j lo (by omega)
  have next := whole43 d (j+1) (by omega) (by omega)
  have firstOK : PieceOK Stair44FieldSites.holes TP (first j (!d)) := by cases d <;> first | exact here | exact next
  have lastOK : PieceOK Stair44FieldSites.holes TP (second j (!d)) := by cases d <;> first | exact here | exact next
  exact (hook43 j jmem _).append (firstOK.append ((hook43 j jmem _).append (lastOK.append (hook43 j jmem _))))


-- oddten:begin SITES
private theorem ot_ogroup_piece43 (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK Stair44FieldSites.holes TP (ogroup d j n) := by
  have hrec := ordinary43 d j n lo hi
  exact ⟨fun x hx => hrec.1 x (WindowFieldCosts.ot_ogroup_sub d j n hx),
    fun x hx => hrec.2 x (WindowFieldCosts.ot_ogroup_sub d j n hx)⟩

private theorem ot_oten_piece43 (d : Bool) (j : Nat) (lo : 1≤j) (hi : j≤83) :
    PieceOK Stair44FieldSites.holes TP (oten j (!d)) := by
  have hrec := pair43 d j lo hi
  exact ⟨fun x hx => hrec.1 x (WindowFieldCosts.ot_oten_sub j (!d) hx),
    fun x hx => hrec.2 x (WindowFieldCosts.ot_oten_sub j (!d) hx)⟩

private theorem tag720_piece : TP (base 720)∈StairHoleSupport.recordArena ∧
    TP (base 720)∉StairHoleSupport.oldHoles ∧ TP (base 720)∉Stair44FieldSites.holes := by
  have e : TP (base 720)=4835 := by
    change StairOuterPlacement.outerPlace _=_
    rw [StairPlaceFast.outerPlace_eqB]
    decide +kernel
  rw [e]
  exact tagOK

private theorem ot_rgroup_piece43 (d : Bool) (j n : Nat) (lo : 1≤j) (hi : j+n≤85) :
    PieceOK Stair44FieldSites.holes TP (rgroup d j n) := by
  have hrec := ot_ogroup_piece43 d j n lo hi
  refine ⟨fun x hx => ?_,fun x hx => ?_⟩
  · rcases Finset.mem_insert.mp (WindowFieldCosts.rgroup_sub d j n hx) with e|m
    · subst e
      exact ⟨tag720_piece.1,tag720_piece.2.1⟩
    · exact hrec.1 x m
  · rcases Finset.mem_insert.mp (WindowFieldCosts.rgroup_sub d j n hx) with e|m
    · subst e
      exact tag720_piece.2.2
    · exact hrec.2 x m

private theorem tagSites_fit :
    tagSites.all (fun q => Stair44OuterSites.fit (StairPlaceFast.outerPlaceB q)) = true := by
  decide +kernel

theorem packTag_ok : PieceOK reserved TP packTag := by
  apply Stair44OuterSites.fits
  intro q hq
  rw [packTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.packTagProg_wires_lt x hx
  have hmem : tagPort x ∈ tagSites := by
    simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  change Stair44OuterSites.fit (StairOuterPlacement.outerPlace (tagPort x)) = true
  rw [StairPlaceFast.outerPlace_eqB]
  exact List.all_eq_true.mp tagSites_fit _ hmem

theorem unpackTag_ok : PieceOK reserved TP unpackTag := by
  apply Stair44OuterSites.fits
  intro q hq
  rw [unpackTag, renameProgram_support] at hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  have lt : x < tagSites.length := tagSites_length ▸ TagPack1542.unpackTagProg_wires_lt x hx
  have hmem : tagPort x ∈ tagSites := by
    simp only [tagPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  change Stair44OuterSites.fit (StairOuterPlacement.outerPlace (tagPort x)) = true
  rw [StairPlaceFast.outerPlace_eqB]
  exact List.all_eq_true.mp tagSites_fit _ hmem

private theorem sLetter435_fit :
    Stair44OuterSites.fit (StairPlaceFast.outerPlaceB (StairPhysicalLayout.sLetter 435)) = true := by
  decide +kernel

private theorem packet_avoids_wire (w : Wire)
    (hchk : (List.range' 1 84).all (fun k => !(StairArchiveInactive.cover k).contains (StairArchiveInactive.preimage k w)) = true)
    (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    w ∉ wires (packet d k) := by
  intro hw
  have yes := StairArchiveInactive.original d k (by omega) hw
  have no := List.all_eq_true.mp hchk k (List.mem_range'_1.mpr ⟨lo, by omega⟩)
  simp [yes] at no

/-- Off the placement's zero region, the archive preimage of a wire does not depend on the packet. -/
theorem preimage_const (k : Nat) (hk : k < 102) (q : Wire)
    (h16 : 16 ≤ OB5.sig 511 (StairArchiveInactive.host.symm q))
    (hw : ¬ Placement5.workRegion (OB5.sig 511 (StairArchiveInactive.host.symm q) - 16))
    (hh : ¬ Placement5.holeRegion (OB5.sig 511 (StairArchiveInactive.host.symm q) - 16)) :
    StairArchiveInactive.preimage k q = OB5.sig 511 (StairArchiveInactive.host.symm q) := by
  unfold StairArchiveInactive.preimage
  generalize OB5.sig 511 (StairArchiveInactive.host.symm q) = x at h16 hw hh ⊢
  apply (Equiv.symm_apply_eq (shifted (Placement5.pi k))).mpr
  have hx : x = base (x - 16) := by simp only [base, Wire] at *; omega
  rw [hx, shifted_base, Placement5.pi_outside k _ hk (fun h => h.elim hw hh)]

/-- Both archive-tag wires at once (also reused by `WindowFieldView.tagged`): their preimages are
packet-independent (`preimage_const`), so the kernel evaluates each preimage once. -/
theorem opk_both_chk : (List.range' 1 84).all (fun k =>
    !(StairArchiveInactive.cover k).contains (StairArchiveInactive.preimage k (base 720)) &&
    !(StairArchiveInactive.cover k).contains
      (StairArchiveInactive.preimage k (StairPhysicalLayout.sLetter 435))) = true := by
  have c := (by decide +kernel :
    (let x := OB5.sig 511 (StairArchiveInactive.host.symm (base 720))
     let y := OB5.sig 511 (StairArchiveInactive.host.symm (StairPhysicalLayout.sLetter 435))
     let fc := [base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base
     decide (16 ≤ x) && !decide (Placement5.workRegion (x - 16)) && !decide (Placement5.holeRegion (x - 16)) &&
     decide (16 ≤ y) && !decide (Placement5.workRegion (y - 16)) && !decide (Placement5.holeRegion (y - 16)) &&
     !fc.contains x && !fc.contains y &&
     (List.range' 1 84).all (fun k => (List.finRange 10).all (fun j =>
       History5.historyMap base (5 * k) j != x && History5.historyMap base (5 * k) j != y))) = true)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at c
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hx16, hxw⟩, hxh⟩, hy16⟩, hyw⟩, hyh⟩, hfx⟩, hfy⟩, hall⟩ := c
  have key : ∀ k z, ([base 2400, base 2409, base 2410] ++ Q6EndpointCell.ids.map base).contains z = false →
      (∀ j ∈ List.finRange 10, History5.historyMap base (5 * k) j ≠ z) →
      (!(StairArchiveInactive.cover k).contains z) = true := by
    intro k z hf hj
    simp only [Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hc
    have hm := List.contains_iff_mem.mp hc
    simp only [StairArchiveInactive.cover, List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · exact Bool.noConfusion (hf.symm.trans (List.contains_iff_mem.mpr (List.mem_append_left _ hm)))
    · exact Bool.noConfusion (hf.symm.trans (List.contains_iff_mem.mpr (List.mem_append_right _ hm)))
    · obtain ⟨j, hjm, hje⟩ := List.mem_map.mp hm
      exact hj j hjm hje
  rw [List.all_eq_true] at hall ⊢
  intro k hk
  have hk' := List.mem_range'_1.mp hk
  have hh := List.all_eq_true.mp (hall k hk)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
  rw [preimage_const k (by omega) _ hx16 hxw hxh, preimage_const k (by omega) _ hy16 hyw hyh,
    Bool.and_eq_true]
  exact ⟨key k _ hfx (fun j hj => (hh j hj).1), key k _ hfy (fun j hj => (hh j hj).2)⟩

private theorem opk_avoids_720 (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    base 720 ∉ wires (opk d k) :=
  fun hw => packet_avoids_wire (base 720)
    (List.all_eq_true.mpr fun j hj => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp opk_both_chk j hj)).1)
    d k lo hi (WindowFieldCosts.ot_opk_sub d k hw)

private theorem opk_avoids_435 (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    StairPhysicalLayout.sLetter 435 ∉ wires (opk d k) :=
  fun hw => packet_avoids_wire (StairPhysicalLayout.sLetter 435)
    (List.all_eq_true.mpr fun j hj => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp opk_both_chk j hj)).2)
    d k lo hi (WindowFieldCosts.ot_opk_sub d k hw)

private theorem ogroup_avoids_wire (w : Wire)
    (hpk : ∀ k, 1 ≤ k → k ≤ 84 → w ∉ wires (opk d k))
    (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    w ∉ wires (ogroup d j n) := by
  unfold ogroup
  induction n generalizing j with
  | zero => intro h; simp [PacketSequence.program, wires] at h
  | succ n ih =>
    intro h
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      wires_append, Finset.mem_union] at h
    · rcases h with h1 | h2
      · exact ih (j + 1) (by omega) (by omega) h1
      · exact hpk j lo (by omega) h2
    · rcases h with h1 | h2
      · exact hpk j lo (by omega) h1
      · exact ih (j + 1) (by omega) (by omega) h2

private theorem fieldHook_avoids_435_chk :
    WindowBankCheck.banks.all (fun j =>
      (StairArchiveRelease.fieldSites j).all (fun q => q != StairPhysicalLayout.sLetter 435)) = true := by
  decide +kernel

private theorem fieldHook_avoids_435 (j : Nat)
    (hj : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (op : StairArchiveRelease.Stage) :
    StairPhysicalLayout.sLetter 435 ∉ wires (StairArchiveRelease.fieldHook j op) := by
  have hchk : (StairArchiveRelease.fieldSites j).all (fun q => q != StairPhysicalLayout.sLetter 435) = true :=
    List.all_eq_true.mp fieldHook_avoids_435_chk j hj
  have hspan : j ∈ List.range' 1 83 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    apply List.mem_range'_1.mpr; omega
  intro hw
  rw [StairArchiveRelease.fieldHook, renameProgram_support] at hw
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hw
  have len : (StairArchiveRelease.fieldSites j).length = 121 := by
    have hh := (ArchiveFieldScratch.layout_frame j hspan).2
    rwa [← StairArchiveRelease.field_layout, List.length_map] at hh
  have lt : x < (StairArchiveRelease.fieldSites j).length :=
    len ▸ (Finset.mem_range.mp (StairArchiveRelease.sub op hx))
  have hmem : StairArchiveRelease.fieldPort j x ∈ StairArchiveRelease.fieldSites j := by
    simp only [StairArchiveRelease.fieldPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  have hne := List.all_eq_true.mp hchk _ hmem
  rw [hxeq] at hne
  simp at hne

private theorem oten_avoids_435 (d : Bool) (j : Nat)
    (hj : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (lo : 1 ≤ j) (hi : j ≤ 83) :
    StairPhysicalLayout.sLetter 435 ∉ wires (oten j (!d)) := by
  intro h
  simp only [oten, wires_append, Finset.mem_union] at h
  rcases h with h1 | h2 | h3 | h4 | h5
  · exact fieldHook_avoids_435 j hj _ h1
  · cases d <;> simp only [ofirst, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h2
    · exact opk_avoids_435 false (j + 1) (by omega) (by omega) h2
    · exact opk_avoids_435 true j lo (by omega) h2
  · exact fieldHook_avoids_435 j hj _ h3
  · cases d <;> simp only [osecond, Bool.not_false, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h4
    · exact opk_avoids_435 false j lo (by omega) h4
    · exact opk_avoids_435 true (j + 1) (by omega) (by omega) h4
  · exact fieldHook_avoids_435 j hj _ h5

private theorem group84Body_ok43_and_avoids435 (d : Bool) :
    PieceOK Stair44FieldSites.holes TP (group84Body d) ∧
    StairPhysicalLayout.sLetter 435 ∉ wires (group84Body d) := by
  have ord {a b : Program}
      (ha : PieceOK Stair44FieldSites.holes TP a ∧ StairPhysicalLayout.sLetter 435 ∉ wires a)
      (hb : PieceOK Stair44FieldSites.holes TP b ∧ StairPhysicalLayout.sLetter 435 ∉ wires b) :
      PieceOK Stair44FieldSites.holes TP (ordered d a b) ∧ StairPhysicalLayout.sLetter 435 ∉ wires (ordered d a b) := by
    cases d <;> simp only [ordered, if_true, if_false, Bool.false_eq_true, wires_append, Finset.mem_union]
    · exact ⟨hb.1.append ha.1, fun h => h.elim hb.2 ha.2⟩
    · exact ⟨ha.1.append hb.1, fun h => h.elim ha.2 hb.2⟩
  have ot (j : Nat) (hj : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) (lo : 1 ≤ j) (hi : j ≤ 83) :
      PieceOK Stair44FieldSites.holes TP (oten j (!d)) ∧ StairPhysicalLayout.sLetter 435 ∉ wires (oten j (!d)) :=
    ⟨ot_oten_piece43 d j lo hi, oten_avoids_435 d j hj lo hi⟩
  have og (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
      PieceOK Stair44FieldSites.holes TP (rgroup d j n) ∧ StairPhysicalLayout.sLetter 435 ∉ wires (rgroup d j n) :=
    ⟨ot_rgroup_piece43 d j n lo hi, rgroup_avoids d (StairPhysicalLayout.sLetter 435) j n (by decide +kernel)
      (ogroup_avoids_wire (StairPhysicalLayout.sLetter 435) (opk_avoids_435 d) j n lo hi)⟩
  have c43 := ord (ot 82 (by decide) (by decide) (by decide)) (og 84 1 (by decide) (by decide))
  have c42 := ord (og 81 1 (by decide) (by decide)) c43
  have c41 := ord (ot 79 (by decide) (by decide) (by decide)) c42
  have c40 := ord (og 78 1 (by decide) (by decide)) c41
  have c39 := ord (ot 76 (by decide) (by decide) (by decide)) c40
  have c38 := ord (og 75 1 (by decide) (by decide)) c39
  have c37 := ord (ot 73 (by decide) (by decide) (by decide)) c38
  have c36 := ord (og 72 1 (by decide) (by decide)) c37
  have c35 := ord (ot 70 (by decide) (by decide) (by decide)) c36
  have c34 := ord (og 69 1 (by decide) (by decide)) c35
  have c33 := ord (ot 67 (by decide) (by decide) (by decide)) c34
  have c32 := ord (og 65 2 (by decide) (by decide)) c33
  have c31 := ord (ot 63 (by decide) (by decide) (by decide)) c32
  have c30 := ord (og 61 2 (by decide) (by decide)) c31
  have c29 := ord (ot 59 (by decide) (by decide) (by decide)) c30
  have c28 := ord (og 57 2 (by decide) (by decide)) c29
  have c27 := ord (ot 55 (by decide) (by decide) (by decide)) c28
  have c26 := ord (og 53 2 (by decide) (by decide)) c27
  have c25 := ord (ot 51 (by decide) (by decide) (by decide)) c26
  have c24 := ord (og 49 2 (by decide) (by decide)) c25
  have c23 := ord (ot 47 (by decide) (by decide) (by decide)) c24
  have c22 := ord (og 45 2 (by decide) (by decide)) c23
  have c21 := ord (ot 43 (by decide) (by decide) (by decide)) c22
  have c20 := ord (og 41 2 (by decide) (by decide)) c21
  have c19 := ord (ot 39 (by decide) (by decide) (by decide)) c20
  have c18 := ord (og 37 2 (by decide) (by decide)) c19
  have c17 := ord (ot 35 (by decide) (by decide) (by decide)) c18
  have c16 := ord (og 33 2 (by decide) (by decide)) c17
  have c15 := ord (ot 31 (by decide) (by decide) (by decide)) c16
  have c14 := ord (og 30 1 (by decide) (by decide)) c15
  have c13 := ord (ot 28 (by decide) (by decide) (by decide)) c14
  have c12 := ord (og 27 1 (by decide) (by decide)) c13
  have c11 := ord (ot 25 (by decide) (by decide) (by decide)) c12
  have c10 := ord (og 24 1 (by decide) (by decide)) c11
  have c9 := ord (ot 22 (by decide) (by decide) (by decide)) c10
  have c8 := ord (og 21 1 (by decide) (by decide)) c9
  have c7 := ord (ot 19 (by decide) (by decide) (by decide)) c8
  have c6 := ord (og 18 1 (by decide) (by decide)) c7
  have c5 := ord (ot 16 (by decide) (by decide) (by decide)) c6
  have c4 := ord (og 15 1 (by decide) (by decide)) c5
  have c3 := ord (ot 13 (by decide) (by decide) (by decide)) c4
  have c2 := ord (og 12 1 (by decide) (by decide)) c3
  exact ord (ot 10 (by decide) (by decide) (by decide)) c2

private theorem newHolesNat_sub_43_or_4835 :
    StairPhysicalLayout.newHolesNat.all (fun v => decide (v ∈ Stair44FieldSites.holes) || (v == 4835)) = true := by
  decide +kernel

private theorem sw_in_range {a b z lo hi : Nat}
    (h : lo ≤ StairPlaceFast.sw a b z ∧ StairPlaceFast.sw a b z ≤ hi)
    (ha : ¬(lo ≤ a ∧ a ≤ hi)) (hb : ¬(lo ≤ b ∧ b ≤ hi)) :
    StairPlaceFast.sw a b z = z := by
  unfold StairPlaceFast.sw at h ⊢
  by_cases h1 : z = a
  · rw [if_pos h1] at h; omega
  · by_cases h2 : z = b
    · rw [if_neg h1, if_pos h2] at h; omega
    · rw [if_neg h1, if_neg h2]

private theorem metaN_not_4835_4839 (j : Nat) :
    ¬(4835 ≤ StairPlaceFast.metaN j ∧ StairPlaceFast.metaN j ≤ 4839) := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => decide
  | j + 12 => unfold StairPlaceFast.metaN; simp

private theorem pwN_window (i : Nat)
    (h : 4835 ≤ StairPlaceFast.pwN i ∧ StairPlaceFast.pwN i ≤ 4839) :
    720 ≤ i ∧ i ≤ 724 ∧ StairPlaceFast.pwN i = 4115 + i := by
  unfold StairPlaceFast.pwN at h ⊢
  by_cases h1 : i < 2314
  · rw [if_pos h1] at h ⊢
    by_cases h2 : 770 ≤ i ∧ i < 1026
    · rw [if_pos h2] at h; omega
    · rw [if_neg h2] at h ⊢
      by_cases h3 : 2056 ≤ i ∧ i < 2312
      · rw [if_pos h3] at h; omega
      · rw [if_neg h3] at h ⊢
        by_cases h4 : 1026 ≤ i <;> by_cases h5 : 2312 ≤ i
        · rw [if_pos h4, if_pos h5] at h; omega
        · rw [if_pos h4, if_neg h5] at h; omega
        · rw [if_neg h4, if_pos h5] at h; omega
        · rw [if_neg h4, if_neg h5] at h ⊢; omega
  · rw [if_neg h1] at h
    exact (metaN_not_4835_4839 (i - 2400) h).elim

private theorem outerPlace_in_4835_4839 (x : Wire)
    (h : 4835 ≤ StairOuterPlacement.outerPlace x ∧ StairOuterPlacement.outerPlace x ≤ 4839) :
    x = StairOuterPlacement.outerPlace x - 4835 + 736 := by
  rw [StairPlaceFast.outerPlace_eqN] at h ⊢
  unfold StairPlaceFast.outerPlaceN StairPlaceFast.kernelPlaceN at h ⊢
  have s1 := sw_in_range h (by omega) (by omega); rw [s1] at h ⊢
  have s2 := sw_in_range h (by omega) (by omega); rw [s2] at h ⊢
  have s3 := sw_in_range h (by omega) (by omega); rw [s3] at h ⊢
  have s4 := sw_in_range h (by omega) (by omega); rw [s4] at h ⊢
  have s5 := sw_in_range h (by omega) (by omega); rw [s5] at h ⊢
  have s6 := sw_in_range h (by omega) (by omega); rw [s6] at h ⊢
  have s7 := sw_in_range h (by omega) (by omega); rw [s7] at h ⊢
  have hpw := pwN_window (StairPlaceFast.sw 785 1813 (StairPlaceFast.fieldPlaceN x) - 16) h
  rw [hpw.2.2]
  have hfp : 736 ≤ StairPlaceFast.sw 785 1813 (StairPlaceFast.fieldPlaceN x) ∧
      StairPlaceFast.sw 785 1813 (StairPlaceFast.fieldPlaceN x) ≤ 740 := by omega
  have hsw0 := sw_in_range hfp (by omega) (by omega)
  rw [hsw0] at hfp ⊢
  unfold StairPlaceFast.fieldPlaceN at hfp ⊢
  have hsw1 := sw_in_range hfp (by omega) (by omega); rw [hsw1] at hfp ⊢
  have hsw2 := sw_in_range hfp (by omega) (by omega); rw [hsw2] at hfp ⊢
  have hsw3 := sw_in_range hfp (by omega) (by omega); rw [hsw3] at hfp ⊢
  have hsw4 := sw_in_range hfp (by omega) (by omega); rw [hsw4] at hfp ⊢
  dsimp only [Wire] at *
  omega

private theorem upgrade44_of_avoids_720 {P : Program}
    (h43 : PieceOK Stair44FieldSites.holes TP P)
    (hdom : ∀ x ∈ wires P, x < 2428)
    (h720 : base 720 ∉ wires P) :
    PieceOK reserved TP P := by
  have _ := hdom
  refine ⟨h43.1, fun x hx bad => ?_⟩
  rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat] at bad
  have hmem := List.all_eq_true.mp newHolesNat_sub_43_or_4835 (TP x) bad
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hmem
  rcases hmem with h43b | h4835
  · exact h43.2 x hx h43b
  · have h1 : x = base 720 := by
      have h4835' : StairOuterPlacement.outerPlace x = 4835 := h4835
      have hxeq := outerPlace_in_4835_4839 x ⟨Nat.le_of_eq h4835'.symm, Nat.le_trans (Nat.le_of_eq h4835') (by decide)⟩
      dsimp only [base, Wire] at *
      omega
    exact h720 (h1 ▸ hx)

private theorem lt_2428_of_inDom {x : Wire} (h : StairRestSupport.InDom x) : x < 2428 := by
  unfold StairRestSupport.InDom StairRestSupport.InDomN at h
  dsimp only [Wire] at *
  omega

theorem group84_ok (d : Bool) : PieceOK reserved TP (group84 d) := by
  have ord {a b : Program} (ha : PieceOK reserved TP a) (hb : PieceOK reserved TP b) :
      PieceOK reserved TP (ordered d a b) := by cases d <;> first | exact ha.append hb | exact hb.append ha
  have h19 : PieceOK reserved TP (ogroup d 1 9) :=
    upgrade44_of_avoids_720 (ot_ogroup_piece43 d 1 9 (by decide) (by decide))
      (fun x hx => lt_2428_of_inDom ((WindowPhysical.ot_ogroup_sound d 1 9 (by decide) (by decide)).good x hx))
      (ogroup_avoids_wire (base 720) (opk_avoids_720 d) 1 9 (by decide) (by decide))
  have ⟨hb43, hb435⟩ := group84Body_ok43_and_avoids435 d
  have h435_ok : TP (StairPhysicalLayout.sLetter 435) ∈ StairHoleSupport.recordArena ∧
      TP (StairPhysicalLayout.sLetter 435) ∉ StairHoleSupport.oldHoles ∧
      TP (StairPhysicalLayout.sLetter 435) ∉ reserved := by
    have hf := sLetter435_fit
    rw [← StairPlaceFast.outerPlace_eqB] at hf
    exact singleton_ok hf
  have hbody : PieceOK reserved TP (renameProgram tagSwap (group84Body d)) := by
    rw [ren]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · dsimp only
      by_cases hx720 : x = base 720
      · subst hx720
        have heq : tagSwap (base 720) = StairPhysicalLayout.sLetter 435 := Equiv.swap_apply_left _ _
        rw [heq]
        exact ⟨h435_ok.1, h435_ok.2.1⟩
      · have hx435 : x ≠ StairPhysicalLayout.sLetter 435 := fun h => hb435 (h ▸ hx)
        rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hx720 hx435]
        exact hb43.1 x hx
    · dsimp only
      by_cases hx720 : x = base 720
      · subst hx720
        have heq : tagSwap (base 720) = StairPhysicalLayout.sLetter 435 := Equiv.swap_apply_left _ _
        rw [heq]
        exact h435_ok.2.2
      · have hx435 : x ≠ StairPhysicalLayout.sLetter 435 := fun h => hb435 (h ▸ hx)
        rw [tagSwap, Equiv.swap_apply_of_ne_of_ne hx720 hx435]
        intro bad
        rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat] at bad
        have hmem := List.all_eq_true.mp newHolesNat_sub_43_or_4835 (TP x) bad
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hmem
        rcases hmem with h43b | h4835
        · exact hb43.2 x hx h43b
        · have h1 : x = base 720 := by
            have h4835' : StairOuterPlacement.outerPlace x = 4835 := h4835
            have hxeq := outerPlace_in_4835_4839 x ⟨Nat.le_of_eq h4835'.symm, Nat.le_trans (Nat.le_of_eq h4835') (by decide)⟩
            dsimp only [base, Wire] at *
            omega
          exact hx720 h1
  exact ord h19 ((packTag_ok.append hbody).append unpackTag_ok)

end ECDSAAdd.Entrant.StairPacket.WindowSites

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

open Arithmetic MappedCompressed StairArchiveInactive StairArchiveRelease RecordedQuantum
open StairArchiveNativeCut StairArchiveTen
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
attribute [local irreducible] wires run opk rpk fieldHook

theorem signHost_ne_tag : signHost ≠ base 720 := by decide +kernel

theorem packet_avoids_sign (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    signHost ∉ wires (packet d k) := by
  intro used
  have pre_eq : preimage k signHost = signHost := by
    rw [WindowSites.preimage_const k (by omega) signHost (by decide +kernel)
      (by decide +kernel) (by decide +kernel)]
    decide +kernel
  have admissible := StairArchiveInactive.original d k (by omega) used
  rw [pre_eq] at admissible
  have check : (List.range' 1 84).all (fun j => !(cover j).contains signHost) = true := by
    decide +kernel
  have out := List.all_eq_true.mp check k (List.mem_range'_1.mpr ⟨lo, by omega⟩)
  simp [admissible] at out

theorem opk_avoids_sign (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    signHost ∉ wires (opk d k) :=
  fun used => packet_avoids_sign d k lo hi (ot_opk_sub d k used)

theorem spk_sub (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    wires (spk d k) ⊆ insert signHost (wires (opk d k)) := by
  rw [spk, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (rpk_sub d k hw) with h | h
  · subst w
    rw [Equiv.swap_apply_left]
    exact Finset.mem_insert_self _ _
  · have ht : w ≠ base 720 := fun he => opk_avoid720 d k lo hi (he ▸ h)
    have hs : w ≠ signHost := fun he => opk_avoids_sign d k lo hi (he ▸ h)
    rw [Equiv.swap_apply_of_ne_of_ne ht hs]
    exact Finset.mem_insert_of_mem h

theorem spk_physical (d : Bool) (k : Nat) (lo : 10 ≤ k) (hi : k ≤ 84) :
    GatePhysical (spk d k) := by
  rw [spk, rpk_hosted d k lo hi]
  exact gatePhysical_rename _ (Equiv.swap _ _).injective _
    (gatePhysical_rename _ (rawSwap.injective.comp
      (StairArchiveInactive.host.injective.comp (OB5.sig_injective 511 (by decide)))) _
      (RouteA.Rolling1588.rawPacket_physical d k (by omega)))

section
attribute [local irreducible] gpk

theorem epk_sub (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    wires (epk d k) ⊆ insert signHost (wires (opk d k)) := by
  rw [epk, renameProgram_support]
  intro q hq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (gpk_sub d k lo hi hw) with h | h
  · subst w
    rw [Equiv.swap_apply_left]
    exact Finset.mem_insert_self _ _
  · have ht : w ≠ base 720 := fun he => opk_avoid720 d k lo hi (he ▸ h)
    have hs : w ≠ signHost := fun he => opk_avoids_sign d k lo hi (he ▸ h)
    rw [Equiv.swap_apply_of_ne_of_ne ht hs]
    exact Finset.mem_insert_of_mem h

theorem epk_physical (d : Bool) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 84) :
    GatePhysical (epk d k) := by
  rw [epk, gpk_hosted d k]
  exact gatePhysical_rename _ (Equiv.swap _ _).injective _
    (gatePhysical_rename _ (rawSwap.injective.comp
      (StairArchiveInactive.host.injective.comp (OB5.sig_injective 511 (by decide)))) _
      (RouteA.Rolling1588.rawPacket_physical d k (by omega)))

theorem egroup_sub (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    wires (egroup d j n) ⊆ insert signHost (wires (ogroup d j n)) := by
  unfold egroup ogroup
  induction n generalizing j with
  | zero =>
    intro q hq
    simp [PacketSequence.program, wires] at hq
  | succ n ih =>
    have head := epk_sub d j lo (by omega)
    have tail := ih (j + 1) (by omega) (by omega)
    intro q hq
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      wires_append, Finset.mem_union, Finset.mem_insert] at hq ⊢
    · rcases hq with h | h
      · have := Finset.mem_insert.mp (tail h); tauto
      · have := Finset.mem_insert.mp (head h); tauto
    · rcases hq with h | h
      · have := Finset.mem_insert.mp (head h); tauto
      · have := Finset.mem_insert.mp (tail h); tauto

theorem egroup_physical (d : Bool) (j n : Nat) (lo : 1 ≤ j) (hi : j + n ≤ 85) :
    GatePhysical (egroup d j n) := by
  unfold egroup
  induction n generalizing j with
  | zero => simp [PacketSequence.program, GatePhysical]
  | succ n ih =>
    have head := epk_physical d j lo (by omega)
    have tail := ih (j + 1) (by omega) (by omega)
    cases d <;> simp only [PacketSequence.program, Bool.false_eq_true, if_false, if_true,
      gatePhysical_append]
    · exact ⟨tail, head⟩
    · exact ⟨head, tail⟩

end

theorem hook_avoids_sign (j : Nat) (hj : j ∈ WindowBankCheck.banks) (op : Stage) :
    signHost ∉ wires (fieldHook j op) := by
  intro used
  rw [fieldHook, renameProgram_support] at used
  obtain ⟨i, hi, eq⟩ := Finset.mem_image.mp used
  have inRange : j ∈ List.range' 1 83 := by
    simp only [WindowBankCheck.banks, List.mem_cons, List.not_mem_nil, or_false] at hj
    exact List.mem_range'_1.mpr (by omega)
  have len : (fieldSites j).length = 121 := by
    have h := (ArchiveFieldScratch.layout_frame j inRange).2
    rwa [← field_layout, List.length_map] at h
  have lt : i < (fieldSites j).length := len ▸ Finset.mem_range.mp (StairArchiveRelease.sub op hi)
  have hmem : fieldPort j i ∈ fieldSites j := by
    simp only [fieldPort, List.getElem?_eq_getElem lt, Option.getD_some, List.getElem_mem]
  have check : WindowBankCheck.banks.all
      (fun b => !(fieldSites b).contains signHost) = true := by decide +kernel
  have out := List.all_eq_true.mp check j hj
  rw [eq] at hmem
  simp [hmem] at out

private theorem xorIntoSign_sub (xs : List Wire) :
    wires (xorIntoSign xs) ⊆ insert signHost xs.toFinset := by
  induction xs with
  | nil => simp [xorIntoSign, wires]
  | cons x xs ih =>
    intro q hq
    rw [xorIntoSign, List.map_cons, wires] at hq
    rcases Finset.mem_union.mp hq with h | h
    · simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at h
      simp only [List.toFinset_cons, Finset.mem_insert]
      exact h.elim (fun he => Or.inr (Or.inl he)) Or.inl
    · exact (Finset.mem_insert.mp (ih h)).elim
        (fun he => Finset.mem_insert.mpr (Or.inl he))
        (fun hu => Finset.mem_insert_of_mem
          (List.mem_toFinset.mpr (List.mem_cons_of_mem x (List.mem_toFinset.mp hu))))

theorem prefixLoanPort_mem (i : Nat) (hi : i < 12) : prefixLoanPort i ∈ tagSites := by
  have h : ∀ k : Fin 12, prefixLoanPort k ∈ tagSites := by decide +kernel
  exact h ⟨i, hi⟩

theorem signBracket_sub :
    wires signBracket ⊆ insert signHost (tagSites.toFinset ∪ signPayload.toFinset) := by
  have renSub (P : Program) (hp : wires P ⊆ Finset.range 12) :
      wires (renameProgram prefixLoanPort P) ⊆ tagSites.toFinset := by
    intro q hq
    rw [renameProgram_support] at hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact List.mem_toFinset.mpr (prefixLoanPort_mem i (Finset.mem_range.mp (hp hi)))
  have px : (prefixDataPorts.map prefixLoanPort).toFinset ⊆ tagSites.toFinset := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have hlt : ∀ n ∈ prefixDataPorts, n < 12 := by decide +kernel
    exact List.mem_toFinset.mpr (prefixLoanPort_mem i (hlt i hi))
  intro q hq
  simp only [signBracket, prefixParity, wires_append, Finset.mem_union] at hq
  simp only [Finset.mem_insert, Finset.mem_union]
  rcases hq with ((a | b) | c) | d
  · exact Or.inr (Or.inl (renSub _ FourScratchPrefix.support.2.2 a))
  · exact (Finset.mem_insert.mp (xorIntoSign_sub _ b)).elim Or.inl (fun h => Or.inr (Or.inl (px h)))
  · exact Or.inr (Or.inl (renSub _ FourScratchPrefix.support.2.1 c))
  · exact (Finset.mem_insert.mp (xorIntoSign_sub _ d)).elim Or.inl (fun h => Or.inr (Or.inr h))

def signPayloadBand (q : Wire) : Prop :=
  (21 ≤ q ∧ q < 441) ∨ (1049 ≤ q ∧ q < 1301) ∨ (1645 ≤ q ∧ q < 1813)

private theorem sign_rebinder_fix : ∀ (rs hs : List Wire) (x : Wire), x ∉ rs → x ∉ hs →
    StairArchiveInactive.rebinder rs hs x = x
  | r :: rs, h :: hs, x, hr, hh => by
    simp only [List.mem_cons, not_or] at hr hh
    simp only [StairArchiveInactive.rebinder, Equiv.trans_apply]
    rw [sign_rebinder_fix rs hs x hr.2 hh.2]
    exact Equiv.swap_apply_of_ne_of_ne hr.1 hh.1
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl

private theorem signPayload_raw_band (k : Nat) (hk : k ∈ List.range' 1 84) (i : Fin 8) :
    signPayloadBand (OB5.sig 511 (History5.historyMap base (5 * k) (NewHistory5.payloadPort i))) := by
  have hk' := List.mem_range'_1.mp hk
  have hi := (NewHistory5.payloadPort i).isLt
  unfold OB5.sig History5.historyMap History5.historyId signPayloadBand
  simp only [MappedCompressed.base, Wire]
  split_ifs <;> omega

theorem signPayload_host_fix (k : Nat) (hk : k ∈ List.range' 1 84) (i : Fin 8) :
    let x := OB5.sig 511 (History5.historyMap base (5 * k) (NewHistory5.payloadPort i))
    StairArchiveInactive.host x = x := by
  let x := OB5.sig 511 (History5.historyMap base (5 * k) (NewHistory5.payloadPort i))
  have bound : signPayloadBand x := signPayload_raw_band k hk i
  have roles : x ∉ StairSchedule.exclusiveRoles := by
    intro h
    simp only [StairWireCheck.exclusiveRoles_eq_nat, StairWireCheck.exclusiveNat,
      List.mem_append, List.mem_range'_1] at h
    unfold signPayloadBand at bound
    dsimp only [Wire] at *
    omega
  have hosts : x ∉ StairPhysicalLayout.hosts 87 := by
    intro h
    have hostBounds : StairWireCheck.hosts87Nat.all (fun w => decide (1561 ≤ w ∧ w ≤ 1633)) = true := by
      decide +kernel
    rw [StairWireCheck.hosts87_eq_nat] at h
    have hh := of_decide_eq_true (List.all_eq_true.mp hostBounds x h)
    unfold signPayloadBand at bound
    dsimp only [Wire] at *
    omega
  exact sign_rebinder_fix _ _ x roles hosts

theorem signPayload_band (q : Wire) (hq : q ∈ signPayload) : signPayloadBand q := by
  change q ∈ (List.range' 1 84).flatMap pkSitesOf at hq
  obtain ⟨k, hk, hq⟩ := List.mem_flatMap.mp hq
  simp only [pkSitesOf, List.mem_map] at hq
  obtain ⟨i, _, rfl⟩ := hq
  have fixed := signPayload_host_fix k hk i
  dsimp only at fixed
  rw [fixed]
  exact signPayload_raw_band k hk i

theorem signPayload_hosted_shape :
    signPayload = (List.range' 8 672).map (fun i =>
      StairArchiveInactive.host (OB5.sig 511 (NewHistory5.payloadWire base i))) := by
  let blocks := (List.range' 1 84).flatMap (fun k => (List.finRange 8).map (fun i => 8*k+i.val))
  have indices : blocks = List.range' 8 672 := by decide +kernel
  rw [← indices]
  dsimp only [blocks]
  rw [List.map_flatMap]
  simp only [signPayload, List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro k _
  simp only [pkSitesOf, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  rw [NewHistory5.payloadWire_packet base k i.val i.isLt]

theorem signPayload_unhosted_shape :
    signPayload = (List.range' 8 672).map (fun i => OB5.sig 511 (NewHistory5.payloadWire base i)) := by
  rw [signPayload_hosted_shape]
  apply List.map_congr_left
  intro n hn
  have span := List.mem_range'_1.mp hn
  have packet : n / 8 ∈ List.range' 1 84 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
  exact signPayload_host_fix (n / 8) packet ⟨n % 8, Nat.mod_lt _ (by decide)⟩

theorem signPayload_range :
    signPayload.all (fun q => decide (16 ≤ q ∧ q < 2330)) = true := by
  apply List.all_eq_true.mpr
  intro q hq
  have h := signPayload_band q hq
  unfold signPayloadBand at h
  apply decide_eq_true_eq.mpr
  dsimp only [Wire] at *
  omega

theorem sten_sub (j : Nat) (lo : 1 ≤ j) (hi : j ≤ 83) (rev : Bool) :
    wires (sten j rev) ⊆ insert signHost (wires (oten j rev)) := by
  have hfirst : wires (sfirst j rev) ⊆ insert signHost (wires (ofirst j rev)) := by
    unfold sfirst ofirst
    exact spk_sub _ _ (by split <;> omega) (by split <;> omega)
  have hsecond : wires (ssecond j rev) ⊆ insert signHost (wires (osecond j rev)) := by
    unfold ssecond osecond
    exact spk_sub _ _ (by split <;> omega) (by split <;> omega)
  intro q hq
  simp only [sten, oten, wires_append, Finset.mem_union, Finset.mem_insert] at hq ⊢
  rcases hq with a | b | c | d | e
  · tauto
  · have := Finset.mem_insert.mp (hfirst b); tauto
  · tauto
  · have := Finset.mem_insert.mp (hsecond d); tauto
  · tauto

private theorem ordered_wires (d : Bool) (A B : Program) :
    wires (ordered d A B) = wires A ∪ wires B := by
  cases d <;> simp [ordered, Finset.union_comm]

private def signBodyRows : List (Nat × Nat) :=
  WindowBankCheck.banks.zip WindowBankCheck.banks.tail

private abbrev signBodyRowOK (r : Nat × Nat) : Prop :=
  r.1 ∈ WindowBankCheck.banks ∧ 10 ≤ r.1 ∧ r.1 ≤ 83 ∧
    1 ≤ r.1 + 2 ∧ r.1 + 2 + (r.2 - (r.1 + 2)) ≤ 85

private theorem signBodyRows_ok : ∀ r ∈ signBodyRows, signBodyRowOK r := by decide +kernel

private def signBodyFold (d : Bool) (pair : Nat → Program) : List (Nat × Nat) → Program
  | [] => ordered d (pair 82) (rgroup d 84 1)
  | r :: rs => ordered d (pair r.1)
      (ordered d (rgroup d (r.1 + 2) (r.2 - (r.1 + 2))) (signBodyFold d pair rs))

section
attribute [local irreducible] ordered sten oten rgroup

theorem signBody_rel (d : Bool) (R : Program → Program → Prop)
    (join : ∀ {A A' B B'}, R A A' → R B B' → R (ordered d A B) (ordered d A' B'))
    (pair : ∀ j ∈ WindowBankCheck.banks, 10 ≤ j → j ≤ 83 → R (sten j (!d)) (oten j (!d)))
    (native : ∀ j n, 1 ≤ j → j + n ≤ 85 → R (rgroup d j n) (rgroup d j n)) :
    R (group84SignBody d) (group84Body d) := by
  have assemble : ∀ xs : List (Nat × Nat), (∀ r ∈ xs, signBodyRowOK r) →
      R (signBodyFold d (fun j => sten j (!d)) xs) (signBodyFold d (fun j => oten j (!d)) xs) := by
    intro xs
    induction xs with
    | nil =>
      intro _
      exact join (pair 82 (by decide) (by decide) (by decide)) (native 84 1 (by decide) (by decide))
    | cons r rs ih =>
      intro valid
      have h := valid r List.mem_cons_self
      have tail := ih (fun q hq => valid q (List.mem_cons_of_mem r hq))
      exact join (pair r.1 h.1 h.2.1 h.2.2.1)
        (join (native (r.1 + 2) (r.2 - (r.1 + 2)) h.2.2.2.1 h.2.2.2.2) tail)
  change R (signBodyFold d (fun j => sten j (!d)) signBodyRows)
    (signBodyFold d (fun j => oten j (!d)) signBodyRows)
  exact assemble signBodyRows signBodyRows_ok
end

theorem signBody_sub (d : Bool) :
    wires (group84SignBody d) ⊆ insert signHost (wires (group84Body d)) := by
  have step {A A' B B' : Program}
      (a : wires A' ⊆ insert signHost (wires A))
      (b : wires B' ⊆ insert signHost (wires B)) :
      wires (ordered d A' B') ⊆ insert signHost (wires (ordered d A B)) := by
    rw [ordered_wires, ordered_wires]
    intro q hq
    simp only [Finset.mem_union, Finset.mem_insert] at hq ⊢
    rcases hq with hl | hr
    · have := Finset.mem_insert.mp (a hl); tauto
    · have := Finset.mem_insert.mp (b hr); tauto
  exact signBody_rel d (fun A B => wires A ⊆ insert signHost (wires B))
    (fun a b => step a b) (fun j _ lo hi => sten_sub j (by omega) hi (!d))
    (fun _ _ _ _ => Finset.subset_insert _ _)

theorem tagSwap_signHost : tagSwap signHost = signHost := by decide +kernel

private theorem rename_sign_sub (f : Wire → Wire) (hf : f signHost = signHost)
    (P Q : Program) (h : wires P ⊆ insert signHost (wires Q)) :
    wires (renameProgram f P) ⊆ insert signHost (wires (renameProgram f Q)) := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp (h hi) with pin | old
  · subst i
    rw [hf]
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    rw [renameProgram_support]
    exact Finset.mem_image_of_mem _ old

private theorem signBracketed_sub (d : Bool)
    (bracket early first pack old body unpack : Program) (tag payload : Finset Wire)
    (hBracket : wires bracket ⊆ insert signHost (tag ∪ payload))
    (hEarly : wires first ⊆ insert signHost (wires early))
    (hBody : wires body ⊆ insert signHost (wires old)) :
    wires (bracket ++ ordered d first (pack ++ body ++ unpack) ++ bracket) ⊆
      insert signHost ((wires (ordered d early (pack ++ old ++ unpack)) ∪ tag) ∪ payload) := by
  intro q used
  simp only [wires_append, ordered_wires, Finset.mem_union, Finset.mem_insert] at used ⊢
  rcases used with (left | (bare | ((packed | newBody) | unpacked))) | right
  · have hit := Finset.mem_insert.mp (hBracket left)
    simp only [Finset.mem_union] at hit
    tauto
  · have hit := Finset.mem_insert.mp (hEarly bare)
    tauto
  · tauto
  · have hit := Finset.mem_insert.mp (hBody newBody)
    tauto
  · tauto
  · have hit := Finset.mem_insert.mp (hBracket right)
    simp only [Finset.mem_union] at hit
    tauto

theorem group84Sign_sub (d : Bool) :
    wires (group84Sign d) ⊆ insert signHost
      ((wires (group84 d) ∪ tagSites.toFinset) ∪ signPayload.toFinset) :=
  signBracketed_sub d signBracket (ogroup d 1 9) (egroup d 1 9) packTag
    (renameProgram tagSwap (group84Body d)) (renameProgram tagSwap (group84SignBody d)) unpackTag
    tagSites.toFinset signPayload.toFinset signBracket_sub
    (egroup_sub d 1 9 (by decide) (by decide))
    (rename_sign_sub tagSwap tagSwap_signHost _ _ (signBody_sub d))

end ECDSAAdd.Entrant.StairPacket.WindowFieldCosts

namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical

open Arithmetic MappedCompressed RecordedQuantum StairPhysicalV3 StairRestSupport
open StairArchiveRelease StairArchiveNativeCut StairArchiveTen WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires group84SignBody group84Body rgroup

private def signPhysicalBool : Instr → Bool
  | .X _ => true
  | .CX c t => decide (c ≠ t)
  | .CCX a b t => decide (a ≠ t ∧ b ≠ t)
  | .measureX _ _ _ => true

theorem signBracket_physical : GatePhysical signBracket := by
  have check : signBracket.all signPhysicalBool = true := by decide +kernel
  intro i hi
  have h := List.all_eq_true.mp check i hi
  cases i <;> simp_all [signPhysicalBool, PhysicalInstr, ProperGate]

private theorem sten_physical (d : Bool) (j : Nat) (lo : 10 ≤ j) (hi : j ≤ 83)
    (pick : j ∈ [10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82]) :
    GatePhysical (sten j (!d)) := by
  have firstOK : GatePhysical (sfirst j (!d)) := by
    unfold sfirst
    exact spk_physical _ _ (by split <;> omega) (by split <;> omega)
  have lastOK : GatePhysical (ssecond j (!d)) := by
    unfold ssecond
    exact spk_physical _ _ (by split <;> omega) (by split <;> omega)
  simp only [sten, gatePhysical_append]
  exact ⟨(hook j pick _).1, firstOK, (hook j pick _).1, lastOK, (hook j pick _).1⟩

private theorem signBody_physical (d : Bool) : GatePhysical (group84SignBody d) := by
  have ord {A B : Program} (a : GatePhysical A) (b : GatePhysical B) :
      GatePhysical (ordered d A B) := by cases d <;> simp [ordered, gatePhysical_append, a, b]
  exact signBody_rel d (fun A _ => GatePhysical A)
    (fun a b => ord a b) (fun j pick lo hi => sten_physical d j lo hi pick)
    (fun j n lo hi => (ot_rgroup_sound d j n lo hi).1)

theorem group84Sign_ok (d : Bool) : Sound (group84Sign d) := by
  refine ⟨?_, ?_⟩
  · have hbody := gatePhysical_rename _ tagSwap.injective _ (signBody_physical d)
    have hnl := egroup_physical d 1 9 (by decide) (by decide)
    have hp := packTag_sound.1
    have hu := unpackTag_sound.1
    cases d <;> simp only [group84Sign, ordered, Bool.false_eq_true, if_false, if_true,
      gatePhysical_append, hbody, hp, hu, hnl, signBracket_physical, and_self]
  · intro q hq
    rcases Finset.mem_insert.mp (group84Sign_sub d hq) with eq | mem
    · subst q; decide +kernel
    · rcases Finset.mem_union.mp mem with left | payload
      · rcases Finset.mem_union.mp left with old | tag
        · exact (group84_ok d).2 q old
        · exact of_decide_eq_true (List.all_eq_true.mp tagSites_inDom q (List.mem_toFinset.mp tag))
      · exact Or.inl (of_decide_eq_true
          (List.all_eq_true.mp signPayload_range q (List.mem_toFinset.mp payload)))

end ECDSAAdd.Entrant.StairPacket.WindowPhysical

namespace ECDSAAdd.Entrant.StairPacket.WindowSites

open Arithmetic MappedCompressed StairConcreteAssembly StairSiteAvoidance
open WindowFieldCosts
set_option maxRecDepth 18000
set_option maxHeartbeats 1600000
attribute [local irreducible] wires group84Sign group84

private theorem signPayload_fit (q : Wire) (hq : q ∈ signPayload) :
    Stair44OuterSites.fit (StairPlaceFast.outerPlaceB q) = true := by
  have band := signPayload_band q hq
  change (21 ≤ q ∧ q < 441) ∨ (1049 ≤ q ∧ q < 1301) ∨ (1645 ≤ q ∧ q < 1813) at band
  dsimp only [Wire] at *
  have good : StairSiteEasy.good39B (StairPlaceFast.outerPlaceB q) = true := by
    rcases band with ⟨lo, hi⟩ | ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact StairSiteEasy.kbTP1 q (by omega) (by omega)
    · exact StairSiteEasy.kbTP5 q (by omega) hi
    · rcases Nat.lt_or_ge q 1672 with h | h
      · exact StairSiteEasy.kbTP7 q (by omega) h
      · rcases Nat.lt_or_ge q 1673 with h' | h'
        · have e : (q : Nat) = 1672 := Nat.le_antisymm (Nat.le_of_lt_succ h') h
          subst q
          decide +kernel
        · rcases Nat.lt_or_ge q 1812 with h'' | h''
          · exact StairSiteEasy.kbTP8 q h' h''
          · have e : (q : Nat) = 1812 := Nat.le_antisymm (Nat.le_of_lt_succ hi) h''
            subst q
            decide +kernel
  have active : StairPlaceFast.outerPlaceB q ∉ Stair44PointMap.retired := by
    intro h
    simp only [Stair44PointMap.retired, List.mem_cons, List.not_mem_nil, or_false] at h
    have placed : 4835 ≤ StairOuterPlacement.outerPlace q ∧ StairOuterPlacement.outerPlace q ≤ 4839 := by
      rw [StairPlaceFast.outerPlace_eqB]
      dsimp only [Wire] at h ⊢
      omega
    have e := outerPlace_in_4835_4839 q placed
    dsimp only [Wire] at *
    omega
  simp only [Stair44OuterSites.fit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨good, active⟩

private theorem group84Sign_wire_ok (d : Bool) (q : Wire) (hq : q ∈ wires (group84Sign d)) :
    TP q ∈ StairHoleSupport.recordArena ∧ TP q ∉ StairHoleSupport.oldHoles ∧ TP q ∉ reserved := by
  have fit_ok {w : Wire} (h : Stair44OuterSites.fit (StairPlaceFast.outerPlaceB w) = true) :
      TP w ∈ StairHoleSupport.recordArena ∧ TP w ∉ StairHoleSupport.oldHoles ∧ TP w ∉ reserved := by
    rw [← StairPlaceFast.outerPlace_eqB] at h
    exact singleton_ok h
  rcases Finset.mem_insert.mp (group84Sign_sub d hq) with pin | h
  · subst q
    exact fit_ok (by decide +kernel)
  · rcases Finset.mem_union.mp h with h | payload
    · rcases Finset.mem_union.mp h with old | tag
      · have ok := group84_ok d
        exact ⟨(ok.1 q old).1, (ok.1 q old).2, ok.2 q old⟩
      · exact fit_ok (List.all_eq_true.mp tagSites_fit q (List.mem_toFinset.mp tag))
    · exact fit_ok (signPayload_fit q (List.mem_toFinset.mp payload))

theorem group84Sign_ok (d : Bool) : PieceOK reserved TP (group84Sign d) :=
  ⟨fun q hq => ⟨(group84Sign_wire_ok d q hq).1, (group84Sign_wire_ok d q hq).2.1⟩,
    fun q hq => (group84Sign_wire_ok d q hq).2.2⟩

end ECDSAAdd.Entrant.StairPacket.WindowSites


namespace ECDSAAdd.Entrant.StairPacket.WindowPhysical
open Arithmetic MappedCompressed Baselines StairPhysicalV3 StairRestSupport StairConcreteAssembly
variable {p : StairSchedule.StairPrimitives}
set_option maxRecDepth 14000
set_option maxHeartbeats 1200000
private theorem callerDomain_inDom {q : Wire} (h : q ∈ StairSemanticFinal.callerDomain) : InDom q := by
  rw [StairSemanticFinal.callerDomain, List.mem_toFinset, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only [StairSemanticFinal.callerIndices, List.mem_append, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  unfold InDom InDomN MappedCompressed.base
  rcases hi with h1 | h2 | h3 | h4 | h5
  · exact Or.inl ⟨by omega, by omega⟩
  · subst h2; exact Or.inr (by decide)
  · subst h3; exact Or.inr (by decide)
  · subst h4; exact Or.inr (by decide)
  · subst h5; exact Or.inr (by decide)

private theorem oddSound1542 (divide : Bool) (d f c : Nat) (hd : d ≤ 44) (hfc : f + c ≤ 102) :
    Sound (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 divide d f c) :=
  ⟨OddFullPass.P1LifeLoan.hostedGroup_physical OddFullPass.P1LifeLoan.hostPlan1542 divide d f c hfc,
   fun _ hq => callerDomain_inDom (OddFullPass.P1LifeLoan.hostedGroup_wires_sub_1542 divide d f c hd hfc hq)⟩

theorem sound_entryTailPrefix (_H : LoanHyp) (P : PrimitiveSlots p) (_hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryTailPrefix p) := by
  have g0 := group84Sign_ok true
  have g14 := oddSound1542 true 14 85 5 (by decide) (by decide)
  have g23 := oddSound1542 true 23 90 3 (by decide) (by decide)
  have g31 := oddSound1542 true 31 93 3 (by decide) (by decide)
  have g37 := oddSound1542 true 37 96 2 (by decide) (by decide)
  have g42 := oddSound1542 true 42 98 2 (by decide) (by decide)
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

theorem sound_exitHeadSuffix (_H : LoanHyp) (P : PrimitiveSlots p) (_hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitHeadSuffix p) := by
  have g0 := group84Sign_ok false
  let Pc := StairPhysicalV3.primitiveSlots_v3 StairPhysicalV3.primitiveChecks
  have cut0 := PackCutOddExit.cutRow0_sound
    (oddSound1542 false 14 85 5 (by decide) (by decide))
    (sound_reverseSegment Pc 87 62 425 450 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut1 := PackCutOddExit.cutRow1_sound
    (oddSound1542 false 23 90 3 (by decide) (by decide))
    (sound_reverseSegment Pc 62 47 450 465 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut2 := PackCutOddExit.cutRow2_sound
    (oddSound1542 false 31 93 3 (by decide) (by decide))
    (sound_reverseSegment Pc 47 32 465 480 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut3 := PackCutOddExit.cutRow3_sound
    (oddSound1542 false 37 96 2 (by decide) (by decide))
    (sound_reverseSegment Pc 32 22 480 490 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega))
  have cut4 := PackCutOddExit.cutRow4_sound
    (oddSound1542 false 42 98 2 (by decide) (by decide))
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

attribute [local irreducible] ECDSAAdd.wires OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan
  OddFullPass.InverseTailCOdd.endPacket760OddLoan44 CompareDecoder.BoundaryLoan.endPacket760DivLoan
  StairEndpointLoan44.endPacket760Loan44 in
theorem sound_entryFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.entryFieldHosted p) := by
  have first := sound_rebindMany _ _ exclusiveRoles_indom (hs.firstPacket true)
    (sound_firstPacketOdd true)
  have pre : Sound (WindowCallerCosts.entryLowPrefix p) := by
    unfold WindowCallerCosts.entryLowPrefix
    exact sound_append (sound_append (sound_append first sound_clearProgram)
      (sound_borrow (sound_entryTailPrefix H P hs))) sound_unprefix
  have tail : Sound (OddFullPass.P1LifeLoan.entryTailSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    unfold OddFullPass.P1LifeLoan.entryTailSuffixOdd
    have hdiv : Sound (renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan) := by
      refine ⟨gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
        OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_physical, ?_⟩
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      have hmem : OB5.sig 511 y ∈ wires (renameProgram (OB5.sig 511) CompareDecoder.BoundaryLoan.endPacket760DivLoan) := by
        rw [renameProgram_support]
        exact Finset.mem_image.mpr ⟨y, OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_wires_sub hy, rfl⟩
      exact (sound_sig 511 (by omega) B.divEndpoint).good _ hmem
    have hcan : Sound OddFullPass.HalfConvertOdd.canon760OddLoan :=
      ⟨OddFullPass.HalfConvertOdd.canon760OddLoan_physical,
       fun q hq => (Finset.mem_union.mp (OddFullPass.HalfConvertOdd.canon760OddLoan_wires_sub hq)).elim
         (B.canon.good q) (sound_copyN.good q)⟩
    exact sound_append (sound_append (sound_append
      (oddSound1542 true 44 100 2 (by decide) (by decide)) hdiv) sound_copyN) hcan
  have suf : Sound (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    unfold OddFullPass.P1LifeLoan.entryLowSuffixOdd
    exact sound_append (sound_append sound_clearProgram (sound_borrow tail)) sound_unprefix
  unfold WindowCallerCosts.entryFieldHosted
  exact sound_append (sound_append (sound_append (sound_append (sound_append
    (sound_fieldRename pre) sound_paritySetup) sound_hostedX)
    (sound_fieldRename suf)) sound_hostedX) sound_paritySetup

attribute [local irreducible] ECDSAAdd.wires OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan
  OddFullPass.InverseTailCOdd.endPacket760OddLoan44 CompareDecoder.BoundaryLoan.endPacket760DivLoan
  StairEndpointLoan44.endPacket760Loan44 in
theorem sound_exitFieldHosted (H : LoanHyp) (P : PrimitiveSlots p) (B : BoundarySlots)
    (hs : HostSlots hostPlan) :
    Sound (WindowCallerCosts.exitFieldHosted p) := by
  have head : Sound (OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
    unfold OddFullPass.P1LifeLoan.exitHeadPrefixOdd
    have hcen : Sound OddFullPass.HalfConvertOdd.center760OddLoan :=
      ⟨OddFullPass.HalfConvertOdd.center760OddLoan_physical,
       fun q hq => (Finset.mem_union.mp (OddFullPass.HalfConvertOdd.center760OddLoan_wires_sub hq)).elim
         (B.center.good q) (sound_copyN.good q)⟩
    have hmul : Sound (renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44) := by
      refine ⟨gatePhysical_rename _ (OB5.sig_injective 511 (by decide)) _
        OddFullPass.InverseTailCOdd.endPacket760OddLoan44_physical, ?_⟩
      intro q hq
      rw [renameProgram_support] at hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
      have hmem : OB5.sig 511 y ∈ wires (renameProgram (OB5.sig 511) (StairEndpointLoan44.endPacket760Loan44 false)) := by
        rw [renameProgram_support]
        exact Finset.mem_image.mpr ⟨y, OddFullPass.InverseTailCOdd.endPacket760OddLoan44_wires_sub hy, rfl⟩
      exact (sound_sig 511 (by omega) B.multEndpoint).good _ hmem
    exact sound_append (sound_append (sound_append hcen sound_copyN) hmul)
      (oddSound1542 false 44 100 2 (by decide) (by decide))
  have pre : Sound (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
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
attribute [local irreducible] wires renameProgram Shadow20.MergeCut.forward Shadow20.MergeCut.reverse
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
    (new : GoodWindow (Shadow20.MergeCut.forward d)) :
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
    (new : GoodWindow (Shadow20.MergeCut.reverse d)) :
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

theorem firstDom (q : Wire) (h : InDom q) : InDom (first q) := by
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

theorem fw (d : Bool) (tail n : Nat) (hn : 15+(405+tail)=n)
    (ref_ : Sound (Rolling1588TickGap.forward d 1 n))
    (p : GatePhysical (Shadow20.MergeCut.forward d)) : Sound (WindowWalkCosts.forward d tail) := by
  subst n
  rw [forward_append d 15 1 (405+tail)] at ref_
  obtain ⟨early,late⟩ := parts ref_
  change Sound (Rolling1588TickGap.forward d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,forward_append d 29 16 (376+tail)] at late
  obtain ⟨pre,ms⟩ := parts late
  change Sound (Rolling1588TickGap.forward d 45 (376+tail)) at ms
  rw [forward_append d 376 45 tail] at ms
  have patch : Sound (Shadow20.MergeCut.forward d) := ⟨p,dom (PartialSites.forwardMixed_domain d)⟩
  have last : Sound (Rolling1588TickGap.forward d 421 tail) := (parts ms).2
  exact sound_append (sound_rename _ first.injective firstDom early)
    (sound_rename _ rest.injective restDom (sound_append (sound_append pre patch) last))

theorem bw (d : Bool) (tail n : Nat) (hn : 15+(405+tail)=n)
    (ref_ : Sound (Rolling1588.reverse d 1 n))
    (p : GatePhysical (Shadow20.MergeCut.reverse d)) : Sound (WindowWalkCosts.backward d tail) := by
  subst n
  rw [reverse_append d 15 1 (405+tail)] at ref_
  obtain ⟨late,early⟩ := parts ref_
  change Sound (Rolling1588.reverse d 16 (405+tail)) at late
  rw [show 405+tail=29+(376+tail) by omega,reverse_append d 29 16 (376+tail)] at late
  obtain ⟨ms,pre⟩ := parts late
  change Sound (Rolling1588.reverse d 45 (376+tail)) at ms
  rw [reverse_append d 376 45 tail] at ms
  have patch : Sound (Shadow20.MergeCut.reverse d) := ⟨p,dom (PartialSites.reverseMixed_domain d)⟩
  have last : Sound (Rolling1588.reverse d 421 tail) := (parts ms).1
  exact sound_append (sound_rename _ rest.injective restDom (sound_append (sound_append last patch) pre))
    (sound_rename _ first.injective firstDom early)
theorem phase {P : Program} (h : Sound P) : GatePhysical (phasePlace P) :=
  rest_physical _ (sound_phaseHost h)

variable (ff : ∀d,GatePhysical (Shadow20.MergeCut.forward d)) (rr : ∀d,GatePhysical (Shadow20.MergeCut.reverse d))

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

private theorem callerIndices_lt_2428_chk :
    StairSemanticFinal.callerIndices.all (fun i => decide (base i < 2428)) = true := by
  decide +kernel

private theorem roles_736_740_chk :
    ([736, 737, 738, 739, 740] : List Wire).all (fun w => decide (w ∈ StairSchedule.exclusiveRoles)) = true := by
  decide

private theorem tpi_mem_tpList {x : Wire} (h : StairSiteEasy.TPI x) : x ∈ StairSiteEasy.tpList := by
  unfold StairSiteEasy.TPI at h
  simp only [StairSiteEasy.tpList, List.mem_append, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false]
  dsimp only [Wire] at *
  omega

private theorem pieceOK_of_tpi_avoids_roles {P : Program}
    (htpi : ∀ x ∈ wires P, StairSiteEasy.TPI x)
    (hav : ∀ r ∈ StairSchedule.exclusiveRoles, r ∉ wires P) :
    PieceOK reserved TP P := by
  have h39 := StairSiteEasy.ok39_of_tpi htpi
  refine ⟨h39.1, fun x hx bad => ?_⟩
  have hgood := StairSiteEasy.tpList_good x (tpi_mem_tpList (htpi x hx))
  have hnot39 := hgood.2.2
  unfold StairSiteEasy.Hole39 at hnot39
  rw [reserved, StairPhysicalLayout.physicalHoles_eq_nat] at bad
  simp only [StairPhysicalLayout.newHolesNat, List.mem_append, List.mem_range'_1] at bad
  have hrange : 4835 ≤ StairOuterPlacement.outerPlace x ∧ StairOuterPlacement.outerPlace x ≤ 4839 := by
    change 4835 ≤ TP x ∧ TP x ≤ 4839
    dsimp only [Wire] at *
    omega
  have hxeq := outerPlace_in_4835_4839 x hrange
  have hxm : x ∈ ([736, 737, 738, 739, 740] : List Wire) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    dsimp only [Wire] at *
    omega
  have hrole : x ∈ StairSchedule.exclusiveRoles :=
    decide_eq_true_eq.mp (List.all_eq_true.mp roles_736_740_chk x hxm)
  exact hav x hrole hx

private theorem hostPlan1542_nonrole :
    ([14, 23, 31, 37, 42, 44] : List Nat).all (fun d =>
      let hs := OddFullPass.P1LifeLoan.hostPlan1542.group true d 0 0
      let rs := StairSchedule.exclusiveRoles.drop d
      hs.all (fun h => decide (h ∉ StairSchedule.exclusiveRoles) && StairSiteEasy.k5tpiB h) &&
      decide (rs.length = hs.length) &&
      decide rs.Nodup && decide hs.Nodup &&
      rs.all (fun r => decide (r ∉ hs))) = true := by
  decide +kernel

private theorem tpList_mem_tpi {x : Wire} (h : x ∈ StairSiteEasy.tpList) : StairSiteEasy.TPI x := by
  simp only [StairSiteEasy.tpList, List.mem_append, List.mem_range'_1, List.mem_cons,
    List.not_mem_nil, or_false] at h
  unfold StairSiteEasy.TPI
  dsimp only [Wire] at *
  omega

private theorem hostedGroup1542_ok (divide : Bool) (d f c : Nat)
    (hsched : (d, f, c) ∈ ([(14, 85, 5), (23, 90, 3), (31, 93, 3), (37, 96, 2), (42, 98, 2), (44, 100, 2)] : List (Nat × Nat × Nat))) :
    PieceOK reserved TP (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 divide d f c) := by
  have hdm : d ∈ ([14, 23, 31, 37, 42, 44] : List Nat) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched ⊢
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp
  have hd : d ≤ 44 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hdm; omega
  have hf1 : 1 ≤ f := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
  have hfc : f + c ≤ 102 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> omega
  have hchk := List.all_eq_true.mp hostPlan1542_nonrole d hdm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem] at hchk
  obtain ⟨⟨⟨⟨hnr_h, hlen⟩, hnd_r⟩, hnd_h⟩, hdisj⟩ := hchk
  have hgrp : OddFullPass.P1LifeLoan.hostPlan1542.group divide d f c =
      OddFullPass.P1LifeLoan.hostPlan1542.group true d 0 0 := rfl
  have hfresh : ∀ q ∈ OddFullPass.P1LifeLoan.hostPlan1542.group divide d f c,
      q ∉ wires (StairSchedule.placedGroups StairConcrete.bestLoans divide d f c) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hsched
    rcases hsched with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact StairField13V3Fresh.hosts_fresh_group 62 (by decide) divide 14 85 5 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 47 (by decide) divide 23 90 3 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 32 (by decide) divide 31 93 3 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 22 (by decide) divide 37 96 2 (by decide) (by decide) (by decide)
    · exact StairField13V3Fresh.hosts_fresh_group 12 (by decide) divide 42 98 2 (by decide) (by decide) (by decide)
    · intro q hq; simp [OddFullPass.P1LifeLoan.hostPlan1542] at hq
  have hmem_props : ∀ x ∈ wires (OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 divide d f c),
      StairSiteEasy.TPI x ∧ x ∉ StairSchedule.exclusiveRoles := by
    intro x hx
    have hstd := OddFullPass.P1LifeLoan.hostedGroup_wires_sub OddFullPass.P1LifeLoan.hostPlan1542 divide d f c hd hx
    unfold StairHostsSchedule.hostedGroup at hstd
    rw [hgrp] at hstd hfresh
    rcases StairSiteEasy.rebind_mem _ _ _ hfresh (fun y hy => hdisj y hy) hnd_r hnd_h hlen.le x hstd with hh | ⟨hP, hnr⟩
    · exact ⟨StairSiteEasy.k5_tpiB _ (hnr_h x hh).2, (hnr_h x hh).1⟩
    · change x ∈ wires (renameProgram (OB5.sig 511) (StairGroups.groups divide d f c)) at hP
      rw [renameProgram_support] at hP
      obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp hP
      obtain ⟨j, hj1, hj2, hjw⟩ := StairSiteEasy.seq_mem divide (StairGroups.packet divide d) c f w hw
      unfold StairGroups.packet at hjw
      rw [renameProgram_support] at hjw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hjw
      have hjr : j ∈ List.range' 1 101 := List.mem_range'_1.mpr ⟨by omega, by omega⟩
      obtain ⟨nt, hr⟩ := StairSiteEasy.basePacket_tgt divide d j hjr hd z hz
      have hnr_all : x ∉ StairSchedule.exclusiveRoles := by
        intro hrole
        rw [← List.take_append_drop d StairSchedule.exclusiveRoles, List.mem_append] at hrole
        exact hrole.elim (fun ht => nt (by change OB5.sig 511 (shifted (Placement5.pi j) z) ∈ _; rw [hwq]; exact ht)) hnr
      rcases hr with hr_role | hr_tpi
      · exact absurd (by rw [← hwq]; exact hr_role) hnr_all
      · exact ⟨by rw [← hwq]; exact hr_tpi, hnr_all⟩
  exact pieceOK_of_tpi_avoids_roles (fun x hx => (hmem_props x hx).1) (fun r hr hmem => (hmem_props r hmem).2 hr)

private theorem callerDomain_lt_2428 {q : Wire} (h : q ∈ StairSemanticFinal.callerDomain) : q < 2428 := by
  rw [StairSemanticFinal.callerDomain, List.mem_toFinset, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact decide_eq_true_eq.mp (List.all_eq_true.mp callerIndices_lt_2428_chk i hi)

theorem pieceOK_sub {holes : List Wire} {f : Wire → Wire} {P Q : Program}
    (h : ∀ q ∈ wires P, q ∈ wires Q) (hq : PieceOK holes f Q) : PieceOK holes f P :=
  ⟨fun x hx => hq.1 x (h x hx), fun x hx => hq.2 x (h x hx)⟩

private theorem entryTailSuffixOdd_ok :
    PieceOK reserved TP (OddFullPass.P1LifeLoan.entryTailSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have hcopy_ok : PieceOK reserved TP HalfFieldOB5.copyN :=
    StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.copyN_all
  have hcopy_43 : PieceOK Stair44FieldSites.holes TP HalfFieldOB5.copyN :=
    ⟨hcopy_ok.1, fun x hx bad => hcopy_ok.2 x hx (Stair44FieldSites.hsub _ bad)⟩
  have hdom_all := OddFullPass.P1LifeLoan.entryTailSuffixOdd_caller
  unfold OddFullPass.P1LifeLoan.entryTailSuffixOdd at hdom_all ⊢
  refine (((hostedGroup1542_ok true 44 100 2 (by decide)).append ?_).append hcopy_ok).append ?_
  · apply upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [StairConcrete.bestLoans_divEndpoint, renameProgram_support]
        rw [renameProgram_support] at hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨y, OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_wires_sub hy, rfl⟩)
        Stair44FieldSites.endpointD)
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
    intro hmem
    rw [renameProgram_support] at hmem
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hmem
    have h720 : base 720 ∈ StairSchedule.exclusiveRoles := by decide +kernel
    have hyEq : y = base 720 := (StairField13V3Clean.sig_pre h720 y).mp hyeq
    subst hyEq
    have hsub_div := OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan_wires_sub hy
    unfold CompareDecoder.BoundaryLoan.endPacket760DivLoan at hsub_div
    rw [renameProgram_support] at hsub_div
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp hsub_div
    have ha720 : a = base 720 := by
      have hfix : Equiv.swap (base 760) (base 717) (base 720) = base 720 := by decide
      exact (Equiv.swap (base 760) (base 717)).injective (haeq.trans hfix.symm)
    subst ha720
    rw [renameProgram_support] at ha
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp ha
    have hb720 : b = base 720 := by
      have hfix : shifted Placement5.pi0 (base 720) = base 720 := by decide +kernel
      exact (shifted Placement5.pi0).injective (hbeq.trans hfix.symm)
    subst hb720
    rcases Finset.mem_union.mp (ControlLoan1589.loanWindow_support _ _ _ _ hb) with h | h
    · rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact absurd h (by decide)
    · obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp h
      have hz720 : z = base 720 := by
        have hfix : Equiv.swap (base 719) (base 510) (base 720) = base 720 := by decide
        exact (Equiv.swap (base 719) (base 510)).injective (hzeq.trans hfix.symm)
      subst hz720
      rw [wires_append, Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact StairSiteEasy.k5_loan_avoids (base 720) (by decide +kernel) hz
      · have hc := (InverseEndpointWires.pad_facts 507 (base 512)).2.2.2.1 hz
        rw [Finset.mem_singleton] at hc
        exact absurd hc (by decide)
  · exact upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [wires_append]
        exact OddFullPass.HalfConvertOdd.canon760OddLoan_wires_sub hq)
        (Stair44FieldSites.canon.append hcopy_43))
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
      OddFullPass.HalfConvertOdd.canon760OddLoan_avoids_720

private theorem exitHeadPrefixOdd_ok :
    PieceOK reserved TP (OddFullPass.P1LifeLoan.exitHeadPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have hcopy_ok : PieceOK reserved TP HalfFieldOB5.copyN :=
    StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.copyN_all
  have hcopy_43 : PieceOK Stair44FieldSites.holes TP HalfFieldOB5.copyN :=
    ⟨hcopy_ok.1, fun x hx bad => hcopy_ok.2 x hx (Stair44FieldSites.hsub _ bad)⟩
  have hdom_all := OddFullPass.P1LifeLoan.exitHeadPrefixOdd_caller
  unfold OddFullPass.P1LifeLoan.exitHeadPrefixOdd at hdom_all ⊢
  refine ((PieceOK.append ?_ hcopy_ok).append ?_).append
      (hostedGroup1542_ok false 44 100 2 (by decide))
  · exact upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [wires_append]
        exact OddFullPass.HalfConvertOdd.center760OddLoan_wires_sub hq)
        (Stair44FieldSites.center.append hcopy_43))
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
      OddFullPass.HalfConvertOdd.center760OddLoan_avoids_720
  · apply upgrade44_of_avoids_720
      (pieceOK_sub (fun q hq => by
        rw [StairHostsSchedule.hostedEndpoint, StairSchedule.placedEndPacket,
          show StairConcrete.bestLoans.endPacket false 68 = StairEndpointLoan44.endPacket760Loan44 false from by
            simp only [StairConcrete.bestLoans, StairConcrete.endPacket, Bool.false_eq_true, if_false, if_true],
          renameProgram_support]
        rw [renameProgram_support] at hq
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_image.mpr ⟨y, OddFullPass.InverseTailCOdd.endPacket760OddLoan44_wires_sub hy, rfl⟩)
        Stair44FieldSites.endpointM)
      (fun q hq => callerDomain_lt_2428 (hdom_all (by simp [wires_append, hq])))
    intro hmem
    rw [renameProgram_support] at hmem
    obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hmem
    have h720 : base 720 ∈ StairSchedule.exclusiveRoles := by decide +kernel
    have hyEq : y = base 720 := (StairField13V3Clean.sig_pre h720 y).mp hyeq
    subst hyEq
    exact StairEndpointLoan44.endPacket760Loan44_avoids (base 720) (by decide +kernel)
      (OddFullPass.InverseTailCOdd.endPacket760OddLoan44_wires_sub hy)

theorem entryField : PieceOK reserved KP
    (WindowCallerCosts.entryFieldHosted checkpointPrimitives) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have ps := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.paritySetup_all
  have hx := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.hostedX_all
  have pk := StairSiteAvoidance.packEnd_rows
  have fpOk : PieceOK reserved lowPlace (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf true) :=
    weaken (JointOdd1588.hostedFirstPacketOdd_pieceOK WindowCallerCosts.oddFirstHalf
      StairPhysicalInventory.physicalHoles (fun _ h => h) true
      (WindowCallerCosts.oddFirstHalf_support true))
  have htail : PieceOK reserved TP (WindowCallerCosts.entryTailPrefix checkpointPrimitives) := by
    unfold WindowCallerCosts.entryTailPrefix
    refine (((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
      ?_).append ?_).append ?_).append ?_).append ?_)
    · exact group84Sign_ok true
    · exact StairSiteAvoidance.forwardSegment_ok hsub 87 62 (by decide) (by decide) (by decide) pk.1
    · exact hostedGroup1542_ok true 14 85 5 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 62 47 (by decide) (by decide) (by decide) pk.2.1
    · exact hostedGroup1542_ok true 23 90 3 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 47 32 (by decide) (by decide) (by decide) pk.2.2.1
    · exact hostedGroup1542_ok true 31 93 3 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 32 22 (by decide) (by decide) (by decide) pk.2.2.2.1
    · exact hostedGroup1542_ok true 37 96 2 (by decide)
    · exact StairSiteAvoidance.forwardSegment_ok hsub 22 12 (by decide) (by decide) (by decide) pk.2.2.2.2
    · exact hostedGroup1542_ok true 42 98 2 (by decide)
    · exact StairSiteAvoidance.forwardLast_ok hsub
  unfold WindowCallerCosts.entryFieldHosted
  refine ((((PieceOK.append ?_ ps).append hx).append ?_).append hx).append ps
  · apply StairSiteAvoidance.ok_field
    unfold WindowCallerCosts.entryLowPrefix
    exact ((fpOk.append (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all)).append
      (StairSiteAvoidance.ok_borrow htail)).append (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)
  · apply StairSiteAvoidance.ok_field
    unfold OddFullPass.P1LifeLoan.entryLowSuffixOdd
    exact ((StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all).append
      (StairSiteAvoidance.ok_borrow entryTailSuffixOdd_ok)).append
      (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)

theorem exitField : PieceOK reserved KP
    (WindowCallerCosts.exitFieldHosted checkpointPrimitives) := by
  have hsub : ∀ x ∈ reserved, x ∈ StairPhysicalInventory.physicalHoles := fun _ h => h
  have ps := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.paritySetup_all
  have hx := StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.hostedX_all
  have up := StairSiteAvoidance.unpackEnd_rows
  have fpOk : PieceOK reserved lowPlace (JointOdd1588.hostedFirstPacketOdd WindowCallerCosts.oddFirstHalf false) :=
    weaken (JointOdd1588.hostedFirstPacketOdd_pieceOK WindowCallerCosts.oddFirstHalf
      StairPhysicalInventory.physicalHoles (fun _ h => h) false
      (WindowCallerCosts.oddFirstHalf_support false))
  have hrows : PieceOK reserved TP
      (StairSchedule.reverseLast checkpointPrimitives ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 42 98 2 ++ StairSchedule.reverseSegment checkpointPrimitives 22 12 490 500 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 37 96 2 ++ StairSchedule.reverseSegment checkpointPrimitives 32 22 480 490 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 31 93 3 ++ StairSchedule.reverseSegment checkpointPrimitives 47 32 465 480 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 23 90 3 ++ StairSchedule.reverseSegment checkpointPrimitives 62 47 450 465 ++
       OddFullPass.P1LifeLoan.hostedGroup OddFullPass.P1LifeLoan.hostPlan1542 false 14 85 5 ++ StairSchedule.reverseSegment checkpointPrimitives 87 62 425 450) := by
    refine ((((((((((PieceOK.append ?_ ?_).append ?_).append ?_).append ?_).append ?_).append ?_).append
      ?_).append ?_).append ?_).append ?_)
    · exact StairSiteAvoidance.reverseLast_ok hsub
    · exact hostedGroup1542_ok false 42 98 2 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 22 12 (by decide) (by decide) (by decide) (by decide) up.2.2.2.2
    · exact hostedGroup1542_ok false 37 96 2 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 32 22 (by decide) (by decide) (by decide) (by decide) up.2.2.2.1
    · exact hostedGroup1542_ok false 31 93 3 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 47 32 (by decide) (by decide) (by decide) (by decide) up.2.2.1
    · exact hostedGroup1542_ok false 23 90 3 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 62 47 (by decide) (by decide) (by decide) (by decide) up.2.1
    · exact hostedGroup1542_ok false 14 85 5 (by decide)
    · exact StairSiteAvoidance.reverseSegment_ok hsub 87 62 (by decide) (by decide) (by decide) (by decide) up.1
  have hhead : PieceOK reserved TP (WindowCallerCosts.exitHeadSuffix checkpointPrimitives) := by
    unfold WindowCallerCosts.exitHeadSuffix
    exact (pieceOK_sub (fun q hq => PackCutOddExit.cutRows_sub hq) hrows).append (group84Sign_ok false)
  unfold WindowCallerCosts.exitFieldHosted
  refine ((((ps.append hx).append ?_).append ps).append hx).append ?_
  · apply StairSiteAvoidance.ok_field
    unfold OddFullPass.P1LifeLoan.exitLowPrefixOdd
    exact ((StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all).append
      (StairSiteAvoidance.ok_borrow exitHeadPrefixOdd_ok)).append
      (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)
  · apply StairSiteAvoidance.ok_field
    unfold WindowCallerCosts.exitLowSuffix
    exact (((StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchClear_all).append
      (StairSiteAvoidance.ok_borrow hhead)).append
      (StairSiteAvoidance.ok_of_all hsub StairSiteAvoidance.scratchUnprefix_all)).append fpOk

private theorem entryFieldCut : PieceOK reserved KP WindowCallerCosts.entryFieldHostedCut :=
  pieceOK_sub (PackCutSub.wires_sub WindowCallerCosts.field_sublist) entryField

theorem phase {P : Program} (v : PieceOK reserved PP P) :
    PieceOK reserved UG (Stair44Outer.phasePlace P) := ok_kernel (ok_phase v)

theorem division (f : GoodWindow (Shadow20.MergeCut.forward true))
    (r : GoodWindow (Shadow20.MergeCut.reverse false)) :
    PieceOK reserved UG WindowCallerCosts.divide :=
  (((((phase (walkF true 4 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.pack)))).append
    (ok_kernel entryFieldCut)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.reverseTail)))).append
    (phase (walkR false 85 (by decide) r))).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.native)))

theorem multiplication (k : Nat) (f : GoodWindow (Shadow20.MergeCut.forward false))
    (r : GoodWindow (Shadow20.MergeCut.reverse true)) :
    PieceOK reserved UG (WindowCallerCosts.multiply k) :=
  (((((phase (walkF false 84 (by decide) f)).append (weaken (ok_kernel (ok_phase Stair44PhaseSites.forwardTail)))).append
    (ok_kernel exitField)).append (weaken (ok_kernel (ok_phase Stair44FirstRow.unpack)))).append
    (phase (walkR true 4 (by decide) r))).append (weaken (Stair44PhaseSites.exitX k))

theorem program_width (C : Point) (f : ∀d, GoodWindow (Shadow20.MergeCut.forward d))
    (r : ∀d,GoodWindow (Shadow20.MergeCut.reverse d)) :
    Challenge.qubits (WindowCallerCosts.program C) ≤ 1542 := by
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
  WindowPhysical.physical (fun d => (Shadow20.MergeCut.physical d).1) (fun d => Shadow20.MergeCut.rphysical d) C

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end

section

namespace ECDSAAdd.Entrant.StairPacket.WindowCallerCosts
open Secp256k1

theorem qubitBound (C : Point) : Challenge.qubits (program C) ≤ 1542 :=
  WindowSites.program_width C PartialSites.forwardMixed_fits PartialSites.reverseMixed_fits

end ECDSAAdd.Entrant.StairPacket.WindowCallerCosts

end




section


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
private theorem pass43 : (List.range' 1 84).all (allowed 43)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h43_1,h43_8⟩,h43_15⟩,h43_22⟩,h43_29⟩,h43_36⟩,h43_43⟩,h43_50⟩,h43_57⟩,h43_64⟩,h43_71⟩,h43_78⟩
private theorem pass35 : (List.range' 1 84).all (allowed 35)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h35_1,h35_8⟩,h35_15⟩,h35_22⟩,h35_29⟩,h35_36⟩,h35_43⟩,h35_50⟩,h35_57⟩,h35_64⟩,h35_71⟩,h35_78⟩
private theorem pass39 : (List.range' 1 84).all (allowed 39)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h39_1,h39_8⟩,h39_15⟩,h39_22⟩,h39_29⟩,h39_36⟩,h39_43⟩,h39_50⟩,h39_57⟩,h39_64⟩,h39_71⟩,h39_78⟩
private theorem pass47 : (List.range' 1 84).all (allowed 47)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h47_1,h47_8⟩,h47_15⟩,h47_22⟩,h47_29⟩,h47_36⟩,h47_43⟩,h47_50⟩,h47_57⟩,h47_64⟩,h47_71⟩,h47_78⟩
private theorem pass51 : (List.range' 1 84).all (allowed 51)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h51_1,h51_8⟩,h51_15⟩,h51_22⟩,h51_29⟩,h51_36⟩,h51_43⟩,h51_50⟩,h51_57⟩,h51_64⟩,h51_71⟩,h51_78⟩
private theorem pass59 : (List.range' 1 84).all (allowed 59)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h59_1,h59_8⟩,h59_15⟩,h59_22⟩,h59_29⟩,h59_36⟩,h59_43⟩,h59_50⟩,h59_57⟩,h59_64⟩,h59_71⟩,h59_78⟩
private theorem pass63 : (List.range' 1 84).all (allowed 63)=true := by
  rw [splitRange]
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h63_1,h63_8⟩,h63_15⟩,h63_22⟩,h63_29⟩,h63_36⟩,h63_43⟩,h63_50⟩,h63_57⟩,h63_64⟩,h63_71⟩,h63_78⟩
theorem pass (h : Nat) (hm : h ∈ banks) : (List.range' 1 84).all (allowed h) = true := by
  simp only [banks,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact pass10
  · exact pass13
  · exact pass16
  · exact pass19
  · exact pass22
  · exact pass25
  · exact pass28
  · exact pass31
  · exact pass35
  · exact pass39
  · exact pass43
  · exact pass47
  · exact pass51
  · exact pass55
  · exact pass59
  · exact pass63
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

theorem maskOf_testBit (l : List Wire) (q : Wire) : (maskOf l).testBit q = l.contains q := by
  rw [maskOf, testBit_maskFold, Nat.zero_testBit, Bool.false_or]

theorem not_mem_of_maskOf {l : List Wire} {q : Wire} (h : (maskOf l).testBit q = false) : q ∉ l :=
  fun m => by rw [testBit_maskOf m] at h; exact Bool.noConfusion h

/-- Banks `j ≠ h`: no slot of `h` is a field port of `j` (one `&&&` of two masks per pair). -/
private def distinct (j h : Nat) := j=h ||
  ((maskOf (slots h)) &&& (maskOf ((List.range 121).map (fieldPort j))) == 0)
private def commonFieldTail : Nat := maskOf ((List.range' 16 105).map (fieldPort 0))

private theorem maskOf_append (a b : List Wire) : maskOf (a ++ b) = maskOf a ||| maskOf b := by
  apply Nat.eq_of_testBit_eq
  intro q
  simp only [maskOf, testBit_maskFold, Nat.zero_testBit, Bool.false_or,
    Nat.testBit_or, List.contains_append]

private theorem field_mask_split (j : Nat) :
    maskOf ((List.range 121).map (fieldPort j)) = maskOf (slots j) ||| commonFieldTail := by
  have ranges : List.range 121 = List.range 16 ++ List.range' 16 105 := by decide +kernel
  have tail : (List.range' 16 105).map (fieldPort j) = (List.range' 16 105).map (fieldPort 0) := by
    apply List.map_congr_left
    intro q hq
    exact fieldPort_tail j q (List.mem_range'_1.mp hq).1
  unfold slots commonFieldTail
  rw [ranges, List.map_append, maskOf_append, tail]

private theorem prefix_masks_separate : banks.all (fun j => banks.all (fun h =>
    j = h || ((maskOf (slots h)) &&& (maskOf (slots j)) == 0))) = true := by
  decide +kernel

private theorem tail_mask_separate : banks.all (fun h =>
    (maskOf (slots h) &&& commonFieldTail) == 0) = true := by
  decide +kernel

private theorem distinct_ok : banks.all (fun j=>banks.all (distinct j))=true := by
  apply List.all_eq_true.mpr
  intro j hj
  apply List.all_eq_true.mpr
  intro h hh
  by_cases same : j = h
  · simp only [distinct, decide_eq_true same, Bool.true_or]
  · have headClear := List.all_eq_true.mp (List.all_eq_true.mp prefix_masks_separate j hj) h hh
    simp only [decide_eq_false same, Bool.false_or, beq_iff_eq] at headClear
    have tail := beq_iff_eq.mp (List.all_eq_true.mp tail_mask_separate h hh)
    simp only [distinct, decide_eq_false same, Bool.false_or, beq_iff_eq, field_mask_split,
      Nat.and_or_distrib_left, headClear, tail, Nat.or_zero]

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
def bankIds : Finset Nat := {10,13,16,19,22,25,28,31,35,39,43,47,51,55,59,63,67,70,73,76,79,82}
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

private theorem run_on_bank_complement (P : Program) (B : Finset Wire) (m : List Bool) (a r : State)
    (phase : a.phase = r.phase) (rest : ∀ q ∉ B, a.basis q = r.basis q) (safe : avoids P B) :
    (run P m a).phase = (run P m r).phase ∧ ∀ q ∉ B, (run P m a).basis q = (run P m r).basis q := by
  have same : mask B a r = a := by
    apply congrArg₂ State.mk phase.symm
    funext q
    by_cases member : q ∈ B
    · exact if_pos member
    · exact (if_neg member).trans (rest q member).symm
  have outcome := mask_run P B m a r safe
  rw [same] at outcome
  have matched := congrArg State.phase outcome
  refine ⟨matched, ?_⟩
  intro q outside
  exact (congrArg (fun s : State => s.basis q) outcome).trans (if_neg outside)

theorem plain (P : Program) (rows : Nat→Nat) (code : Nat→Cols) (m : List Bool) (a r : State)
    (h : Fits rows code a r) (safe : avoids P allBanks) : Fits rows code (run P m a) (run P m r) := by
  obtain ⟨phase, outside⟩ := run_on_bank_complement P allBanks m a r h.phase h.outside safe
  refine ⟨phase, outside, ?_⟩
  intro j hj q hq
  have member : fieldPort j q ∈ allBanks := Finset.mem_biUnion.mpr
    ⟨j, hj, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
  exact (run_preserves_outside P m a _ (safe _ member)).trans (h.bytes j hj q hq)

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
def nativeRanges (j n : Nat) := (j=1 ∧ n=9) ∨ (j=12 ∧ n=1) ∨ (j=15 ∧ n=1) ∨ (j=18 ∧ n=1) ∨ (j=21 ∧ n=1) ∨ (j=24 ∧ n=1) ∨ (j=27 ∧ n=1) ∨ (j=30 ∧ n=1) ∨ (j=33 ∧ n=2) ∨ (j=37 ∧ n=2) ∨ (j=41 ∧ n=2) ∨ (j=45 ∧ n=2) ∨ (j=49 ∧ n=2) ∨ (j=53 ∧ n=2) ∨ (j=57 ∧ n=2) ∨ (j=61 ∧ n=2) ∨ (j=65 ∧ n=2) ∨ (j=69 ∧ n=1) ∨ (j=72 ∧ n=1) ∨ (j=75 ∧ n=1) ∨ (j=78 ∧ n=1) ∨ (j=81 ∧ n=1) ∨ (j=84 ∧ n=1)
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
theorem geometry {j : Nat} (h : j∈bankIds) : j∈ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFieldBanks.mixedBankList ∧ j∈List.range' 1 83 := by
  simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
theorem apart {j : Nat} (hj : j∈bankIds) : ∀ q∈inside j, q∉others j := by
  intro q hi ho
  obtain ⟨k,hk,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,kid⟩ := Finset.mem_erase.mp hk
  exact WindowBankCheck.separate j k (memberList hj) (memberList kid) ne.symm q hi mem
theorem native_safe (j k : Nat) (hj : j∈bankIds) (which : k=j ∨ k=j+1) (d : Bool) :
    avoids (packet d k) (others j) := by
  intro q ho used
  obtain ⟨h,hm,mem⟩ := Finset.mem_biUnion.mp ho
  obtain ⟨ne,hid⟩ := Finset.mem_erase.mp hm
  apply WindowBankCheck.packet_free h k (memberList hid) _ _ _ d q mem used
  all_goals simp only [bankIds,Finset.mem_insert,Finset.mem_singleton] at hj hid
  · apply List.mem_range'_1.mpr; omega
  all_goals omega
theorem hook_safe (j : Nat) (hj : j∈bankIds) (s : Stage) :
    avoids (fieldHook j s) (others j) := by
  intro q ho used
  rw [fieldHook,renameProgram_support] at used
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp used
  exact apart hj _ (Finset.mem_image.mpr ⟨i,sub s hi,rfl⟩) ho
theorem append_safe {P Q : Program} {W : Finset Wire} (p : avoids P W) (q : avoids Q W) :
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
  | true => [.native 1 9,.paired 10,.native 12 1,.paired 13,.native 15 1,.paired 16,.native 18 1,.paired 19,.native 21 1,.paired 22,.native 24 1,.paired 25,.native 27 1,.paired 28,.native 30 1,.paired 31,.native 33 2,.paired 35,.native 37 2,.paired 39,.native 41 2,.paired 43,.native 45 2,.paired 47,.native 49 2,.paired 51,.native 53 2,.paired 55,.native 57 2,.paired 59,.native 61 2,.paired 63,.native 65 2,.paired 67,.native 69 1,.paired 70,.native 72 1,.paired 73,.native 75 1,.paired 76,.native 78 1,.paired 79,.native 81 1,.paired 82,.native 84 1]
  | false => [.native 84 1,.paired 82,.native 81 1,.paired 79,.native 78 1,.paired 76,.native 75 1,.paired 73,.native 72 1,.paired 70,.native 69 1,.paired 67,.native 65 2,.paired 63,.native 61 2,.paired 59,.native 57 2,.paired 55,.native 53 2,.paired 51,.native 49 2,.paired 47,.native 45 2,.paired 43,.native 41 2,.paired 39,.native 37 2,.paired 35,.native 33 2,.paired 31,.native 30 1,.paired 28,.native 27 1,.paired 25,.native 24 1,.paired 22,.native 21 1,.paired 19,.native 18 1,.paired 16,.native 15 1,.paired 13,.native 12 1,.paired 10,.native 1 9]
def initialCode (d : Bool) : Nat→Cols := fun _=>inputCols (enter (!d))
theorem valid_plan (d : Bool) : valid d (plan d) (initialCode d) := by
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

theorem cancel (e : Equiv.Perm Wire) {s t : State}
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
theorem shape' (d : Bool) (p : Nat→Program) : PacketSequence.program d p 1 84 =
  let seq := PacketSequence.program d p
  if d then seq 1 9 ++ ((p 10 ++ p 11) ++ (seq 12 1 ++ ((p 13 ++ p 14) ++ (seq 15 1 ++ ((p 16 ++ p 17) ++ (seq 18 1 ++ ((p 19 ++ p 20) ++ (seq 21 1 ++ ((p 22 ++ p 23) ++ (seq 24 1 ++ ((p 25 ++ p 26) ++ (seq 27 1 ++ ((p 28 ++ p 29) ++ (seq 30 1 ++ ((p 31 ++ p 32) ++ (seq 33 2 ++ ((p 35 ++ p 36) ++ (seq 37 2 ++ ((p 39 ++ p 40) ++ (seq 41 2 ++ ((p 43 ++ p 44) ++ (seq 45 2 ++ ((p 47 ++ p 48) ++ (seq 49 2 ++ ((p 51 ++ p 52) ++ (seq 53 2 ++ ((p 55 ++ p 56) ++ (seq 57 2 ++ ((p 59 ++ p 60) ++ (seq 61 2 ++ ((p 63 ++ p 64) ++ (seq 65 2 ++ ((p 67 ++ p 68) ++ (seq 69 1 ++ ((p 70 ++ p 71) ++ (seq 72 1 ++ ((p 73 ++ p 74) ++ (seq 75 1 ++ ((p 76 ++ p 77) ++ (seq 78 1 ++ ((p 79 ++ p 80) ++ (seq 81 1 ++ ((p 82 ++ p 83) ++ (seq 84 1 ++ []))))))))))))))))))))))))))))))))))))))))))))
  else seq 84 1 ++ ((p 83 ++ p 82) ++ (seq 81 1 ++ ((p 80 ++ p 79) ++ (seq 78 1 ++ ((p 77 ++ p 76) ++ (seq 75 1 ++ ((p 74 ++ p 73) ++ (seq 72 1 ++ ((p 71 ++ p 70) ++ (seq 69 1 ++ ((p 68 ++ p 67) ++ (seq 65 2 ++ ((p 64 ++ p 63) ++ (seq 61 2 ++ ((p 60 ++ p 59) ++ (seq 57 2 ++ ((p 56 ++ p 55) ++ (seq 53 2 ++ ((p 52 ++ p 51) ++ (seq 49 2 ++ ((p 48 ++ p 47) ++ (seq 45 2 ++ ((p 44 ++ p 43) ++ (seq 41 2 ++ ((p 40 ++ p 39) ++ (seq 37 2 ++ ((p 36 ++ p 35) ++ (seq 33 2 ++ ((p 32 ++ p 31) ++ (seq 30 1 ++ ((p 29 ++ p 28) ++ (seq 27 1 ++ ((p 26 ++ p 25) ++ (seq 24 1 ++ ((p 23 ++ p 22) ++ (seq 21 1 ++ ((p 20 ++ p 19) ++ (seq 18 1 ++ ((p 17 ++ p 16) ++ (seq 15 1 ++ ((p 14 ++ p 13) ++ (seq 12 1 ++ ((p 11 ++ p 10) ++ (seq 1 9 ++ [])))))))))))))))))))))))))))))))))))))))))))) := by
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
def other (j : Nat) := if j=43 then 47 else 43
def port (j q : Nat) : Wire :=
  if q<16 then site j q else if q=16 then FrontierEntry1591Field.host else site (other j) (q-17)
def bankCorrection (j : Nat) := renameProgram (port j) region
def correction := bankCorrection 10 ++ (bankCorrection 13 ++ (bankCorrection 16 ++ (bankCorrection 19 ++ (bankCorrection 22 ++ (bankCorrection 25 ++ (bankCorrection 28 ++ (bankCorrection 31 ++ (bankCorrection 35 ++ (bankCorrection 39 ++ (bankCorrection 43 ++ (bankCorrection 47 ++ (bankCorrection 51 ++ (bankCorrection 55 ++ (bankCorrection 59 ++ (bankCorrection 63 ++ (bankCorrection 67 ++ (bankCorrection 70 ++ (bankCorrection 73 ++ (bankCorrection 76 ++ (bankCorrection 79 ++ (bankCorrection 82)))))))))))))))))))))
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
theorem cols (hi:Bool):∀q:Fin 10,get (chronological hi) q=rawCol ((if hi then 10 else 0)+q.val):=by
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
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

def exitFieldHosted (p : StairSchedule.StairPrimitives)
     : Program :=
  WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.exitLowPrefixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (WindowCallerCosts.exitLowSuffix p)

/-- `exitHeadPrefixOdd` without `center760OddLoan`: the register already holds `oddWord (Y / 2)`. -/
def exitHeadPrefixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  HalfFieldOB5.copyN ++ renameProgram (OB5.sig 511) OddFullPass.InverseTailCOdd.endPacket760OddLoan44 ++
    OddFullPass.P1LifeLoan.hostedGroup h false 44 100 2

def exitLowPrefixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  FourScratchWindow.clearProgram ++ renameProgram Prefix1590.borrow (exitHeadPrefixOddNC h) ++
    FourScratchWindow.unprefix

def exitFieldHostedNC (p : StairSchedule.StairPrimitives) : Program :=
  WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (exitLowPrefixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (WindowCallerCosts.exitLowSuffix p)

def entryFieldHostedCut : Program :=
  StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (OddFullPass.P1LifeLoan.entryLowSuffixOdd OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

/-- `OddFullPass.P1LifeLoan.entryTailSuffixOdd` without the trailing `canon760OddLoan`: the
    division leaves `λ` as `oddWord (λ / 2)` on its numerator register. -/
def entryTailSuffixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  OddFullPass.P1LifeLoan.hostedGroup h true 44 100 2 ++
    renameProgram (OB5.sig 511) OddFullPass.CompareDecoderOdd.endPacket760DivOddLoan ++
    HalfFieldOB5.copyN

def entryLowSuffixOddNC (h : StairHostsSchedule.HostPlan) : Program :=
  FourScratchWindow.clearProgram ++
    renameProgram Prefix1590.borrow (entryTailSuffixOddNC h) ++
    FourScratchWindow.unprefix

def entryFieldHostedCutNC : Program :=
  StairSchedule.fieldRename WindowCallerCosts.entryLowPrefixCut ++
    WindowFieldParity.setup ++ StairSchedule.hostedX ++
    StairSchedule.fieldRename (entryLowSuffixOddNC OddFullPass.P1LifeLoan.hostPlan1542) ++
    StairSchedule.hostedX ++ WindowFieldParity.setup

theorem entryTailSuffixOdd_eqNC (h : StairHostsSchedule.HostPlan) :
    OddFullPass.P1LifeLoan.entryTailSuffixOdd h =
      entryTailSuffixOddNC h ++ OddFullPass.HalfConvertOdd.canon760OddLoan := rfl

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

def divideNC : Program :=
  phasePlace (WindowWalkCosts.forward true 4) ++ phasePlace checkpointPrimitives.firstPack ++
    kernelPlace entryFieldHostedCutNC ++
    phasePlace reverseEnd ++ phasePlace (WindowWalkCosts.backward false 85) ++
    phasePlace (renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base))

def multiply (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 84) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHosted checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 4) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

/-- `multiply` with the multiplication kernel that reads its input in odd-word form. -/
def multiplyNC (k : Nat) : Program :=
  phasePlace (WindowWalkCosts.forward false 84) ++ phasePlace forwardEnd ++
    kernelPlace (exitFieldHostedNC checkpointPrimitives) ++
    phasePlace checkpointPrimitives.firstUnpack ++ phasePlace (WindowWalkCosts.backward true 4) ++
    Stair44PointMap.switchX (phasePlace (ParityXExitInverse23Kernel.x1N k))

/-- The square reading `λ` in odd-word form (`SquareOdd.program`). -/
def squareNC (k : Fp) : Program := SquareOdd.program k

/-- `generic` with both field converters deleted: `divideNC`, `squareNC`, `multiplyNC`. -/
def genericNC (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (EntryFuseOdd.entryYAllOdd layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divideNC ++ squareNC (ReflectionE1.correction cx) ++ multiplyNC cx.val ++
    Stair44PointMap.encodeY (EntryFuseOdd.exitYAllOdd layout cy)

/-- The circuit: both field converters deleted (`divideNC`, `multiplyNC`) and the square reading
    the slope in odd-word form (`squareNC`). -/
def generic (cx cy : Fp) : Program := genericNC cx cy

def borrowGenericNC (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (genericNC cx cy))

def finiteNC (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGenericNC cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def programNC (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finiteNC (.some hc) cx cy)

/-- The circuit before the switch (with the two field converters), kept for the cost comparison. -/
def genericOld (cx cy : Fp) : Program :=
  Stair44PointMap.encodeY (EntryFuseOdd.entryYAllOdd layout (-cy)) ++
    Stair44PointMap.switchX (FlagEntry.entryXNew layout (FlagEntry.pkW layout) (-cx)) ++
    divide ++ Stair44Square.program (ReflectionE1.correction cx) ++ multiply cx.val ++
    Stair44PointMap.encodeY (EntryFuseOdd.exitYAllOdd layout cy)

def borrowGenericOld (cx cy : Fp) := renameProgram (Equiv.swap layout.doubleSelect layout.control)
  (renameProgram (FlagTop.rho layout) (genericOld cx cy))

def finiteOld (C : Point) (cx cy : Fp) : Program :=
  Stair44PointMap.encode (FlagTop.stageNew layout C (FlagEntry.pkW layout) ++
    AboveFieldPointDevelop.encode C ++ AboveFieldPointDevelop.eraseB) ++
    borrowGenericOld cx cy ++ Stair44PointMap.encode (AboveFieldPointDevelop.loadB ++
      AboveFieldPointDevelop.decode C ++ ControlPointEncodingDevelop.borrowOut C)

def programOld (C : Point) : Program := match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy hc =>
      renameProgram (Wrapper5.U layout) (finiteOld (.some hc) cx cy)

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
