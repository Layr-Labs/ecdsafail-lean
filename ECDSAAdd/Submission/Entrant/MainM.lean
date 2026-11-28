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

private theorem restR_suffix (P S : Program) (n : Nat) (hS : S.length = 3 * n) :
    restR (P ++ S) n = restR S n := by
  have e0 : (P ++ S).length = P.length + S.length := by simp only [List.length_append]
  have h4 : (P ++ S).drop ((P ++ S).length - 3 * n) = S.drop (S.length - 3 * n) := by
    rw [e0, show P.length + S.length - 3 * n = P.length + (S.length - 3 * n) by omega, drop_suf]
  have h5 : (P ++ S).drop ((P ++ S).length - 2 * n) = S.drop (S.length - 2 * n) := by
    rw [e0, show P.length + S.length - 2 * n = P.length + (S.length - 2 * n) by omega, drop_suf]
  have h6 : (P ++ S).drop ((P ++ S).length - n) = S.drop (S.length - n) := by
    rw [e0, show P.length + S.length - n = P.length + (S.length - n) by omega, drop_suf]
  unfold restR
  rw [h4, h5, h6]

/-- The route suffix of a window reads only the last `3 * n` gates of its untick. -/
private theorem routeSuffix15 (e : InteriorEdge) (j : Fin 26) (hr : e.right = .short j)
    (hlen : (sw15 j).length = 3 * nP15 j)
    (hs : restR (sw15 j) (nP15 j) = passT e.r e.allPairs) :
    restR e.right.baseR e.right.n = passT e.r e.allPairs := by
  obtain ⟨P, hP⟩ := unrouted15_split j
  have hb : restR e.right.baseR e.right.n = restR (Shadow7.unrouted j 0 1) (nP15 j) := by rw [hr]; rfl
  rw [hb, hP, restR_suffix P _ _ hlen]
  exact hs

private theorem routeSuffix20 (e : InteriorEdge) (j : Fin 9) (hr : e.right = .wide j)
    (hlen : (sw20 j).length = 3 * nP20 j)
    (hs : restR (sw20 j) (nP20 j) = passT e.r e.allPairs) :
    restR e.right.baseR e.right.n = passT e.r e.allPairs := by
  obtain ⟨P, hP⟩ := unrouted20_split j
  have hb : restR e.right.baseR e.right.n = restR (unrouted20 j 0 1) (nP20 j) := by rw [hr]; rfl
  rw [hb, hP, restR_suffix P _ _ hlen]
  exact hs

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

set_option maxRecDepth 100000 in
private theorem reverseLowerLeave :
    reverseLowerEdge.left.leaveR.take (reverseLowerEdge.closeR.length + 3 * reverseLowerEdge.count) =
      reverseLowerEdge.closeR ++ reverseLowerEdge.swapR := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem reverseLowerRoute :
    restR reverseLowerEdge.right.baseR reverseLowerEdge.right.n =
      passT reverseLowerEdge.r reverseLowerEdge.allPairs :=
  routeSuffix20 reverseLowerEdge 8 rfl (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 100000 in
private theorem reverseLowerStable : fStable reverseLowerEdge.swapR reverseLowerEdge.interiorMidR := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem reverseLowerChecked : ReverseLowerFacts reverseLowerEdge := by
  refine ⟨reverseLowerLeave, reverseLowerRoute, ?_, ?_, reverseLowerStable, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide +kernel

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
private theorem revE1_facts : ReverseLowerFacts revE1 := by
  refine ⟨?_, routeSuffix15 revE1 1 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE2_facts : ReverseLowerFacts revE2 := by
  refine ⟨?_, routeSuffix15 revE2 2 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE3_facts : ReverseLowerFacts revE3 := by
  refine ⟨?_, routeSuffix15 revE3 3 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE4_facts : ReverseLowerFacts revE4 := by
  refine ⟨?_, routeSuffix15 revE4 4 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE5_facts : ReverseLowerFacts revE5 := by
  refine ⟨?_, routeSuffix15 revE5 5 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE6_facts : ReverseLowerFacts revE6 := by
  refine ⟨?_, routeSuffix15 revE6 6 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE7_facts : ReverseLowerFacts revE7 := by
  refine ⟨?_, routeSuffix15 revE7 7 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE8_facts : ReverseLowerFacts revE8 := by
  refine ⟨?_, routeSuffix20 revE8 0 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE9_facts : ReverseLowerFacts revE9 := by
  refine ⟨?_, routeSuffix20 revE9 1 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE10_facts : ReverseLowerFacts revE10 := by
  refine ⟨?_, routeSuffix20 revE10 2 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE11_facts : ReverseLowerFacts revE11 := by
  refine ⟨?_, routeSuffix20 revE11 3 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE12_facts : ReverseLowerFacts revE12 := by
  refine ⟨?_, routeSuffix20 revE12 4 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE13_facts : ReverseLowerFacts revE13 := by
  refine ⟨?_, routeSuffix20 revE13 5 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE14_facts : ReverseLowerFacts revE14 := by
  refine ⟨?_, routeSuffix20 revE14 6 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE15_facts : ReverseLowerFacts revE15 := by
  refine ⟨?_, routeSuffix20 revE15 7 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE16_facts : ReverseLowerFacts revE16 := by
  refine ⟨?_, routeSuffix15 revE16 20 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE17_facts : ReverseLowerFacts revE17 := by
  refine ⟨?_, routeSuffix15 revE17 21 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE18_facts : ReverseLowerFacts revE18 := by
  refine ⟨?_, routeSuffix15 revE18 22 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE19_facts : ReverseLowerFacts revE19 := by
  refine ⟨?_, routeSuffix15 revE19 23 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
private theorem revE20_facts : ReverseLowerFacts revE20 := by
  refine ⟨?_, routeSuffix15 revE20 24 rfl (by decide +kernel) (by decide +kernel),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
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
