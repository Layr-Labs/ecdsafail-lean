import ECDSAAdd.Submission.Entrant.LeaveReductions

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBNumeric
open SkywalkNat

/-- Odd Stein steps halve the complete sum, including the equality case. -/
theorem odd_step_sum (z : SkywalkNat.State) (hu : z.u % 2 = 1)
    (hv : z.v % 2 = 1) :
    2 * ((step z).u + (step z).v) = z.u + z.v := by
  unfold step
  split_ifs <;> (try dsimp only) <;> omega

/-- Every valid step contracts the sum by at most a factor of two.
The odd-second-rail premise matters because natural division truncates. -/
theorem step_sum_le_two (z : SkywalkNat.State) (hv : z.v % 2 = 1) :
    z.u + z.v ≤ 2 * ((step z).u + (step z).v) := by
  unfold step
  split_ifs <;> (try dsimp only) <;> omega

/-- Unbounded, generic version of the 15-step original/end comparison. -/
theorem original_sum_le (n : Nat) (z : SkywalkNat.State) (hv : z.v % 2 = 1) :
    z.u + z.v ≤ 2^n * ((step^[n] z).u + (step^[n] z).v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have odd := (iter_valid n z (by omega) hv).2.1
    have next := step_sum_le_two (step^[n] z) odd
    rw [Function.iterate_succ_apply']
    calc
      z.u + z.v ≤ 2^n * ((step^[n] z).u + (step^[n] z).v) := ih
      _ ≤ 2^n * (2 * ((step (step^[n] z)).u + (step (step^[n] z)).v)) :=
        Nat.mul_le_mul_left (2^n) next
      _ = 2^(n+1) * ((step (step^[n] z)).u + (step (step^[n] z)).v) := by
        rw [pow_succ]
        ring

/-- Transport a twofold pre-last bound through an odd last step. -/
theorem odd_last_sum_lt (b : Nat) (z : SkywalkNat.State)
    (hu : z.u % 2 = 1) (hv : z.v % 2 = 1)
    (bound : z.u + z.v < 2^(b+17)) :
    (step z).u + (step z).v < 2^(b+16) := by
  have half := odd_step_sum z hu hv
  have scale : 2^(b+17) = 2 * 2^(b+16) := by
    rw [show b+17 = (b+16)+1 by omega, pow_succ]
    ring
  rw [scale] at bound
  omega

private theorem encode_g (g s : Bool) (u v : Int) :
    (SkywalkRails.encode g s u v).g = g := by
  cases g <;> rfl

/-- Final signed orientation records the parity of the pre-last unsigned u.
This is `SkywalkRails.step_orientation` lifted through the existing signed
and unsigned iteration bridge; it does not require a bit-level circuit proof. -/
theorem flags_orientation (n : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : z.v % 2 = 1) :
    (SharedSigned.flags g s (SkywalkTrace.trace (n+1)
      (SkywalkRails.encode g s z.u z.v))).1 =
      decide ((step^[n] z).u % 2 = 0) := by
  have signed := SharedSigned.lift (n+1) g s z hv
  have classified := (SkywalkTrace.iter_code_classified n g s z (by omega) hv).1
  have orient : (SkywalkTrace.next^[n+1] (SkywalkRails.encode g s z.u z.v)).g =
      decide ((step^[n] z).u % 2 = 0) := by
    rw [Function.iterate_succ_apply']
    exact classified
  rw [signed, encode_g] at orient
  exact orient

/-- A false final orientation forces the last unsigned step to be odd. -/
theorem flags_false_last_odd (n : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : z.v % 2 = 1)
    (falseG : (SharedSigned.flags g s (SkywalkTrace.trace (n+1)
      (SkywalkRails.encode g s z.u z.v))).1 = false) :
    (step^[n] z).u % 2 = 1 := by
  have orient := flags_orientation n g s z hv
  rw [falseG] at orient
  have ne : ¬ (step^[n] z).u % 2 = 0 := by
    intro h
    simp [h] at orient
  omega

/-- The reduced input total is strictly below 2^(b+17), in both branches. -/
theorem reduced_sum_lt (b : Nat) (z : SkywalkNat.State)
    (small : Shadow7.SmallIfFar b 15 z) :
    (Shadow.reduced b 15 z).u + (Shadow.reduced b 15 z).v < 2^(b+17) := by
  have upper : (Shadow.reduced b 15 z).u + (Shadow.reduced b 15 z).v <
      2 * Shadow.limb b 15 := by
    by_cases far : Shadow.far b 15 z
    · exact (Shadow.represented b 15 z (small far) far).2.2
    · have low : (z.u+z.v)/Shadow.limb b 15 < 2 := Nat.lt_of_not_ge far
      simpa only [Shadow.reduced, if_neg far] using
        (Nat.div_lt_iff_lt_mul (by unfold Shadow.limb; positivity)).mp low
  have scale : 2 * Shadow.limb b 15 = 2^(b+17) := by
    unfold Shadow.limb
    rw [show b+17 = (b+15+1)+1 by omega, pow_succ]
    ring
  rwa [scale] at upper

/-- Scan row-15 admission: G=false makes the reduced positive sum one bit
narrower. `true_records_shadow7` connects the original transcript to reduced
arithmetic; nonincrease supplies the pre-last bound and the final odd step
halves it. -/
theorem scan_false_sum_lt (b : Nat) (z : SkywalkNat.State)
    (small : Shadow7.SmallIfFar b 15 z) (hv : z.v % 2 = 1) (g s : Bool)
    (falseG : (SharedSigned.flags g s (SkywalkTrace.trace 15
      (SkywalkRails.encode g s z.u z.v))).1 = false) :
    let a := step^[15] (Shadow.reduced b 15 z)
    a.u + a.v < 2^(b+16) := by
  let r := Shadow.reduced b 15 z
  have odd : r.v % 2 = 1 := shadow_odd_shadow7 b z small hv
  have reducedG : (SharedSigned.flags g s (SkywalkTrace.trace 15
      (SkywalkRails.encode g s r.u r.v))).1 = false := by
    simpa only [r, true_records_shadow7 b z small hv g s] using falseG
  have lastOdd := flags_false_last_odd 14 g s r odd reducedG
  have lastV := (iter_valid 14 r (by omega) odd).2.1
  have pre : (step^[14] r).u + (step^[14] r).v < 2^(b+17) :=
    lt_of_le_of_lt (iter_sum_nonincrease 14 r) (reduced_sum_lt b z small)
  change (step^[15] r).u + (step^[15] r).v < 2^(b+16)
  rw [show (15 : Nat) = 14+1 by rfl, Function.iterate_succ_apply']
  exact odd_last_sum_lt b (step^[14] r) lastOdd lastV pre

/-- Floor comparison for the late-adjust original high word. -/
theorem high_le_end_quotient (b original ending : Nat)
    (contraction : original ≤ 2^15 * ending) :
    original / 2^(b+16) ≤ ending / 2^(b+1) := by
  apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos (b+1))).mpr
  have floor := Nat.div_mul_le_self original (2^(b+16))
  have scale : 2^(b+16) = 32768 * 2^(b+1) := by
    calc
      2^(b+16) = 2^15 * 2^(b+1) := by
        rw [← pow_add]
        congr 1
        omega
      _ = 32768 * 2^(b+1) := by norm_num
  rw [scale] at floor ⊢
  norm_num only [Nat.reducePow] at contraction
  nlinarith

/-- Admission.Numeric.odd and .fit discharge the last two premises in Main.
This imports no Main definitions and can live in a small CRT/Main bridge module. -/
theorem originalHigh_fit (b width : Nat) (z : SkywalkNat.State)
    (odd : z.v % 2 = 1)
    (fit : ((step^[15] z).u + (step^[15] z).v) / 2^(b+1) < 2^width) :
    Shadow.high b 15 z < 2^width := by
  have compare := high_le_end_quotient b (z.u+z.v)
    ((step^[15] z).u + (step^[15] z).v) (original_sum_le 15 z odd)
  exact lt_of_le_of_lt compare fit

end ECDSAAdd.Entrant.StairPacket.PBNumeric
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.DI7Scan
open Arithmetic GateMirror

/-- Incoming bits BEFORE row 15's first CX. Physical row 15 is quotient
bit 16; top is the physical row 16 (quotient bit 17). -/
def Incoming (g a b top : Wire) (s : BasisState) : Prop :=
  (s g = false → s a = false ∧ s b = s top) ∧
  (s g = true → s top = false)

/-- The only Boolean identity needed at row 15's central CCX. -/
theorem xor_identity (G A B T : Bool)
    (near : G = false → A = false ∧ B = T)
    (far : G = true → T = false) :
    (G && (B ^^ A)) = ((B ^^ A) ^^ T) := by
  cases G with
  | false => obtain ⟨ha, hb⟩ := near rfl; simp [ha, hb]
  | true => simp [far rfl]

/-- Abstract signed/positive rail image at the incoming boundary. No lower
bits, initial phase, or sign convention at a tie is constrained. -/
theorem incoming_of_rails (g a b top : Wire) (s : BasisState) (G N P : Bool)
    (orient : s g = G)
    (left : s a = if G then N else P)
    (right : s b = if G then P else N)
    (upper : s top = if G then false else N)
    (positiveNarrow : G = false → P = false) :
    Incoming g a b top s := by
  constructor
  · intro h
    have hg : G = false := orient.symm.trans h
    simp [hg, positiveNarrow hg] at left right upper
    exact ⟨left, right.trans upper.symm⟩
  · intro h
    have hg : G = true := orient.symm.trans h
    simpa [hg] using upper

/-- Numerical version of the incoming contract. Here P is quotient bit 16
of the positive sum, N is the signed smaller rail's sign-extension bit, and
positive bit 17 is already zero. `inputRow15` and `inputTight17` supply that
rail image; DI7Numeric.scan_false_sum_lt supplies the false-G bound. -/
theorem incoming_of_sum (g a b top : Wire) (s : BasisState) (G N : Bool)
    (quotient : Nat) (orient : s g = G)
    (left : s a = if G then N else quotient.testBit 16)
    (right : s b = if G then quotient.testBit 16 else N)
    (upper : s top = if G then false else N)
    (falseBound : G = false → quotient < 2^16) :
    Incoming g a b top s :=
  incoming_of_rails g a b top s G N (quotient.testBit 16) orient left right upper
    (fun h => Nat.testBit_lt_two_pow (falseBound h))

/-- Fully arithmetic incoming contract for any signed packet layout. Use
index i=b+16 at the physical scan's row 15. The smaller-word bound and the
positive top bound are existing inputRow15/inputTight17 facts; the false-G
bound is the new orientation bridge. -/
theorem incoming_of_signed_words (L : SkywalkIntegerLayout) (G sg : Bool)
    (u v i : Nat) (s : BasisState)
    (leftValue : signedRegValue L.a s = (SkywalkRails.encode G sg u v).a)
    (rightValue : signedRegValue L.b s = (SkywalkRails.encode G sg u v).b)
    (orient : s L.previous = G)
    (leftLength : i+1 < L.a.length) (rightLength : i+1 < L.b.length)
    (small : u < 2^i) (positiveTop : u+v < 2^(i+1))
    (falseBound : G = false → u+v < 2^i) :
    Incoming L.previous (L.a.getD i 0) (L.b.getD i 0) (L.b.getD (i+1) 0) s := by
  let e := PortalValues.negative sg u
  have row := LeaveSignedCoordinates.pair L G sg u v i s leftValue rightValue orient
    (by omega) (by omega)
  have top := LeaveSignedCoordinates.pair L G sg u v (i+1) s leftValue rightValue orient
    leftLength rightLength
  have lo : (u-e.toNat).testBit i = false :=
    Nat.testBit_lt_two_pow (lt_of_le_of_lt (Nat.sub_le _ _) small)
  have hi : (u-e.toNat).testBit (i+1) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (lt_of_le_of_lt (Nat.sub_le _ _) small)
      (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ i)))
  have sumHi : (u+v).testBit (i+1) = false := Nat.testBit_lt_two_pow positiveTop
  apply incoming_of_rails _ _ _ _ s G e ((u+v).testBit i) orient
  · simpa only [e, lo, Bool.false_xor] using row.1
  · simpa only [e, lo, Bool.false_xor] using row.2
  · simpa only [e, hi, sumHi, Bool.false_xor] using top.2
  · exact fun h => Nat.testBit_lt_two_pow (falseBound h)

/-- Two CXs implement the central CCX under its exact current-bit relation. -/
theorem middle_eq (g a b top : Wire) (s : State) (m : List Bool)
    (ta : top ≠ a)
    (relation : (s.basis g && s.basis b) = (s.basis b ^^ s.basis top)) :
    run [.CX b a, .CX top a] m s = run [.CCX g b a] [] s := by
  apply State.extensionality
  · rfl
  · funext q
    by_cases qa : q = a
    · subst q
      simp only [run, writeBit, Function.update_self, Function.update_of_ne ta]
      rw [Bool.xor_assoc, ← relation]
    · simp [run, writeBit, Function.update_of_ne qa]

def original (g a b : Wire) : List Gate := [.cx a b, .ccx g b a, .cx a b]
def replacement (a b top : Wire) : List Gate := [.cx a b, .cx b a, .cx top a, .cx a b]

/-- Complete row-15 microblock equality on every measurement tape. The
inherited row-16 measured erasure is outside this block. -/
theorem microblock_eq (g a b top : Wire) (s : State) (m : List Bool)
    (gb : g ≠ b) (atop : a ≠ top) (bt : b ≠ top)
    (input : Incoming g a b top s.basis) :
    run (GateMirror.forward (replacement a b top)) m s =
      run (GateMirror.forward (original g a b)) [] s := by
  let u := run [.CX a b] [] s
  have relation : (u.basis g && u.basis b) = (u.basis b ^^ u.basis top) := by
    have h := xor_identity (s.basis g) (s.basis a) (s.basis b) (s.basis top) input.1 input.2
    simpa only [u, run, writeBit, Function.update_self, Function.update_of_ne gb,
      Function.update_of_ne bt.symm] using h
  change run ([.CX a b] ++ ([.CX b a, .CX top a] ++ [.CX a b])) m s =
    run ([.CX a b] ++ ([.CCX g b a] ++ [.CX a b])) [] s
  simp only [run_append, run_take, List.drop_nil]
  change run [.CX a b] _ (run [.CX b a, .CX top a] _ u) =
    run [.CX a b] _ (run [.CCX g b a] [] u)
  rw [middle_eq g a b top u _ atop.symm relation]
  rfl


end ECDSAAdd.Entrant.StairPacket.DI7Scan
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBScan
open Arithmetic GateMirror Partial CRTBarrel
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run
abbrev cutoff (j : Fin 26) := Shadow7.sbP (start j)
abbrev orient (s : Nat) : Wire := s+30
abbrev left15 (s h : Nat) : Wire := s+h+47
abbrev right15 (h : Nat) : Wire := h+802
abbrev right16 (h : Nat) : Wire := h+803
def scanPre (s h : Nat) : List Gate := (Shadow7.fix0P s h).take 50
-- Replace row15 inside the original54-gate head, before the inherited row16 erase.
def head (s : Nat) : List Gate :=
  scanPre s (Shadow7.sbP s) ++
    (DI7Scan.replacement (left15 s (Shadow7.sbP s)) (right15 (Shadow7.sbP s))
      (right16 (Shadow7.sbP s)) ++ (CRTBarrel.headA0 s).drop 53)

theorem head_split (s : Nat) : CRTBarrel.headA0 s =
    scanPre s (Shadow7.sbP s) ++
      (DI7Scan.original (orient s) (left15 s (Shadow7.sbP s)) (right15 (Shadow7.sbP s)) ++
        (CRTBarrel.headA0 s).drop 53) := by rfl

theorem head_zero (s : Nat) : measurementCount (GateMirror.forward (head s)) = 0 := by
  simp [head, scanPre, CRTBarrel.headA0, Shadow7.fix0P, DI7Scan.replacement,
    GateMirror.forward, front, measurementCount]

theorem head_physical : ∀ j : Fin 26,
    (head (start j)).all proper = true := by decide +kernel

theorem head_counts (s : Nat) :
    toffoliCount (GateMirror.forward (head s)) + 1 =
      toffoliCount (GateMirror.forward (CRTBarrel.headA0 s)) ∧
    toffoliCount (GateMirror.inverse (head s)) + 1 =
      toffoliCount (GateMirror.inverse (CRTBarrel.headA0 s)) ∧
    measurementCount (GateMirror.forward (head s)) =
      measurementCount (GateMirror.forward (CRTBarrel.headA0 s)) ∧
    measurementCount (GateMirror.inverse (head s)) =
      measurementCount (GateMirror.inverse (CRTBarrel.headA0 s)) ∧
    Challenge.gateSlots (GateMirror.forward (head s)) =
      Challenge.gateSlots (GateMirror.forward (CRTBarrel.headA0 s)) + 1 ∧
    Challenge.gateSlots (GateMirror.inverse (head s)) =
      Challenge.gateSlots (GateMirror.inverse (CRTBarrel.headA0 s)) + 1 := by
  simp [head, scanPre, CRTBarrel.headA0, Shadow7.fix0P, DI7Scan.replacement,
    GateMirror.forward, GateMirror.inverse, front, back, GateMirror.erase,
    toffoliCount, measurementCount, Challenge.gateSlots, Challenge.instructionSlots]

theorem replacement_allW {P : Wire → Prop} (g a b top : Wire)
    (old : AllW P (DI7Scan.original g a b)) (topIn : P top) :
    AllW P (DI7Scan.replacement a b top) := by
  have pa : P a := old (.cx a b) (by simp [DI7Scan.original]) a (by simp [Gate.wires])
  have pb : P b := old (.cx a b) (by simp [DI7Scan.original]) b (by simp [Gate.wires])
  intro gate member q inside
  simp only [DI7Scan.replacement, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at inside
  all_goals rcases inside with rfl | rfl
  all_goals assumption

theorem head_scope {P : Wire → Prop} (s : Nat)
    (old : AllW P (CRTBarrel.headA0 s)) : AllW P (head s) := by
  have member : Gate.cx (s + Shadow7.sbP s + 48) (Shadow7.sbP s + 803) ∈
      CRTBarrel.headA0 s := by simp [CRTBarrel.headA0, Shadow7.fix0P]
  have topIn : P (right16 (Shadow7.sbP s)) := old _ member _ (by simp [Gate.wires])
  rw [head_split, allW_append_iff, allW_append_iff] at old
  rw [head, allW_append_iff, allW_append_iff]
  exact ⟨old.1, replacement_allW _ _ _ _ old.2.1 topIn, old.2.2⟩


end ECDSAAdd.Entrant.StairPacket.PBScan
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveCutsCore150
open ECDSAAdd.Entrant.StairPacket.CRTBarrel
open CRTBarrel
def beforeRow (s : Nat) := PBScan.head s ++ beforeRowTail s

theorem beforeRow_old (s : Nat) : beforeC5 s = headA0 s ++ beforeRowTail s := rfl


end ECDSAAdd.Entrant.StairPacket.LeaveCutsCore150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror
structure RawValid (s : State) (gs : List Gate) : Prop where
  physical : ∀ g ∈ gs, proper g = true
  prepared : Prepared s gs
  ready : Ready s gs

theorem RawValid.tail {s : State} {g : Gate} {gs : List Gate} (v : RawValid s (g::gs)) :
    RawValid (transition g s) gs :=
  ⟨fun x hx => v.physical x (List.mem_cons_of_mem _ hx),v.prepared.2,v.ready.2⟩

theorem RawValid.default_run {s : State} {gs : List Gate} (v : RawValid s gs) (m : List Bool) :
    run (GateMirror.forward gs) m s = run (GateMirror.forward gs) [] s := by
  induction gs generalizing s m with
  | nil => rfl
  | cons g gs ih =>
    change run ([front g] ++ GateMirror.forward gs) m s = run ([front g] ++ GateMirror.forward gs) [] s
    simp only [run_append,run_take,List.drop_nil]
    rw [head_default g s v.prepared.1 (v.physical _ List.mem_cons_self)]
    exact ih v.tail _

theorem RawValid.parts {s : State} {a b : List Gate} (ok : RawValid s (a++b)) :
    RawValid s a ∧ RawValid (run (GateMirror.forward a) [] s) b := by
  induction a generalizing s with
  | nil => exact ⟨⟨by simp,trivial,trivial⟩,ok⟩
  | cons g gs ih =>
    obtain ⟨left,right⟩ := ih ok.tail
    refine ⟨⟨fun x hx => ok.physical x (List.mem_append_left _ hx),⟨ok.prepared.1,left.prepared⟩,⟨ok.ready.1,left.ready⟩⟩,?_⟩
    change RawValid (run ([front g]++GateMirror.forward gs) [] s) b
    simpa only [run_append,run_take,List.drop_nil] using right

theorem RawValid.undo_run {s : State} {a : List Gate} (v : RawValid s a) (m n : List Bool) :
    run (GateMirror.inverse a) n (run (GateMirror.forward a) m s) = s :=
  invert a s v.physical v.prepared v.ready m n

theorem raw_append {s : State} {a b : List Gate} (va : RawValid s a)
    (vb : RawValid (run (GateMirror.forward a) [] s) b) : RawValid s (a++b) := by
  induction a generalizing s with
  | nil => exact vb
  | cons g gs ih =>
    have after : RawValid (run (GateMirror.forward gs) [] (transition g s)) b := by
      change RawValid (run ([front g]++GateMirror.forward gs) [] s) b at vb
      rw [run_append,run_take,List.drop_nil] at vb
      exact vb
    have rest := ih va.tail after
    exact ⟨fun x hx => by
      rcases List.mem_cons.mp hx with rfl | ht
      · exact va.physical _ List.mem_cons_self
      · exact rest.physical x ht,
      ⟨va.prepared.1,rest.prepared⟩,⟨va.ready.1,rest.ready⟩⟩

theorem dest_forward (gs : List Gate) : (GateMirror.forward gs).map LeaveReadoutFrame.destination = gs.map target := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [GateMirror.forward, List.map_cons] at ih ⊢
    rw [ih]; cases g <;> rfl
end ECDSAAdd.Entrant.StairPacket.DeadJoin
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic GateMirror DeadJoin
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

abbrev Expr := Bool × List Wire

def parity (qs : List Wire) (s : BasisState) : Bool :=
  qs.foldr (fun q b => s q ^^ b) false

def eval (e : Expr) (s : BasisState) : Bool := e.1 ^^ parity e.2 s

def toggleOld (q : Wire) : List Wire → List Wire
  | [] => [q]
  | x::xs => if q=x then xs else x::toggleOld q xs

theorem parity_toggleOld (q : Wire) (qs : List Wire) (s : BasisState) :
    parity (toggleOld q qs) s = (s q ^^ parity qs s) := by
  induction qs with
  | nil => simp [toggleOld,parity]
  | cons x xs ih =>
    by_cases h : q=x
    · subst x; simp [toggleOld,parity,Bool.xor_assoc]
    · rw [toggleOld,if_neg h]
      change (s x ^^ parity (toggleOld q xs) s) = (s q ^^ (s x ^^ parity xs s))
      rw [ih]
      cases s q <;> cases s x <;> cases parity xs s <;> rfl

/-- Normalize parity without permuting unaffected wires. -/
def toggle (q : Wire) (qs : List Wire) : List Wire :=
  if qs.contains q then toggleOld q qs else q::qs

theorem parity_toggle (q : Wire) (qs : List Wire) (s : BasisState) :
    parity (toggle q qs) s = (s q ^^ parity qs s) := by
  unfold toggle
  split
  · exact parity_toggleOld q qs s
  · rfl

def add (a b : Expr) : Expr :=
  (a.1 ^^ b.1, a.2.foldr toggle b.2)

theorem eval_add (a b : Expr) (s : BasisState) :
    eval (add a b) s = (eval a s ^^ eval b s) := by
  obtain ⟨ac,aq⟩ := a
  obtain ⟨bc,bq⟩ := b
  have h : parity (aq.foldr toggle bq) s = (parity aq s ^^ parity bq s) := by
    induction aq with
    | nil => simp [parity]
    | cons q qs ih =>
      change parity (toggle q (qs.foldr toggle bq)) s = (s q ^^ parity qs s ^^ parity bq s)
      rw [parity_toggle,ih,Bool.xor_assoc]
  simp only [add,eval,h]
  cases ac <;> cases bc <;> cases parity aq s <;> cases parity bq s <;> rfl

/-- Pull back one wire through a default mirror transition. Nonlinear targets
are rejected; erased targets pull back to zero. -/
def wirePull (g : Gate) (q : Wire) : Option Expr :=
  if q ≠ target g then some (false,[q]) else
  match g with
  | .x t => some (true,[t])
  | .cx c t => some (false,[t,c])
  | .pop _ _ _ => some (false,[])
  | _ => none

theorem wirePull_sound (g : Gate) (q : Wire) (e : Expr)
    (h : wirePull g q = some e) (s : State) :
    eval e s.basis = (transition g s).basis q := by
  unfold wirePull at h
  split_ifs at h with hq
  · cases h
    cases g <;> simp only [target] at hq <;> simp [eval,parity,transition,front,erase,run,measureAndCorrect,
      ECDSAAdd.correct,writeBit,Function.update_of_ne hq]
  · have eq : q=target g := by simpa using hq
    cases g <;> simp only [target] at eq <;> subst q
    all_goals try { simp at h }
    all_goals cases h
    all_goals simp [eval,parity,transition,front,erase,run,measureAndCorrect,
      ECDSAAdd.correct,writeBit,Bool.xor_comm]

def pullTerms (g : Gate) : List Wire → Option Expr
  | [] => some (false,[])
  | q::qs => do
      let a ← wirePull g q
      let b ← pullTerms g qs
      pure (add a b)

theorem pullTerms_sound (g : Gate) (qs : List Wire) (e : Expr)
    (h : pullTerms g qs = some e) (s : State) :
    eval e s.basis = parity qs (transition g s).basis := by
  induction qs generalizing e with
  | nil => simp [pullTerms] at h; subst e; rfl
  | cons q qs ih =>
    simp only [pullTerms] at h
    cases ha : wirePull g q with
    | none => simp [ha] at h
    | some a =>
      cases hb : pullTerms g qs with
      | none => simp [ha,hb] at h
      | some b =>
        simp [ha,hb] at h
        subst e
        rw [eval_add,wirePull_sound g q a ha s,ih b hb]
        rfl

def stepSlow (g : Gate) (e : Expr) : Option Expr := do
  let b ← pullTerms g e.2
  pure (add (e.1,[]) b)

theorem stepSlow_sound (g : Gate) (e out : Expr) (h : stepSlow g e = some out) (s : State) :
    eval out s.basis = eval e (transition g s).basis := by
  simp only [stepSlow] at h
  cases hb : pullTerms g e.2 with
  | none => simp [hb] at h
  | some b =>
    simp [hb] at h; subst out
    rw [eval_add,pullTerms_sound g e.2 b hb s]
    simp [eval,parity]

/-- An untouched affine support needs no normalization or symbolic substitution. -/
def step (g : Gate) (e : Expr) : Option Expr :=
  if e.2.contains (target g) then stepSlow g e else some e

theorem parity_same (qs : List Wire) (a b : BasisState) (h : ∀q∈qs,a q=b q) :
    parity qs a=parity qs b := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (a q ^^ parity qs a)=(b q ^^ parity qs b)
    rw [h q List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem step_sound (g : Gate) (e out : Expr) (h : step g e = some out) (s : State) :
    eval out s.basis = eval e (transition g s).basis := by
  unfold step at h
  split at h
  · exact stepSlow_sound g e out h s
  · have absent : ¬target g ∈ e.2 := by simpa using ‹¬e.2.contains (target g) = true›
    cases h
    unfold eval
    congr 1
    apply parity_same
    intro q hq
    have neq : q ≠ target g := fun eq => absent (eq ▸ hq)
    cases g <;> simp only [target] at neq <;>
      simp [transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,
        writeBit,Function.update_of_ne neq]

def pull : List Gate → Expr → Option Expr
  | [], e => some e
  | g::gs, e => do
      let b ← pull gs e
      step g b

theorem pull_sound (gs : List Gate) (e out : Expr) (h : pull gs e = some out) (s : State) :
    eval out s.basis = eval e (run (GateMirror.forward gs) [] s).basis := by
  induction gs generalizing out s with
  | nil => simp [pull] at h; subst out; rfl
  | cons g gs ih =>
    simp only [pull] at h
    cases hb : pull gs e with
    | none => simp [hb] at h
    | some b =>
      simp only [hb,Option.bind_some] at h
      rw [step_sound g b out h s,ih b hb (transition g s)]
      change _ = eval e (run ([front g] ++ GateMirror.forward gs) [] s).basis
      rw [run_append,run_take,List.drop_nil]
      rfl

end ECDSAAdd.Entrant.StairPacket.DI7Affine
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBReceiver
open Arithmetic Partial GateMirror CRTBarrel
/-- The original moved leave, before inherited eight admissible splices. -/
def beforePort := CRTBarrel.before
def afterPort := CRTBarrel.afterPart
def latchPop (s : Nat) : Gate := .pop 1570 (Shadow7.sbP s+801) 1571
def selectorPop (s : Nat) : Gate := .pop 1560 (OB5.sig (s+14) (s+1048)) 1565
def selectorSources (s : Nat) : List Wire := [1559,1561,1562,1563,1564,Shadow7.e0P s+7]
def latchPre (s : Nat) := (beforePort s).takeWhile (fun g => g != latchPop s)
def latchPost (s : Nat) := (beforePort s).drop ((latchPre s).length+1)
def selectorPre (s : Nat) := (afterPort s).takeWhile (fun g => g != selectorPop s)
def selectorPost (s : Nat) := (afterPort s).drop ((selectorPre s).length+1)
def receiver (t : Wire) (c : Bool) (qs : List Wire) : List Gate :=
  (if c then [Gate.x t] else []) ++ qs.map (fun q => Gate.cx q t)
def before100 (s : Nat) : List Gate := latchPre s ++ (receiver 1571 true [1556] ++ latchPost s)
def after100 (s : Nat) : List Gate := selectorPre s ++ (receiver 1565 false (selectorSources s) ++ selectorPost s)
def portOps (s : Nat) := beforePort s ++ (Shadow7.leaveBarrel s ++ afterPort s)
end ECDSAAdd.Entrant.StairPacket.PBReceiver
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic Partial GateMirror DeadJoin
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem update_nested (f : BasisState) (t : Wire) (a b : Bool) :
    Function.update (Function.update f t a) t b = Function.update f t b := by
  funext q
  by_cases h : q=t
  · subst q; simp
  · simp [Function.update_of_ne h]

def cxs (qs : List Wire) (t : Wire) : List Gate := qs.map (fun q => .cx q t)
def clear (c : Bool) (qs : List Wire) (t : Wire) : List Gate :=
  (if c then [Gate.x t] else []) ++ cxs qs t

theorem parity_congr (qs : List Wire) (a b : BasisState) (h : ∀ q∈qs,a q=b q) :
    parity qs a=parity qs b := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (a q ^^ parity qs a) = (b q ^^ parity qs b)
    rw [h q List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem cxs_run (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) (m : List Bool) :
    run (GateMirror.forward (cxs qs t)) m s =
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ parity qs s.basis)⟩ := by
  induction qs generalizing s m with
  | nil =>
    simp only [cxs,List.map_nil,GateMirror.forward,List.map_nil,run,parity,List.foldr_nil,Bool.xor_false]
    cases s
    simp [writeBit]
  | cons q qs ih =>
    have qt := away q List.mem_cons_self
    have tail := fun x hx => away x (List.mem_cons_of_mem _ hx)
    have p : parity qs (writeBit s.basis t (s.basis t ^^ s.basis q))=parity qs s.basis :=
      parity_congr qs _ _ (fun x hx => Function.update_of_ne (tail x hx) _ _)
    change run ([Instr.CX q t] ++ GateMirror.forward (cxs qs t)) m s = _
    rw [run_append,run_take]
    change run (GateMirror.forward (cxs qs t)) _ ⟨s.phase,writeBit s.basis t (s.basis t ^^ s.basis q)⟩ = _
    rw [ih tail]
    rw [p]
    simp only [writeBit,Function.update_self,update_nested]
    simp only [parity,List.foldr_cons,Bool.xor_assoc]

theorem clear_run (c : Bool) (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) (m : List Bool) :
    run (GateMirror.forward (clear c qs t)) m s =
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ (c ^^ parity qs s.basis))⟩ := by
  cases c with
  | false => simpa [clear] using cxs_run qs t away s m
  | true =>
    have p : parity qs (writeBit s.basis t (!s.basis t))=parity qs s.basis :=
      parity_congr qs _ _ (fun x hx => Function.update_of_ne (away x hx) _ _)
    simp only [clear,if_true,forward_app,run_append,run_take]
    change run (GateMirror.forward (cxs qs t)) _ ⟨s.phase,writeBit s.basis t (!s.basis t)⟩ = _
    rw [cxs_run qs t away]
    rw [p]
    simp only [writeBit,Function.update_self,update_nested]
    congr 1
    cases s.basis t <;> cases parity qs s.basis <;> rfl

theorem clear_valid (c : Bool) (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) :
    RawValid s (clear c qs t) := by
  have phys : Proper (clear c qs t) := by
    intro g hg
    simp only [clear,List.mem_append] at hg
    rcases hg with hx | hc
    · cases c <;> simp_all [proper]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      simpa [proper] using away q hq
  have plain : ∀ g∈clear c qs t,plainGate g=true := by
    intro g hg
    simp only [clear,List.mem_append] at hg
    rcases hg with hx | hc
    · cases c <;> simp_all [plainGate]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      rfl
  exact ⟨phys,all_prepared _ s phys (fun m => by simp only [clear_run c qs t away]),ready_plain _ (List.all_eq_true.mpr plain) s⟩

/-- Replace a prepared pop with its preserved XOR receiver, transporting the
whole basis, phase, and both independent inverse measurement tapes. -/
theorem raw_replace_pop (a b : List Gate) (x y t : Wire) (c : Bool) (qs : List Wire)
    (s : State) (v : RawValid s (a ++ (Gate.pop x y t :: b)))
    (away : ∀ q∈qs,q≠t)
    (rel : eval (c,t::qs) (run (GateMirror.forward a) [] s).basis=false) :
    RawValid s (a ++ (clear c qs t ++ b)) ∧
    (∀ m,run (GateMirror.forward (a ++ (clear c qs t ++ b))) m s=
      run (GateMirror.forward (a ++ (Gate.pop x y t :: b))) m s) := by
  let u := run (GateMirror.forward a) [] s
  have va := v.parts.1
  have vb := v.parts.2.tail
  have e : run (GateMirror.forward (clear c qs t)) [] u = transition (Gate.pop x y t) u := by
    rw [clear_run c qs t away]
    have z : (u.basis t ^^ (c ^^ parity qs u.basis))=false := by
      change (c ^^ (u.basis t ^^ parity qs u.basis))=false at rel
      have shuffle (c t p : Bool) : (c ^^ (t ^^ p)) = (t ^^ (c ^^ p)) := by
        cases c <;> cases t <;> cases p <;> rfl
      rw [←shuffle]; exact rel
    simp only [z,transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,
      List.headD,Bool.false_and,Bool.xor_false,Bool.false_eq_true,if_false]
  rw [←e] at vb
  have w := raw_append va (raw_append (clear_valid c qs t away u) vb)
  refine ⟨w,?_⟩
  intro m
  rw [w.default_run m,v.default_run m]
  simp only [forward_app,run_append,run_take,List.drop_nil]
  change run (GateMirror.forward b) [] (run (GateMirror.forward (clear c qs t)) [] u) =
    run (GateMirror.forward b) [] (transition (Gate.pop x y t) u)
  rw [e]

end ECDSAAdd.Entrant.StairPacket.DI7Affine
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror

/-- Replace one gate-list block while preserving the trajectory admission
predicate. Only equality on the default tape is needed locally: RawValid
already supplies independence from every measurement tape. -/
theorem raw_replace_valid (a b c replacement : List Gate) (s : State)
    (valid : RawValid s (a ++ (b ++ c)))
    (localValid : RawValid (run (GateMirror.forward a) [] s) replacement)
    (same : run (GateMirror.forward replacement) [] (run (GateMirror.forward a) [] s) =
      run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s)) :
    RawValid s (a ++ (replacement ++ c)) ∧
      ∀ m, run (GateMirror.forward (a ++ (replacement ++ c))) m s =
        run (GateMirror.forward (a ++ (b ++ c))) m s := by
  obtain ⟨va, vbc⟩ := valid.parts
  obtain ⟨_, vc⟩ := vbc.parts
  have suffix : RawValid
      (run (GateMirror.forward replacement) [] (run (GateMirror.forward a) [] s)) c := by
    rw [same]
    exact vc
  have result := raw_append va (raw_append localValid suffix)
  refine ⟨result, fun m => ?_⟩
  rw [result.default_run m, valid.default_run m]
  simp only [forward_app, run_append, List.drop_nil, run_take]
  rw [same]

/-- Four block replacements with all local obligations stated at the ORIGINAL
boundaries. Work from the rightmost block back so no premise has to mention
an already-modified prefix. -/
theorem raw_replace4_valid
    (a0 b1 a1 b2 a2 b3 a3 b4 a4 n1 n2 n3 n4 : List Gate) (s : State)
    (valid : RawValid s (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ a4)))))))))
    (valid1 : RawValid (run (GateMirror.forward a0) [] s) n1)
    (same1 : run (GateMirror.forward n1) [] (run (GateMirror.forward a0) [] s) =
      run (GateMirror.forward b1) [] (run (GateMirror.forward a0) [] s))
    (valid2 : RawValid (run (GateMirror.forward (a0 ++ (b1 ++ a1))) [] s) n2)
    (same2 : run (GateMirror.forward n2) [] (run (GateMirror.forward (a0 ++ (b1 ++ a1))) [] s) =
      run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b1 ++ a1))) [] s))
    (valid3 : RawValid (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ a2))))) [] s) n3)
    (same3 : run (GateMirror.forward n3) []
      (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ a2))))) [] s) =
      run (GateMirror.forward b3) []
      (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ a2))))) [] s))
    (valid4 : RawValid
      (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ a3))))))) [] s) n4)
    (same4 : run (GateMirror.forward n4) []
      (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ a3))))))) [] s) =
      run (GateMirror.forward b4) []
      (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ a3))))))) [] s)) :
    RawValid s (a0 ++ (n1 ++ (a1 ++ (n2 ++ (a2 ++ (n3 ++ (a3 ++ (n4 ++ a4)))))))) ∧
      ∀ m, run (GateMirror.forward
        (a0 ++ (n1 ++ (a1 ++ (n2 ++ (a2 ++ (n3 ++ (a3 ++ (n4 ++ a4))))))))) m s =
        run (GateMirror.forward
        (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ a4))))))))) m s := by
  let p4 := a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ a3)))))
  let p3 := a0 ++ (b1 ++ (a1 ++ (b2 ++ a2)))
  let p2 := a0 ++ (b1 ++ a1)
  have start4 : RawValid s (p4 ++ (b4 ++ a4)) := by
    simpa only [p4, List.append_assoc] using valid
  obtain ⟨v4, e4⟩ := raw_replace_valid p4 b4 a4 n4 s start4 valid4 same4
  have start3 : RawValid s (p3 ++ (b3 ++ (a3 ++ (n4 ++ a4)))) := by
    simpa only [p3, p4, List.append_assoc] using v4
  obtain ⟨v3, e3⟩ := raw_replace_valid p3 b3 (a3 ++ (n4 ++ a4)) n3 s start3 valid3 same3
  have start2 : RawValid s (p2 ++ (b2 ++ (a2 ++ (n3 ++ (a3 ++ (n4 ++ a4)))))) := by
    simpa only [p2, p3, List.append_assoc] using v3
  obtain ⟨v2, e2⟩ := raw_replace_valid p2 b2 (a2 ++ (n3 ++ (a3 ++ (n4 ++ a4)))) n2 s start2 valid2 same2
  have start1 : RawValid s (a0 ++ (b1 ++ (a1 ++ (n2 ++ (a2 ++ (n3 ++ (a3 ++ (n4 ++ a4)))))))) := by
    simpa only [p2, List.append_assoc] using v2
  obtain ⟨v1, e1⟩ := raw_replace_valid a0 b1
    (a1 ++ (n2 ++ (a2 ++ (n3 ++ (a3 ++ (n4 ++ a4)))))) n1 s start1 valid1 same1
  refine ⟨v1, fun m => ?_⟩
  have step1 := e1 m
  have step2 := e2 m
  have step3 := e3 m
  have step4 := e4 m
  simp only [p2, p3, p4, List.append_assoc] at step1 step2 step3 step4
  exact step1.trans (step2.trans (step3.trans step4))

end ECDSAAdd.Entrant.StairPacket.DeadJoin
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBReceiver
open Arithmetic Partial GateMirror DeadJoin DI7Affine
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

private theorem split_first (gs : List Gate) (g : Gate) (present : g ∈ gs) :
    gs = gs.takeWhile (fun x => x != g) ++ g :: gs.drop ((gs.takeWhile (fun x => x != g)).length+1) := by
  induction gs with
  | nil => simp at present
  | cons x xs ih =>
    by_cases h : x=g
    · subst x; simp
    · have member : g∈xs := by simpa [h,Ne.symm h] using present
      simpa [List.takeWhile_cons,h,Ne.symm h,Nat.add_assoc] using congrArg (List.cons x) (ih member)

private theorem latch_present : ∀ j : Fin 26, j.val≤24 → latchPop (start j) ∈ beforePort (start j) := by decide +kernel
private theorem selector_present : ∀ j : Fin 26, j.val≤24 → selectorPop (start j) ∈ afterPort (start j) := by decide +kernel

def selectorExpr (s : Nat) : Expr := (false,1565::selectorSources s)

theorem latch_shape : ∀ j : Fin 26, j.val≤24 → beforePort (start j)=
    latchPre (start j) ++ (latchPop (start j) :: latchPost (start j)) := by
  intro j hi
  exact split_first _ _ (latch_present j hi)

theorem selector_shape : ∀ j : Fin 26, j.val≤24 → afterPort (start j)=
    selectorPre (start j) ++ (selectorPop (start j) :: selectorPost (start j)) := by
  intro j hi
  exact split_first _ _ (selector_present j hi)

theorem latch_pull : ∀ j : Fin 26, j.val≤24 →
    pull (latchPre (start j)) (true,[1571,1556])=some (false,[1556]) := by decide +kernel

theorem selector_after_pull : ∀ j : Fin 26, j.val≤24 →
    pull (selectorPre (start j)) (selectorExpr (start j))=some (selectorExpr (start j)) := by decide +kernel

theorem selector_before_pull : ∀ j : Fin 26, j.val≤24 →
    pull (beforePort (start j)) (selectorExpr (start j))=some (false,[Shadow7.e0P (start j)+7]) := by decide +kernel

private theorem selector_geometry : ∀ j : Fin 26, j.val≤24 →
    1614 ≤ Shadow7.e0P (start j) ∧ Partial.bTopP (start j) ≤ 1300 := by decide +kernel

private theorem bank_away (s i : Nat) (e : 1614 ≤ Shadow7.e0P s)
    (b : Partial.bTopP s ≤ 1300) (hi : i < Shadow7.wpP s + 15) :
    Shadow7.bankW s i ∉ (selectorExpr s).2 := by
  have locations : (i < 3 ∧ Shadow7.bankW s i = Shadow7.e0P s+i) ∨
      Shadow7.bankW s i ≤ 1300 ∨
      (1598 ≤ Shadow7.bankW s i ∧ Shadow7.bankW s i ≤ 1612) := by
    unfold Shadow7.bankW
    split_ifs <;> ((try unfold Wire at *); omega)
  intro member
  simp only [selectorExpr,selectorSources,Prod.snd,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases locations with first | second | third <;> ((try unfold Wire at *); omega)

theorem selector_barrel_quiet : ∀ j : Fin 26, j.val≤24 →
    (Shadow7.leaveBarrel (start j)).all (fun g => !(selectorExpr (start j)).2.contains (target g))=true := by
  intro j hi
  obtain ⟨e,b⟩ := selector_geometry j hi
  let T : Wire → Prop := fun q => q ∉ (selectorExpr (start j)).2
  have control : T 1613 := by
    simp only [T,selectorExpr,selectorSources,Prod.snd,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
    (try unfold Wire at *)
    omega
  have bank : ∀i,i<Shadow7.wpP (start j)+15 → T (Shadow7.bankW (start j) i) :=
    fun i bound => bank_away _ _ e b bound
  have stage : ∀ (xs : List Wire) (d n : Nat), n+d ≤ Shadow7.wpP (start j)+15 →
      AllAT (fun _ => True) T (stageG 1613 (Shadow7.bankW (start j)) xs d n) :=
    fun xs d n bound => allAT_stageG _ _ _ _ _ ⟨trivial,control⟩ (fun _ _ => trivial)
      (fun i ix => ⟨⟨trivial,bank i (by omega)⟩,⟨trivial,bank (i+d) (by omega)⟩⟩)
  have all : AllAT (fun _ => True) T (Shadow7.leaveBarrel (start j)) := by
    unfold Shadow7.leaveBarrel
    exact allAT_append (allAT_append (allAT_append (stage _ _ _ (by omega))
      (stage _ _ _ (by omega))) (stage _ _ _ (by omega))) (stage _ _ _ (by omega))
  apply List.all_eq_true.mpr
  intro g hg
  have away := (all g hg).2
  cases h : (selectorExpr (start j)).2.contains (target g) with
  | false => rfl
  | true => exact False.elim (away (List.contains_iff_mem.mp h))

end ECDSAAdd.Entrant.StairPacket.PBReceiver
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBReceiver
open Arithmetic Partial GateMirror DeadJoin DI7Affine
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
attribute [local irreducible] run

theorem parity_append (a b : List Wire) (s : BasisState) :
    parity (a++b) s = (parity a s ^^ parity b s) := by
  induction a with
  | nil => simp [parity]
  | cons q qs ih =>
    change (s q ^^ parity (qs++b) s) = ((s q ^^ parity qs s) ^^ parity b s)
    rw [ih,Bool.xor_assoc]

theorem parity_reverse (qs : List Wire) (s : BasisState) : parity qs.reverse s=parity qs s := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    rw [List.reverse_cons,parity_append,ih]
    change (parity qs s ^^ (s q ^^ false)) = (s q ^^ parity qs s)
    simp [Bool.xor_comm]

theorem keeps_targets (gs : List Gate) (q : Wire) (h : ∀ g∈gs,target g≠q) (s : State) :
    (run (GateMirror.forward gs) [] s).basis q=s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,eq⟩ := List.mem_map.mp hit
  exact h g hg eq

theorem expr_kept (gs : List Gate) (e : Expr)
    (h : gs.all (fun g => !e.2.contains (target g))=true) (s : State) :
    eval e (run (GateMirror.forward gs) [] s).basis=eval e s.basis := by
  unfold eval
  rw [parity_congr e.2 _ _]
  intro q hq
  apply keeps_targets
  intro g hg eq
  have hh := List.all_eq_true.mp h g hg
  simp only [Bool.not_eq_true'] at hh
  have mem : e.2.contains (target g)=true := List.contains_iff_mem.mpr (eq ▸ hq)
  rw [mem] at hh
  contradiction

theorem latch_valid (j : Fin 26) (hi : j.val≤24) (s : State)
    (v : RawValid s (beforePort (start j))) (zero : s.basis 1556=false) :
    RawValid s (before100 (start j)) ∧
    (∀ m,run (GateMirror.forward (before100 (start j))) m s=
      run (GateMirror.forward (beforePort (start j))) m s) := by
  have p := pull_sound (latchPre (start j)) (true,[1571,1556]) (false,[1556]) (latch_pull j hi) s
  have rel : eval (true,[1571,1556]) (run (GateMirror.forward (latchPre (start j))) [] s).basis=false := by
    rw [←p]; simpa [eval,parity] using zero
  rw [latch_shape j hi] at v
  have w := raw_replace_pop (latchPre (start j)) (latchPost (start j)) 1570
    (Shadow7.sbP (start j)+801) 1571 true [1556] s v (by simp) rel
  constructor
  · exact w.1
  · intro m
    rw [latch_shape j hi]
    exact w.2 m

theorem selector_valid (j : Fin 26) (hi : j.val≤24) (s : State)
    (v : RawValid s (afterPort (start j))) (related : eval (selectorExpr (start j)) s.basis=false) :
    RawValid s (after100 (start j)) ∧
    (∀ m,run (GateMirror.forward (after100 (start j))) m s=
      run (GateMirror.forward (afterPort (start j))) m s) := by
  have p := pull_sound (selectorPre (start j)) (selectorExpr (start j))
    (selectorExpr (start j)) (selector_after_pull j hi) s
  have rel : eval (selectorExpr (start j)) (run (GateMirror.forward (selectorPre (start j))) [] s).basis=false := by
    rw [←p]
    exact related
  have away : ∀ q∈selectorSources (start j),q≠1565 := by
    simp [selectorSources,Shadow7.e0P]; omega
  rw [selector_shape j hi] at v
  have w := raw_replace_pop (selectorPre (start j)) (selectorPost (start j)) 1560
    (OB5.sig (start j+14) (start j+1048)) 1565 false (selectorSources (start j)) s v away rel
  constructor
  · exact w.1
  · intro m
    rw [selector_shape j hi]
    exact w.2 m

theorem receiver_port_valid (j : Fin 26) (hi : j.val≤24) (s : State)
    (v : RawValid s (portOps (start j)))
    (zeroLatch : s.basis 1556=false) (zeroAggregate : s.basis (Shadow7.e0P (start j)+7)=false) :
    RawValid s (before100 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after100 (start j))) ∧
    (∀ m,run (GateMirror.forward (before100 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after100 (start j)))) m s=
      run (GateMirror.forward (portOps (start j))) m s) ∧
    run (GateMirror.forward (before100 (start j))) [] s=
      run (GateMirror.forward (beforePort (start j))) [] s := by
  change RawValid s (beforePort (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterPort (start j))) at v
  obtain ⟨lv,le⟩ := latch_valid j hi s v.parts.1 zeroLatch
  let u := run (GateMirror.forward (beforePort (start j))) [] s
  let t := run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] u
  have relu : eval (selectorExpr (start j)) u.basis=false := by
    have p := pull_sound (beforePort (start j)) (selectorExpr (start j))
      (false,[Shadow7.e0P (start j)+7]) (selector_before_pull j hi) s
    rw [←p]; simpa [eval,parity] using zeroAggregate
  have relt : eval (selectorExpr (start j)) t.basis=false := by
    rw [expr_kept _ _ (selector_barrel_quiet j hi) u]; exact relu
  obtain ⟨sv,se⟩ := selector_valid j hi t v.parts.2.parts.2 relt
  have suffixv : RawValid s ((beforePort (start j) ++ Shadow7.leaveBarrel (start j)) ++ (afterPort (start j) ++ [])) := by
    simpa only [List.append_nil,List.append_assoc] using v
  obtain ⟨w,we⟩ := raw_replace_valid (beforePort (start j) ++ Shadow7.leaveBarrel (start j))
    (afterPort (start j)) [] (after100 (start j)) s suffixv
    (by simpa only [forward_app,run_append,run_take,List.drop_nil] using sv)
    (by simpa only [forward_app,run_append,run_take,List.drop_nil] using se [])
  simp only [List.append_nil,List.append_assoc] at w we
  obtain ⟨r,re⟩ := raw_replace_valid [] (beforePort (start j))
    (Shadow7.leaveBarrel (start j) ++ after100 (start j)) (before100 (start j)) s
    (by simpa using w) (by simpa only [GateMirror.forward,List.map_nil,run] using lv) (by simpa only [GateMirror.forward,List.map_nil,run] using le [])
  refine ⟨by simpa using r,?_,le []⟩
  intro m
  have first : run (GateMirror.forward (before100 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after100 (start j)))) m s =
      run (GateMirror.forward (beforePort (start j) ++ (Shadow7.leaveBarrel (start j) ++ after100 (start j)))) m s := by
    simpa using re m
  exact first.trans (by simpa only [portOps,List.append_nil,List.append_assoc] using we m)
end ECDSAAdd.Entrant.StairPacket.PBReceiver
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBReceiver
open Arithmetic Partial GateMirror DeadJoin Challenge
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 2000000

theorem receiver_counts (a b : List Gate) (x y t : Wire) (qs : List Wire) (c : Bool) :
    toffoliCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) =
      toffoliCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    toffoliCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      toffoliCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 1 =
      measurementCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) =
      measurementCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    gateSlots (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 2 =
      gateSlots (GateMirror.forward (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat ∧
    gateSlots (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      gateSlots (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat := by
  have hm : (qs.map (fun q => Gate.cx q t)).countP isMake = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isMake] using ih
  have hp : (qs.map (fun q => Gate.cx q t)).countP isPop = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isPop] using ih
  have hc : (qs.map (fun q => Gate.cx q t)).countP isCCX = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isCCX] using ih
  cases c <;> simp [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,
    receiver,List.countP_append,List.countP_cons,isMake,isPop,isCCX,hm,hp,hc,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem deltas100 (j : Fin 26) (hi : j.val≤24) :
    toffoliCount (GateMirror.forward (before100 (start j))) + toffoliCount (GateMirror.forward (after100 (start j))) =
      toffoliCount (GateMirror.forward (beforePort (start j))) + toffoliCount (GateMirror.forward (afterPort (start j))) ∧
    toffoliCount (GateMirror.inverse (before100 (start j))) + toffoliCount (GateMirror.inverse (after100 (start j))) + 2 =
      toffoliCount (GateMirror.inverse (beforePort (start j))) + toffoliCount (GateMirror.inverse (afterPort (start j))) ∧
    measurementCount (GateMirror.forward (before100 (start j))) + measurementCount (GateMirror.forward (after100 (start j))) + 2 =
      measurementCount (GateMirror.forward (beforePort (start j))) + measurementCount (GateMirror.forward (afterPort (start j))) ∧
    measurementCount (GateMirror.inverse (before100 (start j))) + measurementCount (GateMirror.inverse (after100 (start j))) =
      measurementCount (GateMirror.inverse (beforePort (start j))) + measurementCount (GateMirror.inverse (afterPort (start j))) ∧
    gateSlots (GateMirror.forward (before100 (start j))) + gateSlots (GateMirror.forward (after100 (start j))) =
      gateSlots (GateMirror.forward (beforePort (start j))) + gateSlots (GateMirror.forward (afterPort (start j))) + 4 ∧
    gateSlots (GateMirror.inverse (before100 (start j))) + gateSlots (GateMirror.inverse (after100 (start j))) =
      gateSlots (GateMirror.inverse (beforePort (start j))) + gateSlots (GateMirror.inverse (afterPort (start j))) + 6 := by
  have latch := receiver_counts (latchPre (start j)) (latchPost (start j)) 1570
    (Shadow7.sbP (start j)+801) 1571 [1556] true
  have sel := receiver_counts (selectorPre (start j)) (selectorPost (start j)) 1560
    (OB5.sig (start j+14) (start j+1048)) 1565 (selectorSources (start j)) false
  change _ at latch sel
  have ls := latch_shape j hi
  have ss := selector_shape j hi
  simp only [latchPop] at ls
  simp only [selectorPop] at ss
  rw [←ls] at latch
  rw [←ss] at sel
  change _ at latch sel
  simp only [selectorSources,List.length_cons,List.length_nil,Bool.toNat_true,Bool.toNat_false] at latch sel
  dsimp only [before100,after100,selectorSources]
  omega
end ECDSAAdd.Entrant.StairPacket.PBReceiver
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBOps
open Arithmetic Partial GateMirror CRTBarrel
/-- The original moved leave, before inherited eight admissible splices. -/
def beforePort := LeaveCutsCore150.beforeRow
def afterPort := CRTBarrel.afterPartC3
def latchPop (s : Nat) : Gate := .pop 1570 (Shadow7.sbP s+801) 1571
def selectorPop (s : Nat) : Gate := .pop 1560 (OB5.sig (s+14) (s+1048)) 1565
def selectorSources (s : Nat) : List Wire := [1559,1561,1562,1563,1564,Shadow7.e0P s+7]
def latchPre (s : Nat) := (beforePort s).takeWhile (fun g => g != latchPop s)
def latchPost (s : Nat) := (beforePort s).drop ((latchPre s).length+1)
def selectorPre (s : Nat) := (afterPort s).takeWhile (fun g => g != selectorPop s)
def selectorPost (s : Nat) := (afterPort s).drop ((selectorPre s).length+1)
def receiver (t : Wire) (c : Bool) (qs : List Wire) : List Gate :=
  (if c then [Gate.x t] else []) ++ qs.map (fun q => Gate.cx q t)
def before100 (s : Nat) : List Gate := latchPre s ++ (receiver 1571 true [1556] ++ latchPost s)
def after100 (s : Nat) : List Gate := selectorPre s ++ (receiver 1565 false (selectorSources s) ++ selectorPost s)
def portOps (s : Nat) := beforePort s ++ (Shadow7.leaveBarrel s ++ afterPort s)
end ECDSAAdd.Entrant.StairPacket.PBOps
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBOps
open Arithmetic Partial GateMirror DeadJoin DI7Affine
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

private theorem split_first (gs : List Gate) (g : Gate) (present : g ∈ gs) :
    gs = gs.takeWhile (fun x => x != g) ++ g :: gs.drop ((gs.takeWhile (fun x => x != g)).length+1) := by
  induction gs with
  | nil => simp at present
  | cons x xs ih =>
    by_cases h : x=g
    · subst x; simp
    · have member : g∈xs := by simpa [h,Ne.symm h] using present
      simpa [List.takeWhile_cons,h,Ne.symm h,Nat.add_assoc] using congrArg (List.cons x) (ih member)

private theorem latch_present : ∀ j : Fin 26, j.val≤24 → latchPop (start j) ∈ beforePort (start j) := by decide +kernel
private theorem selector_present : ∀ j : Fin 26, j.val≤24 → selectorPop (start j) ∈ afterPort (start j) := by decide +kernel

def selectorExpr (s : Nat) : Expr := (false,1565::selectorSources s)

theorem latch_shape : ∀ j : Fin 26, j.val≤24 → beforePort (start j)=
    latchPre (start j) ++ (latchPop (start j) :: latchPost (start j)) := by
  intro j hi
  exact split_first _ _ (latch_present j hi)

theorem selector_shape : ∀ j : Fin 26, j.val≤24 → afterPort (start j)=
    selectorPre (start j) ++ (selectorPop (start j) :: selectorPost (start j)) := by
  intro j hi
  exact split_first _ _ (selector_present j hi)


end ECDSAAdd.Entrant.StairPacket.PBOps
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBOps
open Arithmetic Partial GateMirror DeadJoin Challenge
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 2000000

theorem receiver_counts (a b : List Gate) (x y t : Wire) (qs : List Wire) (c : Bool) :
    toffoliCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) =
      toffoliCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    toffoliCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      toffoliCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 1 =
      measurementCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) =
      measurementCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    gateSlots (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 2 =
      gateSlots (GateMirror.forward (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat ∧
    gateSlots (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      gateSlots (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat := by
  have hm : (qs.map (fun q => Gate.cx q t)).countP isMake = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isMake] using ih
  have hp : (qs.map (fun q => Gate.cx q t)).countP isPop = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isPop] using ih
  have hc : (qs.map (fun q => Gate.cx q t)).countP isCCX = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simpa [isCCX] using ih
  cases c <;> simp [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,
    receiver,List.countP_append,List.countP_cons,isMake,isPop,isCCX,hm,hp,hc,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem deltas100 (j : Fin 26) (hi : j.val≤24) :
    toffoliCount (GateMirror.forward (before100 (start j))) + toffoliCount (GateMirror.forward (after100 (start j))) =
      toffoliCount (GateMirror.forward (beforePort (start j))) + toffoliCount (GateMirror.forward (afterPort (start j))) ∧
    toffoliCount (GateMirror.inverse (before100 (start j))) + toffoliCount (GateMirror.inverse (after100 (start j))) + 2 =
      toffoliCount (GateMirror.inverse (beforePort (start j))) + toffoliCount (GateMirror.inverse (afterPort (start j))) ∧
    measurementCount (GateMirror.forward (before100 (start j))) + measurementCount (GateMirror.forward (after100 (start j))) + 2 =
      measurementCount (GateMirror.forward (beforePort (start j))) + measurementCount (GateMirror.forward (afterPort (start j))) ∧
    measurementCount (GateMirror.inverse (before100 (start j))) + measurementCount (GateMirror.inverse (after100 (start j))) =
      measurementCount (GateMirror.inverse (beforePort (start j))) + measurementCount (GateMirror.inverse (afterPort (start j))) ∧
    gateSlots (GateMirror.forward (before100 (start j))) + gateSlots (GateMirror.forward (after100 (start j))) =
      gateSlots (GateMirror.forward (beforePort (start j))) + gateSlots (GateMirror.forward (afterPort (start j))) + 4 ∧
    gateSlots (GateMirror.inverse (before100 (start j))) + gateSlots (GateMirror.inverse (after100 (start j))) =
      gateSlots (GateMirror.inverse (beforePort (start j))) + gateSlots (GateMirror.inverse (afterPort (start j))) + 6 := by
  have latch := receiver_counts (latchPre (start j)) (latchPost (start j)) 1570
    (Shadow7.sbP (start j)+801) 1571 [1556] true
  have sel := receiver_counts (selectorPre (start j)) (selectorPost (start j)) 1560
    (OB5.sig (start j+14) (start j+1048)) 1565 (selectorSources (start j)) false
  change _ at latch sel
  have ls := latch_shape j hi
  have ss := selector_shape j hi
  simp only [latchPop] at ls
  simp only [selectorPop] at ss
  rw [←ls] at latch
  rw [←ss] at sel
  change _ at latch sel
  simp only [selectorSources,List.length_cons,List.length_nil,Bool.toNat_true,Bool.toNat_false] at latch sel
  dsimp only [before100,after100,selectorSources]
  omega
end ECDSAAdd.Entrant.StairPacket.PBOps
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBScope100
open Arithmetic Partial GateMirror DeadJoin PBOps
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-- Arbitrary predicates need only the additional affine source wires. No
search through a complete emitted program is used in this interface. -/
theorem receiver_allW {P : Wire→Prop} (t : Wire) (c : Bool) (qs : List Wire)
    (ht : P t) (hq : ∀q∈qs,P q) : AllW P (receiver t c qs) := by
  intro g hg q occurs
  simp only [receiver,List.mem_append] at hg
  rcases hg with hx | hc
  · cases c <;> simp_all [Gate.wires]
  · obtain ⟨src,hs,rfl⟩ := List.mem_map.mp hc
    simp only [Gate.wires,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at occurs
    rcases occurs with rfl | rfl
    · exact hq _ hs
    · exact ht

theorem before_allW {P : Wire→Prop} (j : Fin 26) (hi : j.val≤24)
    (old : AllW P (beforePort (start j))) (flag : P 1556) : AllW P (before100 (start j)) := by
  rw [latch_shape j hi,allW_append_iff] at old
  have head := old.2 (latchPop (start j)) List.mem_cons_self
  have tgt : P 1571 := head 1571 (by simp [latchPop,Gate.wires])
  rw [before100,allW_append_iff,allW_append_iff]
  exact ⟨old.1,receiver_allW _ _ _ tgt (by simpa using flag),
    fun g hg => old.2 g (List.mem_cons_of_mem _ hg)⟩

theorem after_allW {P : Wire→Prop} (j : Fin 26) (hi : j.val≤24)
    (old : AllW P (afterPort (start j))) (sources : ∀q∈selectorSources (start j),P q) :
    AllW P (after100 (start j)) := by
  rw [selector_shape j hi,allW_append_iff] at old
  have head := old.2 (selectorPop (start j)) List.mem_cons_self
  have tgt : P 1565 := head 1565 (by simp [selectorPop,Gate.wires])
  rw [after100,allW_append_iff,allW_append_iff]
  exact ⟨old.1,receiver_allW _ _ _ tgt sources,
    fun g hg => old.2 g (List.mem_cons_of_mem _ hg)⟩

/-- Six fixed tag/aggregate wires, checked directly against the existing
geometric footprint; independent of all emitted program lengths. -/
theorem sources_box : ∀j:Fin 26,j.val≤24 → ∀q∈selectorSources (start j),
    Partial.leaveBox (start j) q ∧ Shadow7.leaveBox2 (start j) q := by
  letI (s q : Nat) : Decidable (Partial.leaveBox s q) := by
    unfold Partial.leaveBox; infer_instance
  letI (s q : Nat) : Decidable (Shadow7.leaveBox2 s q) := by
    unfold Shadow7.leaveBox2; infer_instance
  decide

theorem flag_box : ∀j:Fin 26,j.val≤24 →
    Partial.leaveBox (start j) 1556 ∧ Shadow7.leaveBox2 (start j) 1556 := by
  letI (s q : Nat) : Decidable (Partial.leaveBox s q) := by
    unfold Partial.leaveBox; infer_instance
  letI (s q : Nat) : Decidable (Shadow7.leaveBox2 s q) := by
    unfold Shadow7.leaveBox2; infer_instance
  decide
end ECDSAAdd.Entrant.StairPacket.PBScope100
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBOps
open Arithmetic Partial GateMirror DeadJoin
private theorem proper_parts {a b : List Gate} (old : Proper (a++b)) : Proper a ∧ Proper b :=
  ⟨fun g hg => old g (List.mem_append_left _ hg), fun g hg => old g (List.mem_append_right _ hg)⟩

theorem receiver_proper (t : Wire) (c : Bool) (qs : List Wire)
    (away : ∀q∈qs,q≠t) : Proper (receiver t c qs) := by
  intro g hg
  simp only [receiver,List.mem_append] at hg
  rcases hg with hx | hc
  · cases c <;> simp_all [proper]
  · obtain ⟨src,hs,rfl⟩ := List.mem_map.mp hc
    simpa [proper] using away src hs

theorem before100_proper (j : Fin 26) (hi : j.val≤24)
    (old : Proper (beforePort (start j))) : Proper (before100 (start j)) := by
  rw [latch_shape j hi] at old
  obtain ⟨a,b⟩ := proper_parts old
  exact proper_append a (proper_append (receiver_proper _ _ _ (by simp))
    (fun g hg => b g (List.mem_cons_of_mem _ hg)))

theorem after100_proper (j : Fin 26) (hi : j.val≤24)
    (old : Proper (afterPort (start j))) : Proper (after100 (start j)) := by
  rw [selector_shape j hi] at old
  obtain ⟨a,b⟩ := proper_parts old
  exact proper_append a (proper_append (receiver_proper _ _ _ (by simp [selectorSources,Shadow7.e0P]; omega))
    (fun g hg => b g (List.mem_cons_of_mem _ hg)))

end ECDSAAdd.Entrant.StairPacket.PBOps
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveCutsCore150
open ECDSAAdd.Entrant.StairPacket.CRTBarrel
open CRTBarrel
def leave (j : Fin 26) : Program :=
  let s := start j
  if j.val ≤ 24 then
    GateMirror.forward (PBOps.before100 s) ++ barrel s false ++ GateMirror.forward (PBOps.after100 s)
  else Shadow7.leaveMoveP j

def unleave (j : Fin 26) : Program :=
  let s := start j
  if j.val ≤ 24 then
    GateMirror.inverse (PBOps.after100 s) ++ barrel s true ++ GateMirror.inverse (PBOps.before100 s)
  else Shadow7.leaveMoveInvP j

def params : WindowFold.Pieces Program := { Shadow7.params with leave := leave, leaveInv := unleave }

end ECDSAAdd.Entrant.StairPacket.LeaveCutsCore150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveWindow150
open ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false



theorem split_ops (s : Nat) :
    Shadow7.leaveMoveOps s = CRTBarrel.before s ++ (Shadow7.leaveBarrel s ++ CRTBarrel.afterPart s) := by
  simp only [Shadow7.leaveMoveOps, CRTBarrel.before, CRTBarrel.afterPart, List.append_assoc]

theorem forward_append (a b : List Gate) :
    GateMirror.forward (a ++ b) = GateMirror.forward a ++ GateMirror.forward b := by
  simp only [GateMirror.forward, List.map_append]

theorem inverse_append (a b : List Gate) : inverse (a ++ b) = inverse b ++ inverse a := by
  simp only [inverse, List.map_append, List.reverse_append]

/-- The blocks whose leave is the CRT barrel leave (`LeaveCutsCore150.leave`'s guard): every block 1..22 of the exit-420
window. -/
def crtBlocks (j : Fin 26) : Bool := j.val ≤ 24

theorem inBlocks_iff (j : Fin 26) : crtBlocks j = true ↔ (j.val ≤ 24) := by
  simp only [crtBlocks, decide_eq_true_eq]

/-! Counts. -/

/-- The rebuilt leave's prefix and suffix carry the Shadow7 move leave's counts minus its barrel stage. -/
theorem parts_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.before (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 104 ∧
    toffoliCount (inverse (CRTBarrel.afterPart (start j))) + toffoliCount (inverse (CRTBarrel.before (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 136 ∧
    measurementCount (GateMirror.forward (CRTBarrel.before (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 93 ∧
    measurementCount (inverse (CRTBarrel.afterPart (start j))) +
      measurementCount (inverse (CRTBarrel.before (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 61 ∧
    gateSlots (GateMirror.forward (CRTBarrel.before (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPart (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 649 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPart (start j))) + gateSlots (inverse (CRTBarrel.before (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 617 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := Shadow7.leaveMove_counts j (by omega) (by omega)
  obtain ⟨b1, b2, c1, c2, d1, d2⟩ := (Shadow7.counts_leaveBarrel (start j)).programs
  rw [Shadow7.leaveMoveP, split_ops, forward_append, forward_append] at t1 m1 s1
  rw [Shadow7.leaveMoveInvP, split_ops, inverse_append, inverse_append] at t2 m2 s2
  simp only [toffoliCount_append, measurementCount_append, gateSlots_append] at t1 t2 m1 m2 s1 s2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem before_split (s : Nat) : CRTBarrel.before s =
    CRTBarrel.headA s ++ ([.make (Shadow7.sbP s + 1577) (Shadow7.sbP s + 1578) 1559] ++ CRTBarrel.headC s) := by
  simp only [CRTBarrel.before, CRTBarrel.headA, CRTBarrel.headC, Partial.leaveFix3, List.append_assoc, List.cons_append,
    List.nil_append]

theorem after_split (s : Nat) : CRTBarrel.afterPart s =
    CRTBarrel.tailD s ++ ([.pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559] ++ CRTBarrel.tailE s) := by
  simp only [CRTBarrel.afterPart, CRTBarrel.tailD, CRTBarrel.tailE, Shadow7.leaveLowStore_split, Shadow7.lowSign,
    List.append_assoc, List.cons_append, List.nil_append]

theorem beforeC_split (s : Nat) :
    CRTBarrel.beforeC s = CRTBarrel.headA s ++ ([.cx (Shadow7.sbP s + 1578) 1559] ++ CRTBarrel.headC s) := rfl

theorem afterPartC_split (s : Nat) :
    CRTBarrel.afterPartC s = CRTBarrel.tailD s ++ ([.cx (Shadow7.e0P s + 4) 1559] ++ CRTBarrel.tailE s) := rfl

/-- The CNOT flag pair: one Toffoli and one measurement fewer in each direction than `parts_counts`. -/
theorem partsC_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.beforeC (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 103 ∧
    toffoliCount (inverse (CRTBarrel.afterPartC (start j))) + toffoliCount (inverse (CRTBarrel.beforeC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 135 ∧
    measurementCount (GateMirror.forward (CRTBarrel.beforeC (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 92 ∧
    measurementCount (inverse (CRTBarrel.afterPartC (start j))) +
      measurementCount (inverse (CRTBarrel.beforeC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 60 ∧
    gateSlots (GateMirror.forward (CRTBarrel.beforeC (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 648 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPartC (start j))) + gateSlots (inverse (CRTBarrel.beforeC (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 616 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := parts_counts j h0 h1
  rw [before_split, after_split] at t1 t2 m1 m2 s1 s2
  rw [beforeC_split, afterPartC_split]
  have c1 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have c2 : ∀ a b t : Wire, toffoliCount (inverse [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have c3 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have c4 : ∀ a b t : Wire, toffoliCount (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have c5 : ∀ b t : Wire, toffoliCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have c6 : ∀ b t : Wire, toffoliCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d1 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have d2 : ∀ a b t : Wire, measurementCount (inverse [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have d3 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have d4 : ∀ a b t : Wire, measurementCount (inverse [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have d5 : ∀ b t : Wire, measurementCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d6 : ∀ b t : Wire, measurementCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have e1 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have e2 : ∀ a b t : Wire, gateSlots (inverse [Gate.make a b t]) = 2 := fun _ _ _ => rfl
  have e3 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.pop a b t]) = 2 := fun _ _ _ => rfl
  have e4 : ∀ a b t : Wire, gateSlots (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have e5 : ∀ b t : Wire, gateSlots (GateMirror.forward [Gate.cx b t]) = 1 := fun _ _ => rfl
  have e6 : ∀ b t : Wire, gateSlots (inverse [Gate.cx b t]) = 1 := fun _ _ => rfl
  simp only [forward_append, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append,
    c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, e1, e2, e3, e4, e5, e6] at t1 t2 m1 m2 s1 s2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem fix0P_cut (s h : Nat) :
    Shadow7.fix0P s h = (Shadow7.fix0P s h).take 54 ++ ([.ccx (s+30) (h+803) (s+h+48)] ++ (Shadow7.fix0P s h).drop 55) := rfl

theorem headA_cut (s : Nat) : CRTBarrel.headA s =
    CRTBarrel.headA0 s ++ ([.ccx (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++ CRTBarrel.headA1 s) := by
  have e := fix0P_cut s (Shadow7.sbP s)
  simp only [CRTBarrel.headA, CRTBarrel.headA0, CRTBarrel.headA1]
  conv_lhs => rw [e]
  simp only [List.append_assoc]

theorem before_split4 (s : Nat) : CRTBarrel.before s =
    CRTBarrel.headA0 s ++ ([.ccx (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++ (CRTBarrel.headA1 s ++
      ([.make (Shadow7.sbP s + 1577) (Shadow7.sbP s + 1578) 1559] ++ CRTBarrel.headC s))) := by
  rw [before_split, headA_cut]
  simp only [List.append_assoc]

theorem beforeC4_split (s : Nat) : CRTBarrel.beforeC4 s =
    CRTBarrel.headA0 s ++ ([.pop (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++
      (CRTBarrel.headA1 s ++ ([.cx (Shadow7.sbP s + 1578) 1559] ++ CRTBarrel.headC s))) := rfl

theorem beforeC_cut (s : Nat) : CRTBarrel.beforeC s =
    CRTBarrel.headA0 s ++ ([.ccx (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++
      (CRTBarrel.headA1 s ++ ([.cx (Shadow7.sbP s + 1578) 1559] ++ CRTBarrel.headC s))) := by
  rw [beforeC_split, headA_cut]
  simp only [List.append_assoc]

/-- Row 17's erasure on top of `partsC_counts`: one Toffoli fewer and one measurement more forward. -/
theorem partsC4_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.beforeC4 (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 102 ∧
    toffoliCount (inverse (CRTBarrel.afterPartC (start j))) + toffoliCount (inverse (CRTBarrel.beforeC4 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 135 ∧
    measurementCount (GateMirror.forward (CRTBarrel.beforeC4 (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 93 ∧
    measurementCount (inverse (CRTBarrel.afterPartC (start j))) +
      measurementCount (inverse (CRTBarrel.beforeC4 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 60 ∧
    gateSlots (GateMirror.forward (CRTBarrel.beforeC4 (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 649 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPartC (start j))) + gateSlots (inverse (CRTBarrel.beforeC4 (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 616 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := partsC_counts j h0 h1
  rw [beforeC_cut] at t1 t2 m1 m2 s1 s2
  rw [beforeC4_split]
  have c1 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.ccx a b t]) = 1 := fun _ _ _ => rfl
  have c2 : ∀ a b t : Wire, toffoliCount (inverse [Gate.ccx a b t]) = 1 := fun _ _ _ => rfl
  have c3 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have c4 : ∀ a b t : Wire, toffoliCount (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have d1 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.ccx a b t]) = 0 := fun _ _ _ => rfl
  have d2 : ∀ a b t : Wire, measurementCount (inverse [Gate.ccx a b t]) = 0 := fun _ _ _ => rfl
  have d3 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have d4 : ∀ a b t : Wire, measurementCount (inverse [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have e1 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.ccx a b t]) = 1 := fun _ _ _ => rfl
  have e2 : ∀ a b t : Wire, gateSlots (inverse [Gate.ccx a b t]) = 1 := fun _ _ _ => rfl
  have e3 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.pop a b t]) = 2 := fun _ _ _ => rfl
  have e4 : ∀ a b t : Wire, gateSlots (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  simp only [forward_append, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append,
    c1, c2, c3, c4, d1, d2, d3, d4, e1, e2, e3, e4] at t1 t2 m1 m2 s1 s2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem moveRows_cut (s : Nat) :
    Shadow7.moveRows s = (Partial.tagsP.getD 0 0, Shadow7.a0P s + 0) :: (Shadow7.moveRows s).drop 1 := rfl

theorem headC_cut (s : Nat) : CRTBarrel.headC s = CRTBarrel.headC0 s ++ ([.cx (Shadow7.a0P s + 0) (Shadow7.e0P s + 6),
    .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P s + 6) (Shadow7.a0P s + 0), .cx (Shadow7.a0P s + 0) (Shadow7.e0P s + 6)] ++
    CRTBarrel.headC1 s) := by
  have e := moveRows_cut s
  simp only [CRTBarrel.headC, CRTBarrel.headC0, CRTBarrel.headC1, Shadow7.leaveFix5Move]
  conv_lhs => rw [e]
  simp only [rowGates, List.append_assoc, List.cons_append, List.nil_append]

theorem beforeC5_split (s : Nat) : CRTBarrel.beforeC5 s =
    CRTBarrel.headA0 s ++ ([.pop (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++ (CRTBarrel.headA1 s ++
      ([.cx (Shadow7.sbP s + 1578) 1559] ++ (CRTBarrel.headC0 s ++
      ([.make (Partial.tagsP.getD 0 0) (Shadow7.a0P s + 0) (Shadow7.e0P s + 6), .cx (Shadow7.e0P s + 6) (Shadow7.a0P s + 0)] ++
        CRTBarrel.headC1 s))))) := rfl

theorem beforeC4_cut (s : Nat) : CRTBarrel.beforeC4 s =
    CRTBarrel.headA0 s ++ ([.pop (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++ (CRTBarrel.headA1 s ++
      ([.cx (Shadow7.sbP s + 1578) 1559] ++ (CRTBarrel.headC0 s ++
      ([.cx (Shadow7.a0P s + 0) (Shadow7.e0P s + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P s + 6) (Shadow7.a0P s + 0),
        .cx (Shadow7.a0P s + 0) (Shadow7.e0P s + 6)] ++ CRTBarrel.headC1 s))))) := by
  rw [beforeC4_split, headC_cut]

/-- Row 0's make form on top of `partsC4_counts`: one inverse Toffoli fewer (an erasure instead), one forward gate fewer. -/
theorem partsC5_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 102 ∧
    toffoliCount (inverse (CRTBarrel.afterPartC (start j))) + toffoliCount (inverse (CRTBarrel.beforeC5 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 134 ∧
    measurementCount (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 93 ∧
    measurementCount (inverse (CRTBarrel.afterPartC (start j))) +
      measurementCount (inverse (CRTBarrel.beforeC5 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 61 ∧
    gateSlots (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPartC (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 648 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPartC (start j))) + gateSlots (inverse (CRTBarrel.beforeC5 (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 616 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := partsC4_counts j h0 h1
  rw [beforeC4_cut] at t1 t2 m1 m2 s1 s2
  rw [beforeC5_split]
  have c1 : ∀ a b c t u : Wire, toffoliCount (GateMirror.forward [Gate.cx a b, Gate.ccx c b a, Gate.cx a b]) = 1 :=
    fun _ _ _ _ _ => rfl
  have c2 : ∀ a b c t u : Wire, toffoliCount (inverse [Gate.cx a b, Gate.ccx c b a, Gate.cx a b]) = 1 := fun _ _ _ _ _ => rfl
  have c3 : ∀ a b c : Wire, toffoliCount (GateMirror.forward [Gate.make c a b, Gate.cx b a]) = 1 := fun _ _ _ => rfl
  have c4 : ∀ a b c : Wire, toffoliCount (inverse [Gate.make c a b, Gate.cx b a]) = 0 := fun _ _ _ => rfl
  have d1 : ∀ a b c : Wire, measurementCount (GateMirror.forward [Gate.cx a b, Gate.ccx c b a, Gate.cx a b]) = 0 :=
    fun _ _ _ => rfl
  have d2 : ∀ a b c : Wire, measurementCount (inverse [Gate.cx a b, Gate.ccx c b a, Gate.cx a b]) = 0 := fun _ _ _ => rfl
  have d3 : ∀ a b c : Wire, measurementCount (GateMirror.forward [Gate.make c a b, Gate.cx b a]) = 0 := fun _ _ _ => rfl
  have d4 : ∀ a b c : Wire, measurementCount (inverse [Gate.make c a b, Gate.cx b a]) = 1 := fun _ _ _ => rfl
  have e1 : ∀ a b c : Wire, gateSlots (GateMirror.forward [Gate.cx a b, Gate.ccx c b a, Gate.cx a b]) = 3 := fun _ _ _ => rfl
  have e2 : ∀ a b c : Wire, gateSlots (inverse [Gate.cx a b, Gate.ccx c b a, Gate.cx a b]) = 3 := fun _ _ _ => rfl
  have e3 : ∀ a b c : Wire, gateSlots (GateMirror.forward [Gate.make c a b, Gate.cx b a]) = 2 := fun _ _ _ => rfl
  have e4 : ∀ a b c : Wire, gateSlots (inverse [Gate.make c a b, Gate.cx b a]) = 3 := fun _ _ _ => rfl
  simp only [forward_append, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append,
    c1 _ _ _ 0 0, c2 _ _ _ 0 0, c3, c4, d1, d2, d3, d4, e1, e2, e3, e4] at t1 t2 m1 m2 s1 s2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem wordGM_snoc (a : Wire) (r : HighBankJoin.Column) (hr : r.hot = none) :
    ∀ rs : List HighBankJoin.Column,
      Partial.wordGM a (rs ++ [r]) = CRTBarrel.wordPre a rs ++ (Partial.pairGM r.low a r.shadow r.tube ++ CRTBarrel.wordPost a rs)
  | [] => by simp [Partial.wordGM, CRTBarrel.wordPre, CRTBarrel.wordPost, hr, Partial.toggleG]
  | x :: rs => by
    simp only [List.cons_append, Partial.wordGM, CRTBarrel.wordPre, CRTBarrel.wordPost, wordGM_snoc a r hr rs, List.append_assoc]

theorem wordGM_split (a : Wire) :
    ∀ rs : List HighBankJoin.Column, Partial.wordGM a rs = CRTBarrel.wordPre a rs ++ CRTBarrel.wordPost a rs
  | [] => rfl
  | x :: rs => by simp only [Partial.wordGM, CRTBarrel.wordPre, CRTBarrel.wordPost, wordGM_split a rs, List.append_assoc]

theorem columnsP_cut (s : Nat) : Shadow7.columnsP s =
    CRTBarrel.colsC s ++ [⟨decide (16 < Shadow7.lowsP s), none, Shadow7.a0P s + 16, Shadow7.bankW s 16⟩] := by
  simp only [Shadow7.columnsP, CRTBarrel.colsC]
  rw [show List.range 17 = List.range 16 ++ [16] from List.range_succ, List.map_append]
  simp

theorem tailD_cut (s : Nat) : CRTBarrel.tailD s = CRTBarrel.tailD0 s ++
    (Partial.pairGM (decide (16 < Shadow7.lowsP s)) 1614 (Shadow7.a0P s + 16) (Shadow7.bankW s 16) ++ CRTBarrel.tailD1 s) := by
  simp only [CRTBarrel.tailD, CRTBarrel.tailD0, CRTBarrel.tailD1, Shadow7.leaveJoinMove, columnsP_cut,
    wordGM_snoc 1614 ⟨decide (16 < Shadow7.lowsP s), none, Shadow7.a0P s + 16, Shadow7.bankW s 16⟩ rfl, List.append_assoc]

/-- A high join pair whose shadow cell is zero is the identity. -/
private theorem low16_all : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 → decide (16 < Shadow7.lowsP (start j)) = false := by
  decide +kernel

theorem afterPartC2_split (s : Nat) : CRTBarrel.afterPartC2 s =
    CRTBarrel.tailD0 s ++ (CRTBarrel.tailD1 s ++ ([.cx (Shadow7.e0P s + 4) 1559] ++ CRTBarrel.tailE s)) := rfl

/-- The join's top pair dropped on top of `partsC5_counts`: one inverse Toffoli and one forward measurement fewer. -/
theorem partsC6_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPartC2 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 102 ∧
    toffoliCount (inverse (CRTBarrel.afterPartC2 (start j))) + toffoliCount (inverse (CRTBarrel.beforeC5 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 133 ∧
    measurementCount (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPartC2 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 92 ∧
    measurementCount (inverse (CRTBarrel.afterPartC2 (start j))) +
      measurementCount (inverse (CRTBarrel.beforeC5 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 61 ∧
    gateSlots (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPartC2 (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 644 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPartC2 (start j))) + gateSlots (inverse (CRTBarrel.beforeC5 (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 613 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := partsC5_counts j h0 h1
  rw [afterPartC_split, tailD_cut, low16_all j h0 h1] at t1 t2 m1 m2 s1 s2
  rw [afterPartC2_split]
  have c1 : ∀ a b c : Wire, toffoliCount (GateMirror.forward (Partial.pairGM false a b c)) = 0 := fun _ _ _ => rfl
  have c2 : ∀ a b c : Wire, toffoliCount (inverse (Partial.pairGM false a b c)) = 1 := fun _ _ _ => rfl
  have d1 : ∀ a b c : Wire, measurementCount (GateMirror.forward (Partial.pairGM false a b c)) = 1 := fun _ _ _ => rfl
  have d2 : ∀ a b c : Wire, measurementCount (inverse (Partial.pairGM false a b c)) = 0 := fun _ _ _ => rfl
  have e1 : ∀ a b c : Wire, gateSlots (GateMirror.forward (Partial.pairGM false a b c)) = 4 := fun _ _ _ => rfl
  have e2 : ∀ a b c : Wire, gateSlots (inverse (Partial.pairGM false a b c)) = 3 := fun _ _ _ => rfl
  simp only [forward_append, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append,
    c1, c2, d1, d2, e1, e2] at t1 t2 m1 m2 s1 s2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem store0 (s : Nat) : Shadow7.storeW s 0 = 1558 := by
  simp only [Shadow7.storeW, Partial.storeW]
  split_ifs <;> ((try unfold Shadow7.e0P at *); (try unfold Wire at *); omega)

theorem store1 (s : Nat) : Shadow7.storeW s 1 = 1559 := by
  simp only [Shadow7.storeW, Partial.storeW]
  split_ifs <;> ((try unfold Shadow7.e0P at *); (try unfold Wire at *); omega)

theorem tailE_cut (s : Nat) : CRTBarrel.tailE s = CRTBarrel.tailE0 s ++
    ([.make 1558 (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559] ++ (CRTBarrel.chainMid s ++
      ([.pop 1558 (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559] ++ CRTBarrel.tailE1 s))) := by
  simp only [CRTBarrel.tailE, CRTBarrel.tailE0, CRTBarrel.storeHead, CRTBarrel.chainMid, CRTBarrel.tailE1, Shadow7.leaveStoreMapped, Partial.chainG, Nat.zero_add, store0,
    store1, if_pos rfl, ite_true, if_true, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

theorem afterPartC3_split (s : Nat) : CRTBarrel.afterPartC3 s =
    CRTBarrel.tailD0 s ++ (CRTBarrel.tailD1 s ++ ([.cx (Shadow7.e0P s + 4) 1559] ++ (CRTBarrel.tailE0 s ++
      ([.cx (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559] ++ (CRTBarrel.chainMid s ++
        ([.cx (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559] ++ CRTBarrel.tailE1 s)))))) := rfl

/-- The store chain's level-0 pair as CNOTs on top of `partsC6_counts`: one Toffoli and one measurement fewer in each
direction. -/
theorem partsC8_counts (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      toffoliCount (GateMirror.forward (CRTBarrel.afterPartC3 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 101 ∧
    toffoliCount (inverse (CRTBarrel.afterPartC3 (start j))) + toffoliCount (inverse (CRTBarrel.beforeC5 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 132 ∧
    measurementCount (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      measurementCount (GateMirror.forward (CRTBarrel.afterPartC3 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 91 ∧
    measurementCount (inverse (CRTBarrel.afterPartC3 (start j))) +
      measurementCount (inverse (CRTBarrel.beforeC5 (start j))) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 60 ∧
    gateSlots (GateMirror.forward (CRTBarrel.beforeC5 (start j))) +
      gateSlots (GateMirror.forward (CRTBarrel.afterPartC3 (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 643 + 3*Shadow7.wpP (start j + 15) ∧
    gateSlots (inverse (CRTBarrel.afterPartC3 (start j))) + gateSlots (inverse (CRTBarrel.beforeC5 (start j))) =
      6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 612 + 3*Shadow7.wpP (start j + 15) := by
  obtain ⟨t1, t2, m1, m2, s1, s2⟩ := partsC6_counts j h0 h1
  rw [afterPartC2_split, tailE_cut] at t1 t2 m1 m2 s1 s2
  rw [afterPartC3_split]
  have c1 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have c2 : ∀ a b t : Wire, toffoliCount (inverse [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have c3 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have c4 : ∀ a b t : Wire, toffoliCount (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have c5 : ∀ b t : Wire, toffoliCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have c6 : ∀ b t : Wire, toffoliCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d1 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have d2 : ∀ a b t : Wire, measurementCount (inverse [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have d3 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have d4 : ∀ a b t : Wire, measurementCount (inverse [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have d5 : ∀ b t : Wire, measurementCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d6 : ∀ b t : Wire, measurementCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have e1 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have e2 : ∀ a b t : Wire, gateSlots (inverse [Gate.make a b t]) = 2 := fun _ _ _ => rfl
  have e3 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.pop a b t]) = 2 := fun _ _ _ => rfl
  have e4 : ∀ a b t : Wire, gateSlots (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have e5 : ∀ b t : Wire, gateSlots (GateMirror.forward [Gate.cx b t]) = 1 := fun _ _ => rfl
  have e6 : ∀ b t : Wire, gateSlots (inverse [Gate.cx b t]) = 1 := fun _ _ => rfl
  simp only [forward_append, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append,
    c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, e1, e2, e3, e4, e5, e6] at t1 t2 m1 m2 s1 s2 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end ECDSAAdd.Entrant.StairPacket.LeaveWindow150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBScanRow
open ECDSAAdd.Entrant.StairPacket.ScanRow16
open GateMirror Partial Challenge

theorem beforeRow_counts (s : Nat) :
    toffoliCount (GateMirror.forward (LeaveCutsCore150.beforeRow s)) + 1 = toffoliCount (GateMirror.forward (CRTBarrel.beforeC5 s)) ∧
    toffoliCount (inverse (LeaveCutsCore150.beforeRow s)) + 1 = toffoliCount (inverse (CRTBarrel.beforeC5 s)) ∧
    measurementCount (GateMirror.forward (LeaveCutsCore150.beforeRow s)) = measurementCount (GateMirror.forward (CRTBarrel.beforeC5 s)) ∧
    measurementCount (inverse (LeaveCutsCore150.beforeRow s)) = measurementCount (inverse (CRTBarrel.beforeC5 s)) ∧
    gateSlots (GateMirror.forward (LeaveCutsCore150.beforeRow s)) = gateSlots (GateMirror.forward (CRTBarrel.beforeC5 s)) + 1 ∧
    gateSlots (inverse (LeaveCutsCore150.beforeRow s)) = gateSlots (inverse (CRTBarrel.beforeC5 s)) + 1 := by
  obtain ⟨a,b,c,d,e,f⟩ := PBScan.head_counts s
  rw [LeaveCutsCore150.beforeRow,CRTBarrel.beforeRow_old]
  simp only [LeaveWindow150.forward_append,LeaveWindow150.inverse_append,toffoliCount_append,measurementCount_append,gateSlots_append]
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

theorem beforeRow_allW {P : Wire → Prop} (s : Nat) (covered : AllW P (CRTBarrel.beforeC5 s)) :
    AllW P (LeaveCutsCore150.beforeRow s) := by
  rw [CRTBarrel.beforeRow_old,allW_append_iff] at covered
  rw [LeaveCutsCore150.beforeRow,allW_append_iff]
  exact ⟨PBScan.head_scope s covered.1,covered.2⟩

theorem beforeRow_proper (j : Fin 26) (old : ∀ g ∈ CRTBarrel.beforeC5 (start j), proper g = true) :
    ∀ g ∈ LeaveCutsCore150.beforeRow (start j), proper g = true := by
  have keep := List.all_eq_true.mpr old
  simp only [CRTBarrel.beforeRow_old,List.all_append,Bool.and_eq_true] at keep
  apply List.all_eq_true.mp
  simp only [LeaveCutsCore150.beforeRow,List.all_append,Bool.and_eq_true]
  exact ⟨PBScan.head_physical j,keep.2⟩

end ECDSAAdd.Entrant.StairPacket.PBScanRow
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveWindow150
open ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
/-- The rebuilt leave and its mirror: the Shadow7 counts with the barrel stage replaced by the CRT barrel. -/
theorem leave_metrics (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    toffoliCount (LeaveCutsCore150.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 3*Shadow7.lowsP (start j) + 100 + CRTBarrel.barrelT (start j) false ∧
    toffoliCount (LeaveCutsCore150.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 129 + CRTBarrel.barrelT (start j) true ∧
    measurementCount (LeaveCutsCore150.leave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + Shadow7.lowsP (start j) + 89 + CRTBarrel.barrelM (start j) false ∧
    measurementCount (LeaveCutsCore150.unleave j) =
      Shadow7.wpP (start j) + Shadow7.liveW (start j) + 2*Shadow7.lowsP (start j) + 60 + CRTBarrel.barrelM (start j) true ∧
    gateSlots (LeaveCutsCore150.leave j) = 6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 10*Shadow7.lowsP (start j) + 648 +
      3*Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) false ∧
    gateSlots (LeaveCutsCore150.unleave j) = 6*Shadow7.wpP (start j) + 5*Shadow7.liveW (start j) + 11*Shadow7.lowsP (start j) + 619 +
      3*Shadow7.wpP (start j + 15) + CRTBarrel.barrelSlots (start j) true := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := partsC8_counts j h0 h1
  obtain ⟨r1,r2,r3,r4,r5,r6⟩ := PBScanRow.beforeRow_counts (start j)
  obtain ⟨d1,d2,e1,e2,k1,k2⟩ := PBOps.deltas100 j h1
  dsimp only [PBOps.beforePort,PBOps.afterPort] at d1 d2 e1 e2 k1 k2
  obtain ⟨f1, f2, f3⟩ := CRTBarrel.barrel_metrics j h0 h1 false
  obtain ⟨g1, g2, g3⟩ := CRTBarrel.barrel_metrics j h0 h1 true
  simp only [LeaveCutsCore150.leave, LeaveCutsCore150.unleave, h1, ↓reduceIte, toffoliCount_append,
    measurementCount_append, gateSlots_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem leave_other (j : Fin 26) (h : ¬(j.val ≤ 24)) :
    LeaveCutsCore150.leave j = Shadow7.leaveMoveP j ∧ LeaveCutsCore150.unleave j = Shadow7.leaveMoveInvP j := by
  simp only [LeaveCutsCore150.leave, LeaveCutsCore150.unleave, h, ↓reduceIte, and_self]

/-! Coverage and physicality of the rebuilt leaves. -/

theorem barrel_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) (mir : Bool) :
    ∀ q ∈ wires (CRTBarrel.barrel (start j) mir), leaveBox (start j) q := by
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  intro q hq
  rcases CRTBarrel.barrel_wires j h0 h1 mir q hq with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩ | ht
  · have bc := Shadow7.bank_cases w1 (by omega) hi
    have r := Shadow7.rail_win w1 (by omega)
    unfold leaveBox; ((try unfold Wire at *); omega)
  · have pc := Shadow7.pool_cases (i := 17+k) w1 (by omega)
    unfold leaveBox; ((try unfold Wire at *); omega)
  · have t : ∀ q ∈ tagsP, 1556 ≤ q ∧ q ≤ 1576 := by decide
    have := t q ht; unfold leaveBox; ((try unfold Wire at *); omega)

theorem parts_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (CRTBarrel.before (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPart (start j)) := by
  have a := Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box j (by omega) (by omega))
  rw [split_ops, allW_append_iff, allW_append_iff] at a
  exact ⟨a.1, a.2.2⟩

theorem allW_swap {P : Wire → Prop} (a c : List Gate) (g g' : Gate) (sub : ∀ q ∈ g'.wires, q ∈ g.wires)
    (h : AllW P (a ++ ([g] ++ c))) : AllW P (a ++ ([g'] ++ c)) := by
  intro x hx q hq
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx) q hq
  · rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact h g (List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton_self _))) q (sub q hq)
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx)) q hq

theorem beforeC_allW {P : Wire → Prop} {s : Nat} (h : AllW P (CRTBarrel.before s)) : AllW P (CRTBarrel.beforeC s) := by
  rw [before_split] at h
  rw [beforeC_split]
  refine allW_swap _ _ _ _ (fun q hq => ?_) h
  simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  tauto

theorem afterPartC_allW {P : Wire → Prop} {s : Nat} (h : AllW P (CRTBarrel.afterPart s)) :
    AllW P (CRTBarrel.afterPartC s) := by
  rw [after_split] at h
  rw [afterPartC_split]
  refine allW_swap _ _ _ _ (fun q hq => ?_) h
  simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  tauto

theorem partsC_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (CRTBarrel.beforeC (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPartC (start j)) := by
  obtain ⟨a, b⟩ := parts_box j h0 h1
  exact ⟨beforeC_allW a, afterPartC_allW b⟩

theorem beforeC4_allW {P : Wire → Prop} {s : Nat} (h : AllW P (CRTBarrel.before s)) : AllW P (CRTBarrel.beforeC4 s) := by
  have h3 := beforeC_allW h
  rw [beforeC_cut] at h3
  rw [beforeC4_split]
  refine allW_swap _ _ _ _ (fun q hq => ?_) h3
  exact hq

theorem partsC4_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (CRTBarrel.beforeC4 (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPartC (start j)) := by
  obtain ⟨a, b⟩ := parts_box j h0 h1
  exact ⟨beforeC4_allW a, afterPartC_allW b⟩

theorem allW_swapL {P : Wire → Prop} (a c b b' : List Gate) (sub : ∀ g' ∈ b', ∀ q ∈ g'.wires, ∃ g ∈ b, q ∈ g.wires)
    (h : AllW P (a ++ (b ++ c))) : AllW P (a ++ (b' ++ c)) := by
  intro x hx q hq
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx) q hq
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨g, hg, hqg⟩ := sub x hx q hq
      exact h g (List.mem_append_right _ (List.mem_append_left _ hg)) q hqg
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx)) q hq

theorem beforeC5_cut (s : Nat) (seg : List Gate) :
    CRTBarrel.headA0 s ++ ([.pop (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++ (CRTBarrel.headA1 s ++
      ([.cx (Shadow7.sbP s + 1578) 1559] ++ (CRTBarrel.headC0 s ++ (seg ++ CRTBarrel.headC1 s))))) =
    (CRTBarrel.headA0 s ++ ([.pop (s+30) (Shadow7.sbP s + 803) (s + Shadow7.sbP s + 48)] ++ (CRTBarrel.headA1 s ++
      ([.cx (Shadow7.sbP s + 1578) 1559] ++ CRTBarrel.headC0 s)))) ++ (seg ++ CRTBarrel.headC1 s) := by
  simp only [List.append_assoc]

theorem beforeC5_allW {P : Wire → Prop} {s : Nat} (h : AllW P (CRTBarrel.before s)) : AllW P (CRTBarrel.beforeC5 s) := by
  have h4 := beforeC4_allW h
  rw [beforeC4_cut, beforeC5_cut] at h4
  rw [beforeC5_split, beforeC5_cut]
  refine allW_swapL _ _ _ _ (fun g' hg' q hq => ⟨.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P s + 6) (Shadow7.a0P s + 0),
    by simp, ?_⟩) h4
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl <;> simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢ <;> tauto

theorem partsC5_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (CRTBarrel.beforeC5 (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPartC (start j)) := by
  obtain ⟨a, b⟩ := parts_box j h0 h1
  exact ⟨beforeC5_allW a, afterPartC_allW b⟩

theorem allW_drop {P : Wire → Prop} (a b c : List Gate) (h : AllW P (a ++ (b ++ c))) : AllW P (a ++ c) := by
  intro x hx q hq
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx) q hq
  · exact h x (List.mem_append_right _ (List.mem_append_right _ hx)) q hq

theorem afterPartC2_allW {P : Wire → Prop} {s : Nat} (h : AllW P (CRTBarrel.afterPart s)) :
    AllW P (CRTBarrel.afterPartC2 s) := by
  have h2 := afterPartC_allW h
  rw [afterPartC_split, tailD_cut] at h2
  simp only [List.append_assoc] at h2
  rw [afterPartC2_split]
  exact allW_drop _ _ _ h2

theorem partsC6_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (CRTBarrel.beforeC5 (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPartC2 (start j)) := by
  obtain ⟨a, b⟩ := parts_box j h0 h1
  exact ⟨beforeC5_allW a, afterPartC2_allW b⟩

theorem allW_swap2 {P : Wire → Prop} (a b c : List Gate) (g1 g1' g2 g2' : Gate)
    (sub1 : ∀ q ∈ g1'.wires, q ∈ g1.wires) (sub2 : ∀ q ∈ g2'.wires, q ∈ g2.wires)
    (h : AllW P (a ++ ([g1] ++ (b ++ ([g2] ++ c))))) : AllW P (a ++ ([g1'] ++ (b ++ ([g2'] ++ c)))) := by
  intro x hx q hq
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl | hx | rfl | hx
  · exact h x (by simp [hx]) q hq
  · exact h g1 (by simp) q (sub1 q hq)
  · exact h x (by simp [hx]) q hq
  · exact h g2 (by simp) q (sub2 q hq)
  · exact h x (by simp [hx]) q hq

theorem afterPartC3_allW {P : Wire → Prop} {s : Nat} (h : AllW P (CRTBarrel.afterPart s)) :
    AllW P (CRTBarrel.afterPartC3 s) := by
  have h2 := afterPartC2_allW h
  rw [afterPartC2_split, tailE_cut] at h2
  rw [afterPartC3_split]
  have sub : ∀ (g : Gate), g = .make 1558 (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559 ∨ g = .pop 1558 (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559 →
      ∀ q ∈ (GateMirror.Gate.cx (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559).wires, q ∈ g.wires := by
    intro g hg q hq
    rcases hg with rfl | rfl <;> simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢ <;>
      tauto
  have h3 := allW_swap2 (CRTBarrel.tailD0 s ++ (CRTBarrel.tailD1 s ++ ([.cx (Shadow7.e0P s + 4) 1559] ++ CRTBarrel.tailE0 s)))
    (CRTBarrel.chainMid s) (CRTBarrel.tailE1 s) (.make 1558 (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559) (.cx (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559) (.pop 1558 (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559)
    (.cx (Shadow7.a0P s + Shadow7.lowsP s - 1) 1559) (sub _ (Or.inl rfl)) (sub _ (Or.inr rfl)) (by simpa only [List.append_assoc] using h2)
  simpa only [List.append_assoc] using h3

theorem partsC8_box (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    AllW (leaveBox (start j)) (LeaveCutsCore150.beforeRow (start j)) ∧ AllW (leaveBox (start j)) (CRTBarrel.afterPartC3 (start j)) := by
  obtain ⟨a, b⟩ := parts_box j h0 h1
  exact ⟨PBScanRow.beforeRow_allW _ (beforeC5_allW a), afterPartC3_allW b⟩

theorem partsPB_box (j : Fin 26) (h0 : 0≤j.val) (h1 : j.val≤24) :
    AllW (leaveBox (start j)) (PBOps.before100 (start j)) ∧
    AllW (leaveBox (start j)) (PBOps.after100 (start j)) := by
  obtain ⟨a,b⟩ := partsC8_box j h0 h1
  exact ⟨PBScope100.before_allW j h1 a (PBScope100.flag_box j h1).1,
    PBScope100.after_allW j h1 b (fun q hq => (PBScope100.sources_box j h1 q hq).1)⟩

theorem leave_eq (j : Fin 26) (_h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    LeaveCutsCore150.leave j = GateMirror.forward (PBOps.before100 (start j)) ++ CRTBarrel.barrel (start j) false ++
      GateMirror.forward (PBOps.after100 (start j)) ∧
    LeaveCutsCore150.unleave j = inverse (PBOps.after100 (start j)) ++ CRTBarrel.barrel (start j) true ++
      inverse (PBOps.before100 (start j)) := by
  simp only [LeaveCutsCore150.leave, LeaveCutsCore150.unleave, h1, ↓reduceIte, and_self]

/-- `WindowCovered.leaveBox_dom` through block 22 (start 405), as `WindowCovered7.leaveBox_dom405`. -/
theorem cov_of_box {P : Program} {s : Nat} (lo : 45 ≤ s) (hi : s ≤ 405) (h : ∀ q ∈ wires P, leaveBox s q) :
    WindowCovered.CoveredW P := by
  intro q hq
  have b := h q hq
  rw [WindowCovered.dom_iff]; unfold leaveBox at b; omega

theorem leave_cov (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    WindowCovered.CoveredW (LeaveCutsCore150.leave j) ∧ WindowCovered.CoveredW (LeaveCutsCore150.unleave j) := by
  obtain ⟨pb, pa⟩ := partsPB_box j h0 h1
  obtain ⟨bf, bi⟩ := allW_programs pb
  obtain ⟨af, ai⟩ := allW_programs pa
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  have cbf := cov_of_box w1 (by omega) bf
  have caf := cov_of_box w1 (by omega) af
  have cbi := cov_of_box w1 (by omega) bi
  have cai := cov_of_box w1 (by omega) ai
  have cb0 := cov_of_box w1 (by omega) (barrel_box j h0 h1 false)
  have cb1 := cov_of_box w1 (by omega) (barrel_box j h0 h1 true)
  rw [(leave_eq j h0 h1).1, (leave_eq j h0 h1).2]
  exact ⟨WindowCovered.appW (WindowCovered.appW cbf cb0) caf, WindowCovered.appW (WindowCovered.appW cai cb1) cbi⟩

def forward45plus1 (d : Bool) : Program := forwardW LeaveCutsCore150.params d first WindowParams7.rest7

def reverse45plus1 (d : Bool) : Program := reverseW LeaveCutsCore150.params d first WindowParams7.rest7

theorem assembly (d : Bool) : forward45plus1 d = forwardW LeaveCutsCore150.params d first WindowParams7.rest7 := rfl

theorem unwind_assembly (d : Bool) : reverse45plus1 d = reverseW LeaveCutsCore150.params d first WindowParams7.rest7 := rfl

end ECDSAAdd.Entrant.StairPacket.LeaveWindow150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBReplace
open Partial GateMirror CRTBarrel.LeaveSplice
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem replace10 (a0 b1 a1 b2 a2 b3 a3 b4 a4 b5 a5 b6 a6 b7 a7 b8 a8 b9 a9 b10 a10 : List Gate) (f0 r0 f1 r1 f2 r2 f3 r3 f4 r4 f5 r5 f6 r6 f7 r7 f8 r8 f9 r9 f10 r10 : Program) (s : State)
    (v : Valid s (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8 ++ (b9 ++ (a9 ++ (b10 ++ (a10))))))))))))))))))))))
    (same0 : ∀ t, run f0 t s = run (GateMirror.forward a0) [] s)
    (back0 : ∀ t, run r0 t (run (GateMirror.forward a0) [] s) = s)
    (same1 : ∀ t, run f1 t (run (GateMirror.forward (a0)) [] s) = run (GateMirror.forward b1) [] (run (GateMirror.forward (a0)) [] s))
    (back1 : ∀ t, run r1 t (run (GateMirror.forward b1) [] (run (GateMirror.forward (a0)) [] s)) = (run (GateMirror.forward (a0)) [] s))
    (same2 : ∀ t, run f2 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s) = run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s))
    (back2 : ∀ t, run r2 t (run (GateMirror.forward b2) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1)))) [] s))
    (same3 : ∀ t, run f3 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s) = run (GateMirror.forward b3) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s))
    (back3 : ∀ t, run r3 t (run (GateMirror.forward b3) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2)))))) [] s))
    (same4 : ∀ t, run f4 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s) = run (GateMirror.forward b4) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s))
    (back4 : ∀ t, run r4 t (run (GateMirror.forward b4) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3)))))))) [] s))
    (same5 : ∀ t, run f5 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s) = run (GateMirror.forward b5) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s))
    (back5 : ∀ t, run r5 t (run (GateMirror.forward b5) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4)))))))))) [] s))
    (same6 : ∀ t, run f6 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s) = run (GateMirror.forward b6) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s))
    (back6 : ∀ t, run r6 t (run (GateMirror.forward b6) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5)))))))))))) [] s))
    (same7 : ∀ t, run f7 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s) = run (GateMirror.forward b7) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s))
    (back7 : ∀ t, run r7 t (run (GateMirror.forward b7) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6)))))))))))))) [] s))
    (same8 : ∀ t, run f8 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s) = run (GateMirror.forward b8) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s))
    (back8 : ∀ t, run r8 t (run (GateMirror.forward b8) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7)))))))))))))))) [] s))
    (same9 : ∀ t, run f9 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8)))))))))))))))))) [] s) = run (GateMirror.forward b9) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8)))))))))))))))))) [] s))
    (back9 : ∀ t, run r9 t (run (GateMirror.forward b9) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8)))))))))))))))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8)))))))))))))))))) [] s))
    (same10 : ∀ t, run f10 t (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8 ++ (b9 ++ (a9)))))))))))))))))))) [] s) = run (GateMirror.forward b10) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8 ++ (b9 ++ (a9)))))))))))))))))))) [] s))
    (back10 : ∀ t, run r10 t (run (GateMirror.forward b10) [] (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8 ++ (b9 ++ (a9)))))))))))))))))))) [] s)) = (run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8 ++ (b9 ++ (a9)))))))))))))))))))) [] s))
    : (∀ m, run (f0 ++ f1 ++ GateMirror.forward a1 ++ f2 ++ GateMirror.forward a2 ++ f3 ++ GateMirror.forward a3 ++ f4 ++ GateMirror.forward a4 ++ f5 ++ GateMirror.forward a5 ++ f6 ++ GateMirror.forward a6 ++ f7 ++ GateMirror.forward a7 ++ f8 ++ GateMirror.forward a8 ++ f9 ++ GateMirror.forward a9 ++ f10 ++ GateMirror.forward a10) m s = run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8 ++ (b9 ++ (a9 ++ (b10 ++ (a10)))))))))))))))))))))) m s) ∧
      (∀ m n, run (GateMirror.inverse a10 ++ r10 ++ GateMirror.inverse a9 ++ r9 ++ GateMirror.inverse a8 ++ r8 ++ GateMirror.inverse a7 ++ r7 ++ GateMirror.inverse a6 ++ r6 ++ GateMirror.inverse a5 ++ r5 ++ GateMirror.inverse a4 ++ r4 ++ GateMirror.inverse a3 ++ r3 ++ GateMirror.inverse a2 ++ r2 ++ GateMirror.inverse a1 ++ r1 ++ r0) n (run (f0 ++ f1 ++ GateMirror.forward a1 ++ f2 ++ GateMirror.forward a2 ++ f3 ++ GateMirror.forward a3 ++ f4 ++ GateMirror.forward a4 ++ f5 ++ GateMirror.forward a5 ++ f6 ++ GateMirror.forward a6 ++ f7 ++ GateMirror.forward a7 ++ f8 ++ GateMirror.forward a8 ++ f9 ++ GateMirror.forward a9 ++ f10 ++ GateMirror.forward a10) m s) = s) := by
  simp only [CRTBarrel.FlagCut.run_nil_append] at same1 back1 same2 back2 same3 back3 same4 back4 same5 back5 same6 back6 same7 back7 same8 back8 same9 back9 same10 back10
  obtain ⟨va0, w0⟩ := v.parts
  obtain ⟨vb1, w1⟩ := w0.parts
  obtain ⟨va1, w2⟩ := w1.parts
  obtain ⟨vb2, w3⟩ := w2.parts
  obtain ⟨va2, w4⟩ := w3.parts
  obtain ⟨vb3, w5⟩ := w4.parts
  obtain ⟨va3, w6⟩ := w5.parts
  obtain ⟨vb4, w7⟩ := w6.parts
  obtain ⟨va4, w8⟩ := w7.parts
  obtain ⟨vb5, w9⟩ := w8.parts
  obtain ⟨va5, w10⟩ := w9.parts
  obtain ⟨vb6, w11⟩ := w10.parts
  obtain ⟨va6, w12⟩ := w11.parts
  obtain ⟨vb7, w13⟩ := w12.parts
  obtain ⟨va7, w14⟩ := w13.parts
  obtain ⟨vb8, w15⟩ := w14.parts
  obtain ⟨va8, w16⟩ := w15.parts
  obtain ⟨vb9, w17⟩ := w16.parts
  obtain ⟨va9, w18⟩ := w17.parts
  obtain ⟨vb10, w19⟩ := w18.parts
  have va10 := w19
  have emitted (m : List Bool) : run (f0 ++ f1 ++ GateMirror.forward a1 ++ f2 ++ GateMirror.forward a2 ++ f3 ++ GateMirror.forward a3 ++ f4 ++ GateMirror.forward a4 ++ f5 ++ GateMirror.forward a5 ++ f6 ++ GateMirror.forward a6 ++ f7 ++ GateMirror.forward a7 ++ f8 ++ GateMirror.forward a8 ++ f9 ++ GateMirror.forward a9 ++ f10 ++ GateMirror.forward a10) m s = (run (GateMirror.forward a10) [] (run (GateMirror.forward b10) [] (run (GateMirror.forward a9) [] (run (GateMirror.forward b9) [] (run (GateMirror.forward a8) [] (run (GateMirror.forward b8) [] (run (GateMirror.forward a7) [] (run (GateMirror.forward b7) [] (run (GateMirror.forward a6) [] (run (GateMirror.forward b6) [] (run (GateMirror.forward a5) [] (run (GateMirror.forward b5) [] (run (GateMirror.forward a4) [] (run (GateMirror.forward b4) [] (run (GateMirror.forward a3) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward a2) [] (run (GateMirror.forward b2) [] (run (GateMirror.forward a1) [] (run (GateMirror.forward b1) [] (run (GateMirror.forward a0) [] s))))))))))))))))))))) := by
    simp only [run_append, run_take, same0, same1, va1.default_run, same2, va2.default_run, same3, va3.default_run, same4, va4.default_run, same5, va5.default_run, same6, va6.default_run, same7, va7.default_run, same8, va8.default_run, same9, va9.default_run, same10, va10.default_run]
  have old (m : List Bool) : run (GateMirror.forward (a0 ++ (b1 ++ (a1 ++ (b2 ++ (a2 ++ (b3 ++ (a3 ++ (b4 ++ (a4 ++ (b5 ++ (a5 ++ (b6 ++ (a6 ++ (b7 ++ (a7 ++ (b8 ++ (a8 ++ (b9 ++ (a9 ++ (b10 ++ (a10)))))))))))))))))))))) m s = (run (GateMirror.forward a10) [] (run (GateMirror.forward b10) [] (run (GateMirror.forward a9) [] (run (GateMirror.forward b9) [] (run (GateMirror.forward a8) [] (run (GateMirror.forward b8) [] (run (GateMirror.forward a7) [] (run (GateMirror.forward b7) [] (run (GateMirror.forward a6) [] (run (GateMirror.forward b6) [] (run (GateMirror.forward a5) [] (run (GateMirror.forward b5) [] (run (GateMirror.forward a4) [] (run (GateMirror.forward b4) [] (run (GateMirror.forward a3) [] (run (GateMirror.forward b3) [] (run (GateMirror.forward a2) [] (run (GateMirror.forward b2) [] (run (GateMirror.forward a1) [] (run (GateMirror.forward b1) [] (run (GateMirror.forward a0) [] s))))))))))))))))))))) := by
    simp only [forward_app, run_append, run_take, va0.default_run, vb1.default_run, va1.default_run, vb2.default_run, va2.default_run, vb3.default_run, va3.default_run, vb4.default_run, va4.default_run, vb5.default_run, va5.default_run, vb6.default_run, va6.default_run, vb7.default_run, va7.default_run, vb8.default_run, va8.default_run, vb9.default_run, va9.default_run, vb10.default_run, va10.default_run]
  refine ⟨fun m => (emitted m).trans (old m).symm, ?_⟩
  intro m n
  rw [emitted]
  have undoA10 (l : List Bool) := va10.undo_run [] l
  have undoA9 (l : List Bool) := va9.undo_run [] l
  have undoA8 (l : List Bool) := va8.undo_run [] l
  have undoA7 (l : List Bool) := va7.undo_run [] l
  have undoA6 (l : List Bool) := va6.undo_run [] l
  have undoA5 (l : List Bool) := va5.undo_run [] l
  have undoA4 (l : List Bool) := va4.undo_run [] l
  have undoA3 (l : List Bool) := va3.undo_run [] l
  have undoA2 (l : List Bool) := va2.undo_run [] l
  have undoA1 (l : List Bool) := va1.undo_run [] l
  simp only [run_append, run_take, undoA10, back10, undoA9, back9, undoA8, back8, undoA7, back7, undoA6, back6, undoA5, back5, undoA4, back4, undoA3, back3, undoA2, back2, undoA1, back1]
  exact back0 _
end ECDSAAdd.Entrant.StairPacket.PBReplace
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBReceiver
open Arithmetic Partial GateMirror CRTBarrel DeadJoin DI7Affine
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Local receiver pair for one ORIGINAL prepared pop boundary. The retained
make/pop parts elsewhere can be replaced simultaneously by PBReplace.replace10. -/
theorem receiver_pair (x y t : Wire) (c : Bool) (qs : List Wire) (u : State)
    (v : CRTBarrel.LeaveSplice.Valid u [.pop x y t])
    (away : ∀ q∈qs,q≠t) (rel : eval (c,t::qs) u.basis=false) :
    (∀ m,run (GateMirror.forward (receiver t c qs)) m u=
      run (GateMirror.forward [.pop x y t]) [] u) ∧
    (∀ n,run (GateMirror.inverse (receiver t c qs)) n
      (run (GateMirror.forward [.pop x y t]) [] u)=u) := by
  have raw : RawValid u ([] ++ (Gate.pop x y t :: [])) :=
    ⟨v.physical,v.prepared,v.ready⟩
  obtain ⟨w,e⟩ := raw_replace_pop [] [] x y t c qs u raw away
    (by simpa only [GateMirror.forward,List.map_nil,run] using rel)
  simp only [List.nil_append,List.append_nil] at w e
  have shape : clear c qs t = receiver t c qs := rfl
  rw [shape] at w e
  refine ⟨fun m => (e m).trans (v.default_run m),fun n => ?_⟩
  have back := w.undo_run [] n
  rw [e []] at back
  exact back

/-- Prefix/suffix splits used by the new 10-middle simultaneous splice. -/
def latchHead (s : Nat) := (headA1 s).takeWhile (fun g => g != latchPop s)
def latchTail (s : Nat) := (headA1 s).drop ((latchHead s).length+1)
def selectorHead (s : Nat) := (tailD1 s).takeWhile (fun g => g != selectorPop s)
def selectorTail (s : Nat) := (tailD1 s).drop ((selectorHead s).length+1)

theorem latch_source_split : ∀ j : Fin 26,j.val≤24 → headA1 (start j)=
    latchHead (start j) ++ (latchPop (start j)::latchTail (start j)) := by decide +kernel

theorem selector_source_split : ∀ j : Fin 26,j.val≤24 → tailD1 (start j)=
    selectorHead (start j) ++ (selectorPop (start j)::selectorTail (start j)) := by decide +kernel

theorem latch_prefix_shape : ∀ j : Fin 26,j.val≤24 → latchPre (start j)=
    headA0 (start j) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803)
      (start j+Shadow7.sbP (start j)+48)] ++ latchHead (start j)) := by decide +kernel

theorem selector_prefix_shape : ∀ j : Fin 26,j.val≤24 → selectorPre (start j)=
    tailD0 (start j) ++ (pairGM false 1614 (Shadow7.a0P (start j)+16)
      (Shadow7.bankW (start j) 16) ++ selectorHead (start j)) := by decide +kernel

theorem latch_relation (j : Fin 26) (hi : j.val≤24) (s : State)
    (zero : s.basis 1556=false) :
    eval (true,[1571,1556]) (run (GateMirror.forward (latchPre (start j))) [] s).basis=false := by
  have p := pull_sound (latchPre (start j)) (true,[1571,1556]) (false,[1556]) (latch_pull j hi) s
  rw [←p]
  simpa [eval,parity] using zero

theorem selector_relation (j : Fin 26) (hi : j.val≤24) (s : State)
    (zero : s.basis (Shadow7.e0P (start j)+7)=false) :
    eval (selectorExpr (start j))
      (run (GateMirror.forward (selectorPre (start j))) []
        (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) []
          (run (GateMirror.forward (beforePort (start j))) [] s))).basis=false := by
  have p := pull_sound (beforePort (start j)) (selectorExpr (start j))
    (false,[Shadow7.e0P (start j)+7]) (selector_before_pull j hi) s
  have rel : eval (selectorExpr (start j))
      (run (GateMirror.forward (beforePort (start j))) [] s).basis=false := by
    rw [←p]
    simpa [eval,parity] using zero
  have a := pull_sound (selectorPre (start j)) (selectorExpr (start j))
    (selectorExpr (start j)) (selector_after_pull j hi)
    (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) []
      (run (GateMirror.forward (beforePort (start j))) [] s))
  rw [←a,expr_kept _ _ (selector_barrel_quiet j hi)]
  exact rel
theorem before100_decomposed : ∀ j : Fin 26,j.val≤24 → PBOps.before100 (start j)=
    PBScan.head (start j) ++ (.pop (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48) ::
    (latchHead (start j) ++ (receiver 1571 true [1556] ++ (latchTail (start j) ++
    (.cx (Shadow7.sbP (start j)+1578) 1559 :: (headC0 (start j) ++
    (.make (tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6) ::
     .cx (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)) :: headC1 (start j)))))))) := by decide +kernel

theorem after100_decomposed : ∀ j : Fin 26,j.val≤24 → PBOps.after100 (start j)=
    tailD0 (start j) ++ (selectorHead (start j) ++ (receiver 1565 false (selectorSources (start j)) ++
    (selectorTail (start j) ++ (.cx (Shadow7.e0P (start j)+4) 1559 :: (tailE0 (start j) ++
    (.cx (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559 :: (chainMid (start j) ++
    (.cx (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559 :: tailE1 (start j))))))))) := by decide +kernel

end ECDSAAdd.Entrant.StairPacket.PBReceiver
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBScan
open Arithmetic GateMirror Partial CRTBarrel
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run
theorem coordinates : ∀ j : Fin 26, j.val ≤ 24 →
    let L := IntegerPacket.ports (Shadow7.shape j) 15
    cutoff j + 17 < L.a.length ∧ cutoff j + 17 < L.b.length ∧
    windowNet j L.previous = orient (start j) ∧
    windowNet j (L.a.getD (cutoff j+16) 0) = left15 (start j) (cutoff j) ∧
    windowNet j (L.b.getD (cutoff j+16) 0) = right15 (cutoff j) ∧
    windowNet j (L.b.getD (cutoff j+17) 0) = right16 (cutoff j) := by
  decide +kernel

/-- The first 50 source gates leave all four row-15 contract wires alone. -/
theorem prefix_checked : ∀ j : Fin 26, j.val ≤ 24 →
    (scanPre (start j) (cutoff j)).all (fun gate => decide
      (target gate ≠ orient (start j) ∧ target gate ≠ left15 (start j) (cutoff j) ∧
       target gate ≠ right15 (cutoff j) ∧ target gate ≠ right16 (cutoff j))) = true := by
  decide +kernel

theorem geometry : ∀ j : Fin 26, j.val ≤ 24 →
    orient (start j) ≠ right15 (cutoff j) ∧
    left15 (start j) (cutoff j) ≠ right15 (cutoff j) ∧
    left15 (start j) (cutoff j) ≠ right16 (cutoff j) ∧
    right15 (cutoff j) ≠ right16 (cutoff j) := by
  decide +kernel

theorem frame (gs : List Gate) (q : Wire) (free : ∀ gate ∈ gs, target gate ≠ q)
    (s : State) (m : List Bool) :
    (run (GateMirror.forward gs) m s).basis q = s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [LeaveJ7.dest_forward]
  rintro hit
  obtain ⟨gate, member, same⟩ := List.mem_map.mp hit
  exact free gate member same

theorem prefix_incoming (j : Fin 26) (hi : j.val ≤ 24) (s : State)
    (input : DI7Scan.Incoming (orient (start j)) (left15 (start j) (cutoff j))
      (right15 (cutoff j)) (right16 (cutoff j)) s.basis) :
    DI7Scan.Incoming (orient (start j)) (left15 (start j) (cutoff j))
      (right15 (cutoff j)) (right16 (cutoff j))
      (run (GateMirror.forward (scanPre (start j) (cutoff j))) [] s).basis := by
  have checked := List.all_eq_true.mp (prefix_checked j hi)
  have g := frame _ (orient (start j))
    (fun gate member => (of_decide_eq_true (checked gate member)).1) s []
  have a := frame _ (left15 (start j) (cutoff j))
    (fun gate member => (of_decide_eq_true (checked gate member)).2.1) s []
  have b := frame _ (right15 (cutoff j))
    (fun gate member => (of_decide_eq_true (checked gate member)).2.2.1) s []
  have t := frame _ (right16 (cutoff j))
    (fun gate member => (of_decide_eq_true (checked gate member)).2.2.2) s []
  simpa only [DI7Scan.Incoming, g, a, b, t] using input

/-- Generic numeric-to-physical row-15 bridge, before any scan gates run. -/
theorem incoming_rails (j : Fin 26) (hi : j.val ≤ 24) (s : State)
    (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) s.basis)
    (small : u < 2^(cutoff j+16)) (tight : u+v < 2^(cutoff j+17))
    (falseBound : G = false → u+v < 2^(cutoff j+16)) :
    DI7Scan.Incoming (orient (start j)) (left15 (start j) (cutoff j))
      (right15 (cutoff j)) (right16 (cutoff j)) s.basis := by
  let L := IntegerPacket.ports (Shadow7.shape j) 15
  obtain ⟨la, lb, cg, ca, cb, ct⟩ := coordinates j hi
  have previous : mappedBasis j s.basis L.previous = G := by
    have eq := ready.2.2.1
    cases G <;> exact eq
  have raw := DI7Scan.incoming_of_signed_words L G sg u v (cutoff j+16)
    (mappedBasis j s.basis) ready.1 ready.2.1 previous
    (by simpa only [Nat.add_assoc] using la) (by simpa only [Nat.add_assoc] using lb)
    small (by simpa only [Nat.add_assoc] using tight) falseBound
  change DI7Scan.Incoming (windowNet j L.previous)
    (windowNet j (L.a.getD (cutoff j+16) 0))
    (windowNet j (L.b.getD (cutoff j+16) 0))
    (windowNet j (L.b.getD ((cutoff j+16)+1) 0)) s.basis at raw
  change windowNet j L.previous = orient (start j) at cg
  change windowNet j (L.a.getD (cutoff j+16) 0) = left15 (start j) (cutoff j) at ca
  change windowNet j (L.b.getD (cutoff j+16) 0) = right15 (cutoff j) at cb
  change windowNet j (L.b.getD (cutoff j+17) 0) = right16 (cutoff j) at ct
  rw [show (cutoff j+16)+1 = cutoff j+17 by omega, cg, ca, cb, ct] at raw
  exact raw

def finalFlags (z : SkywalkNat.State) (g sg : Bool) : Bool × Bool :=
  SharedSigned.flags g sg (SkywalkTrace.trace 15 (SkywalkRails.encode g sg z.u z.v))

/-- Exact admitted arithmetic input: finalFlags is definitionally Main's
Admission.flags, but this helper has no Main dependency. -/
theorem incoming_admitted (j : Fin 26) (hi : j.val ≤ 24) (s : State)
    (z : SkywalkNat.State) (g sg : Bool)
    (small : Shadow7.SmallIfFar (cutoff j) 15 z) (odd : z.v % 2 = 1)
    (ready : let a := SkywalkNat.step^[15] (Shadow.reduced (cutoff j) 15 z)
      Shadow7.onRails j 15 (SkywalkRails.encode (finalFlags z g sg).1 (finalFlags z g sg).2 a.u a.v) s.basis) :
    DI7Scan.Incoming (orient (start j)) (left15 (start j) (cutoff j))
      (right15 (cutoff j)) (right16 (cutoff j)) s.basis := by
  have row := (LeaveShadowRails.inputRow15 (cutoff j) z small).1
  have tight := LeaveShadowRails.inputTight17 (cutoff j) z small
  have upper := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (cutoff j))).mp tight
  apply incoming_rails j hi s _ _ (finalFlags z g sg).1 (finalFlags z g sg).2 ready
  · simpa only [← pow_add, Nat.add_comm 16 (cutoff j)] using row
  · simpa only [← pow_add, Nat.add_comm 17 (cutoff j)] using upper
  · exact fun h => PBNumeric.scan_false_sum_lt (cutoff j) z small odd g sg h


theorem head_same (j : Fin 26) (hi : j.val ≤ 24) (s : State)
    (input : DI7Scan.Incoming (orient (start j)) (left15 (start j) (cutoff j))
      (right15 (cutoff j)) (right16 (cutoff j)) s.basis) (m : List Bool) :
    run (GateMirror.forward (head (start j))) m s =
      run (GateMirror.forward (CRTBarrel.headA0 (start j))) [] s := by
  obtain ⟨gb, ab, atop, bt⟩ := geometry j hi
  rw [head_split]
  simp only [head, forward_app, run_append, run_take, List.drop_nil]
  have plainPre : ∀ n, run (GateMirror.forward (scanPre (start j) (cutoff j))) n s =
      run (GateMirror.forward (scanPre (start j) (cutoff j))) [] s := by
    intro n
    have eq := run_take (GateMirror.forward (scanPre (start j) (cutoff j))) n s
    have zero : measurementCount (GateMirror.forward (scanPre (start j) (cutoff j))) = 0 := by
      simp [scanPre, Shadow7.fix0P, GateMirror.forward, front, measurementCount]
    simpa only [zero, List.take_zero] using eq.symm
  rw [plainPre]
  rw [DI7Scan.microblock_eq _ _ _ _ _ _ gb atop bt (prefix_incoming j hi s input)]
  have plainPost (u : State) (tape : List Bool) :
      run (GateMirror.forward ((CRTBarrel.headA0 (start j)).drop 53)) tape u =
      run (GateMirror.forward ((CRTBarrel.headA0 (start j)).drop 53)) [] u := by
    have eq := run_take (GateMirror.forward ((CRTBarrel.headA0 (start j)).drop 53)) tape u
    have zero : measurementCount (GateMirror.forward ((CRTBarrel.headA0 (start j)).drop 53)) = 0 := by rfl
    simpa only [zero,List.take_zero] using eq.symm
  exact plainPost _ _

theorem head_valid (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    CRTBarrel.LeaveSplice.Valid s (head (start j)) := by
  have phys : ∀ gate ∈ head (start j), proper gate = true :=
    fun gate member => List.all_eq_true.mp (head_physical j) gate member
  refine ⟨phys, all_prepared _ s phys ?_, ready_plain _ ?_ s⟩
  · intro m
    have eq := run_take (GateMirror.forward (head (start j))) m s
    rw [head_zero, List.take_zero] at eq
    rw [← eq]
    exact no_phase _ s
  · simp [head, scanPre, CRTBarrel.headA0, Shadow7.fix0P, DI7Scan.replacement, plainGate]

theorem admitted_same {j : Fin 26} (hi : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : LeaveJ7.Admission.Inputs j s z g sg) (m : List Bool) :
    run (GateMirror.forward (head (start j))) m s =
      run (GateMirror.forward (CRTBarrel.headA0 (start j))) [] s := by
  apply head_same j hi s
  exact incoming_admitted j hi s z g sg h.farSmall h.odd h.ready

theorem head_back (j : Fin 26) (hi : j.val ≤ 24) (s : State)
    (input : DI7Scan.Incoming (orient (start j)) (left15 (start j) (cutoff j))
      (right15 (cutoff j)) (right16 (cutoff j)) s.basis) (m : List Bool) :
    run (GateMirror.inverse (head (start j))) m
      (run (GateMirror.forward (CRTBarrel.headA0 (start j))) [] s) = s := by
  rw [← head_same j hi s input []]
  exact (head_valid j hi s).undo_run [] m

theorem admitted_back {j : Fin 26} (hi : j.val ≤ 24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : LeaveJ7.Admission.Inputs j s z g sg) (m : List Bool) :
    run (GateMirror.inverse (head (start j))) m
      (run (GateMirror.forward (CRTBarrel.headA0 (start j))) [] s) = s := by
  apply head_back j hi s
  exact incoming_admitted j hi s z g sg h.farSmall h.odd h.ready



end ECDSAAdd.Entrant.StairPacket.PBScan
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.PBReceiverFast
open ECDSAAdd Arithmetic Partial GateMirror CRTBarrel

private structure Pair (old forward reverse : Program) (u : State) : Prop where
  fwd : ∀ m, run forward m u = run old [] u
  back : ∀ n, run reverse n (run old [] u) = u

private theorem transportPair (old forward reverse : Program) {u v : State}
    (e : u = v) (p : Pair old forward reverse u) : Pair old forward reverse v := by
  cases e
  exact p

private theorem prefix1 (j : Fin 26) :
    (headA0 (start j)) = (headA0 (start j)) := by
  rfl

private theorem state1 (j : Fin 26) (s : State) :
    run (GateMirror.forward ((headA0 (start j)))) [] s = run (GateMirror.forward ((headA0 (start j)))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix1 j)

private theorem prefix2 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)))) = PBReceiver.latchPre (start j) := by
  simp only [PBReceiver.latch_prefix_shape j hi,List.cons_append,List.nil_append]

private theorem state2 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)))))) [] s = run (GateMirror.forward (PBReceiver.latchPre (start j))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix2 j hi)

private theorem prefix3 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)))))) = (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((headA1 (start j)))) := by
  simp only [PBReceiver.latch_source_split j hi,List.cons_append,List.nil_append]

private theorem state3 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)))))))) [] s = run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((headA1 (start j)))))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix3 j hi)

private theorem prefix4 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)))))))) = (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((headA1 (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)))))) := by
  simp only [PBReceiver.latch_source_split j hi,List.append_assoc,List.cons_append,List.nil_append]

private theorem state4 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)))))))))) [] s = run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((headA1 (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)))))))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix4 j hi)

private theorem prefix5 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)))))))))) = CRTBarrel.before (start j) := by
  simp only [PBReceiver.latch_source_split j hi,FlagCut5.before_split5,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero]

private theorem state5 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)))))))))))) [] s = run (GateMirror.forward (CRTBarrel.before (start j))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix5 j hi)

private theorem prefix6 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)))))))))))) = headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j))))))))) := by
  simp only [PBReceiver.latch_source_split j hi,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero]

private theorem state6 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)))))))))))))) [] s = run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j))))))))))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix6 j hi)

private theorem prefix7 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)))))))))))))) = PBReceiver.beforePort (start j) ++ (Shadow7.leaveBarrel (start j) ++ PBReceiver.selectorPre (start j)) := by
  simp only [PBReceiver.latch_source_split j hi,PBReceiver.selector_prefix_shape j hi,PBReceiver.beforePort,FlagCut5.before_split5,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero]

private theorem state7 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)))))))))))))))) [] s = run (GateMirror.forward (PBReceiver.selectorPre (start j))) [] (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (PBReceiver.beforePort (start j))) [] s)) := by
  rw [prefix7 j hi,FlagCut.run_nil_append,FlagCut.run_nil_append]

private theorem prefix8 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)))))))))))))))) = headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))) := by
  simp only [PBReceiver.latch_source_split j hi,PBReceiver.selector_source_split j hi,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero]

private theorem state8 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)))))))))))))))))) [] s = run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix8 j hi)

private theorem prefix9 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)) ++ ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] ++ ((tailE0 (start j)))))))))))))))))) = headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))) := by
  simp only [PBReceiver.latch_source_split j hi,PBReceiver.selector_source_split j hi,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero]

private theorem state9 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)) ++ ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] ++ ((tailE0 (start j)))))))))))))))))))) [] s = run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix9 j hi)

private theorem prefix10 (j : Fin 26) (hi : j.val ≤ 24) :
    (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)) ++ ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] ++ ((tailE0 (start j)) ++ ([.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559] ++ ((chainMid (start j)))))))))))))))))))) = headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))) := by
  simp only [PBReceiver.latch_source_split j hi,PBReceiver.selector_source_split j hi,List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero]

private theorem state10 (j : Fin 26) (hi : j.val ≤ 24) (s : State) :
    run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)) ++ ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] ++ ((tailE0 (start j)) ++ ([.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559] ++ ((chainMid (start j)))))))))))))))))))))) [] s = run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s := by
  exact congrArg (fun p : List Gate => run (GateMirror.forward p) [] s) (prefix10 j hi)

private theorem callback1 (j : Fin 26) (u : State)
    (ha : (start j+30) ≠ (start j+Shadow7.sbP (start j)+48)) (hb : (Shadow7.sbP (start j)+803) ≠ (start j+Shadow7.sbP (start j)+48)) (hv : u.basis (start j+Shadow7.sbP (start j)+48) = (u.basis (start j+30) && u.basis (Shadow7.sbP (start j)+803))) :
    Pair (GateMirror.forward ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)])) ([GateMirror.erase (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)]) ([.CCX (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)]) (u) := by
  exact ⟨fun m => FlagCut4.erase_ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48) u ha hb hv m, fun n => FlagCut4.ccx_twice (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48) u ha hb n⟩

private theorem callback3 (j : Fin 26) (u : State)
    (apart : (Shadow7.sbP (start j)+1578) ≠ 1559) (imp : u.basis (Shadow7.sbP (start j)+1578) = true → u.basis (Shadow7.sbP (start j)+1577) = true) :
    Pair (GateMirror.forward ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559])) ([.CX (Shadow7.sbP (start j)+1578) 1559]) ([.CX (Shadow7.sbP (start j)+1578) 1559]) (u) := by
  exact ⟨fun m => FlagCut.ccx_cx (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559 u imp m, fun n => FlagCut.ccx_cx_back (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559 u apart imp n⟩

private theorem callback4 (j : Fin 26) (u : State)
    (hxy : (Shadow7.a0P (start j)+0) ≠ (Shadow7.e0P (start j)+6)) (htx : (Partial.tagsP.getD 0 0) ≠ (Shadow7.a0P (start j)+0)) (hty : (Partial.tagsP.getD 0 0) ≠ (Shadow7.e0P (start j)+6)) (zero : u.basis (Shadow7.e0P (start j)+6) = false) :
    Pair (GateMirror.forward ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)])) ([.CCX (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j))]) ([.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),GateMirror.erase (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)]) (u) := by
  exact ⟨fun m => FlagCut5.swap_make (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)+0) (Shadow7.e0P (start j)+6) u hxy htx hty zero m, fun n => FlagCut5.swap_make_back (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)+0) (Shadow7.e0P (start j)+6) u hxy htx hty zero n⟩

private theorem callback6 (j : Fin 26) (u : State)
    (apart : (Shadow7.a0P (start j)+16) ≠ (Shadow7.bankW (start j) 16)) (zero : u.basis (Shadow7.a0P (start j)+16) = false) :
    Pair (GateMirror.forward ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)))) ([]) ([]) (u) := by
  exact ⟨fun m => (FlagCut6.pair_high_id 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16) u apart zero).symm, fun n => FlagCut6.pair_high_id 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16) u apart zero⟩

private theorem callback8 (j : Fin 26) (u : State)
    (apart : Shadow7.e0P (start j)+4 ≠ 1559) (value : u.basis 1559 = u.basis (Shadow7.e0P (start j)+4)) :
    Pair (GateMirror.forward ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559])) ([.CX (Shadow7.e0P (start j)+4) 1559]) ([.CX (Shadow7.e0P (start j)+4) 1559]) (u) := by
  exact ⟨fun m => FlagCut.erase_cx (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 u value m, fun n => FlagCut.erase_cx_back (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 u apart value n⟩

private theorem callback9 (j : Fin 26) (u : State)
    (apart : (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) ≠ 1559) (imp : u.basis (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) = true → u.basis 1558 = true) :
    Pair (GateMirror.forward ([.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) (u) := by
  exact ⟨fun m => FlagCut.ccx_cx 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559 u imp m, fun n => FlagCut.ccx_cx_back 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559 u apart imp n⟩

private theorem callback10 (j : Fin 26) (u : State)
    (apart : (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) ≠ 1559) (value : u.basis 1559 = u.basis (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1)) :
    Pair (GateMirror.forward ([.pop 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) (u) := by
  exact ⟨fun m => FlagCut.erase_cx 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559 u value m, fun n => FlagCut.erase_cx_back 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559 u apart value n⟩

end ECDSAAdd.Entrant.StairPacket.PBReceiverFast
end

section
namespace ECDSAAdd.Entrant.StairPacket.Core150Targets
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open CRTBarrel Partial GateMirror LeaveJ7 CRTBarrel.LeaveSplice
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
theorem headA_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (headA (start j)).all (fun g => decide (target g ≠ Shadow7.sbP (start j) + 1577 ∧
      target g ≠ Shadow7.sbP (start j) + 1578)) = true := by decide +kernel

theorem pre5_targets : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    (headA0 (start j) ++ ([GateMirror.Gate.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++
      (headA1 (start j) ++ ([GateMirror.Gate.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++
      headC0 (start j))))).all (fun g => decide (target g ≠ Shadow7.e0P (start j) + 6)) = true := by decide +kernel

theorem lit_targets16 : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    ((Partial.leaveFix1 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix2P (start j) (Shadow7.sbP (start j)) ++
      [GateMirror.Gate.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ headC0 (start j) ++
      [GateMirror.Gate.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6),
        GateMirror.Gate.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0),
        GateMirror.Gate.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++
      (rowGates (Shadow7.e0P (start j) + 6) ((Shadow7.moveRows (start j)).drop 1) ++
        (Partial.leaveFix5 (start j) (Shadow7.sbP (start j))).drop 43)) ++ tailD0 (start j)).all
      (fun g => decide (target g ≠ Shadow7.a0P (start j) + 16)) = true := by decide +kernel
end ECDSAAdd.Entrant.StairPacket.Core150Targets
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.Admission150
open ECDSAAdd.Entrant.StairPacket.LeaveJ7.Admission
open Partial GateMirror CRTBarrel

section
attribute [local irreducible] ECDSAAdd.run
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false

/-- Forward equality and inverse restoration for the actual moved leave, including its
measurement offsets. The two tapes are independent. -/
theorem Inputs.crt_pair20 {j : Fin 26} (lo : 0≤j.val) (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) :
    (∀ m, run (LeaveCutsCore150.leave j) m s = run (Shadow7.leaveP j) m s) ∧
    (∀ m n, run (LeaveCutsCore150.unleave j) n (run (LeaveCutsCore150.leave j) m s) = s) := by
  have l16 := LeaveWindow150.low16_all j lo hi
  have v := LeaveSplice.moved_valid lo (by omega) h
  rw [LeaveCut.move_shape] at v
  obtain ⟨same, back⟩ := LeaveCut.barrel_pair j lo (by omega) (run (GateMirror.forward (CRTBarrel.before (start j))) [] s) (LeaveCut.input lo (by omega) h)
  rw [FlagCut5.before_split5] at v
  rw [LeaveWindow150.after_split, LeaveWindow150.tailD_cut, l16, LeaveWindow150.tailE_cut] at v
  simp only [List.append_assoc] at v
  have imp0 : s.basis (Shadow7.sbP (start j) + 1578) = true → s.basis (Shadow7.sbP (start j) + 1577) = true := by
    rw [← FlagCut.e0P_four, ← FlagCut.e0P_three, h.side, h.far]
    intro hs
    exact ((Bool.and_eq_true _ _).mp hs).1
  have hA := List.all_eq_true.mp (Core150Targets.headA_targets j lo (by omega))
  rw [LeaveWindow150.headA_cut] at hA
  have k3 := FlagCut.keeps_of_targets (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) (Shadow7.sbP (start j) + 1577)
    (fun g hg => (of_decide_eq_true (hA g hg)).1) [] s
  have k4 := FlagCut.keeps_of_targets (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) (Shadow7.sbP (start j) + 1578)
    (fun g hg => (of_decide_eq_true (hA g hg)).2) [] s
  have imp1 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j))))) [] s).basis (Shadow7.sbP (start j) + 1578) = true →
      (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j))))) [] s).basis (Shadow7.sbP (start j) + 1577) = true := by
    rw [k3, k4]; exact imp0
  have far_ne : Shadow7.sbP (start j) + 1578 ≠ 1559 := by omega
  have v' : LeaveSplice.Valid s ((headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC (start j) ++
      (Shadow7.leaveBarrel (start j) ++ (tailD (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ tailE (start j))))))) := by
    rw [LeaveWindow150.headC_cut, LeaveWindow150.tailD_cut, l16, LeaveWindow150.tailE_cut]
    simpa only [List.append_assoc] using v
  obtain ⟨_, v1⟩ := v'.parts
  obtain ⟨vb1, _⟩ := v1.parts
  have fresh := vb1.ready.1
  simp only [GateMirror.Fresh] at fresh
  have kM (q : Wire) (hq : q = 1559 ∨ q = Shadow7.e0P (start j) + 4) (t : State) :
      (run (GateMirror.forward (headC (start j) ++ (Shadow7.leaveBarrel (start j) ++ tailD (start j)))) [] t).basis q = t.basis q := by
    apply FlagCut.keeps_of_targets
    intro g hg
    have := FlagCut.mid_targets j lo hi g hg
    rcases hq with rfl | rfl
    · exact this.1
    · exact this.2
  have re : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))) = (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j)))) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC (start j) ++ (Shadow7.leaveBarrel (start j) ++ tailD (start j)))) := by
    rw [LeaveWindow150.headC_cut, LeaveWindow150.tailD_cut, l16]; simp only [List.append_assoc]
  have hv3 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))))) [] s).basis 1559 =
      (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))))) [] s).basis (Shadow7.e0P (start j) + 4) := by
    rw [re, FlagCut.run_nil_append, FlagCut.run_nil_append, kM 1559 (Or.inl rfl), kM _ (Or.inr rfl), FlagCut.e0P_four]
    exact FlagCut.make_flag _ _ _ _ fresh far_ne imp1
  have ne4 : Shadow7.e0P (start j) + 4 ≠ 1559 := by unfold Shadow7.e0P; omega
  have hv0 := FlagCut4.row17_value lo hi h
  have ha0 : start j + 30 ≠ start j + Shadow7.sbP (start j) + 48 := by omega
  have hb0 : Shadow7.sbP (start j) + 803 ≠ start j + Shadow7.sbP (start j) + 48 := by
    have := (start_win7 j lo (by omega)).2; unfold start at *; omega
  have hP := List.all_eq_true.mp (Core150Targets.pre5_targets j lo hi)
  have zero6 : s.basis (Shadow7.e0P (start j) + 6) = false := h.zero _ (by simp [LeaveJ7.watched])
  have hyR := (FlagCut.keeps_of_targets _ (Shadow7.e0P (start j) + 6) (fun g hg => of_decide_eq_true (hP g hg)) [] s).trans zero6
  have win := start_win7 j lo hi
  have rw7 := Shadow7.rail_win win.1 win.2
  have t0 : Partial.tagsP.getD 0 0 = 1576 := rfl
  have hxy : Shadow7.a0P (start j) + 0 ≠ Shadow7.e0P (start j) + 6 := by
    unfold Shadow7.a0P Shadow7.e0P at *; ((try unfold Wire at *); omega)
  have htx : Partial.tagsP.getD 0 0 ≠ Shadow7.a0P (start j) + 0 := by
    rw [t0]; unfold Shadow7.a0P at *; ((try unfold Wire at *); omega)
  have hty : Partial.tagsP.getD 0 0 ≠ Shadow7.e0P (start j) + 6 := by
    rw [t0]; unfold Shadow7.e0P at *; ((try unfold Wire at *); omega)
  have top : (run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s).basis
      (Shadow7.a0P (start j) + 16) = false := by
    have scan := LeaveJ7.inputScan_result j lo hi s [] _ _ _ _ h.ready h.fresh
    have row := (scan.2.2.1 17 (by decide)).1
    have tight := LeaveShadowRails.inputTight17 (Shadow7.sbP (start j)) z h.farSmall
    rw [Nat.testBit_lt_two_pow tight] at row
    have idx : Shadow7.a0P (start j) - 1 + 17 = Shadow7.a0P (start j) + 16 := by unfold Shadow7.a0P; omega
    rw [idx] at row
    exact row
  have hL := List.all_eq_true.mp (Core150Targets.lit_targets16 j lo hi)
  have eqJ : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j))))))))) = Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++
      ((Partial.leaveFix1 (start j) (Shadow7.sbP (start j)) ++ Shadow7.fix2P (start j) (Shadow7.sbP (start j)) ++
        [.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ headC0 (start j) ++ [.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (rowGates (Shadow7.e0P (start j) + 6) ((Shadow7.moveRows (start j)).drop 1) ++
        (Partial.leaveFix5 (start j) (Shadow7.sbP (start j))).drop 43)) ++
      (Shadow7.leaveAdjust (start j) ++ (Shadow7.leaveBarrel (start j) ++ tailD0 (start j)))) := by
    have e := LeaveWindow150.fix0P_cut (start j) (Shadow7.sbP (start j))
    simp only [headA0, headA1, headC1]
    conv_rhs => rw [e]
    simp only [List.append_assoc]
  have hJ : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j))))))))))) [] s).basis (Shadow7.a0P (start j) + 16) = false := by
    rw [eqJ, FlagCut.run_nil_append]
    refine (FlagCut.keeps_of_targets _ _ (fun g hg => ?_) [] _).trans top
    rcases List.mem_append.mp hg with h1 | h1
    · exact of_decide_eq_true (hL g (List.mem_append_left _ h1))
    · rcases List.mem_append.mp h1 with h2 | h2
      · exact FlagCut6.adjust_targets16 win.1 win.2 g h2
      · rcases List.mem_append.mp h2 with h3 | h3
        · exact FlagCut6.barrel_targets16 win.1 win.2 g h3
        · exact of_decide_eq_true (hL g (List.mem_append_right _ h3))
  have hne16 : Shadow7.a0P (start j) + 16 ≠ Shadow7.bankW (start j) 16 := by
    have bc := Shadow7.bank_cases (i := 16) win.1 win.2 (by unfold Shadow7.wpP; omega)
    unfold Shadow7.a0P Shadow7.e0P at *; ((try unfold Wire at *); omega)
  -- the store chain's carry-in 1558 is 1 at its level-0 make and pop
  have eq7 : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))) = (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559])))))))))))) ++ tailE0 (start j) := by simp only [List.append_assoc]
  have h1558M : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s).basis 1558 = true := by
    rw [eq7, FlagCut.run_nil_append]; exact FlagCut7.tailE0_1558 j lo hi _
  have eq8 : headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))) = (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j)))))))))))))) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ chainMid (start j)) := by simp only [List.append_assoc]
  have h1558P : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s).basis 1558 = true := by
    rw [eq8, FlagCut.run_nil_append, FlagCut.run_nil_append,
      FlagCut.keeps_of_targets _ _ (fun g hg => FlagCut7.chainMid_targets _ g hg)]
    rw [FlagCut.keeps_of_targets [.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] 1558 (fun g hg => by
      simp only [List.mem_singleton] at hg; subst hg; simp [GateMirror.target])]
    exact h1558M
  have v8 : LeaveSplice.Valid s ((headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j)))))))))))))))) ++ ([.pop 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ tailE1 (start j))) := by
    simpa only [List.append_assoc] using v
  obtain ⟨_, w8⟩ := v8.parts
  obtain ⟨vb8, _⟩ := w8.parts
  have val8 := vb8.prepared.1
  simp only [GateMirror.ValueOK] at val8
  have hv8 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s).basis 1559 = (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) := by
    rw [val8, h1558P, Bool.true_and]
  have imp7 : (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s).basis (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) = true →
      (run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s).basis 1558 = true := fun _ => h1558M
  have topne : (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) ≠ 1559 := by
    unfold Shadow7.a0P at *; ((try unfold Wire at *); omega)
  have head := And.intro (PBScan.admitted_same hi h) (PBScan.admitted_back hi h)
  let fastSourceState1 : State := run (GateMirror.forward ((headA0 (start j)))) [] s
  let fastSourceState2 : State := run (GateMirror.forward (PBReceiver.latchPre (start j))) [] s
  let fastSourceState3 : State := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((headA1 (start j)))))) [] s
  let fastSourceState4 : State := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((headA1 (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)))))))) [] s
  let fastSourceState5 : State := run (GateMirror.forward (CRTBarrel.before (start j))) [] s
  let fastSourceState6 : State := run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j))))))))))) [] s
  let fastSourceState7 : State := run (GateMirror.forward (PBReceiver.selectorPre (start j))) [] (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (PBReceiver.beforePort (start j))) [] s))
  let fastSourceState8 : State := run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j))))))))))))) [] s
  let fastSourceState9 : State := run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j))))))))))))))) [] s
  let fastSourceState10 : State := run (GateMirror.forward (headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j))))))))))))))))) [] s
  have original := LeaveSplice.moved_valid lo (by omega) h
  rw [LeaveCut.move_shape] at original
  have vb : LeaveSplice.Valid s (PBReceiver.beforePort (start j)) := original.parts.1
  rw [PBReceiver.latch_shape j hi] at vb
  have vl : LeaveSplice.Valid
      (run (GateMirror.forward (PBReceiver.latchPre (start j))) [] s) [PBReceiver.latchPop (start j)] := by
    have t := vb.parts.2
    exact ⟨fun g hg => t.physical g (by rcases List.mem_singleton.mp hg with rfl; exact List.mem_cons_self),⟨t.prepared.1,trivial⟩,⟨t.ready.1,trivial⟩⟩
  have lp := PBReceiver.receiver_pair 1570 (Shadow7.sbP (start j)+801) 1571 true [1556] fastSourceState2 vl
    (by simp) (PBReceiver.latch_relation j hi s (h.scratch _ (by simp)))
  let u := run (GateMirror.forward (PBReceiver.beforePort (start j))) [] s
  let barrelState := run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] u
  have va : LeaveSplice.Valid barrelState (PBReceiver.afterPort (start j)) := original.parts.2.parts.2
  rw [PBReceiver.selector_shape j hi] at va
  have vs : LeaveSplice.Valid
      (run (GateMirror.forward (PBReceiver.selectorPre (start j))) [] barrelState) [PBReceiver.selectorPop (start j)] := by
    have p := va.parts.2
    exact ⟨fun g hg => p.physical g (by rcases List.mem_singleton.mp hg with rfl; exact List.mem_cons_self),⟨p.prepared.1,trivial⟩,⟨p.ready.1,trivial⟩⟩
  have sp := PBReceiver.receiver_pair 1560 (OB5.sig (start j+14) (start j+1048)) 1565 false
    (PBReceiver.selectorSources (start j)) fastSourceState7 vs
    (by simp [PBReceiver.selectorSources,Shadow7.e0P]; omega)
    (PBReceiver.selector_relation j hi s (h.zero _ (by simp [LeaveJ7.watched])))
  have fastLocalPair1 : PBReceiverFast.Pair (GateMirror.forward ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)])) ([GateMirror.erase (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)]) ([.CCX (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)]) (fastSourceState1) := PBReceiverFast.callback1 j fastSourceState1 ha0 hb0 hv0
  have fastPair1 := PBReceiverFast.transportPair
    (GateMirror.forward ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)])) ([GateMirror.erase (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)]) ([.CCX (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)])
    (u := fastSourceState1) (v := run (GateMirror.forward ((headA0 (start j)))) [] s)
    (PBReceiverFast.state1 j s).symm fastLocalPair1
  have fastLocalPair2 : PBReceiverFast.Pair (GateMirror.forward ([PBReceiver.latchPop (start j)])) (GateMirror.forward (PBReceiver.receiver 1571 true [1556])) (GateMirror.inverse (PBReceiver.receiver 1571 true [1556])) (fastSourceState2) := by
    refine ⟨?_, ?_⟩
    · simpa only [PBReceiver.latchPop] using lp.1
    · simpa only [PBReceiver.latchPop] using lp.2
  have fastPair2 := PBReceiverFast.transportPair
    (GateMirror.forward ([PBReceiver.latchPop (start j)])) (GateMirror.forward (PBReceiver.receiver 1571 true [1556])) (GateMirror.inverse (PBReceiver.receiver 1571 true [1556]))
    (u := fastSourceState2) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)))))) [] s)
    (PBReceiverFast.state2 j hi s).symm fastLocalPair2
  have fastLocalPair3 : PBReceiverFast.Pair (GateMirror.forward ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559])) ([.CX (Shadow7.sbP (start j)+1578) 1559]) ([.CX (Shadow7.sbP (start j)+1578) 1559]) (fastSourceState3) := PBReceiverFast.callback3 j fastSourceState3 far_ne imp1
  have fastPair3 := PBReceiverFast.transportPair
    (GateMirror.forward ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559])) ([.CX (Shadow7.sbP (start j)+1578) 1559]) ([.CX (Shadow7.sbP (start j)+1578) 1559])
    (u := fastSourceState3) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)))))))) [] s)
    (PBReceiverFast.state3 j hi s).symm fastLocalPair3
  have fastLocalPair4 : PBReceiverFast.Pair (GateMirror.forward ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)])) ([.CCX (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j))]) ([.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),GateMirror.erase (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)]) (fastSourceState4) := PBReceiverFast.callback4 j fastSourceState4 hxy htx hty hyR
  have fastPair4 := PBReceiverFast.transportPair
    (GateMirror.forward ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)])) ([.CCX (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j))]) ([.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),GateMirror.erase (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)])
    (u := fastSourceState4) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)))))))))) [] s)
    (PBReceiverFast.state4 j hi s).symm fastLocalPair4
  have fastLocalPair5 : PBReceiverFast.Pair (GateMirror.forward ((Shadow7.leaveBarrel (start j)))) (barrel (start j) false) (barrel (start j) true) (fastSourceState5) := ⟨same,back⟩
  have fastPair5 := PBReceiverFast.transportPair
    (GateMirror.forward ((Shadow7.leaveBarrel (start j)))) (barrel (start j) false) (barrel (start j) true)
    (u := fastSourceState5) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)))))))))))) [] s)
    (PBReceiverFast.state5 j hi s).symm fastLocalPair5
  have fastLocalPair6 : PBReceiverFast.Pair (GateMirror.forward ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)))) ([]) ([]) (fastSourceState6) := PBReceiverFast.callback6 j fastSourceState6 hne16 hJ
  have fastPair6 := PBReceiverFast.transportPair
    (GateMirror.forward ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)))) ([]) ([])
    (u := fastSourceState6) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)))))))))))))) [] s)
    (PBReceiverFast.state6 j hi s).symm fastLocalPair6
  have fastLocalPair7 : PBReceiverFast.Pair (GateMirror.forward ([PBReceiver.selectorPop (start j)])) (GateMirror.forward (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j)))) (GateMirror.inverse (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j)))) (fastSourceState7) := by
    refine ⟨?_, ?_⟩
    · simpa only [PBReceiver.selectorPop] using sp.1
    · simpa only [PBReceiver.selectorPop] using sp.2
  have fastPair7 := PBReceiverFast.transportPair
    (GateMirror.forward ([PBReceiver.selectorPop (start j)])) (GateMirror.forward (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j)))) (GateMirror.inverse (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j))))
    (u := fastSourceState7) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)))))))))))))))) [] s)
    (PBReceiverFast.state7 j hi s).symm fastLocalPair7
  have fastLocalPair8 : PBReceiverFast.Pair (GateMirror.forward ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559])) ([.CX (Shadow7.e0P (start j)+4) 1559]) ([.CX (Shadow7.e0P (start j)+4) 1559]) (fastSourceState8) := PBReceiverFast.callback8 j fastSourceState8 ne4 hv3
  have fastPair8 := PBReceiverFast.transportPair
    (GateMirror.forward ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559])) ([.CX (Shadow7.e0P (start j)+4) 1559]) ([.CX (Shadow7.e0P (start j)+4) 1559])
    (u := fastSourceState8) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)))))))))))))))))) [] s)
    (PBReceiverFast.state8 j hi s).symm fastLocalPair8
  have fastLocalPair9 : PBReceiverFast.Pair (GateMirror.forward ([.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) (fastSourceState9) := PBReceiverFast.callback9 j fastSourceState9 topne imp7
  have fastPair9 := PBReceiverFast.transportPair
    (GateMirror.forward ([.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])
    (u := fastSourceState9) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)) ++ ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] ++ ((tailE0 (start j)))))))))))))))))))) [] s)
    (PBReceiverFast.state9 j hi s).symm fastLocalPair9
  have fastLocalPair10 : PBReceiverFast.Pair (GateMirror.forward ([.pop 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) (fastSourceState10) := PBReceiverFast.callback10 j fastSourceState10 topne hv8
  have fastPair10 := PBReceiverFast.transportPair
    (GateMirror.forward ([.pop 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])
    (u := fastSourceState10) (v := run (GateMirror.forward ((headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)) ++ ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] ++ ((tailE0 (start j)) ++ ([.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559] ++ ((chainMid (start j)))))))))))))))))))))) [] s)
    (PBReceiverFast.state10 j hi s).symm fastLocalPair10
  obtain ⟨f,r⟩ := PBReplace.replace10
    (headA0 (start j))
    [.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)]
    (PBReceiver.latchHead (start j))
    [PBReceiver.latchPop (start j)]
    (PBReceiver.latchTail (start j))
    [.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559]
    (headC0 (start j))
    [.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)]
    (headC1 (start j))
    (Shadow7.leaveBarrel (start j))
    (tailD0 (start j))
    (Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16))
    (PBReceiver.selectorHead (start j))
    [PBReceiver.selectorPop (start j)]
    (PBReceiver.selectorTail (start j))
    [.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559]
    (tailE0 (start j))
    [.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]
    (chainMid (start j))
    [.pop 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]
    (tailE1 (start j))
    (GateMirror.forward (PBScan.head (start j))) (GateMirror.inverse (PBScan.head (start j)))
    ([GateMirror.erase (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)]) ([.CCX (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)])
    (GateMirror.forward (PBReceiver.receiver 1571 true [1556])) (GateMirror.inverse (PBReceiver.receiver 1571 true [1556]))
    ([.CX (Shadow7.sbP (start j)+1578) 1559]) ([.CX (Shadow7.sbP (start j)+1578) 1559])
    ([.CCX (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j))]) ([.CX (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),GateMirror.erase (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)])
    (barrel (start j) false) (barrel (start j) true)
    ([]) ([])
    (GateMirror.forward (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j)))) (GateMirror.inverse (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j))))
    ([.CX (Shadow7.e0P (start j)+4) 1559]) ([.CX (Shadow7.e0P (start j)+4) 1559])
    ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559])
    ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) ([.CX (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559]) s
    (by simpa only [PBReceiver.latch_source_split j hi,PBReceiver.selector_source_split j hi,PBReceiver.latch_prefix_shape j hi,PBReceiver.selector_prefix_shape j hi,PBReceiver.latchPop,PBReceiver.selectorPop,PBReceiver.beforePort,PBReceiver.afterPort,u,barrelState,FlagCut5.before_split5,LeaveCut.move_shape,List.append_assoc,List.cons_append,List.nil_append,FlagCut.run_nil_append] using v)
    head.1 head.2
    fastPair1.fwd fastPair1.back
    fastPair2.fwd fastPair2.back
    fastPair3.fwd fastPair3.back
    fastPair4.fwd fastPair4.back
    fastPair5.fwd fastPair5.back
    fastPair6.fwd fastPair6.back
    fastPair7.fwd fastPair7.back
    fastPair8.fwd fastPair8.back
    fastPair9.fwd fastPair9.back
    fastPair10.fwd fastPair10.back
  have fprog : LeaveCutsCore150.leave j = GateMirror.forward (PBScan.head (start j)) ++
      [GateMirror.erase (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++
      GateMirror.forward (PBReceiver.latchHead (start j)) ++ GateMirror.forward (PBReceiver.receiver 1571 true [1556]) ++ GateMirror.forward (PBReceiver.latchTail (start j)) ++ [.CX (Shadow7.sbP (start j) + 1578) 1559] ++
      GateMirror.forward (headC0 (start j)) ++
      [.CCX (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6),
        .CX (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0)] ++
      GateMirror.forward (headC1 (start j)) ++ barrel (start j) false ++ GateMirror.forward (tailD0 (start j)) ++ [] ++ GateMirror.forward (PBReceiver.selectorHead (start j)) ++ GateMirror.forward (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j))) ++ GateMirror.forward (PBReceiver.selectorTail (start j)) ++
      [.CX (Shadow7.e0P (start j) + 4) 1559] ++ GateMirror.forward (tailE0 (start j)) ++ [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.forward (chainMid (start j)) ++
      [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.forward (tailE1 (start j)) := by
    simp only [LeaveCutsCore150.leave, if_pos hi, PBReceiver.before100_decomposed j hi, PBReceiver.after100_decomposed j hi, forward_app, FlagCut.fwd_cons, front, List.append_assoc,
      List.cons_append, List.nil_append, List.append_nil, Nat.add_zero]
  have uprog : LeaveCutsCore150.unleave j = GateMirror.inverse (tailE1 (start j)) ++ [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.inverse (chainMid (start j)) ++
      [.CX (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ GateMirror.inverse (tailE0 (start j)) ++ [.CX (Shadow7.e0P (start j) + 4) 1559] ++
      GateMirror.inverse (PBReceiver.selectorTail (start j)) ++ GateMirror.inverse (PBReceiver.receiver 1565 false (PBReceiver.selectorSources (start j))) ++ GateMirror.inverse (PBReceiver.selectorHead (start j)) ++ [] ++ GateMirror.inverse (tailD0 (start j)) ++ barrel (start j) true ++ GateMirror.inverse (headC1 (start j)) ++
      [.CX (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0),
        GateMirror.erase (Partial.tagsP.getD 0 0) (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++
      GateMirror.inverse (headC0 (start j)) ++
      [.CX (Shadow7.sbP (start j) + 1578) 1559] ++ GateMirror.inverse (PBReceiver.latchTail (start j)) ++ GateMirror.inverse (PBReceiver.receiver 1571 true [1556]) ++ GateMirror.inverse (PBReceiver.latchHead (start j)) ++
      [.CCX (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++
      GateMirror.inverse (PBScan.head (start j)) := by
    simp only [LeaveCutsCore150.unleave, if_pos hi, PBReceiver.before100_decomposed j hi, PBReceiver.after100_decomposed j hi, FlagCut.inv_app, FlagCut.inv_cons, GateMirror.back,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil, Nat.add_zero]
  have shape : Shadow7.leaveMoveOps (start j) = headA0 (start j) ++ ([.ccx (start j + 30) (Shadow7.sbP (start j) + 803) (start j + Shadow7.sbP (start j) + 48)] ++ (headA1 (start j) ++ ([.make (Shadow7.sbP (start j) + 1577) (Shadow7.sbP (start j) + 1578) 1559] ++ (headC0 (start j) ++ ([.cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6), .ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) + 0), .cx (Shadow7.a0P (start j) + 0) (Shadow7.e0P (start j) + 6)] ++ (headC1 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (tailD0 (start j) ++ (Partial.pairGM false 1614 (Shadow7.a0P (start j) + 16) (Shadow7.bankW (start j) 16) ++ (tailD1 (start j) ++ ([.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] ++ (tailE0 (start j) ++ ([.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (chainMid (start j) ++ ([.pop 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559] ++ (tailE1 (start j))))))))))))))))) := by
    rw [LeaveCut.move_shape, FlagCut5.before_split5, LeaveWindow150.after_split, LeaveWindow150.tailD_cut, l16, LeaveWindow150.tailE_cut]
    simp only [List.append_assoc]
  have shape10 : Shadow7.leaveMoveOps (start j) = (headA0 (start j)) ++ ([.ccx (start j+30) (Shadow7.sbP (start j)+803) (start j+Shadow7.sbP (start j)+48)] ++ ((PBReceiver.latchHead (start j)) ++ ([PBReceiver.latchPop (start j)] ++ ((PBReceiver.latchTail (start j)) ++ ([.make (Shadow7.sbP (start j)+1577) (Shadow7.sbP (start j)+1578) 1559] ++ ((headC0 (start j)) ++ ([.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6),.ccx (Partial.tagsP.getD 0 0) (Shadow7.e0P (start j)+6) (Shadow7.a0P (start j)),.cx (Shadow7.a0P (start j)) (Shadow7.e0P (start j)+6)] ++ ((headC1 (start j)) ++ ((Shadow7.leaveBarrel (start j)) ++ ((tailD0 (start j)) ++ ((Partial.pairGM false 1614 (Shadow7.a0P (start j)+16) (Shadow7.bankW (start j) 16)) ++ ((PBReceiver.selectorHead (start j)) ++ ([PBReceiver.selectorPop (start j)] ++ ((PBReceiver.selectorTail (start j)) ++ ([.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] ++ ((tailE0 (start j)) ++ ([.make 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559] ++ ((chainMid (start j)) ++ ([.pop 1558 (Shadow7.a0P (start j)+Shadow7.lowsP (start j)-1) 1559] ++ ((tailE1 (start j)))))))))))))))))))))) := by
    rw [shape,PBReceiver.latch_source_split j hi,PBReceiver.selector_source_split j hi]
    simp only [List.append_assoc,List.cons_append,List.nil_append,Nat.add_zero]
  simp only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil,Nat.add_zero] at fprog uprog f r shape10
  refine ⟨?_, ?_⟩
  · intro m
    rw [fprog, f m, ← shape10]
    exact h.sameMove (Nat.zero_le _) (by omega) m
  · intro m n
    rw [uprog, fprog]
    exact r m n


end

/-- `crt_pair20` on the whole 24-block window: the CRT barrel leave on every block 0..23. -/
theorem Inputs.crt_pair {j : Fin 26} (lo : 0≤j.val) (hi : j.val≤24) {s : State} {z : SkywalkNat.State}
    {g sg : Bool} (h : Inputs j s z g sg) :
    (∀ m, run (LeaveCutsCore150.leave j) m s = run (Shadow7.leaveP j) m s) ∧
    (∀ m n, run (LeaveCutsCore150.unleave j) n (run (LeaveCutsCore150.leave j) m s) = s) :=
  Inputs.crt_pair20 lo hi h

end ECDSAAdd.Entrant.StairPacket.Admission150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveWindow150
open ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option maxRecDepth 10000

theorem barrel_box2 (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    ∀ q ∈ wires (CRTBarrel.barrel (start j) mir), Shadow7.leaveBox2 (start j) q := by
  obtain ⟨w1, w2⟩ := start_win7 j (Nat.zero_le _) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ :=
    Shadow7.rail_win w1 (by omega)
  intro q hq
  rcases CRTBarrel.barrel_wires j lo hi mir q hq with ⟨i, bound, rfl⟩ | ⟨k, hk, rfl⟩ | tag
  · rcases Shadow7.bank_cases w1 (by omega) bound with ⟨a, e⟩ | ⟨a, b, e, c, d⟩ | ⟨a, e, c⟩
    · rw [e]; apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega
    · rw [e]; apply Shadow7.box2_B w1 (by omega) <;> (try unfold Wire at *) <;> omega
    · rw [e]; apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega
  · have pc := Shadow7.pool_cases (i := 17+k) w1 (by omega)
    apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega
  · have bounds : ∀ w ∈ tagsP, 1556 ≤ w ∧ w ≤ 1576 := by decide
    obtain ⟨t1, t2⟩ := bounds q tag
    apply Shadow7.box2_S w1 (by omega) <;> (try unfold Wire at *) <;> omega

/-- `LeaveJ7.leaveMove_keeps` for the CRT leave: a wire outside `Shadow7.leaveBox2` keeps its value. -/
theorem leave_keeps20 (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (q : Wire)
    (outside : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (LeaveCutsCore150.leave j) m s).basis q = s.basis q := by
  apply run_preserves_outside
  intro hit
  have pieces : AllW (Shadow7.leaveBox2 (start j)) (Shadow7.leaveMoveOps (start j)) :=
    Shadow7.allW_leaveMove (start j) (Shadow7.leaveOps_box2 j (Nat.zero_le _) (by omega))
  rw [split_ops, allW_append_iff, allW_append_iff] at pieces
  have pre : ∀ w ∈ wires (GateMirror.forward (PBOps.before100 (start j))), Shadow7.leaveBox2 (start j) w :=
    (allW_programs (P := Shadow7.leaveBox2 (start j)) (ops := PBOps.before100 (start j)) (PBScope100.before_allW j hi (PBScanRow.beforeRow_allW _ (beforeC5_allW pieces.1)) (PBScope100.flag_box j hi).2)).1
  have post : ∀ w ∈ wires (GateMirror.forward (PBOps.after100 (start j))), Shadow7.leaveBox2 (start j) w :=
    (allW_programs (P := Shadow7.leaveBox2 (start j)) (ops := PBOps.after100 (start j)) (PBScope100.after_allW j hi (afterPartC3_allW pieces.2.2) (fun q hq => (PBScope100.sources_box j hi q hq).2))).1
  rw [(leave_eq j lo hi).1, wires_append, wires_append] at hit
  rcases Finset.mem_union.mp hit with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact outside (pre q h)
    · exact outside (barrel_box2 j lo hi false q h)
  · exact outside (post q h)

/-- `leave_keeps20` on the whole 22-block window (`LeaveJ7.leaveMove_keeps` for `LeaveCutsCore150.leave`): the CRT barrel
leave on every block 1..22 (the move-leave branch is vacuous). -/
theorem leave_keeps (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (q : Wire)
    (outside : ¬ Shadow7.leaveBox2 (start j) q) (m : List Bool) (s : State) :
    (run (LeaveCutsCore150.leave j) m s).basis q = s.basis q :=
  leave_keeps20 j lo hi q outside m s

end ECDSAAdd.Entrant.StairPacket.LeaveWindow150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-- dadon's `At240`/`At255` for any block `k` (the saved keys are `window_strong`'s `Key`). -/
structure AtJ (k : Fin 26) (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain : Domain (start k) x p raw
  input : InputAt (start k) (signedAt (start k) x p g sg) raw
  cut : PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (flagNeg (start k) x p sg)
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p))
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) raw) (eraseSites (EnterJ7.pending k) s)
  facts : PastFacts (NativeJ7.prev k) (ArchiveJ7.rawPorts (NativeJ7.prev k)) (Shadow7.sbP (start (NativeJ7.prev k)))
      (unsigned (start (NativeJ7.prev k)) x p) pg ps
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d (NativeJ7.prev k) (unsigned (start (NativeJ7.prev k)) x p))) s
  pastCanonical : signedAt (start (NativeJ7.prev k)) x p pg ps=WideReference.canonical (start (NativeJ7.prev k)) x p

/-- The hand-off at tick `t` (a block start). -/
def ReadyW (d:Bool) (x p:Nat) (t:Nat) (s:State) : Prop :=
  ∃ k : Fin 26, start k=t ∧ ∃ raw g sg pg ps, AtJ k d x p raw s g sg pg ps

/-- Block `i`'s saved archive key (dadon's `Saved (start i) x p (codePorts) d`). -/
def KeyW (d:Bool) (x p:Nat) (i:Fin 26) (s:State) : Prop :=
  ∃row<63145, Chronology (start i) x p row ∧ Kept (ArchiveJ7.codePorts i) d row s

/-- The window's precondition: the stock walk at tick 120 (dadon's `Before` at 225). -/
def BeforeW (d:Bool) (x p:Nat) (s:State) := ∃raw:State,
  Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis ∧ s=pullState (OB5.sig (start WindowParams.first-1)) raw

/-- par-c2's archive-scratch hypothesis of `NativeJ7.from_domain(_matched)`. -/
def ScratchAt (j : Fin 26) (d:Bool) (m:List Bool) (s:State) : Prop :=
  ∀k:Fin 157,23≤k.val →
    let pre:=run (Shadow7.enterP j) m s
    let tape:=m.drop (measurementCount (Shadow7.enterP j))
    (run (NativeJ7.program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) tape pre)).basis
      (ArchiveJ7.rawPorts (NativeJ7.prev j) k)=false

-- ===== Leaves (statements fixed here; each becomes a theorem) =====

/-- L2: the archive scratch of block `j` is clean after its pack (par-d2's ScratchWrap). -/
abbrev ScratchSpec : Prop :=
  ∀ (j : Fin 26), 1≤j.val → j.val≤24 → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool)
    (m:List Bool), AtJ j d x p raw s g sg pg ps → ScratchAt j d m s

/-- L3: the (move) leave undoes (GlueB's `Admission.Inputs.roundtrip`, on the window's move leave). -/
abbrev RoundtripSpec : Prop :=
  ∀ (j : Fin 26), 0≤j.val → j.val≤24 → ∀ (v:State) (z:SkywalkNat.State) (G S:Bool),
    LeaveJ7.Admission.Inputs j v z G S → ∀ m n:List Bool, run (LeaveCutsCore150.unleave j) n (run (LeaveCutsCore150.leave j) m v)=v

/-- The block after the window's first block. -/
def firstNext : Fin 26 := ⟨WindowParams.first.val+1,by decide⟩

/-- L9: the first block's endpoint at `start WindowParams.first` (dadon's `NativePack225.stock_endpoint`, first form). -/
abbrev FirstSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    ∃g s:Bool,
      InputAt (start WindowParams.first) (encode g s (unsigned (start WindowParams.first) x p).u (unsigned (start WindowParams.first) x p).v) raw ∧
      LeaveJ7.Admission.Inputs WindowParams.first
        (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))
        (unsigned (start WindowParams.first) x p) g s ∧
      PackedCut (EnterJ7.lowerPairs firstNext) (EnterJ7.upperPairs firstNext) (EnterJ7.gate firstNext)
        (EnterJ7.flagN firstNext) (EnterJ7.flagF firstNext) (EnterJ7.flagU firstNext)
        (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g s).2 (unsigned (start WindowParams.first+15) x p).u)
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p)))
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p) ∧ 2^(Shadow7.sbP (start WindowParams.first+15))≤(unsigned (start WindowParams.first+15) x p).u))
        (pullState (EnterJ7.pull firstNext)
          (endRaw (start WindowParams.first) raw (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))))
        (eraseSites (EnterJ7.pending firstNext) (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))) ∧
      PastFacts WindowParams.first (ArchiveJ7.rawPorts WindowParams.first) (Shadow7.sbP (start WindowParams.first)) (unsigned (start WindowParams.first) x p) g s
        (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d WindowParams.first (unsigned (start WindowParams.first) x p)))
        (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))

/-- L10: the first window (portal 120, enter, pack) keeps the phase and undoes (dadon's `NativePack225.first_window`). -/
abbrev FirstBackSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)).phase=raw.phase ∧
    ∀k, run (NativeFirstJ7.enteredUnwind WindowParams.first d ++ Shadow7.portalInvP (start WindowParams.first)) k
      (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))=
      pullState (OB5.sig (start WindowParams.first-1)) raw

-- ===== Program bridges =====

theorem prev_of (i k : Fin 26) (hk : k.val=i.val+1) : NativeJ7.prev k=i := Fin.ext (by simp only [NativeJ7.prev]; omega)

theorem start_succ (i k : Fin 26) (hk : k.val=i.val+1) : start k=start i+15 := by simp only [StairPacket.start]; omega

theorem next_eq (d:Bool) (i k : Fin 26) (hk : k.val=i.val+1) :
    (nextF LeaveCutsCore150.params d i k).flatten=NativeJ7.nextWindow k d++LeaveCutsCore150.leave k := by
  have e:=prev_of i k hk
  subst e
  simp only [nextF,LeaveCutsCore150.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeJ7.nextWindow,NativeJ7.window,Shadow7.body,NativeJ7.withArchive,NativeJ7.program,List.append_assoc]

theorem nextR_eq (d:Bool) (i k : Fin 26) (hk : k.val=i.val+1) :
    (nextR LeaveCutsCore150.params d i k).flatten=LeaveCutsCore150.unleave k++NativeJ7.nextUnwind k d := by
  have e:=prev_of i k hk
  subst e
  simp only [nextR,LeaveCutsCore150.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeJ7.nextUnwind,NativeJ7.unwind,Shadow7.unbody,NativeJ7.fromArchive,NativeJ7.reverse,List.append_assoc]

theorem first_eq (d:Bool) :
    (LeaveCutsCore150.params.portal (start WindowParams.first) :: firstF LeaveCutsCore150.params d WindowParams.first).flatten=
      (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d)++LeaveCutsCore150.leave WindowParams.first := by
  simp only [firstF,LeaveCutsCore150.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeFirstJ7.enteredWindow,NativeFirstJ7.window,Shadow7.body,NativeFirstJ7.program,List.append_assoc]

theorem firstR_eq (d:Bool) :
    (firstR LeaveCutsCore150.params d WindowParams.first++[LeaveCutsCore150.params.portalInv (start WindowParams.first)]).flatten=
      LeaveCutsCore150.unleave WindowParams.first++(NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) := by
  simp only [firstR,LeaveCutsCore150.params,Shadow7.params,ofParts,List.cons_append,List.nil_append,List.flatten_cons,List.flatten_nil,
    List.append_nil,NativeFirstJ7.enteredUnwind,NativeFirstJ7.unwind,Shadow7.unbody,NativeFirstJ7.reverse,List.append_assoc]


/-- The move leave runs like the reference leave after block `k`'s head, from any hand-off state. -/
theorem sameAt (L2 : ScratchSpec) (k : Fin 26) (h2 : 1≤k.val) (h19 : k.val≤24) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) (n:List Bool) :
    run (LeaveCutsCore150.leave k) n (run (NativeJ7.nextWindow k d) m s)=run (Shadow7.leaveP k) n (run (NativeJ7.nextWindow k d) m s) := by
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k (by omega) (by omega) d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k (by omega) (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  exact (Admission150.Inputs.crt_pair (by omega) (by omega) native.1).1 n

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- The saved key cells of block `i` are its archive's first 16 code ports. -/
theorem bank_cells (i : Fin 26) (q : Wire) (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    q ∈ cellsRestoreP (start i + 15) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  have hl : (cellsRestoreP (start i + 15)).length = 16 := by simp [cellsRestoreP]
  have hj : j.val < (cellsRestoreP (start i + 15)).length := by rw [hl]; exact j.isLt
  simp only [ArchiveJ7.codePorts, ArchiveJ7.code_split, List.append_assoc]
  rw [List.getD_append _ _ _ _ hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem _

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem scratch : ScratchSpec := by
  intro j h2 h19 d x p good raw s g sg pg ps m pre
  have numbers := LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have hist := WideReference.pulled_history j rfl pre.domain
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)
  let Z:=encode g sg T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) (unsigned (start j) x p) numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s (unsigned (start j) x p) g sg m numbers.farSmall pre.cut
    (readInput (start j) x p raw g sg pre.input) hist
  exact NativeJ7.scratch_raw_clean j h2 (by omega) d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut

theorem roundtrip : RoundtripSpec := by
  intro j h2 h19 v z G S h m n
  exact (Admission150.Inputs.crt_pair (by omega) (by omega) h).2 m n

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

abbrev EndpointUpTo (J : Nat) : Prop :=
  ∀ (j k : Fin 26), k.val=j.val+1 → WindowParams.first.val+1≤j.val → j.val≤J → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:ScratchAt j d m s) (pg ps cross:Bool)
    (prior:PastFacts (NativeJ7.prev j) (ArchiveJ7.rawPorts (NativeJ7.prev j)) (Shadow7.sbP (start (NativeJ7.prev j)))
      (unsigned (start (NativeJ7.prev j)) x p) pg ps cross s),
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (NativeJ7.nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))

abbrev KeepLeaveUpTo (J : Nat) : Prop :=
  ∀ (k : Fin 26), 1≤k.val → k.val≤J → ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts (NativeJ7.prev k)),
    ∀ (v:State) (n:List Bool), (run (LeaveCutsCore150.leave k) n v).basis q=v.basis q

abbrev KeepOlderUpTo (J : Nat) : Prop :=
  ∀ (i k i' : Fin 26), k.val=i.val+1 → 0≤ i'.val → i'.val+2≤k.val → k.val≤J → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i'), ∀ (s:State) (m:List Bool),
    (run (nextF LeaveCutsCore150.params d i k).flatten m s).basis q=s.basis q

/-- The leaves of a window whose last block is `J`. -/
structure LeavesUpTo (J : Nat) : Prop where
  endpoint : EndpointUpTo J
  scratch : ScratchSpec
  roundtrip : RoundtripSpec
  keepLeave : KeepLeaveUpTo J
  keepOlder : KeepOlderUpTo J
  first : FirstSpec
  firstBack : FirstBackSpec

/-- The last block's frame at the exit (exit ports `ports`). -/
def LastAt (ports : Ports) (J : Fin 26) (d:Bool) (x p:Nat) (s:State) : Prop :=
  ∃row<63145,Chronology (start J) x p row ∧ Frame ports (code d) row s

/-- The exit of a window whose last block is `J`: its step (from the hand-off at `start J+15` to the last frame) and
the keys it keeps. -/
structure ExitLeaves (J : Fin 26) (ports : Ports) : Prop where
  step : ∀ (d:Bool) (x:Nat), Bounds x p → Checked (exitF LeaveCutsCore150.params d (start J+15)).flatten
    (exitR LeaveCutsCore150.params d (start J+15)).flatten (ReadyW d x p (start J+15)) (LastAt ports J d x p)
  keep : ∀ (i : Fin 26), WindowParams.first.val ≤ i.val → i.val < J.val → ∀ (d:Bool), ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i),
    ∀ (s:State) (m:List Bool), (run (exitF LeaveCutsCore150.params d (start J+15)).flatten m s).basis q=s.basis q

theorem interiorG (J : Nat) (hJ : J ≤ 24) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 26) (hk : k.val=i.val+1)
    (h4 : WindowParams.first.val+1≤k.val) (h12 : k.val≤J) :
    Checked (nextF LeaveCutsCore150.params d i k).flatten (nextR LeaveCutsCore150.params d i k).flatten
      (ReadyW d x p (start k)) (ReadyW d x p (start k+15)) := by
  rw [next_eq d i k hk,nextR_eq d i k hk]
  apply pair (F:=NativeJ7.nextWindow k d) (F':=LeaveCutsCore150.leave k) (R:=NativeJ7.nextUnwind k d) (R':=LeaveCutsCore150.unleave k)
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  let k0:=k
  let v:=run (NativeJ7.nextWindow k0 d) m s
  let n:=m.drop (measurementCount (NativeJ7.nextWindow k0 d))
  let out:=run (Shadow7.leaveP k0) n v
  let raw':=endRaw (start k0) raw v
  let k1:Fin 26:=⟨k0.val+1,by omega⟩
  have p1:NativeJ7.prev k1=k0:=prev_of k0 k1 rfl
  have s1:start k1=start k0+15:=start_succ k0 k1 rfl
  let flags:=LeaveJ7.Admission.flags (unsigned (start k0) x p) g sg
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have h2 : 1≤k0.val := by omega
  have h19 : k0.val≤24 := by omega
  have curr:=readInput (start k0) x p raw g sg pre.input
  have scr:=L.scratch k0 h2 h19 d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k0 h2 h19 d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨cut,facts⟩:=L.endpoint k0 k1 rfl h4 h12 d x p good raw s m n pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  have hin:=native.1
  have carried:=stepInput_gen_shadow7 (start k0) (Shadow7.sbP (start k0)) x p (by simp only [StairPacket.start]; omega)
    (by simp only [StairPacket.start]; omega) good raw v g sg pre.domain pre.input hin.farSmall
  have lastPhase:out.phase=raw'.phase:=cutPhase cut
  have prevPhase:s.phase=raw.phase:=cutPhase pre.cut
  have ph:=lastPhase.trans ((endRaw_phase (start k0) x p (by simp only [StairPacket.start]; omega) good raw v
    pre.domain).trans prevPhase.symm)
  have canon:=unique_input pre.input (fixed_input _ _ _ (by simp only [StairPacket.start]; omega) good raw pre.domain)
  have same:run (LeaveCutsCore150.leave k0) n v=run (Shadow7.leaveP k0) n v:=(Admission150.Inputs.crt_pair (by omega) (by omega) hin).1 n
  show (run (LeaveCutsCore150.leave k0) n v).phase=s.phase ∧ ReadyW d x p (start k+15) (run (LeaveCutsCore150.leave k0) n v) ∧
    (∀t,run (LeaveCutsCore150.unleave k0) t (run (LeaveCutsCore150.leave k0) n v)=v) ∧ (∀t,run (NativeJ7.nextUnwind k d) t v=s)
  rw [same]
  refine ⟨ph,⟨k1,s1,raw',flags.1,flags.2,g,sg,?_⟩,fun t=>by rw [← same]; exact L.roundtrip k0 (by omega) h19 v _ g sg hin n t,
    native.2.2.2⟩
  refine ⟨?_,?_,cut,?_,?_⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [p1]; exact facts
  · rw [p1]; exact canon

theorem firstStepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (LeaveCutsCore150.params.portal (start WindowParams.first) :: firstF LeaveCutsCore150.params d WindowParams.first).flatten
      (firstR LeaveCutsCore150.params d WindowParams.first++[LeaveCutsCore150.params.portalInv (start WindowParams.first)]).flatten
      (BeforeW d x p) (ReadyW d x p (start WindowParams.first+15)) := by
  rw [first_eq d,firstR_eq d]
  apply pair (F:=Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) (F':=LeaveCutsCore150.leave WindowParams.first)
    (R:=NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) (R':=LeaveCutsCore150.unleave WindowParams.first)
  intro s m h
  obtain ⟨raw,stage,rfl⟩:=h
  let v:=run (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)
  let n:=m.drop (measurementCount (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d))
  let out:=run (Shadow7.leaveP WindowParams.first) n v
  let raw':=endRaw (start WindowParams.first) raw v
  obtain ⟨g,sg,input,hin,cut,facts⟩:=L.first d x p good raw m n stage
  let flags:=LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g sg
  have dom:=initial (start WindowParams.first) x p (by decide) d raw stage
  have carried:=stepInput_gen_shadow7 (start WindowParams.first) (Shadow7.sbP (start WindowParams.first)) x p (by decide) (by decide) good raw v g sg dom input hin.farSmall
  have base:out.phase=raw'.phase:=cutPhase cut
  have ph:=base.trans (endRaw_phase (start WindowParams.first) x p (by decide) good raw v dom)
  have back:=L.firstBack d x p good raw m stage
  have same:run (LeaveCutsCore150.leave WindowParams.first) n v=run (Shadow7.leaveP WindowParams.first) n v:=
    (Admission150.Inputs.crt_pair (by decide) (by decide) hin).1 n
  show (run (LeaveCutsCore150.leave WindowParams.first) n v).phase=(pullState (OB5.sig (start WindowParams.first-1)) raw).phase ∧
    ReadyW d x p (start WindowParams.first+15) (run (LeaveCutsCore150.leave WindowParams.first) n v) ∧
    (∀t,run (LeaveCutsCore150.unleave WindowParams.first) t (run (LeaveCutsCore150.leave WindowParams.first) n v)=v) ∧
    (∀t,run (NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) t v=pullState (OB5.sig (start WindowParams.first-1)) raw)
  rw [same]
  exact ⟨ph,⟨firstNext,rfl,raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,
    unique_input input (fixed_input (start WindowParams.first) x p (by decide) good raw dom)⟩,
    fun t=>by rw [← same]; exact L.roundtrip WindowParams.first (by decide) (by decide) v _ g sg hin n t,back.2⟩

theorem receiptG (J : Nat) (hJ : J ≤ 24) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 26) (hk : k.val=i.val+1)
    (h2 : 1≤k.val) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → KeyW d x p i (run (nextF LeaveCutsCore150.params d i k).flatten m s) := by
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  have pk:=prev_of i k hk
  rw [next_eq d i k hk,←pk]
  simp only [run_append,run_take]
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L.scratch k h2 (by omega) d x p good raw s g sg pg ps m pre
  have native:=NativeJ7.from_domain_matched k h2 (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology (start (NativeJ7.prev k)) x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  exact ⟨row,bound,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepLeave k h2 h12 q hq _ _)⟩

theorem keepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (i k : Fin 26) (hk : k.val=i.val+1) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → ∀ i' : Fin 26, WindowParams.first.val ≤ i'.val → i'.val< i.val → KeyW d x p i' s →
      KeyW d x p i' (run (nextF LeaveCutsCore150.params d i k).flatten m s) := by
  intro s m _ i' h1 h2 key
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  obtain ⟨r,lim,chr,kept⟩:=key
  exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepOlder i k i' hk (by omega) (by omega) h12 d q hq s m)⟩

/-- The window's stock chain, generic in its last block `J` and its interior list `rest`. -/
theorem checkedG (J : Fin 26) (h4 : WindowParams.first.val+1 ≤ J.val) (hJ : J.val ≤ 24) (ports : Ports) (rest : List (Fin 26))
    (consec : Consec WindowParams.first rest) (mem : ∀ k ∈ rest, WindowParams.first.val+1 ≤ k.val ∧ k.val ≤ J.val)
    (exitT : exitTick WindowParams.first rest = start J+15)
    (L : LeavesUpTo J.val) (X : ExitLeaves J ports) (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (forwardW LeaveCutsCore150.params d WindowParams.first rest)
      (reverseW LeaveCutsCore150.params d WindowParams.first rest)
      (BeforeW d x p) (FinalW WindowParams.first J ports d x p) := by
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have bl:blockOf (exitTick WindowParams.first rest)=J.val+1:=by rw [exitT]; exact blockOf_next J
  have h:=window_strong LeaveCutsCore150.params d (ReadyW d x p) (KeyW d x p) (BeforeW d x p) (LastAt ports J d x p)
    WindowParams.first rest consec (firstStepG J.val L d x p good)
    (fun i k hm hk=>interiorG J.val (by omega) L d x p good i k hk (mem k hm).1 (mem k hm).2)
    (fun i k hm hk=>receiptG J.val (by omega) L d x p good i k hk (by have := mem k hm; omega) (by have := mem k hm; omega))
    (fun i k hm hk s m r i' h1 h2=>keepG J.val L d x p i k hk (by have := mem k hm; omega) s m r i' (by omega) h2)
    (by rw [exitT]; exact X.step d x good)
    (by
      intro s m _ i h1 h2 key
      rw [bl] at h2
      revert key
      rw [exitT]
      intro key
      obtain ⟨r,lim,chr,kept⟩:=key
      exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>X.keep i (by omega) (by omega) d q hq s m)⟩)
  refine checked_mono h ?_
  intro s ⟨last,saved⟩
  refine ⟨?_, last⟩
  intro k h1 h2
  obtain ⟨r, lim, chr, kept⟩ := saved k h1 (by rw [bl]; omega)
  exact ⟨r, lim, chr, ArchiveJ7.kept_stock k d r s kept⟩

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- One B-side code cell `OB5.sig t (t+1034+c)`, `c ≤ 8`: unmoved below 1301, else in the fold. -/
theorem bcell (t c : Nat) (ht : t ≤ 420) (hc : c ≤ 8) :
    (OB5.sig t (t+1034+c) = t+1034+c ∧ t+1034+c ≤ 1300) ∨
    (OB5.sig t (t+1034+c) = 3113-(t+1034+c) ∧ 1301 ≤ t+1034+c) := by
  by_cases h : 1301 ≤ t+1034+c
  · exact Or.inr ⟨NativeJ7.sig_moved _ _ (Or.inl ⟨h, by omega⟩), h⟩
  · exact Or.inl ⟨NativeJ7.sig_kept _ _ (by omega) (by omega), by omega⟩

/-- The 16 restore cells of tick `t ≤ 405`, sig-aware. -/
theorem cells_rangeG (t : Nat) (ht : t ≤ 420) (q : Nat) (h : q ∈ cellsRestoreP t) :
    (t+6 ≤ q ∧ q ≤ t+15) ∨ (t+1034 ≤ q ∧ q ≤ t+1042 ∧ q ≤ 1300) ∨ (2071 ≤ q+t ∧ q+t ≤ 2079 ∧ q ≤ 1812) := by
  have b0 := bcell t 0 ht (by omega)
  have b1 := bcell t 1 ht (by omega)
  have b3 := bcell t 3 ht (by omega)
  have b5 := bcell t 5 ht (by omega)
  have b6 := bcell t 6 ht (by omega)
  have b8 := bcell t 8 ht (by omega)
  simp only [Nat.add_zero] at b0
  simp only [cellsRestoreP, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  first
  | omega
  | (rcases b0 with ⟨e, l⟩ | ⟨e, l⟩ <;> rw [e] <;> omega)
  | (rcases b1 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1035 = t+1034+1 by omega]; rw [e]) <;> omega)
  | (rcases b3 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1037 = t+1034+3 by omega]; rw [e]) <;> omega)
  | (rcases b5 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1039 = t+1034+5 by omega]; rw [e]) <;> omega)
  | (rcases b6 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1040 = t+1034+6 by omega]; rw [e]) <;> omega)
  | (rcases b8 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1042 = t+1034+8 by omega]; rw [e]) <;> omega)

theorem key_rangeG (i : Fin 26) (hi : i.val ≤ 24) (q : Nat)
    (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    (start i+21 ≤ q ∧ q ≤ start i+30) ∨ (start i+1049 ≤ q ∧ q ≤ start i+1057 ∧ q ≤ 1300) ∨
    (2056 ≤ q+start i ∧ q+start i ≤ 2064 ∧ q ≤ 1812) := by
  have c := cells_rangeG (start i + 15) (by simp only [StairPacket.start]; omega) q (bank_cells i q h)
  omega

theorem keepLeaveG : KeepLeaveUpTo 24 := by
  intro k h2 h18 q hq v n
  have c := key_rangeG (NativeJ7.prev k) (by simp only [NativeJ7.prev]; omega) q hq
  have pk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
  obtain ⟨w1, w2⟩ := start_win7 k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  exact LeaveWindow150.leave_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega) n v

theorem keepOlderG : KeepOlderUpTo 24 := by
  intro i k i' hk h2 hik h18 d q hq s m
  have hs : start i' + 30 ≤ start k := by simp only [StairPacket.start]; omega
  have c := key_rangeG i' (by omega) q hq
  obtain ⟨w1, w2⟩ := start_win7 k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have sk : start k ≤ 405 := by simp only [StairPacket.start]; omega
  have pk : NativeJ7.prev k = i := Fin.ext (by simp only [NativeJ7.prev]; omega)
  rw [next_eq d i k hk]
  simp only [run_append, run_take]
  rw [LeaveWindow150.leave_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega)]
  simp only [NativeJ7.nextWindow, NativeJ7.window, run_append, run_take]
  have native : ¬Shadow7.MayTouch k (windowNet k q) := by
    have mid : (Shadow7.shape k).mid = Shadow7.sbP (start k)+16 := rfl
    rcases c with c | c | c
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have moved : windowNet k q = 3113 - q := by
        show OB5.sig (start k + 14) q = _
        exact NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, by omega⟩)
      rw [moved]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
  have port : q ∉ EnterJ7.ports k := by
    simp only [EnterJ7.ports, List.mem_cons, List.not_mem_nil, or_false]
    simp only [Wire] at *
    omega
  have admin : q ∉ NativeJ7.support k ++ ArchiveJ7.rawPortsList (NativeJ7.prev k) := by
    rw [List.mem_append, ArchiveJ7.raw_split]
    intro mem
    rcases mem with mem | mem
    · simp only [NativeJ7.support, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
      · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base, Wire] at *; omega)
          (by simp only [MappedCompressed.base, Wire] at *; omega)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
      · by_cases mv : 1301 ≤ 1044 + v
        · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨by simp only [MappedCompressed.base]; omega,
            by simp only [MappedCompressed.base]; omega⟩)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
        · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base]; omega)
            (by simp only [MappedCompressed.base]; omega)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
    · rw [List.mem_append] at mem
      have tk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
      rcases mem with mem | mem
      · simp only [ArchiveJ7.rawHead, cellsLoadP, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false, tk] at mem
        rcases mem with ⟨c', hc, e | e⟩ | e
        · simp only [Wire] at *; omega
        · by_cases mv : 1301 ≤ start k + 1034 + c'
          · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e
            simp only [Wire] at *; omega
          · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)] at e
            simp only [Wire] at *; omega
        · simp only [Shadow7.e0P, Wire] at *; omega
      · obtain ⟨kk, hkk, e⟩ := List.mem_map.mp mem
        have hk' := List.mem_range.mp hkk
        rw [tk] at e
        have qv : (q:Nat) = Shadow7.scratchS (start k) kk := e.symm
        rcases Shadow7.scratchS_cases (start k) kk (by omega) hk' with ⟨-, lo, hi⟩ | ⟨-, lo, hi⟩ <;>
          (simp only [Wire] at *; omega)
  exact Shadow7.ext_head (Shadow7.enterP k) k (NativeJ7.withArchive k d) _ s m _ q native (EnterJ7.notWire k port) admin
    (NativeJ7.admin_cover k (by omega) (by omega) d)
theorem endpoint22 : EndpointUpTo 24 := by
  intro j k hk h4 h18 d x p good raw s m n domain G S cut input scratch pg ps cross prior
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have hne : start j ≠ WideReference.firstBlock := by
    simp only [WideReference.firstBlock, StairPacket.start]; omega
  exact NativeJ7.stock_endpointG j k hk (by omega) h18 hne d x p good raw s m n domain G S cut input scratch pg ps cross
    prior (NativeJ7.band_clean_gen j (by omega) h18 d x p good raw s m domain _ _ _ cut)


/-- Every interior leaf of the window up to block 20 (start 375). -/
theorem leaves22 : LeavesUpTo 24 :=
  ⟨endpoint22, scratch, roundtrip, keepLeaveG, keepOlderG, NativeFirstJ7.first, NativeFirstJ7.firstBack⟩

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false


end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveStock150
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run

/-- The generic hand-off at block 21 is the exit-405 hand-off (pairs, flags, pending, raw ports of block 20). -/
theorem exitBridge420 :
    EnterJ7.lowerPairs ⟨25,by decide⟩=Portal420Flag7.loPairs ∧ EnterJ7.upperPairs ⟨25,by decide⟩=Portal420Flag7.hiPairs ∧
    EnterJ7.gate ⟨25,by decide⟩=435 ∧ EnterJ7.flagN ⟨25,by decide⟩=1618 ∧ EnterJ7.flagF ⟨25,by decide⟩=1616 ∧
    EnterJ7.flagU ⟨25,by decide⟩=1617 ∧ EnterJ7.pending ⟨25,by decide⟩=ParkEndpoint4207.src ∧
    ArchiveJ7.rawPorts ⟨24,by decide⟩ 20=1619 ∧ ArchiveJ7.rawPorts ⟨24,by decide⟩ 21=1620 ∧
    ArchiveJ7.rawPorts ⟨24,by decide⟩ 22=1621 := by
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩ <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem exitProg420 (d:Bool) : (exitF LeaveCutsCore150.params d 420).flatten=NativePack4207.lastWindow d ∧
    (exitR LeaveCutsCore150.params d 420).flatten=NativePack4207.lastUnwind d := by
  constructor
  · simp only [exitF,LeaveCutsCore150.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack4207.lastWindow,NativePack4207.endSlice,EndTick4207.physP,EndTick4207.P,NativePack4207.program,List.append_assoc]
  · simp only [exitR,LeaveCutsCore150.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack4207.lastUnwind,NativePack4207.endUndo,EndTick4207.physQ,EndTick4207.Q,NativePack4207.reverse,List.append_assoc]

/-- The exit at 420 (dadon's `step270` rendered at 420). -/
theorem exitStep420 (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (exitF LeaveCutsCore150.params d (start ⟨24,by decide⟩+15)).flatten
      (exitR LeaveCutsCore150.params d (start ⟨24,by decide⟩+15)).flatten
      (ReadyW d x p (start ⟨24,by decide⟩+15)) (LastAt ArchiveBoundary4207.codePorts ⟨24,by decide⟩ d x p) := by
  have e420 : start ⟨24,by decide⟩+15=420 := rfl
  rw [e420]
  obtain ⟨ef,er⟩:=exitProg420 d
  rw [ef,er]
  intro s m h
  obtain ⟨k,ek,raw,g,sg,pg,ps,pre⟩:=h
  have k20:k=⟨25,by decide⟩:=Fin.ext (by have := ek; simp only [StairPacket.start] at this; show k.val=25; omega)
  subst k20
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,r20,r21,r22⟩:=exitBridge420
  let z:=unsigned 420 x p
  have short:Shadow7.SmallIfFar 39 15 z:=(Shadow7.Envelope.inputs x p 420 (lt_trans good.small good.cap) good.cap (by decide)).1
  have old:=LeaveJ7.Admission.actualNumbers ⟨24,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 39 420 x p=(2*2^55≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have cut:=pre.cut
  have e20:start (⟨25,by decide⟩:Fin 26)=420:=rfl
  have sb:Shadow7.sbP 420=39:=by decide
  rw [bl,bu,bg,bn,bf,bu',bp] at cut
  simp only [e20,sb] at cut
  have facts:=pre.facts
  have mode:s.basis 1619=decide (Shadow.far 46 15 (unsigned 405 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1620=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 405 x p).v<(unsigned 405 x p).u))
        ((Shadow7.physicalCells ArchiveBoundary4207.sourceIdx s).take 5)):=by rw [←r21]; simpa only [Shadow7.physicalCells_eq] using facts.suffix
  have cross:s.basis 1621=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      HighBankSum.crossBit (LeaveJ7.TrueMiddle.d ⟨24,by decide⟩ (unsigned 405 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack4207.matched_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 420 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 405 x p) pg ps _
    old.odd old.farSmall (by simpa only [Shadow7.physicalCells_eq] using facts.records) mode side cross
  obtain ⟨r,lim,truth,frame⟩:=last.2.1
  have pc:signedAt 405 x p pg ps=WideReference.canonical 405 x p:=pre.pastCanonical
  have chr:Chronology 405 x p r:=by unfold Chronology;rw [←pc];exact truth
  exact ⟨last.1,⟨r,lim,chr,frame⟩,last.2.2⟩


/-- A wire bound for a whole program from a per-instruction check. -/
theorem wires_bound405 (P : Program) (b : Nat) (h : P.all (fun i => decide (∀ q ∈ i.wires, q < b)) = true) :
    ∀ q ∈ wires P, q < b := by
  induction P with
  | nil => intro q hq; simp [wires] at hq
  | cons i p ih =>
    intro q hq
    simp only [wires, Finset.mem_union] at hq
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases hq with hq | hq
    · exact of_decide_eq_true h.1 q hq
    · exact ih h.2 q hq

theorem portalInv_low420 : ∀ q ∈ wires (Shadow7.portalInvP 420), q < 1640 :=
  wires_bound405 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem park_low420 : ∀ q ∈ wires (Shadow7.parkP 420), q < 1640 :=
  wires_bound405 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem raw420_ranges : ∀ w ∈ ArchiveBoundary4207.rawPortsList,
    (426 ≤ w ∧ w ≤ 435) ∨ (1650 ≤ w ∧ w ≤ 1659) ∨ (879 ≤ w ∧ w ≤ 881) ∨ (1556 ≤ w ∧ w ≤ 1647) ∨
    (882 ≤ w ∧ w ≤ 923) := by
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

/-- The exit pieces at 420 never touch the window's key cells (blocks first..19; first = block 1, tick 90). -/
theorem keepExit420 : ∀ (i : Fin 26), WindowParams.first.val ≤ i.val → i.val < 24 → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i), ∀ (s:State) (m:List Bool),
    (run (exitF LeaveCutsCore150.params d (start ⟨24,by decide⟩+15)).flatten m s).basis q=s.basis q := by
  intro i h3 h17 d q hq s m
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have c := key_rangeG i (by omega) q hq
  have si : 45 ≤ start i ∧ start i ≤ 390 := by simp only [StairPacket.start]; omega
  have e420 : start ⟨24,by decide⟩+15=420 := rfl
  rw [e420]
  simp only [exitF, LeaveCutsCore150.params,Shadow7.params, ofParts, List.flatten_cons, List.flatten_nil, List.append_nil, run_append, run_take]
  -- exit archive load
  rw [run_preserves_outside (Shadow7.exitLoadP 420 d) _ _ q (fun hit => by
    have r := raw420_ranges q (List.mem_toFinset.mp (ArchiveBoundary4207.load_cover d hit))
    simp only [Wire] at *; omega)]
  -- stock pack at 410
  rw [run_preserves_outside _ _ _ q (fun hit => by
    rw [renameProgram_support] at hit
    obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hit
    have pc := (WindowCovered.pack_cells d 410 (by decide) (by decide)).1 w hw
    obtain ⟨r, r1, r2, er | er⟩ := pc <;> rw [er, OB5.sig_nat] at e <;> unfold OB5.sigNat at e <;>
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> split_ifs at e <;>
      simp only [MappedCompressed.base, Wire] at * <;> omega)]
  -- the stock tick at 420
  have nt : q ∉ wires (renameProgram (OB5.sig 420) (TickRanges.tick base 420)) :=
    EndTick4207.physical_free EndTick4207.P EndTick4207.supports.1 q (by
      apply WideReference.away (by decide)
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 16 ≤ n → n = n - 16 + 16 := fun n h => by omega
        exact ⟨q - 16, by omega, Or.inl (hn q (by omega))⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 1044 ≤ n → n = 1028 + (n - 1044) + 16 := fun n h => by omega
        exact ⟨q - 1044, by omega, Or.inr (hn q (by omega))⟩
      · rw [NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, hh⟩)]
        have hn : ∀ n : Nat, n ≤ 1812 → 1301 ≤ 3113 - n → 3113 - n = 1028 + (2069 - n) + 16 := fun n h h' => by omega
        exact ⟨2069 - q, by omega, Or.inr (hn q hh (by omega))⟩)
  rw [run_preserves_outside _ _ _ q nt]
  -- exit portal (inverse) and park
  rw [run_preserves_outside (Shadow7.portalInvP 420) _ _ q (fun hit => by
    have f := portalInv_low420 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.portal_wires 420 (by decide) (by decide)).2 q hit
      have hr : railP 420 = 93 := by decide
      unfold footP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]
  rw [run_preserves_outside (Shadow7.parkP 420) _ _ q (fun hit => by
    have f := park_low420 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.park_wires 420 (by decide) (by decide)).1 q hit
      have hr : railP 420 = 93 := by decide
      unfold parkFootP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]

/-- The exit of the window whose last block is 20 (start 405): the exit at 405. -/
theorem exitLeaves420 : ExitLeaves ⟨24,by decide⟩ ArchiveBoundary4207.codePorts :=
  ⟨exitStep420, keepExit420⟩

end ECDSAAdd.Entrant.StairPacket.LeaveStock150
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.LeaveWindow150
open ECDSAAdd.Entrant.StairPacket.CRTWindow
open Arithmetic MappedCompressed WindowFold Baselines Challenge GateMirror Partial WindowParams
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! The ledger: the Shadow7 closed forms with the 20 window leaves replaced. -/

def tcV : Pieces Nat := { WindowParams7.tcV with
  leave := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+100+CRTBarrel.barrelT (start j) false
    else if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+115 else toffoliCount (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+129+CRTBarrel.barrelT (start j) true
    else if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+147 else toffoliCount (Shadow7.leaveMoveInvP j) }

def mcV : Pieces Nat := { WindowParams7.mcV with
  leave := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+89+CRTBarrel.barrelM (start j) false
    else if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+93 else measurementCount (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+60+CRTBarrel.barrelM (start j) true
    else if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+61 else measurementCount (Shadow7.leaveMoveInvP j) }

def slotsV : Pieces Nat := { WindowParams7.slotsV with
  leave := fun j => if crtBlocks j then
      6*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+648+3*Shadow7.wpP (start j+15)+
        CRTBarrel.barrelSlots (start j) false
    else if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+746+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)
  leaveInv := fun j => if crtBlocks j then
      6*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+619+3*Shadow7.wpP (start j+15)+
        CRTBarrel.barrelSlots (start j) true
    else if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+714+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveInvP j) }

/-! Projections of the structure update, by rewriting (a defeq check of `LeaveCutsCore150.params` against
`Shadow7.params` would unfold the leave programs). -/

theorem params_enter : LeaveCutsCore150.params.enter = Shadow7.params.enter := by simp only [LeaveCutsCore150.params]

theorem params_enterInv : LeaveCutsCore150.params.enterInv = Shadow7.params.enterInv := by simp only [LeaveCutsCore150.params]

theorem params_leave : LeaveCutsCore150.params.leave = LeaveCutsCore150.leave := by simp only [LeaveCutsCore150.params]

theorem params_leaveInv : LeaveCutsCore150.params.leaveInv = LeaveCutsCore150.unleave := by simp only [LeaveCutsCore150.params]

theorem params_load : LeaveCutsCore150.params.load = Shadow7.params.load := by simp only [LeaveCutsCore150.params]

theorem params_restore : LeaveCutsCore150.params.restore = Shadow7.params.restore := by simp only [LeaveCutsCore150.params]

theorem params_portal : LeaveCutsCore150.params.portal = Shadow7.params.portal := by simp only [LeaveCutsCore150.params]

theorem params_portalInv : LeaveCutsCore150.params.portalInv = Shadow7.params.portalInv := by simp only [LeaveCutsCore150.params]

theorem params_park : LeaveCutsCore150.params.park = Shadow7.params.park := by simp only [LeaveCutsCore150.params]

theorem params_parkInv : LeaveCutsCore150.params.parkInv = Shadow7.params.parkInv := by simp only [LeaveCutsCore150.params]

theorem params_exitLoad : LeaveCutsCore150.params.exitLoad = Shadow7.params.exitLoad := by simp only [LeaveCutsCore150.params]

theorem params_exitRestore : LeaveCutsCore150.params.exitRestore = Shadow7.params.exitRestore := by simp only [LeaveCutsCore150.params]

theorem params_routed : LeaveCutsCore150.params.routed = Shadow7.params.routed := by simp only [LeaveCutsCore150.params]

theorem params_unrouted : LeaveCutsCore150.params.unrouted = Shadow7.params.unrouted := by simp only [LeaveCutsCore150.params]

theorem params_pack : LeaveCutsCore150.params.pack = Shadow7.params.pack := by simp only [LeaveCutsCore150.params]

theorem params_unpack : LeaveCutsCore150.params.unpack = Shadow7.params.unpack := by simp only [LeaveCutsCore150.params]

theorem params_tick : LeaveCutsCore150.params.tick = Shadow7.params.tick := by simp only [LeaveCutsCore150.params]

theorem params_receiver : LeaveCutsCore150.params.receiver = Shadow7.params.receiver := by simp only [LeaveCutsCore150.params]

/-- Outside the CRT blocks the leave is the plain Shadow7 move leave, priced by the base's closed forms. -/
theorem base_leave (j : Fin 26) :
    toffoliCount (Shadow7.leaveMoveP j) = (if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+3*Shadow7.lowsP (start j)+115 else toffoliCount (Shadow7.leaveMoveP j)) ∧
    toffoliCount (Shadow7.leaveMoveInvP j) = (if WindowParams.inBlocks j then 5*Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+147 else toffoliCount (Shadow7.leaveMoveInvP j)) ∧
    measurementCount (Shadow7.leaveMoveP j) = (if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+Shadow7.lowsP (start j)+93 else measurementCount (Shadow7.leaveMoveP j)) ∧
    measurementCount (Shadow7.leaveMoveInvP j) = (if WindowParams.inBlocks j then Shadow7.wpP (start j)+Shadow7.liveW (start j)+2*Shadow7.lowsP (start j)+61 else measurementCount (Shadow7.leaveMoveInvP j)) ∧
    gateSlots (Shadow7.leaveMoveP j) ≤ (if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+10*Shadow7.lowsP (start j)+746+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveP j)) ∧
    gateSlots (Shadow7.leaveMoveInvP j) ≤ (if WindowParams.inBlocks j then 18*Shadow7.wpP (start j)+5*Shadow7.liveW (start j)+11*Shadow7.lowsP (start j)+714+3*Shadow7.wpP (start j+15) else gateSlots (Shadow7.leaveMoveInvP j)) := by
  by_cases h : WindowParams.inBlocks j = true
  · simp only [h, ↓reduceIte]
    simp only [WindowParams.inBlocks, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨t1, t2, m1, m2, s1, s2⟩ := Shadow7.leaveMove_counts j (by omega) (by omega)
    exact ⟨t1, t2, m1, m2, s1.le, s2.le⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte, le_refl, and_self]

theorem tc_eq : LeaveCutsCore150.params.map toffoliCount = tcV := by
  have h := WindowParams7.tc_eq
  unfold Pieces.map at h ⊢
  simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
  unfold tcV
  rw [← h]
  dsimp only
  congr 1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).1]
      exact (base_leave j).1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).2]
      exact (base_leave j).2.1

theorem mc_eq : LeaveCutsCore150.params.map measurementCount = mcV := by
  have h := WindowParams7.mc_eq
  unfold Pieces.map at h ⊢
  simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
  unfold mcV
  rw [← h]
  dsimp only
  congr 1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).1]
      exact (base_leave j).2.2.1
  · funext j
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.2.1
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).2]
      exact (base_leave j).2.2.2.1

private theorem map_leave_update {α β : Type} (P : Pieces α) (f : α → β)
    (a b : Fin 26 → α) :
    Pieces.map f {P with leave := a, leaveInv := b} =
      {P.map f with leave := fun j => f (a j), leaveInv := fun j => f (b j)} := rfl

private theorem le_leave_update {P V : Pieces Nat} (h : P.Le V)
    {a b x y : Fin 26 → Nat} (forward : ∀ j, a j ≤ x j) (mirror : ∀ j, b j ≤ y j) :
    Pieces.Le {P with leave := a, leaveInv := b} {V with leave := x, leaveInv := y} :=
  ⟨h.enter, h.enterInv, forward, mirror, h.load, h.restore, h.portal, h.portalInv, h.park,
    h.parkInv, h.exitLoad, h.exitRestore, h.routed, h.unrouted, h.pack, h.unpack, h.tick, h.receiver⟩

theorem slots_le : (LeaveCutsCore150.params.map gateSlots).Le slotsV := by
  rw [LeaveCutsCore150.params, map_leave_update]
  unfold slotsV
  refine le_leave_update WindowParams7.slots_le ?_ ?_
  · intro j; dsimp only
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.2.2.1.le
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).1]
      exact (base_leave j).2.2.2.2.1
  · intro j; dsimp only
    by_cases hc : j.val ≤ 24
    · rw [if_pos ((inBlocks_iff j).mpr hc)]; exact (leave_metrics j (Nat.zero_le _) hc).2.2.2.2.2.le
    · rw [if_neg (mt (inBlocks_iff j).mp hc), (leave_other j hc).2]
      exact (base_leave j).2.2.2.2.2

theorem counts (d : Bool) (j : Fin 26) (js : List (Fin 26)) :
    toffoliCount (forwardW LeaveCutsCore150.params d j js)=(forwardL tcV d j js).sum ∧
    toffoliCount (reverseW LeaveCutsCore150.params d j js)=(reverseL tcV d j js).sum ∧
    measurementCount (forwardW LeaveCutsCore150.params d j js)=(forwardL mcV d j js).sum ∧
    measurementCount (reverseW LeaveCutsCore150.params d j js)=(reverseL mcV d j js).sum := by
  have f := measure_forward toffoliCount toffoliCount_append LeaveCutsCore150.params d j js
  have r := measure_reverse toffoliCount toffoliCount_append LeaveCutsCore150.params d j js
  have g := measure_forward measurementCount measurementCount_append LeaveCutsCore150.params d j js
  have q := measure_reverse measurementCount measurementCount_append LeaveCutsCore150.params d j js
  change toffoliCount _=(forwardL (LeaveCutsCore150.params.map toffoliCount) d j js).sum at f
  change toffoliCount _=(reverseL (LeaveCutsCore150.params.map toffoliCount) d j js).sum at r
  change measurementCount _=(forwardL (LeaveCutsCore150.params.map measurementCount) d j js).sum at g
  change measurementCount _=(reverseL (LeaveCutsCore150.params.map measurementCount) d j js).sum at q
  rw [tc_eq] at f r
  rw [mc_eq] at g q
  exact ⟨f,r,g,q⟩

/-- The CRT window (blocks 1..22, exit 420; CRT barrel on 1..22): counts by one Nat decide over the closed forms. -/
theorem ship_counts :
    toffoliCount (forwardW LeaveCutsCore150.params true first WindowParams7.rest7)=128011 ∧
    toffoliCount (forwardW LeaveCutsCore150.params false first WindowParams7.rest7)=128011 ∧
    toffoliCount (reverseW LeaveCutsCore150.params true first WindowParams7.rest7)=128353 ∧
    toffoliCount (reverseW LeaveCutsCore150.params false first WindowParams7.rest7)=128378 ∧
    measurementCount (forwardW LeaveCutsCore150.params true first WindowParams7.rest7)=66269 ∧
    measurementCount (forwardW LeaveCutsCore150.params false first WindowParams7.rest7)=66269 ∧
    measurementCount (reverseW LeaveCutsCore150.params true first WindowParams7.rest7)=65626 ∧
    measurementCount (reverseW LeaveCutsCore150.params false first WindowParams7.rest7)=65651 := by
  rw [(counts true first WindowParams7.rest7).1,(counts false first WindowParams7.rest7).1,(counts true first WindowParams7.rest7).2.1,(counts false first WindowParams7.rest7).2.1,
    (counts true first WindowParams7.rest7).2.2.1,(counts false first WindowParams7.rest7).2.2.1,(counts true first WindowParams7.rest7).2.2.2,
    (counts false first WindowParams7.rest7).2.2.2]
  decide +kernel

theorem slot_sums : (forwardL slotsV true first WindowParams7.rest7).sum ≤ 2370644 ∧ (forwardL slotsV false first WindowParams7.rest7).sum ≤ 2370644 ∧
    (reverseL slotsV true first WindowParams7.rest7).sum ≤ 2333949 ∧ (reverseL slotsV false first WindowParams7.rest7).sum ≤ 2333949 := by
  decide +kernel

/-- Slot bounds of the CRT window (upper bounds only; the judge has no slot ceiling). -/
theorem ship_slots : gateSlots (forwardW LeaveCutsCore150.params true first WindowParams7.rest7) ≤ 2370644 ∧
    gateSlots (forwardW LeaveCutsCore150.params false first WindowParams7.rest7) ≤ 2370644 ∧
    gateSlots (reverseW LeaveCutsCore150.params true first WindowParams7.rest7) ≤ 2333949 ∧
    gateSlots (reverseW LeaveCutsCore150.params false first WindowParams7.rest7) ≤ 2333949 := by
  rw [measure_forward gateSlots gateSlots_append, measure_forward gateSlots gateSlots_append,
    measure_reverse gateSlots gateSlots_append, measure_reverse gateSlots gateSlots_append]
  exact ⟨(forwardL_le slots_le true first WindowParams7.rest7).trans slot_sums.1,
    (forwardL_le slots_le false first WindowParams7.rest7).trans slot_sums.2.1,
    (reverseL_le slots_le true first WindowParams7.rest7).trans slot_sums.2.2.1,
    (reverseL_le slots_le false first WindowParams7.rest7).trans slot_sums.2.2.2⟩

theorem parts_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.before (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPart (start j), proper g = true) := by
  have p := WindowPhysicalW7.leaveMove_proper j (by omega) (by omega)
  rw [split_ops] at p
  exact ⟨fun g hg => p g (List.mem_append_left _ hg),
    fun g hg => p g (List.mem_append_right _ (List.mem_append_right _ hg))⟩

theorem proper_swap (a c : List Gate) (g g' : Gate) (hg : proper g' = true)
    (h : ∀ x ∈ a ++ ([g] ++ c), proper x = true) : ∀ x ∈ a ++ ([g'] ++ c), proper x = true := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx)
  · rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hg
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem partsC_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := parts_proper j h0 h1
  rw [before_split] at pb
  rw [after_split] at pa
  rw [beforeC_split, afterPartC_split]
  refine ⟨proper_swap _ _ _ _ ?_ pb, proper_swap _ _ _ _ ?_ pa⟩
  · simp only [proper, decide_eq_true_eq]; ((try unfold Wire at *); omega)
  · simp only [proper, decide_eq_true_eq]; unfold Shadow7.e0P; ((try unfold Wire at *); omega)

theorem partsC4_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC4 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC_proper j h0 h1
  rw [beforeC_cut] at pb
  rw [beforeC4_split]
  refine ⟨proper_swap _ _ _ _ ?_ pb, pa⟩
  have := (start_win7 j h0 (by omega)).2
  simp only [proper, decide_eq_true_eq]
  unfold start at *
  constructor <;> ((try unfold Wire at *); omega)

theorem proper_swapL (a c b b' : List Gate) (hb : ∀ g ∈ b', proper g = true)
    (h : ∀ x ∈ a ++ (b ++ c), proper x = true) : ∀ x ∈ a ++ (b' ++ c), proper x = true := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx)
  · rcases List.mem_append.mp hx with hx | hx
    · exact hb x hx
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem partsC5_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC5 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC4_proper j h0 h1
  rw [beforeC4_cut, beforeC5_cut] at pb
  rw [beforeC5_split, beforeC5_cut]
  refine ⟨proper_swapL _ _ _ _ ?_ pb, pa⟩
  have win := start_win7 j h0 h1
  have r := Shadow7.rail_win win.1 win.2
  have t0 : Partial.tagsP.getD 0 0 = 1576 := rfl
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> simp only [proper, decide_eq_true_eq, t0] <;> unfold Shadow7.a0P Shadow7.e0P at * <;>
    ((try unfold Wire at *); omega)

theorem partsC6_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC5 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC2 (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC5_proper j h0 h1
  refine ⟨pb, ?_⟩
  rw [afterPartC_split, tailD_cut] at pa
  simp only [List.append_assoc] at pa
  rw [afterPartC2_split]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact pa x (List.mem_append_left _ hx)
  · exact pa x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem proper_swap2 (a b c : List Gate) (g1 g1' g2 g2' : Gate) (hg1 : proper g1' = true) (hg2 : proper g2' = true)
    (h : ∀ x ∈ a ++ ([g1] ++ (b ++ ([g2] ++ c))), proper x = true) :
    ∀ x ∈ a ++ ([g1'] ++ (b ++ ([g2'] ++ c))), proper x = true := by
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl | hx | rfl | hx
  · exact h x (by simp [hx])
  · exact hg1
  · exact h x (by simp [hx])
  · exact hg2
  · exact h x (by simp [hx])

theorem partsC8_proper (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    (∀ g ∈ CRTBarrel.beforeC5 (start j), proper g = true) ∧ (∀ g ∈ CRTBarrel.afterPartC3 (start j), proper g = true) := by
  obtain ⟨pb, pa⟩ := partsC6_proper j h0 h1
  refine ⟨pb, ?_⟩
  rw [afterPartC2_split, tailE_cut] at pa
  rw [afterPartC3_split]
  have hp : proper (GateMirror.Gate.cx (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) = true := by
    have win := start_win7 j h0 h1
    have r := Shadow7.rail_win win.1 win.2
    simp only [proper, decide_eq_true_eq]; unfold Shadow7.a0P at *; ((try unfold Wire at *); omega)
  have := proper_swap2 (CRTBarrel.tailD0 (start j) ++ (CRTBarrel.tailD1 (start j) ++
      ([.cx (Shadow7.e0P (start j) + 4) 1559] ++ CRTBarrel.tailE0 (start j))))
    (CRTBarrel.chainMid (start j)) (CRTBarrel.tailE1 (start j)) (.make 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) (.cx (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559)
    (.pop 1558 (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) (.cx (Shadow7.a0P (start j) + Shadow7.lowsP (start j) - 1) 1559) hp hp (by simpa only [List.append_assoc] using pa)
  simpa only [List.append_assoc] using this

theorem leave_phys (j : Fin 26) (h0 : 0 ≤ j.val) (h1 : j.val ≤ 24) :
    GatePhysical (LeaveCutsCore150.leave j) ∧ GatePhysical (LeaveCutsCore150.unleave j) := by
  obtain ⟨pb, pa⟩ := partsC8_proper j h0 h1
  have b := physical_of_proper _ (PBOps.before100_proper j h1 (PBScanRow.beforeRow_proper j pb))
  have a := physical_of_proper _ (PBOps.after100_proper j h1 pa)
  rw [(leave_eq j h0 h1).1, (leave_eq j h0 h1).2]
  exact ⟨WindowPhysicalW.appP (WindowPhysicalW.appP b.1 (CRTBarrel.barrel_phys j h0 h1 false)) a.1,
    WindowPhysicalW.appP (WindowPhysicalW.appP a.2 (CRTBarrel.barrel_phys j h0 h1 true)) b.2⟩

theorem params_onE (d : Bool) : LeaveCutsCore150.params.OnE WindowCovered.CoveredW d 0 24 := by
  have h := WindowCovered7.params_onE d
  constructor
  · intro j h0 h1
    have s := h.block j h0 h1
    simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
    by_cases hc : j.val ≤ 24
    · have l := leave_cov j (Nat.zero_le _) hc
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
    · have e := leave_other j hc
      rw [e.1, e.2]
      have l := WindowCovered7.leaveMove_cov j h0 h1
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.first j hj
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.later j h0 h1
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.saved j h0 h1
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.exit j hj

/-- The CRT window (both directions, both kernels) lies in the K2 domain. -/
theorem window_covered (d : Bool) :
    WindowCovered.CoveredW (forwardW LeaveCutsCore150.params d WindowParams.first WindowParams7.rest7) ∧
    WindowCovered.CoveredW (reverseW LeaveCutsCore150.params d WindowParams.first WindowParams7.rest7) :=
  ⟨flatten_of WindowCovered.nilW (fun ha hb => WindowCovered.appW ha hb) _
      (forwardL_onE (params_onE d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide)),
    flatten_of WindowCovered.nilW (fun ha hb => WindowCovered.appW ha hb) _
      (reverseL_onE (params_onE d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide))⟩

theorem params_onE_phys (d : Bool) : LeaveCutsCore150.params.OnE GatePhysical d 0 24 := by
  have h := WindowPhysicalW7.params_onE_phys d
  constructor
  · intro j h0 h1
    have s := h.block j h0 h1
    simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]
    by_cases hc : j.val ≤ 24
    · have l := leave_phys j (Nat.zero_le _) hc
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
    · have e := leave_other j hc
      rw [e.1, e.2]
      have l := WindowPhysicalW7.leaveMove_phys j h0 h1
      exact ⟨s.1, s.2.1, l.1, l.2, s.2.2.2.2⟩
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.first j hj
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.later j h0 h1
  · intro j h0 h1; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.saved j h0 h1
  · intro j hj; simp only [params_enter, params_enterInv, params_leave, params_leaveInv, params_load, params_restore, params_portal, params_portalInv, params_park, params_parkInv, params_exitLoad, params_exitRestore, params_routed, params_unrouted, params_pack, params_unpack, params_tick, params_receiver]; exact h.exit j hj

/-- The CRT window (both directions, both kernels) is physical. -/
theorem window_physical (d : Bool) :
    GatePhysical (forwardW LeaveCutsCore150.params d WindowParams.first WindowParams7.rest7) ∧
    GatePhysical (reverseW LeaveCutsCore150.params d WindowParams.first WindowParams7.rest7) :=
  ⟨flatten_of WindowPhysicalW.nilP (fun ha hb => WindowPhysicalW.appP ha hb) _
      (forwardL_onE (params_onE_phys d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide)),
    flatten_of WindowPhysicalW.nilP (fun ha hb => WindowPhysicalW.appP ha hb) _
      (reverseL_onE (params_onE_phys d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide))⟩

theorem ship_toffoliF_true : toffoliCount (forwardW LeaveCutsCore150.params true first WindowParams7.rest7) = 128011 :=
  ship_counts.1

theorem ship_toffoliF_false : toffoliCount (forwardW LeaveCutsCore150.params false first WindowParams7.rest7) = 128011 :=
  ship_counts.2.1

theorem ship_toffoliR_true : toffoliCount (reverseW LeaveCutsCore150.params true first WindowParams7.rest7) = 128353 :=
  ship_counts.2.2.1

theorem ship_toffoliR_false : toffoliCount (reverseW LeaveCutsCore150.params false first WindowParams7.rest7) = 128378 :=
  ship_counts.2.2.2.1

theorem ship_measureF : measurementCount (forwardW LeaveCutsCore150.params true first WindowParams7.rest7) = 66269 ∧
    measurementCount (forwardW LeaveCutsCore150.params false first WindowParams7.rest7) = 66269 :=
  ⟨ship_counts.2.2.2.2.1, ship_counts.2.2.2.2.2.1⟩

theorem ship_measureR : measurementCount (reverseW LeaveCutsCore150.params true first WindowParams7.rest7) = 65626 ∧
    measurementCount (reverseW LeaveCutsCore150.params false first WindowParams7.rest7) = 65651 :=
  ship_counts.2.2.2.2.2.2

theorem ship_slotsF : gateSlots (forward45plus1 true) ≤ 2370644 ∧ gateSlots (forward45plus1 false) ≤ 2370644 :=
  ⟨ship_slots.1, ship_slots.2.1⟩

theorem ship_slotsR : gateSlots (reverse45plus1 true) ≤ 2333949 ∧ gateSlots (reverse45plus1 false) ≤ 2333949 :=
  ship_slots.2.2

end ECDSAAdd.Entrant.StairPacket.LeaveWindow150
end
