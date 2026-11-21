import ECDSAAdd.Framework.RunAppendAgreement
import ECDSAAdd.Submission.Entrant.BOptimizations
import ECDSAAdd.Submission.Entrant.StairSideA
import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.QTop
import ECDSAAdd.Submission.Entrant.Stair44Stock
import Mathlib.Tactic
import ECDSAAdd.Framework.WireRenamePool
import ECDSAAdd.Submission.Entrant.MainB

section

section

namespace ECDSAAdd.Entrant.StairPacket.WindowFieldParity
open Arithmetic MappedCompressed CodecBitSliceVerify WindowParityDirty
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
def addr (i : Nat) := OB5.sig 511 (NewHistory5.payloadWire base i)
private def block (j : Nat) := (List.range 16).map (8*j+·)
private def stable0 := List.range 152
private def stable1 := List.range' 168 8
private def stable2 := List.range' 192 8
private def stable3 := List.range' 216 8
private def stable4 := List.range' 240 8
private def stable5 := List.range' 264 8
private def stable6 := List.range' 288 8
private def stable7 := List.range' 312 8
private def stable8 := List.range' 336 8
private def stable9 := List.range' 360 8
private def stable10 := List.range' 384 8
private def stable11 := List.range' 408 8
private def stable12 := List.range' 432 8
private def stable13 := List.range' 456 8
private def stable14 := List.range' 480 8
private def stable15 := List.range' 504 8
private def stable16 := List.range' 528 8
private def stable17 := List.range' 552 8
private def stable18 := List.range' 576 8
private def stable19 := List.range' 600 216
private theorem split : List.range 816 = stable0 ++ block 19 ++ stable1 ++ block 22 ++ stable2 ++ block 25 ++ stable3 ++ block 28 ++ stable4 ++ block 31 ++ stable5 ++ block 34 ++ stable6 ++ block 37 ++ stable7 ++ block 40 ++ stable8 ++ block 43 ++ stable9 ++ block 46 ++ stable10 ++ block 49 ++ stable11 ++ block 52 ++ stable12 ++ block 55 ++ stable13 ++ block 58 ++ stable14 ++ block 61 ++ stable15 ++ block 64 ++ stable16 ++ block 67 ++ stable17 ++ block 70 ++ stable18 ++ block 73 ++ stable19 := by decide +kernel
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
def Elsewhere (i : Nat) := i<152 ∨ (168 ≤ i ∧ i<176) ∨ (192 ≤ i ∧ i<200) ∨ (216 ≤ i ∧ i<224) ∨ (240 ≤ i ∧ i<248) ∨ (264 ≤ i ∧ i<272) ∨ (288 ≤ i ∧ i<296) ∨ (312 ≤ i ∧ i<320) ∨ (336 ≤ i ∧ i<344) ∨ (360 ≤ i ∧ i<368) ∨ (384 ≤ i ∧ i<392) ∨ (408 ≤ i ∧ i<416) ∨ (432 ≤ i ∧ i<440) ∨ (456 ≤ i ∧ i<464) ∨ (480 ≤ i ∧ i<488) ∨ (504 ≤ i ∧ i<512) ∨ (528 ≤ i ∧ i<536) ∨ (552 ≤ i ∧ i<560) ∨ (576 ≤ i ∧ i<584) ∨ (600 ≤ i ∧ i<816)
def stockParity (s : State) := TraceParity5.parity (FrontierEntry1591Field.controls.map s.basis)
private theorem allSum (s : State) : stockParity s=
    ((((((((((((((((((((((((((((((((((((((sum stable0 s ^^ sum (block 19) s) ^^ sum stable1 s) ^^ sum (block 22) s) ^^ sum stable2 s) ^^ sum (block 25) s) ^^ sum stable3 s) ^^ sum (block 28) s) ^^ sum stable4 s) ^^ sum (block 31) s) ^^ sum stable5 s) ^^ sum (block 34) s) ^^ sum stable6 s) ^^ sum (block 37) s) ^^ sum stable7 s) ^^ sum (block 40) s) ^^ sum stable8 s) ^^ sum (block 43) s) ^^ sum stable9 s) ^^ sum (block 46) s) ^^ sum stable10 s) ^^ sum (block 49) s) ^^ sum stable11 s) ^^ sum (block 52) s) ^^ sum stable12 s) ^^ sum (block 55) s) ^^ sum stable13 s) ^^ sum (block 58) s) ^^ sum stable14 s) ^^ sum (block 61) s) ^^ sum stable15 s) ^^ sum (block 64) s) ^^ sum stable16 s) ^^ sum (block 67) s) ^^ sum stable17 s) ^^ sum (block 70) s) ^^ sum stable18 s) ^^ sum (block 73) s) ^^ sum stable19 s) := by
  unfold stockParity FrontierEntry1591Field.controls ParityHost5.payloadControls
  rw [split]
  simp only [List.map_append,List.map_map,join,sum,Function.comp_def,addr]
private theorem pair_step (p q s x y : Bool) : (((p ^^ x) ^^ s) ^^ ((q ^^ y) ^^ s)) = ((p ^^ q) ^^ (x ^^ y)) := by
  cases p <;> cases q <;> cases s <;> cases x <;> cases y <;> rfl
theorem fold_pair (rows : Nat→Nat) (dirs : Nat→Bool) (a b : State)
    (rest : ∀i,Elsewhere i→a.basis (addr i)=b.basis (addr i))
    (custom : ∀j,j=19 ∨ j=22 ∨ j=25 ∨ j=28 ∨ j=31 ∨ j=34 ∨ j=37 ∨ j=40 ∨ j=43 ∨ j=46 ∨ j=49 ∨ j=52 ∨ j=55 ∨ j=58 ∨ j=61 ∨ j=64 ∨ j=67 ∨ j=70 ∨ j=73 → ∀i<16,a.basis (site j i)=(get (ArchivePortAction.code (dirs j)) i).testBit (rows j))
    (stock : ∀j,j=19 ∨ j=22 ∨ j=25 ∨ j=28 ∨ j=31 ∨ j=34 ∨ j=37 ∨ j=40 ∨ j=43 ∨ j=46 ∨ j=49 ∨ j=52 ∨ j=55 ∨ j=58 ∨ j=61 ∨ j=64 ∨ j=67 ∨ j=70 ∨ j=73 → ∀i<16,b.basis (site j i)=(get (StairArchiveNativeCut.canonical (dirs j) (dirs j)) i).testBit (rows j)) :
    (stockParity a ^^ stockParity b) =
    ((((((((((((((((((((parity (ArchivePortAction.code (dirs 19))).testBit (rows 19) ^^ (parity (StairArchiveNativeCut.canonical (dirs 19) (dirs 19))).testBit (rows 19)) ^^ ((parity (ArchivePortAction.code (dirs 22))).testBit (rows 22) ^^ (parity (StairArchiveNativeCut.canonical (dirs 22) (dirs 22))).testBit (rows 22))) ^^ ((parity (ArchivePortAction.code (dirs 25))).testBit (rows 25) ^^ (parity (StairArchiveNativeCut.canonical (dirs 25) (dirs 25))).testBit (rows 25))) ^^ ((parity (ArchivePortAction.code (dirs 28))).testBit (rows 28) ^^ (parity (StairArchiveNativeCut.canonical (dirs 28) (dirs 28))).testBit (rows 28))) ^^ ((parity (ArchivePortAction.code (dirs 31))).testBit (rows 31) ^^ (parity (StairArchiveNativeCut.canonical (dirs 31) (dirs 31))).testBit (rows 31))) ^^ ((parity (ArchivePortAction.code (dirs 34))).testBit (rows 34) ^^ (parity (StairArchiveNativeCut.canonical (dirs 34) (dirs 34))).testBit (rows 34))) ^^ ((parity (ArchivePortAction.code (dirs 37))).testBit (rows 37) ^^ (parity (StairArchiveNativeCut.canonical (dirs 37) (dirs 37))).testBit (rows 37))) ^^ ((parity (ArchivePortAction.code (dirs 40))).testBit (rows 40) ^^ (parity (StairArchiveNativeCut.canonical (dirs 40) (dirs 40))).testBit (rows 40))) ^^ ((parity (ArchivePortAction.code (dirs 43))).testBit (rows 43) ^^ (parity (StairArchiveNativeCut.canonical (dirs 43) (dirs 43))).testBit (rows 43))) ^^ ((parity (ArchivePortAction.code (dirs 46))).testBit (rows 46) ^^ (parity (StairArchiveNativeCut.canonical (dirs 46) (dirs 46))).testBit (rows 46))) ^^ ((parity (ArchivePortAction.code (dirs 49))).testBit (rows 49) ^^ (parity (StairArchiveNativeCut.canonical (dirs 49) (dirs 49))).testBit (rows 49))) ^^ ((parity (ArchivePortAction.code (dirs 52))).testBit (rows 52) ^^ (parity (StairArchiveNativeCut.canonical (dirs 52) (dirs 52))).testBit (rows 52))) ^^ ((parity (ArchivePortAction.code (dirs 55))).testBit (rows 55) ^^ (parity (StairArchiveNativeCut.canonical (dirs 55) (dirs 55))).testBit (rows 55))) ^^ ((parity (ArchivePortAction.code (dirs 58))).testBit (rows 58) ^^ (parity (StairArchiveNativeCut.canonical (dirs 58) (dirs 58))).testBit (rows 58))) ^^ ((parity (ArchivePortAction.code (dirs 61))).testBit (rows 61) ^^ (parity (StairArchiveNativeCut.canonical (dirs 61) (dirs 61))).testBit (rows 61))) ^^ ((parity (ArchivePortAction.code (dirs 64))).testBit (rows 64) ^^ (parity (StairArchiveNativeCut.canonical (dirs 64) (dirs 64))).testBit (rows 64))) ^^ ((parity (ArchivePortAction.code (dirs 67))).testBit (rows 67) ^^ (parity (StairArchiveNativeCut.canonical (dirs 67) (dirs 67))).testBit (rows 67))) ^^ ((parity (ArchivePortAction.code (dirs 70))).testBit (rows 70) ^^ (parity (StairArchiveNativeCut.canonical (dirs 70) (dirs 70))).testBit (rows 70))) ^^ ((parity (ArchivePortAction.code (dirs 73))).testBit (rows 73) ^^ (parity (StairArchiveNativeCut.canonical (dirs 73) (dirs 73))).testBit (rows 73))) := by
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
  have h10 := stable_sum stable10 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable10,List.mem_range'_1] using hi)))))))))))))
  have h11 := stable_sum stable11 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable11,List.mem_range'_1] using hi))))))))))))))
  have h12 := stable_sum stable12 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable12,List.mem_range'_1] using hi)))))))))))))))
  have h13 := stable_sum stable13 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable13,List.mem_range'_1] using hi))))))))))))))))
  have h14 := stable_sum stable14 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable14,List.mem_range'_1] using hi)))))))))))))))))
  have h15 := stable_sum stable15 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable15,List.mem_range'_1] using hi))))))))))))))))))
  have h16 := stable_sum stable16 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable16,List.mem_range'_1] using hi)))))))))))))))))))
  have h17 := stable_sum stable17 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable17,List.mem_range'_1] using hi))))))))))))))))))))
  have h18 := stable_sum stable18 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
    simpa only [stable18,List.mem_range'_1] using hi)))))))))))))))))))))
  have h19 := stable_sum stable19 a b (fun i hi=>rest i (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by
    simpa only [stable19,List.mem_range'_1] using hi))))))))))))))))))))))
  rw [allSum a,allSum b,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,fromData _ _ _ _ (custom 19 (Or.inl rfl)),fromData _ _ _ _ (custom 22 (Or.inr (Or.inl rfl))),fromData _ _ _ _ (custom 25 (Or.inr (Or.inr (Or.inl rfl)))),fromData _ _ _ _ (custom 28 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),fromData _ _ _ _ (custom 31 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),fromData _ _ _ _ (custom 34 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),fromData _ _ _ _ (custom 37 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))),fromData _ _ _ _ (custom 40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))),fromData _ _ _ _ (custom 43 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))),fromData _ _ _ _ (custom 46 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))),fromData _ _ _ _ (custom 49 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))),fromData _ _ _ _ (custom 52 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))),fromData _ _ _ _ (custom 55 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))),fromData _ _ _ _ (custom 58 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))),fromData _ _ _ _ (custom 61 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))),fromData _ _ _ _ (custom 64 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))),fromData _ _ _ _ (custom 67 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))),fromData _ _ _ _ (custom 70 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))),fromData _ _ _ _ (custom 73 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))))))))))),fromData _ _ _ _ (stock 19 (Or.inl rfl)),fromData _ _ _ _ (stock 22 (Or.inr (Or.inl rfl))),fromData _ _ _ _ (stock 25 (Or.inr (Or.inr (Or.inl rfl)))),fromData _ _ _ _ (stock 28 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),fromData _ _ _ _ (stock 31 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),fromData _ _ _ _ (stock 34 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),fromData _ _ _ _ (stock 37 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))),fromData _ _ _ _ (stock 40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))),fromData _ _ _ _ (stock 43 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))),fromData _ _ _ _ (stock 46 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))),fromData _ _ _ _ (stock 49 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))),fromData _ _ _ _ (stock 52 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))),fromData _ _ _ _ (stock 55 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))),fromData _ _ _ _ (stock 58 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))),fromData _ _ _ _ (stock 61 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))),fromData _ _ _ _ (stock 64 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))),fromData _ _ _ _ (stock 67 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))),fromData _ _ _ _ (stock 70 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))))),fromData _ _ _ _ (stock 73 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))))))))))]
  rw [pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,pair_step,Bool.xor_self,Bool.false_xor]
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

/-- dadon's `Ref240/255/270` for any block `j` of the window from block `f` (tick `start f`): the block's stock hand-off (build-chain's
`AtJ`), the logical state agrees with the stock run of `j-3` blocks off the archived cells (par-d2's `mask`/`progW`),
and the holes of the banks of blocks `3..j-2` (cleared by blocks `4..j-1`) are zero. -/
def RefW (f j : Fin 23) (d:Bool) (x:Nat) (initial s:State) : Prop :=
  ∃raw g sg pg ps,AtJ j d x p raw s g sg pg ps ∧
    Except (OrdinaryChainW.mask (start f) (j.val-f.val)) raw
      (run (OrdinaryChainW.progW (start f) d (j.val-f.val)) [] (run (span (start f) (15*(j.val-f.val))) [] initial)) ∧
    ∀q∈StockWindowGeo.holes (start f) (j.val-f.val-1),raw.basis q=false

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

/-- L11 (new, first form at 90 (block 1); dadon's `StockWindowTicket.ordinary225`): the first block's logical end state is
the stock run of its 15 ticks with the five pre-window letters (group 85) encoded. -/
abbrev FirstOrdinarySpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis),
    Except [] (endRaw 90 raw (run (portalP 90 ++ NativeFirstJ.enteredWindow WindowParams.first d) m
        (pullState (OB5.sig 89) raw)))
      (run (Rolling1588.encodeAt base d 85) [] (run (span 90 15) [] raw))

theorem not_firstF (f k : Fin 23) (hfb : start f=firstBlock) (hk : f.val<k.val) : start k≠firstBlock := by
  rw [←hfb]; simp only [StairPacket.start]; omega

/-- build-chain's `FirstSpec` for any first block `f` (next block `k1`); `FirstSpec = FirstSpecF first ⟨4⟩`. -/
abbrev FirstSpecF (f k1 : Fin 23) : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis),
    ∃g s:Bool,
      InputAt (start f) (encode g s (unsigned (start f) x p).u (unsigned (start f) x p).v) raw ∧
      LeaveJ.Admission.Inputs f
        (run (portalP (start f) ++ NativeFirstJ.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw))
        (unsigned (start f) x p) g s ∧
      PackedCut (EnterJ.lowerPairs k1) (EnterJ.upperPairs k1) (EnterJ.gate k1)
        (EnterJ.flagN k1) (EnterJ.flagF k1) (EnterJ.flagU k1)
        (PortalValues.negative (LeaveJ.Admission.flags (unsigned (start f) x p) g s).2 (unsigned (start f+15) x p).u)
        (decide (Shadow.far (sbP (start f+15)) 15 (unsigned (start f+15) x p)))
        (decide (Shadow.far (sbP (start f+15)) 15 (unsigned (start f+15) x p) ∧ 2^(sbP (start f+15))≤(unsigned (start f+15) x p).u))
        (pullState (EnterJ.pull k1)
          (endRaw (start f) raw (run (portalP (start f) ++ NativeFirstJ.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw))))
        (eraseSites (EnterJ.pending k1) (run (leaveP f) n
          (run (portalP (start f) ++ NativeFirstJ.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)))) ∧
      PastFacts f (ArchiveJ.rawPorts f) (sbP (start f)) (unsigned (start f) x p) g s
        (HighBankSum.cross (LeaveJ.TrueMiddle.d f (unsigned (start f) x p)))
        (run (leaveP f) n
          (run (portalP (start f) ++ NativeFirstJ.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)))

theorem first_ship (F:FirstSpec) : FirstSpecF WindowParams.first ⟨2,by decide⟩ := F

/-- `FirstOrdinarySpec` for any first block `f`. -/
abbrev FirstOrdinarySpecF (f : Fin 23) : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis),
    Except [] (endRaw (start f) raw (run (portalP (start f) ++ NativeFirstJ.enteredWindow f d) m
        (pullState (OB5.sig (start f-1)) raw)))
      (run (Rolling1588.encodeAt base d (start f-5)) [] (run (span (start f) 15) [] raw))

theorem firstOrdinary_ship (FO:FirstOrdinarySpec) : FirstOrdinarySpecF WindowParams.first := FO

theorem first_eqF (d:Bool) (f:Fin 23) :
    (WindowParams.params.portal (start f) :: firstF WindowParams.params d f).flatten=
      (portalP (start f)++NativeFirstJ.enteredWindow f d)++leaveMoveP f := by
  simp only [firstF,WindowParams.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeFirstJ.enteredWindow,NativeFirstJ.window,StairPacket.body,NativeFirstJ.program,List.append_assoc]

/-- The move leave of the first block `f` runs like its reference leave (`FirstSpecF` gives the leave input). -/
theorem firstSameF (f k1:Fin 23) (hf1:1≤f.val) (hk1:k1.val=f.val+1) (F:FirstSpecF f k1) (d:Bool) (x p:Nat)
    (good:Bounds x p) (raw:State) (m n:List Bool) (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis) :
    run (leaveMoveP f) n (run (portalP (start f)++NativeFirstJ.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw))=
      run (leaveP f) n (run (portalP (start f)++NativeFirstJ.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)) := by
  obtain ⟨g,sg,input,hin,cut,facts⟩:=F d x p good raw m n stage
  exact LeaveJ.Admission.Inputs.sameMove hf1 (by omega) hin n

theorem run_nil_eq (m:List Bool) (s:State) : run [] m s=s := by
  with_unfolding_all rfl


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
  let z:=unsigned 90 x p
  let origin:=pullState (OB5.sig 89) raw
  let cut:=run (portalP 90) m origin
  let n:=m.drop (measurementCount (portalP 90))
  let pre:=run (Partial.enterP j) n cut
  let tape:=n.drop (measurementCount (Partial.enterP j))
  let T:=Shadow.reduced (sbP 90) 15 z
  obtain ⟨G,S,inputAt,frame,-⟩:=NativeFirstJ.first_core d x p good raw m stage
  have eqg:(SkywalkRails.encode G S (unsigned 90 x p).u (unsigned 90 x p).v).g=G:=by cases G <;> rfl
  have input:SkywalkIntegerInput (W.compactSkywalkTickLayout base 90)
      (SkywalkRails.encode G S (unsigned 90 x p).u (unsigned 90 x p).v).a
      (SkywalkRails.encode G S (unsigned 90 x p).u (unsigned 90 x p).v).b G raw.basis:=by
    unfold InputAt at inputAt; rwa [eqg] at inputAt
  have nums:=LeaveJ.Admission.actualNumbers j (by decide) (by decide) x p good
  have dom:=initial 90 x p (by decide) d raw stage
  have hist:=pulled_history j rfl dom
  have ready:=EnterJ.ready_from_cut_at j raw cut z G S n nums.small frame input hist
  have to':T.v%2=1:=shadow_odd (sbP 90) z nums.small nums.odd
  have parity:((encode G S T.u T.v).a+(encode G S T.u T.v).b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have inp:=NativeFirstJ.history_from_stock j (by decide) (by decide) raw cut pre frame n tape rfl _ parity ready.2
  have res:=resultF j (by decide) (by decide) old_first d raw pre tape x p good dom inp
  have fb:start j=firstBlock:=rfl
  have firstB:oldStart (start j)=start j-5 ∧ oldCount (start j)=5:=by
    rw [fb]; exact ⟨oldStart_first,oldCount_first⟩
  intro q _
  have w:=windowF j (by decide) (by decide) firstB d raw _ res q
  have e:run (portalP 90++NativeFirstJ.enteredWindow WindowParams.first d) m origin=
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



-- ==== window390: Main's exit-270 pieces at the exit 375 (build-chain's exit360/renderM360.py via helpers/window390/main/renderM_x.py, from Main w4-345-entry): the exit's
-- blank holes, dadon's finalBank receipt (selected_*), the terminal bank (Ordinary375Terminal) and resultW375. ====
section

namespace ECDSAAdd.Entrant.StairPacket
open Arithmetic MappedCompressed IntegerPacket SkywalkRails ArchivePortAction
set_option maxRecDepth 18000
set_option maxHeartbeats 2300000
attribute [local irreducible] run routed measurementCount body
namespace NativePack375
open ArchiveBoundary375
def fourHoles : List Wire := [1702,1700,1697,1695]
theorem blank_slots : ∀q∈fourHoles,∃i:Fin 157,16 ≤ i.val ∧ codePorts i=q := by decide +kernel
theorem cleared_holes (d:Bool) (row:Nat) (s:State) (frame:Frame codePorts (code d) row s) :
    ∀q∈fourHoles,s.basis q=false := by
  intro q hq
  obtain ⟨i,hi,rfl⟩:=blank_slots q hq
  rw [frame,archive_blank d i hi,Nat.zero_testBit]
end NativePack375
end ECDSAAdd.Entrant.StairPacket

end

section

namespace ECDSAAdd.Entrant.StairPacket.NativePack375
open Arithmetic MappedCompressed Secp256k1 IntegerPacket ArchivePortAction ArchiveBoundary375
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000
attribute [local irreducible] run
open StockCanonicalRow ArchiveBoundary375 ParkEndpoint375 Portal375Flag Secp256k1 SkywalkRails StairArchiveTrace
theorem selected_generic (p q:Program) (d:Bool) (s:State) (m:List Bool) (step:Transition q s (run p m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^76)
    (prior:PastFacts sourceIdx rawPorts 76 past G S cross s) :
    let out:=run (p ++ (program d ++ (Partial.exitLoadP 375) d)) m s
    out.phase=s.phase ∧ (let v:=key 76 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run ((Partial.exitRestoreP 375) d ++ (reverse d ++ q)) n out=s := by
  let tick:=run p m s
  let e:=m.drop (measurementCount p)
  let pre:=run (program d) e tick
  let f:=e.drop (measurementCount (program d))
  have ⟨legal,row,limit,frame⟩:=archive_ready d s tick e past G S cross odd small prior step.keptFive step.keptBank step.scratch
  have truth:=frame_key sourceIdx rawPorts chronological row 76 past G S cross s pre prior
    (fun i=>(outside d _ (bank_out i) e tick).trans (step.keptBank i)) frame
  have spec:=select_spec ⟨row,limit,truth⟩
  have fresh:=reframe limit truth rawPorts pre frame
  have enc:=source_law d tick e legal
  have act:=load_run d _ spec.1 pre f fresh
  exact sequence_law p (program d) ((Partial.exitLoadP 375) d) ((Partial.exitRestoreP 375) d)
    (reverse d) q s m (fun out=>let v:=key 76 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out)
    tick rfl step.phase step.undo pre rfl enc.1 enc.2 (run ((Partial.exitLoadP 375) d) f pre) rfl act.1
    ⟨spec.1,spec.2,act.2.1⟩ (fun n=>roundtrip d _ spec.1 pre f n fresh)

theorem selected_slice (d:Bool) (s:State) (m:List Bool) (step:TickStep s (run EndTick375.physP m s))
    (past:SkywalkNat.State) (G S cross:Bool) (odd:past.v%2=1) (small:min past.u past.v<2^76)
    (prior:PastFacts sourceIdx rawPorts 76 past G S cross s) :
    let out:=run (endSlice d) m s
    out.phase=s.phase ∧ (let v:=key 76 past cross (SkywalkTrace.trace 15 (encode G S past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ Frame codePorts (code d) (select v) out) ∧
      ∀n,run (endUndo d) n out=s :=
  selected_generic EndTick375.physP EndTick375.physQ d s m step past G S cross odd small prior
theorem selected_last (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw original s:State) (m:List Bool)
    (read:EndTick375.Reads raw original) (stage:Rolling1588.Integer.Stage base d x p 375 original.basis)
    (hist:raw.basis (base (1028+375))=false) (swapSlot:raw.basis (base (2053-375))=false)
    (z:SkywalkNat.State) (small:min z.u z.v<2^69) (G S:Bool)
    (input:SkywalkIntegerInput EndTick375.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 390 1648 1646 1647 (PortalValues.negative S z.u)
      (decide (3*2^85≤z.u+z.v)) (decide (3*2^85≤z.u+z.v ∧ 2^69≤z.u)) (pullState (OB5.sig 374) raw) (eraseSites src s))
    (empty:∀q∈dst,s.basis q=false) (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^76)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1649=decide (Shadow.far 76 15 past))
    (angle:s.basis 1650=(decide (Shadow.far 76 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1651=(decide (Shadow.far 76 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 76 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  let n:=m.drop (measurementCount (Partial.parkP 375))
  let one:=run (Partial.portalInvP 375) n (run (Partial.parkP 375) m s)
  let tape:=n.drop (measurementCount (Partial.portalInvP 375))
  have restored:=parked_release z small raw s m n G S input cut empty
  have facts:=after_park raw s _ _ _ cut past pg ps cross records mode angle flipped
  have tick:=observe_tick d x hx0 hx raw original s read stage hist swapSlot tape
  have eqOne:one=stash s (pullState (OB5.sig 374) raw):=restored.1
  have A:PastFacts sourceIdx rawPorts 76 past pg ps cross one :=by rw [eqOne];exact facts
  have B:TickStep one (run EndTick375.physP tape one):=by rw [eqOne];exact tick
  have body:=selected_slice d one tape B past pg ps cross odd pm A
  have phase:one.phase=s.phase:=(congrArg State.phase restored.1).trans cut.phase.symm
  dsimp only [lastWindow,lastUnwind]
  simp only [run_append,run_take]
  refine ⟨body.1.trans phase,body.2.1,?_⟩
  intro t
  rw [body.2.2 t]
  exact restored.2 _ _
theorem selected_from_domain (d:Bool) (x:Nat) (hx0:0<x) (hx:x<p) (raw s:State) (m:List Bool)
    (domain:WideReference.Domain 375 x p raw) (z:SkywalkNat.State) (small:min z.u z.v<2^69) (G S:Bool)
    (input:SkywalkIntegerInput EndTick375.L (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (cut:PackedCut loPairs hiPairs 390 1648 1646 1647 (PortalValues.negative S z.u)
      (decide (3*2^85≤z.u+z.v)) (decide (3*2^85≤z.u+z.v ∧ 2^69≤z.u)) (pullState (OB5.sig 374) raw) (eraseSites src s))
    (past:SkywalkNat.State) (pg ps cross:Bool) (odd:past.v%2=1) (pm:min past.u past.v<2^76)
    (records:physicalCells sourceIdx s=SkywalkTrace.trace 15 (encode pg ps past.u past.v))
    (mode:s.basis 1649=decide (Shadow.far 76 15 past))
    (angle:s.basis 1650=(decide (Shadow.far 76 15 past) && afterFlags (decide (past.v<past.u)) ((physicalCells sourceIdx s).take 5)))
    (flipped:s.basis 1651=(decide (Shadow.far 76 15 past) && cross)) :
    let out:=run (lastWindow d) m s
    out.phase=s.phase ∧ (let v:=key 76 past cross (SkywalkTrace.trace 15 (encode pg ps past.u past.v)); select v<63145 ∧ Encodes v (select v) ∧ ArchivePortAction.Frame codePorts (code d) (select v) out) ∧
      ∀t,run (lastUnwind d) t out=s := by
  obtain ⟨ref,stage,read,history,swapSlot,empty⟩:=WideReference.terminal375 d x raw domain
  exact selected_last d x hx0 hx raw ref s m read stage history swapSlot z small G S input cut
    (empty_from_cut _ _ _ _ _ cut empty) past pg ps cross odd pm records mode angle flipped
end ECDSAAdd.Entrant.StairPacket.NativePack375

end

section

namespace ECDSAAdd.Entrant.StairPacket.Ordinary375Terminal
open Arithmetic MappedCompressed NativePack375 ArchivePortAction ArchiveBoundary375 ParkEndpoint375 CodecBitSliceVerify
set_option maxRecDepth 40000
set_option maxHeartbeats 3800000
attribute [local irreducible] run
def newBank := (List.range' 365 10).flatMap (fun r=>[OB5.sig 375 (base r), OB5.sig 375 (base (1028+r))])
def ordinary := (List.finRange 10).map history
def zeros:=List.range' 1556 134++dst

theorem basis (d:Bool) (raw payload:State) (m n:List Bool)
    (row:Nat)
    (clear:∀q∈zeros,raw.basis (OB5.sig 375 q)=false)
    (frame:Frame codePorts (code d) row (run ((Partial.exitLoadP 375) d) n
      (run (program d) m (stash payload (pullState (OB5.sig 375) raw))))) :
    let out:=run ((Partial.exitLoadP 375) d) n (run (program d) m (stash payload (pullState (OB5.sig 375) raw)))
    let wide:=run (Rolling1588.encodeAt base d 360) [] raw
    ∀q∉newBank,out.basis q=wide.basis (OB5.sig 375 q) := by
  let inp:=stash payload (pullState (OB5.sig 375) raw)
  let mid:=run (program d) m inp
  let wide:=run (Rolling1588.encodeAt base d 360) [] raw
  let coords:=History5.historyMap base 360
  have geom:∀i:Fin 10,history i∉dst ∧ OB5.sig 375 (history i)=coords i ∧ history i∉rawPortsList := by dsimp only [coords];decide +kernel
  have agree (i:Fin 10):inp.basis (history i)=raw.basis (coords i):=by
    simp only [inp,stash,if_neg (geom i).1,pullState,(geom i).2.1]
  have injected:Function.Injective coords:=by dsimp only [coords];decide +kernel
  have keep (q:Wire) (no:q∉ordinary) : wide.basis (OB5.sig 375 q)=raw.basis (OB5.sig 375 q) := by
    have cover:wires (Rolling1588.encodeAt base d 360) ⊆ ((List.finRange 10).map coords).toFinset:=by dsimp only [coords];cases d <;> decide +kernel
    apply run_preserves_outside
    intro h
    obtain ⟨i,_,e⟩:=List.mem_map.mp (List.mem_toFinset.mp (cover h))
    have e':OB5.sig 375 (history i)=OB5.sig 375 q:=(geom i).2.1.trans e
    have unique:history i=q:=by simpa only [OB5.sig_invol 375 (by decide)] using congrArg (OB5.sig 375) e'
    exact no (List.mem_map.mpr ⟨i,List.mem_finRange i,unique⟩)
  dsimp only
  intro q outside
  by_cases normal:q∈ordinary
  · obtain ⟨i,_,rfl⟩:=List.mem_map.mp normal
    rw [run_preserves_outside ((Partial.exitLoadP 375) d) _ _ _ (fun h=>(geom i).2.2 (List.mem_toFinset.mp (load_cover d h))), (geom i).2.1]
    have encoded:=ArchiveOrdinaryFive.stock_relocated d history coords histInj injected inp raw m [] agree i
    rw [←(equals d).1] at encoded
    exact encoded
  rw [keep q normal]
  by_cases touched:q∈rawPortsList
  · have mask:∀q∈rawPortsList,q∈newBank ∨ (q∈zeros ∧ ∃i:Fin 157,16≤ i.val ∧ codePorts i=q) := by decide +kernel
    obtain ⟨blank,i,hi,slot⟩:=(mask q touched).resolve_left outside
    rw [clear q blank,←slot,frame,archive_blank _ _ hi,Nat.zero_testBit]
  · have no:q∉wires ((Partial.exitLoadP 375) d):=fun h=>touched (List.mem_toFinset.mp (load_cover d h))
    have mask:∀q∈dst,q∈rawPortsList:=by decide +kernel
    have notDst:q∉dst:=fun h=>touched (mask q h)
    rw [run_preserves_outside _ _ _ _ no]
    exact (NativePack375.outside d q (fun i e=>normal (List.mem_map.mpr ⟨i,List.mem_finRange i,e.symm⟩)) _ _).trans
      (by simp only [stash,if_neg notDst,pullState])
end ECDSAAdd.Entrant.StairPacket.Ordinary375Terminal

end

section

namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic IntegerPacket MappedCompressed Secp256k1 WideReference SkywalkRails NativePack375 Partial ParkEndpoint375 StockWindowTicket
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

/-- `Ordinary270Native.result` with the exit frame as a hypothesis (dadon took it from `step270`, which needs
`At270.saved225/240`; the generic hand-off `AtJ 13` has no saved keys). Proof otherwise dadon's. -/
theorem resultW375 (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg:Bool) (m:List Bool)
    (domain:Domain 375 x p raw) (input:InputAt 375 (signedAt 375 x p g sg) raw)
    (cut:PackedCut Portal375Flag.loPairs Portal375Flag.hiPairs 390 1648 1646 1647 (flagNeg 375 x p sg)
      (decide (farAt 69 375 x p)) (decide (farAt 69 375 x p ∧ 2^69≤(unsigned 375 x p).u))
      (pullState (OB5.sig 374) raw) (eraseSites ParkEndpoint375.src s))
    (last:StockWindowW.LastAt ArchiveBoundary375.codePorts ⟨19,by decide⟩ d x p (run (lastWindow d) m s)) :
    ArchiveHistoryCompare.Except Ordinary375Terminal.newBank (run (lastWindow d) m s)
      (pullState (OB5.sig 375) (run (Rolling1588.encodeAt base d 360) [] (run EndTick375.canonical [] raw))) := by
  obtain ⟨ref,stage,read,hist,spare,spaces⟩:=WideReference.terminal375 d x raw domain
  let z:=unsigned 375 x p
  let v:=run EndTick375.canonical [] raw
  let p1:=m.drop (measurementCount (Partial.parkP 375))
  let p2:=p1.drop (measurementCount (Partial.portalInvP 375))
  let p3:=p2.drop (measurementCount EndTick375.physP)
  let p4:=p3.drop (measurementCount (program d))
  have lim:min z.u z.v<2^69:=true_small x p 375 (lt_trans good.small good.cap) good.cap (by decide)
  have mode:farAt 69 375 x p=(3*2^85≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have first:=parked_release z lim raw s m p1 g sg (readInput 375 x p raw g sg input)
    (by simpa only [mode] using cut) (empty_from_cut _ _ _ _ _ cut spaces)
  have tick:=EndTick375.physical d x good.nonzero good.small raw ref s read stage hist spare p2
  let loaded:=run ((Partial.exitLoadP 375) d) p4 (run (program d) p3 (stash s (pullState (OB5.sig 375) v)))
  have actual:run (lastWindow d) m s=loaded := by
    simp only [lastWindow,endSlice,run_append,run_take]
    change run ((Partial.exitLoadP 375) d) p4 (run (program d) p3 (run EndTick375.physP p2 (run (Partial.portalInvP 375) p1 (run (Partial.parkP 375) m s))))=_
    rw [first.1,tick.1]
  obtain ⟨row,_,_,frame⟩:=last
  rw [actual] at frame
  have zeros (q:Wire) (h:q∈Ordinary375Terminal.zeros) : v.basis (OB5.sig 375 q)=false:=by
    rcases List.mem_append.mp h with carryLane|tag
    · have table:∀q∈List.range' 1556 134,∃k:Fin 134,OB5.sig 375 q=1556+k.val:=by decide +kernel
      obtain ⟨k,eq⟩:=table _ carryLane
      rw [eq];exact (EndTick375.after_cells d x good.nonzero good.small raw ref read stage).2 k
    · have coords:∀q∈dst,OB5.sig 375 q=OB5.sig 374 q := by decide +kernel
      have nocell:=EndTick375.spared q tag
      have cover:=W.compactSkywalkTick_support base 375 (by decide) base_pool_nodup
      have no:OB5.sig 375 q∉wires EndTick375.canonical:=fun used=>nocell (List.mem_toFinset.mp (cover used))
      exact (run_preserves_outside _ _ _ _ no).trans (by rw [coords q tag];exact spaces q tag)
  rw [actual]
  exact Ordinary375Terminal.basis d v s p3 p4 row zeros frame

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG

end

-- ==== end window390 Main exit pieces ====

section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic IntegerPacket MappedCompressed Secp256k1 WideReference SkywalkRails Partial StockWindowTicket StockWindowW
set_option maxRecDepth 30000
set_option maxHeartbeats 3500000
attribute [local irreducible] run

/-- The generic hand-off at block 20 is the exit-375 cut (build-chain's (at 360) `exitBridge375`). -/
theorem exitCut375 (d:Bool) (x:Nat) (raw s:State) (g sg pg ps:Bool)
    (pre:AtJ ⟨20,by decide⟩ d x p raw s g sg pg ps) :
    PackedCut Portal375Flag.loPairs Portal375Flag.hiPairs 390 1648 1646 1647 (flagNeg 375 x p sg)
      (decide (farAt 69 375 x p)) (decide (farAt 69 375 x p ∧ 2^69≤(unsigned 375 x p).u))
      (pullState (OB5.sig 374) raw) (eraseSites ParkEndpoint375.src s) := by
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,-,-,-⟩:=StockWindowW.exitBridge375
  have cut:=pre.cut
  rw [bl,bu,bg,bn,bf,bu',bp] at cut
  have e19:start (⟨20,by decide⟩:Fin 23)=375:=rfl
  have sb:sbP 375=69:=by decide
  have pl:EnterJ.pull ⟨20,by decide⟩=OB5.sig 374:=rfl
  simp only [e19,sb,pl] at cut
  exact cut

/-- The exit frame at 375 from the generic hand-off (build-chain's (at 360) `exitStep375`, its `LastAt` part). -/
theorem exitLast375 (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool)
    (pre:AtJ ⟨20,by decide⟩ d x p raw s g sg pg ps) (m:List Bool) :
    LastAt ArchiveBoundary375.codePorts ⟨19,by decide⟩ d x p (run (NativePack375.lastWindow d) m s) := by
  have h:=StockWindowW.exitStep375 d x good s m ⟨⟨20,by decide⟩,rfl,raw,g,sg,pg,ps,pre⟩
  have e375:start (⟨19,by decide⟩:Fin 23)+15=375:=rfl
  rw [e375,(StockWindowW.exitProg375 d).1] at h
  exact h.2.1

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ===== Part 6: generic over the window's length (blocks 4..J, exit e = 120+15n) =====
section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 ArchiveHistoryCompare StockWindowW
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run measurementCount body

/-- build-chain's `EndpointSpec` for interior blocks `I..J` (`EndpointSpec = EndpointBetween 4 12`). -/
abbrev EndpointBetween (I J : Nat) : Prop :=
  ∀ (j k : Fin 23), k.val=j.val+1 → I≤j.val → j.val≤J → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ.lowerPairs j) (EnterJ.upperPairs j) (EnterJ.gate j) (EnterJ.flagN j) (EnterJ.flagF j)
      (EnterJ.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ.pull j) raw) (eraseSites (EnterJ.pending j) s))
    (input:SkywalkIntegerInput (EnterJ.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:ScratchAt j d m s) (pg ps cross:Bool)
    (prior:PastFacts (NativeJ.prev j) (ArchiveJ.rawPorts (NativeJ.prev j)) (sbP (start (NativeJ.prev j)))
      (unsigned (start (NativeJ.prev j)) x p) pg ps cross s),
    PackedCut (EnterJ.lowerPairs k) (EnterJ.upperPairs k) (EnterJ.gate k) (EnterJ.flagN k) (EnterJ.flagF k)
      (EnterJ.flagU k)
      (PortalValues.negative (LeaveJ.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ.pull k) (endRaw (start j) raw (run (NativeJ.nextWindow j d) m s)))
      (eraseSites (EnterJ.pending k) (run (leaveP j) n (run (NativeJ.nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ.rawPorts j) (sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.cross (LeaveJ.TrueMiddle.d j (unsigned (start j) x p)))
      (run (leaveP j) n (run (NativeJ.nextWindow j d) m s))

theorem endpoint_ship (L1:EndpointSpec) : EndpointBetween 4 12 := L1

/-- dadon's `pinned{s}` for block `k ≤ J`. -/
theorem pinnedG (I J:Nat) (hI2:2≤I) (hJ:J≤19) (L1:EndpointBetween I J) (L2:ScratchSpec) (k k1:Fin 23)
    (hk:k1.val=k.val+1) (hIk:I≤k.val) (hkJ:k.val≤J) (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool)
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
  obtain ⟨cut,facts⟩:=L1 k k1 hk hIk hkJ d x p good raw s m n pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  have hin:=native.1
  have carried:=stepInput_gen (start k) (sbP (start k)) x p (by simp only [StairPacket.start]; omega)
    (by simp only [StairPacket.start]; omega) good raw v g sg pre.domain pre.input hin.small
  have canon:=unique_input pre.input (fixed_input _ _ _ (by simp only [StairPacket.start]; omega) good raw pre.domain)
  refine ⟨flags.1,flags.2,g,sg,⟨?_,?_,cut,?_,?_⟩⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [p1]; exact facts
  · rw [p1]; exact canon

/-- `OB5.sig s` and `OB5.sig (s+14)` move a B-side cell of the block's last ten ticks alike (any block). -/
theorem sigNat_same (s r : Nat) (hs : s≤360) (h1 : s≤r+8) (h2 : r+1≤s) :
    OB5.sigNat (s+14) (1028+r+16)=OB5.sigNat s (1028+r+16) := by
  unfold OB5.sigNat
  by_cases a : 1301≤1028+r+16
  · rw [if_pos (Or.inl ⟨a,by omega⟩),if_pos (Or.inl ⟨a,by omega⟩)]
  · rw [if_neg (by rintro (⟨x,_⟩|⟨x,_⟩) <;> omega),if_neg (by rintro (⟨x,_⟩|⟨x,_⟩) <;> omega)]

theorem hole_sig (k : Fin 23) (h18 : k.val≤19) (r : Nat) (h1 : start k≤r+8) (h2 : r+1≤start k) :
    OB5.sig (start k+14) (base (1028+r))=OB5.sig (start k) (base (1028+r)) := by
  have s0 : start k≤360 := by simp only [StairPacket.start]; omega
  exact sigNat_same (start k) r s0 h1 h2

theorem hole_four (k : Fin 23) (h1 : 1≤k.val) (h18 : k.val≤19) (r : Nat)
    (hr : r=start k-8 ∨ r=start k-6 ∨ r=start k-3 ∨ r=start k-1) :
    OB5.sig (start k) (base (1028+r))∈NativeJ.fourHoles k := by
  rw [NativeJ.fourHoles_eq k h1]
  have s0 : 90≤start k := by simp only [StairPacket.start]; omega
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rcases hr with rfl|rfl|rfl|rfl
  · left; congr 1; simp only [base,Wire]; omega
  · right; left; congr 1; simp only [base,Wire]; omega
  · right; right; left; congr 1; simp only [base,Wire]; omega
  · right; right; right; congr 1; simp only [base,Wire]; omega

/-- dadon's `ordinary{s}` for block `k ≤ 19`. -/
theorem ordinaryG (f:Fin 23) (hfb:start f=firstBlock) (k:Fin 23) (hfk:f.val<k.val) (h18:k.val≤19) (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State)
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
  have hne:=not_firstF f k hfb hfk
  have h:=OrdinaryJ.native k (by omega) (by omega) ⟨oldStart_interior hne,oldCount_interior hne⟩ d x p good raw s
    pre.domain m (m.drop (measurementCount (Partial.enterP k))) _ _ _ pre.cut _ parity ready.2.1
  simpa only [NativeJ.nextWindow,NativeJ.window,run_append,run_take] using h

/-- dadon's `holes{s}` for block `k ≤ 19` (the sig-moved holes of blocks ≥ 270 included). -/
theorem holesG (f:Fin 23) (hfb:start f=firstBlock) (L2:ScratchSpec) (k:Fin 23) (hfk:f.val<k.val) (h2:2≤k.val) (h18:k.val≤19) (d:Bool) (x:Nat) (good:Bounds x p)
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
  have hne:=not_firstF f k hfb hfk
  have s0 : 105≤start k ∧ start k≤360 := by simp only [StairPacket.start]; omega
  have bound:start k+14≤511:=by omega
  have r0 : start k-8≤r ∧ r≤start k-1 := by rcases hr with rfl|rfl|rfl|rfl <;> omega
  have mem:base (1028+r)∈oldSites (start k):=by
    simp only [oldSites,oldStart_interior hne,oldCount_interior hne,List.mem_flatMap,List.mem_range'_1,
      List.mem_cons,List.not_mem_nil,or_false]
    exact ⟨r,⟨by omega,by omega⟩,Or.inr rfl⟩
  rw [endRaw_inside_gen _ bound _ _ _ mem,hole_sig k h18 r (by omega) (by omega)]
  exact clear _ (hole_four k (by omega) h18 r hr)

/-- dadon's `next240/next255` for any interior block `k` (`I ≤ k ≤ J`) of the window from block `f`. -/
theorem nextG (f:Fin 23) (hfb:start f=firstBlock) (I J:Nat) (hI2:2≤I) (hIf:f.val+1≤I) (hJ:J≤19)
    (L1:EndpointBetween I J) (L2:ScratchSpec) (d:Bool) (x:Nat) (good:Bounds x p)
    (initial s:State) (k k1:Fin 23) (hk:k1.val=k.val+1) (hIk:I≤k.val) (hkJ:k.val≤J) (m:List Bool)
    (h:RefW f k d x initial s) :
    RefW f k1 d x initial (run (NativeJ.nextWindow k d++leaveMoveP k) m s) := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  rw [run_append,run_take,sameAt L2 k (by omega) (by omega) d x p good raw s g sg pg ps m pre]
  obtain ⟨a,b,c,e,pre'⟩:=pinnedG I J hI2 hJ L1 L2 k k1 hk hIk hkJ d x good raw s g sg pg ps m pre
  have hfk:f.val<k.val:=by omega
  have hne:=not_firstF f k hfb hfk
  have sf : 75≤start f ∧ start f+15≤start k := by simp only [StairPacket.start]; omega
  have s0 : start k≤360 := by simp only [StairPacket.start]; omega
  have sk:start k=start f+15*(k.val-f.val):=by simp only [StairPacket.start]; omega
  refine ⟨_,a,b,c,e,pre',?_,?_⟩
  · have step:=ordinaryG f hfb k hfk (by omega) d x good raw s g sg pg ps m pre
    have step':Except (OrdinaryChainW.newBank (start f) (start f+15*(k.val-f.val)))
        (endRaw (start k) raw (run (NativeJ.nextWindow k d) m s))
        (run (Rolling1588.encodeAt base d (OrdinaryChainW.group (start f) (k.val-f.val))) []
          (run (span (start f+15*(k.val-f.val)) 15) [] raw)):=by
      rw [←sk,OrdinaryChainW.newBank,if_neg (by omega),OrdinaryChainW.group,if_neg (by omega),
        show start f+15*(k.val-f.val)-15=start k-15 by omega]
      exact step
    have e1:k1.val-f.val=(k.val-f.val)+1:=by omega
    rw [e1]
    exact OrdinaryChainW.add (start f) (by omega) (k.val-f.val) (by omega) (by omega) d raw initial _ old step'
  · have e1:k1.val-f.val-1=(k.val-f.val-1)+1:=by omega
    rw [e1,holes_succ]
    intro q hq
    rcases List.mem_append.mp hq with h|h
    · apply OrdinaryChainW.carry (start k) (by omega) (StockWindowGeo.holes (start f) (k.val-f.val-1)) ?_ ?_ raw _ zeros q h
      · intro w hw hit
        obtain ⟨r,r1,r2,rfl⟩:=hole_cell (start f) (k.val-f.val-1) (by omega) w hw
        obtain ⟨r',a1,a2,e'⟩:=old_cell hit
        rw [oldStart_interior hne] at a1 a2
        rw [oldCount_interior hne] at a2
        rcases e' with e'|e' <;> simp only [base,Wire] at e' <;> omega
      · intro w hw
        obtain ⟨r,r1,r2,rfl⟩:=hole_cell (start f) (k.val-f.val-1) (by omega) w hw
        right; simp only [base,Wire]; omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      have g0:∀i,StockWindowGeo.gstart (start f) i=start f-5+5*i:=fun i=>by simp only [StockWindowGeo.gstart]
      rcases h with rfl|rfl|rfl|rfl
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-8) (Or.inl rfl)
        rw [show 1028+StockWindowGeo.gstart (start f) (2+3*(k.val-f.val-1))+2=1028+(start k-8) by rw [g0]; omega]; exact this
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-6) (Or.inr (Or.inl rfl))
        rw [show 1028+StockWindowGeo.gstart (start f) (2+3*(k.val-f.val-1))+4=1028+(start k-6) by rw [g0]; omega]; exact this
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-3) (Or.inr (Or.inr (Or.inl rfl)))
        rw [show 1028+StockWindowGeo.gstart (start f) (3+3*(k.val-f.val-1))+2=1028+(start k-3) by rw [g0]; omega]; exact this
      · have := holesG f hfb L2 k hfk (by omega) (by omega) d x good raw s g sg pg ps m pre (start k-1) (Or.inr (Or.inr (Or.inr rfl)))
        rw [show 1028+StockWindowGeo.gstart (start f) (3+3*(k.val-f.val-1))+4=1028+(start k-1) by rw [g0]; omega]; exact this

/-- The interior fold over blocks `I..J` of the window from block `f`. -/
theorem chainG (f:Fin 23) (hfb:start f=firstBlock) (I J:Nat) (hI2:2≤I) (hIf:f.val+1≤I) (hJ:J≤19)
    (L1:EndpointBetween I J) (L2:ScratchSpec) (d:Bool) (x:Nat) (good:Bounds x p) (initial:State) :
    ∀(i:Fin 23) (js:List (Fin 23)),Consec i js → (∀k∈js,I≤k.val ∧ k.val≤J) →
    ∀(j j':Fin 23),j.val=i.val+1 → j'.val=(lastBlock i js).val+1 → ∀s m,RefW f j d x initial s →
      RefW f j' d x initial (run (chainF WindowParams.params d i js).flatten m s)
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
    exact chainG f hfb I J hI2 hIf hJ L1 L2 d x good initial j js rest (fun k hk=>hb k (List.mem_cons_of_mem _ hk))
      ⟨j.val+1,by omega⟩ j' rfl (by simpa only [lastBlock] using hj') _ _
      (nextG f hfb I J hI2 hIf hJ L1 L2 d x good initial s j ⟨j.val+1,by omega⟩ rfl bk.1 bk.2 _ h)

/-- The exit's stock-frame bank: the cells of its last ten ticks in the exit frame. -/
def newBankE (e:Nat) : List Wire := (OrdinaryChainW.cells10 (e-10)).map (OB5.sig e)

/-- The window's exit at `e` (hand-off block `jx`): the exit pieces agree with the stock exit tick off the last
bank, and the last bank's four holes are zero (the exit archive's blank code slots). Ship: `exitShip`. -/
abbrev ExitSpec (e:Nat) (jx:Fin 23) : Prop :=
  ∀ (d:Bool) (x:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool) (m:List Bool),
    AtJ jx d x p raw s g sg pg ps →
    Except (newBankE e) (run (exitF WindowParams.params d e).flatten m s)
      (pullState (OB5.sig e) (run (Rolling1588.encodeAt base d (e-15)) [] (run (span e 1) [] raw))) ∧
    ∀ r, (r=e-8 ∨ r=e-6 ∨ r=e-3 ∨ r=e-1) →
      (run (exitF WindowParams.params d e).flatten m s).basis (OB5.sig e (base (1028+r)))=false

theorem exitShip (L7:ExitProgSpec) (L8:ExitBridgeSpec) : ExitSpec 270 ⟨13,by decide⟩ := by
  intro d x good raw s g sg pg ps m pre
  rw [(L7 d).1]
  have lastF:=exitLast L8 d x good raw s g sg pg ps pre m
  have direct:=resultW d x good raw s g sg m pre.domain pre.input (exitCut L8 d x raw s g sg pg ps pre) lastF
  have nb:Ordinary270Terminal.newBank=newBankE 270:=by decide
  have one:span 270 1=EndTick.canonical:=by simp [span,EndTick.canonical]
  refine ⟨?_,?_⟩
  · rw [←nb,one,show 270-15=255 from rfl]; exact direct
  · obtain ⟨row,_,_,frame⟩:=lastF
    have cleared:=NativePack270.cleared_holes d row _ frame
    intro r hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact cleared _ (by decide)

theorem projectG (e:Nat) (he:e≤511) (raw out W:State) (direct:Except (newBankE e) out (pullState (OB5.sig e) W)) :
    Except (OrdinaryChainW.cells10 (e-10)) (pullState (OB5.sig e) out) W := by
  intro q absent
  have free:OB5.sig e q∉newBankE e:=by
    intro hit
    obtain ⟨w,hw,ew⟩:=List.mem_map.mp hit
    have := OB5.sig_injective e he ew
    exact absent (this ▸ hw)
  have := direct _ free
  simpa only [pullState,OB5.sig_invol e he] using this

theorem old_hole_G (e:Nat) (he:e+1≤512) (d:Bool) (raw out:State) (r:Nat) (r2:r+16≤e)
    (direct:Except (newBankE e) out
      (pullState (OB5.sig e) (run (Rolling1588.encodeAt base d (e-15)) [] (run (span e 1) [] raw))))
    (clear:raw.basis (base (1028+r))=false) :
    out.basis (OB5.sig e (base (1028+r)))=false := by
  have notNew:OB5.sig e (base (1028+r))∉newBankE e:=by
    intro hit
    obtain ⟨w,hw,ew⟩:=List.mem_map.mp hit
    have ew' := OB5.sig_injective e (by omega) ew
    subst ew'
    simp only [OrdinaryChainW.cells10,List.mem_flatMap,List.mem_range'_1,List.mem_cons,List.not_mem_nil,
      or_false] at hw
    obtain ⟨r',⟨a,b⟩,e1|e1⟩:=hw <;> simp only [base,Wire] at e1 <;> omega
  have eq:=direct _ notNew
  change out.basis _=(run (Rolling1588.encodeAt base d (e-15)) [] (run (span e 1) [] raw)).basis
    (OB5.sig e (OB5.sig e (base (1028+r)))) at eq
  rw [OB5.sig_invol e (by omega)] at eq
  have enc:base (1028+r)∉wires (Rolling1588.encodeAt base d (e-15)):=by
    intro used
    obtain ⟨r',a,b,e'|e'⟩:=OrdinaryChainW.encode_cells d (e-15) _ used <;> simp only [base,Wire] at e' <;> omega
  have tick:base (1028+r)∉wires (span e 1):=pastOffSpan e 1 _ he ⟨r,by omega,Or.inr rfl⟩
  rw [eq,run_preserves_outside _ _ _ _ enc,run_preserves_outside _ _ _ _ tick]
  exact clear

/-- dadon's `last270`/`terminal`, generic: window from block `f`, `n` banks, exit `start f+15n` (hand-off `jx`). -/
theorem lastG (f:Fin 23) (n:Nat) (hn:1≤n) (he:start f+15*n+1≤512) (jx:Fin 23) (hjx:jx.val=n+f.val)
    (X:ExitSpec (start f+15*n) jx)
    (d:Bool) (x:Nat) (good:Bounds x p) (initial s:State) (m:List Bool) (h:RefW f jx d x initial s) :
    ∀q∉StockWindowGeo.archives (start f) n,(run (exitF WindowParams.params d (start f+15*n)).flatten m s).basis q=
      (StockArchiveReferenceW.common (start f) n d initial).basis q := by
  obtain ⟨raw,g,sg,pg,ps,pre,old,zeros⟩:=h
  obtain ⟨direct,lastHoles⟩:=X d x good raw s g sg pg ps m pre
  have sf : 75≤start f := by simp only [StairPacket.start]; omega
  have e3:jx.val-f.val=n:=by omega
  have e4:jx.val-f.val-1=n-1:=by omega
  rw [e3] at old
  rw [e4] at zeros
  have all:=OrdinaryChainW.add_last (start f) (by omega) n hn he d raw initial _ old
    (projectG (start f+15*n) (by omega) raw _ _ direct)
  apply finishW (start f) n (by omega) hn (by omega) d _ initial all
  obtain ⟨n',rfl⟩:∃n',n=n'+1:=⟨n-1,by omega⟩
  intro w hw
  rw [holes_succ] at hw
  rcases List.mem_append.mp hw with h|h
  · obtain ⟨r,r1,r2,rfl⟩:=hole_cell (start f) n' (by omega) w h
    exact old_hole_G (start f+15*(n'+1)) he d raw _ r (by omega) direct
      (zeros _ (by simpa only [show n'+1-1=n' by omega] using h))
  · have g0:∀i,StockWindowGeo.gstart (start f) i=start f-5+5*i:=fun i=>by simp only [StockWindowGeo.gstart]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    · rw [show 1028+StockWindowGeo.gstart (start f) (2+3*n')+2=1028+(start f+15*(n'+1)-8) by rw [g0]; omega]
      exact lastHoles _ (Or.inl rfl)
    · rw [show 1028+StockWindowGeo.gstart (start f) (2+3*n')+4=1028+(start f+15*(n'+1)-6) by rw [g0]; omega]
      exact lastHoles _ (Or.inr (Or.inl rfl))
    · rw [show 1028+StockWindowGeo.gstart (start f) (3+3*n')+2=1028+(start f+15*(n'+1)-3) by rw [g0]; omega]
      exact lastHoles _ (Or.inr (Or.inr (Or.inl rfl)))
    · rw [show 1028+StockWindowGeo.gstart (start f) (3+3*n')+4=1028+(start f+15*(n'+1)-1) by rw [g0]; omega]
      exact lastHoles _ (Or.inr (Or.inr (Or.inr rfl)))

/-- dadon's `begin225` at the first block `f` (next block `k1`), from the first-form leaves only. -/
theorem beginG (f k1:Fin 23) (hf1:1≤f.val) (hk1:k1.val=f.val+1) (F:FirstSpecF f k1) (FO:FirstOrdinarySpecF f)
    (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis) :
    RefW f k1 d x raw (run ((portalP (start f)++NativeFirstJ.enteredWindow f d)++
      leaveMoveP f) m (pullState (OB5.sig (start f-1)) raw)) := by
  rw [run_append,run_take,firstSameF f k1 hf1 hk1 F d x p good raw m _ stage]
  have sf : 75≤start f ∧ start f≤405 := by simp only [StairPacket.start]; omega
  let v:=run (portalP (start f)++NativeFirstJ.enteredWindow f d) m (pullState (OB5.sig (start f-1)) raw)
  let n:=m.drop (measurementCount (portalP (start f)++NativeFirstJ.enteredWindow f d))
  obtain ⟨g,sg,input,hin,cut,facts⟩:=F d x p good raw m n stage
  let flags:=LeaveJ.Admission.flags (unsigned (start f) x p) g sg
  have dom:=initial (start f) x p (by omega) d raw stage
  have carried:=stepInput_gen (start f) (sbP (start f)) x p (by omega) (by omega) good raw v g sg dom input hin.small
  have s1:start k1=start f+15:=by simp only [StairPacket.start]; omega
  have p1:NativeJ.prev k1=f:=Fin.ext (by simp only [NativeJ.prev]; omega)
  refine ⟨endRaw (start f) raw v,flags.1,flags.2,g,sg,⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [s1]; exact cut
  · rw [p1]; exact facts
  · rw [p1]; exact unique_input input (fixed_input (start f) x p (by omega) good raw dom)
  · rw [show k1.val-f.val=1 by omega]
    have fo:=FO d x p good raw m stage
    simp only [OrdinaryChainW.mask,OrdinaryChainW.progW,OrdinaryChainW.newBank,OrdinaryChainW.group,
      Nat.mul_zero,Nat.add_zero,if_true,List.nil_append,Nat.mul_one]
    exact fo
  · rw [show k1.val-f.val-1=0 by omega]
    intro q hq
    simp [StockWindowGeo.holes,StockWindowGeo.packed] at hq

/-- `OrdinaryChain.wires` for any window over the fold: first block `f` (tick `start f`), interior blocks `I..J`,
`n` banks, exit `start f+15n`. Ship: f = 3, n = 10; 345: f = 3, n = 16; 90..345: f = 1, n = 18; 90..360: f = 1, n = 19. -/
theorem wiresFold (f k1:Fin 23) (hk1:k1.val=f.val+1) (hfb:start f=firstBlock)
    (I J:Nat) (hI2:2≤I) (hIf:f.val+1≤I) (hJ:J≤19)
    (L1:EndpointBetween I J) (L2:ScratchSpec) (F:FirstSpecF f k1) (FO:FirstOrdinarySpecF f)
    (js:List (Fin 23)) (consec:Consec f js) (hb:∀k∈js,I≤k.val ∧ k.val≤J)
    (n:Nat) (hn:1≤n) (he:start f+15*n+1≤512) (hl:(lastBlock f js).val+1=n+f.val)
    (jx:Fin 23) (hjx:jx.val=n+f.val) (X:ExitSpec (start f+15*n) jx)
    (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start f) raw.basis) :
    ∀q∉StockWindowGeo.archives (start f) n,
      (run (forwardW WindowParams.params d f js) m (pullState (OB5.sig (start f-1)) raw)).basis q=
      (StockArchiveReferenceW.common (start f) n d raw).basis q := by
  have et:exitTick f js=start f+15*n:=by
    simp only [exitTick,lastStart_eq,StairPacket.start]; omega
  have sp:forwardW WindowParams.params d f js=
      (((WindowParams.params.portal (start f) :: firstF WindowParams.params d f).flatten++
        (chainF WindowParams.params d f js).flatten)++
        (exitF WindowParams.params d (start f+15*n)).flatten):=by
    rw [forwardW,forwardL,et]
    simp only [List.flatten_cons,List.flatten_append,List.append_assoc]
  have beg:∀k,RefW f k1 d x raw (run ((WindowParams.params.portal (start f) ::
      firstF WindowParams.params d f).flatten) k (pullState (OB5.sig (start f-1)) raw)):=by
    intro k
    rw [first_eqF d f]
    exact beginG f k1 (by have e:75+15*(f:Nat)=75+15*(WindowParams.first:Nat):=hfb; have f1:(WindowParams.first:Nat)=1:=rfl; omega)
      hk1 F FO d x good raw k stage
  rw [sp,run_append,run_append]
  exact lastG f n hn he jx hjx X d x good raw _ _
    (chainG f hfb I J hI2 hIf hJ L1 L2 d x good raw f js consec hb k1 jx hk1 (by omega) _ _ (beg _))

/-- Blocks of the 90..360 window (`WindowParams.rest = 2..19`, SA's `WindowCovered.rest_eq`). -/
theorem mem_rest19 {k : Fin 23} (h : k ∈ WindowParams.rest) : 2 ≤ k.val ∧ k.val ≤ 19 := by
  simp only [WindowParams.rest,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at h
  omega

theorem lastBlock_360 : lastBlock WindowParams.first WindowParams.rest=⟨19,by decide⟩ := by
  rw [WindowCovered.rest_eq]; rfl

-- ==== window390: the exit at 375 (Window: Exit375 + LExit375; here: MainExit375 + Glue375 above Part 6) ====
/-- window390 (from build-chain's (at 360) main360): the exit at 375 (`resultW375` + the exit's blank holes), as `exitShip` at 270. -/
theorem exit375 : ExitSpec 375 ⟨20,by decide⟩ := by
  intro d x good raw s g sg pg ps m pre
  rw [(StockWindowW.exitProg375 d).1]
  have lastF:=exitLast375 d x good raw s g sg pg ps pre m
  have direct:=resultW375 d x good raw s g sg m pre.domain pre.input (exitCut375 d x raw s g sg pg ps pre) lastF
  have nb:Ordinary375Terminal.newBank=newBankE 375:=by decide
  have one:span 375 1=EndTick375.canonical:=by simp [span,EndTick375.canonical]
  refine ⟨?_,?_⟩
  · rw [←nb,one,show 375-15=360 from rfl]; exact direct
  · obtain ⟨row,_,_,frame⟩:=lastF
    have cleared:=NativePack375.cleared_holes d row _ frame
    intro r hr
    rcases hr with rfl|rfl|rfl|rfl <;> exact cleared _ (by decide)

theorem wires360 (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) :
    ∀q∉StockWindowGeo.archives 90 19,(run (Partial.forward45plus1 d) m (pullState (OB5.sig 89) raw)).basis q=
      (StockArchiveReferenceW.common 90 19 d raw).basis q :=
  wiresFold WindowParams.first ⟨2,by decide⟩ rfl rfl 2 19 (by decide) (by decide) (by decide) leaves19.endpoint
    leaves19.scratch (first_ship leaves19.first) (firstOrdinary_ship firstOrdinary)
    WindowParams.rest WindowCovered.consec (fun k hk=>mem_rest19 hk) 19 (by decide) (by decide) (by rw [lastBlock_360]; rfl)
    ⟨20,by decide⟩ rfl exit375 d x good raw m stage

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

section
namespace ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
open Arithmetic MappedCompressed WideReference Secp256k1 StockWindowW

/-- `OrdinaryChain.wires` of the ship (window 120..255, exit 270). -/
theorem wiresShip (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) :
    ∀q∉StockWindowGeo.archives 90 19,(run (Partial.forward45plus1 d) m (pullState (OB5.sig 89) raw)).basis q=
      (StockArchiveReferenceW.common 90 19 d raw).basis q :=
  wires360 d x good raw m stage

end ECDSAAdd.Entrant.StairPacket.OrdinaryChainG
end

-- ==== end build-main2 OrdW ====

-- ==== build-main2: the ship's stock comparison API (window 90..360, exit 375, 19 banks) ====
-- dadon's 3-bank names (StockArchiveReference.common, StockStrongChain.result, StockArchiveBanks.*,
-- StockRowVector.rows/binding, StockBaseline.comparison) re-opened as instances of the generic W sections.
section
namespace ECDSAAdd.Entrant.StairPacket.StockWindowChainP
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1 StockCanonicalRow StockWindowW StockStrongChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run measurementCount key select WideReference.canonical
/-- window390: the exit archive's code ports at 375 (first 16 = `cellsRestoreP 375`). -/
def ExitPorts375 : Ports := ArchiveBoundary375.codePorts
/-- window390: the exit at 375 (its step to the last frame and the keys it keeps). -/
theorem exitLeaves375 : ExitLeaves ⟨19,by decide⟩ ExitPorts375 := StockWindowW.exitLeaves375
/-- window390 (from build-chain's (at 360) main360): dadon's `finalBank` at 375 (the exit archive keeps block 19's key; `finalS` at 270). -/
theorem finalKey375 : ∀ (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (m:List Bool), ReadyW d x p 375 s →
    SavedKey (value x p 360 (sbP 360) (StockRowVectorW.crossW ⟨19,by decide⟩)) ExitPorts375 d
      (run (exitF WindowParams.params d 375).flatten m s) := by
  intro d x good s m h
  obtain ⟨k,ek,raw,g,sg,pg,ps,pre⟩:=h
  have k19:k=⟨20,by decide⟩:=Fin.ext (by have := ek; simp only [StairPacket.start] at this; show k.val=20; omega)
  subst k19
  rw [(StockWindowW.exitProg375 d).1]
  have cut:=OrdinaryChainG.exitCut375 d x raw s g sg pg ps pre
  obtain ⟨-,-,-,-,-,-,-,r20,r21,r22⟩:=StockWindowW.exitBridge375
  let z:=unsigned 375 x p
  have short:min z.u z.v<2^69:=true_small x p 375 (lt_trans good.small good.cap) good.cap (by decide)
  have old:=LeaveJ.Admission.actualNumbers ⟨19,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 69 375 x p=(3*2^85≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have facts:=pre.facts
  have mode:s.basis 1649=decide (Shadow.far 76 15 (unsigned 360 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1650=(decide (Shadow.far 76 15 (unsigned 360 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 360 x p).v<(unsigned 360 x p).u))
        ((physicalCells ArchiveBoundary375.sourceIdx s).take 5)):=by rw [←r21]; exact facts.suffix
  have cross:s.basis 1651=(decide (Shadow.far 76 15 (unsigned 360 x p)) &&
      HighBankSum.cross (LeaveJ.TrueMiddle.d ⟨19,by decide⟩ (unsigned 360 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack375.selected_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 375 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 360 x p) pg ps _
    old.odd old.small facts.records mode side cross
  have canon:signedAt 360 x p pg ps=WideReference.canonical 360 x p:=pre.pastCanonical
  unfold signedAt at canon
  have cert:=last.2.1
  dsimp only at cert
  rw [canon] at cert
  have sbq:sbP 360=76:=by decide
  rw [sbq]
  exact ⟨cert.1,cert.2.1,kept_frame _ _ _ _ cert.2.2⟩

theorem mem19 {k : Fin 23} (h : k ∈ WindowParams.rest) : 2 ≤ k.val ∧ k.val ≤ (⟨19,by decide⟩:Fin 23).val := by
  simp only [WindowParams.rest,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq] at h
  show 2 ≤ k.val ∧ k.val ≤ 19
  omega
theorem exitT375 : exitTick WindowParams.first WindowParams.rest=start ⟨19,by decide⟩+15 := by
  rw [WindowCovered.rest_eq]; rfl

/-- `StockWindowChain.result` of the 90..360 window (Final = FinalW 1 19 at 375), from build-chain's `checkedG`. -/
theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) :
    let start:=pullState (OB5.sig 89) raw
    let out:=run (forward45plus1 d) m start
    out.phase=raw.phase ∧ FinalW ⟨1,by decide⟩ ⟨19,by decide⟩ ExitPorts375 d x p out ∧
      ∀n,run (reverse45plus1 d) n out=start := by
  have law:=checkedG ⟨19,by decide⟩ (by decide) (by decide) ExitPorts375 WindowParams.rest WindowCovered.consec
    (fun k hk=>mem19 hk) exitT375 leaves19 exitLeaves375 d x good
  rw [←Partial.assembly,←Partial.unwind_assembly] at law
  exact law _ m ⟨raw,stage,rfl⟩

/-- Block `i`'s saved key (dadon's `SavedKey (value x p s b cross{s}) codePorts{s+15}`), for every block. -/
def KeyS (d:Bool) (x p:Nat) (i:Fin 23) (s:State) : Prop :=
  SavedKey (value x p (start i) (sbP (start i)) (StockRowVectorW.crossW i)) (ArchiveJ.codePorts i) d s
def KeyLast (d:Bool) (x p:Nat) (s:State) : Prop :=
  SavedKey (value x p 360 (sbP 360) (StockRowVectorW.crossW ⟨19,by decide⟩)) ExitPorts375 d s
def LastS (d:Bool) (x p:Nat) (s:State) : Prop := LastAt ExitPorts375 ⟨19,by decide⟩ d x p s ∧ KeyLast d x p s

/-- dadon's `selected{s}` receipt for any interior block `k ≤ 19` (saves block `i = k-1`'s key). -/
theorem receiptS (d:Bool) (x p:Nat) (good:Bounds x p) (i k:Fin 23) (hk:k.val=i.val+1)
    (h2:2≤k.val) (h18:k.val≤19) :
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
  have scr:=leaves19.scratch k h2 (by omega) d x p good raw s g sg pg ps m pre
  have cert:=NativeJ.selected_receipt k (by omega) (by omega) d raw s m (unsigned (start k) x p) g sg nums.odd nums.small
    pre.cut curr hist scr (unsigned (start (NativeJ.prev k)) x p) pg ps _ old.odd old.small pre.facts
  have canon:=pre.pastCanonical
  unfold signedAt at canon
  dsimp only at cert
  rw [canon] at cert
  exact ⟨cert.1,cert.2.1,ArchiveWindowPreserve.keep cert.2.2 (fun q hq=>leaves19.keepLeave k h2 h18 q hq _ _)⟩

theorem keyS_eq (x p b:Nat) (hb:1+b<23) :
    StockRowVectorW.keys ⟨1,by decide⟩ x p b=value x p (start ⟨1+b,hb⟩) (sbP (start ⟨1+b,hb⟩))
      (StockRowVectorW.crossW ⟨1+b,hb⟩) := by
  have e:start (⟨1,by decide⟩:Fin 23)+15*b=start ⟨1+b,hb⟩:=by simp only [StairPacket.start]; omega
  simp only [StockRowVectorW.keys,dif_pos hb]
  rw [e]

/-- The window's strong chain with the 19 saved keys (window_strong instance; dadon's `StockStrongChain.result`). -/
theorem strong (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) :
    let start0:=pullState (OB5.sig 89) raw
    let out:=run (forward45plus1 d) m start0
    out.phase=raw.phase ∧ StockRowVectorW.final ⟨1,by decide⟩ ⟨19,by decide⟩ ExitPorts375 d x p out ∧
      ∀n,run (reverse45plus1 d) n out=start0 := by
  have bl:blockOf (exitTick WindowParams.first WindowParams.rest)=20:=by rw [exitT375]; rfl
  have lastC:Checked (exitF WindowParams.params d (exitTick WindowParams.first WindowParams.rest)).flatten
      (exitR WindowParams.params d (exitTick WindowParams.first WindowParams.rest)).flatten
      (ReadyW d x p (exitTick WindowParams.first WindowParams.rest)) (LastS d x p):=by
    rw [exitT375]
    intro s n h
    have e:=exitLeaves375.step d x good s n h
    exact ⟨e.1,⟨e.2.1,finalKey375 d x good s n h⟩,e.2.2⟩
  have strong:=window_strong WindowParams.params d (ReadyW d x p) (KeyS d x p) (BeforeW d x p) (LastS d x p)
    WindowParams.first WindowParams.rest WindowCovered.consec (firstStepG 19 leaves19 d x p good)
    (fun i k hm hk=>interiorG 19 (by decide) leaves19 d x p good i k hk (mem19 hm).1 (mem19 hm).2)
    (fun i k hm hk=>receiptS d x p good i k hk (by have h:2 ≤ k.val:=(mem19 hm).1; omega)
      (by have h:k.val ≤ 19:=(mem19 hm).2; omega))
    (fun i k hm hk s n _ i' h1 h2 key=>by
      obtain ⟨rr,c,kept⟩:=key
      have f3:WindowParams.first.val=1:=rfl
      exact ⟨rr,c,ArchiveWindowPreserve.keep kept (fun q hq=>leaves19.keepOlder i k i' hk (by omega) (by omega)
        (by have h:k.val ≤ 19:=(mem19 hm).2; exact h) d q hq s n)⟩)
    lastC
    (by
      intro s n _ i h1 h2 key
      rw [bl] at h2
      revert key
      rw [exitT375]
      intro key
      obtain ⟨r,c,kept⟩:=key
      exact ⟨r,c,ArchiveWindowPreserve.keep kept (fun q hq=>exitLeaves375.keep i h1 (by show i.val < 19; omega) d q hq s n)⟩)
  rw [Partial.assembly,Partial.unwind_assembly]
  intro start0 out
  obtain ⟨ph,⟨⟨_,lastKey⟩,saved⟩,undo⟩:=strong start0 m ⟨raw,stage,rfl⟩
  refine ⟨ph,?_,undo⟩
  intro b hb
  change 1+b ≤ 19 at hb
  have lt:1+b<23:=by omega
  rw [keyS_eq x p b lt]
  unfold ArchiveStockRows.bankPorts
  by_cases h:(⟨1,by decide⟩:Fin 23).val+b<(⟨19,by decide⟩:Fin 23).val
  · rw [dif_pos h]
    change 1+b < 19 at h
    exact saved ⟨1+b,lt⟩ (by show 1 ≤ 1+b; omega) (by rw [bl]; show 1+b+2 ≤ 20; omega)
  · rw [dif_neg h]
    change ¬(1+b < 19) at h
    have e:(⟨1+b,lt⟩:Fin 23)=⟨19,by decide⟩:=Fin.ext (by show 1+b=19; omega)
    rw [e]
    have s19:start (⟨19,by decide⟩:Fin 23)=360:=rfl
    rw [s19]
    exact lastKey
end ECDSAAdd.Entrant.StairPacket.StockWindowChainP
end

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

/-- dadon's name: the window's strong chain (19 keys; window390: window_strong instance at 375). -/
theorem result (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) :
    let start0:=pullState (OB5.sig 89) raw
    let out:=run (forward45plus1 d) m start0
    out.phase=raw.phase ∧ StockRowVectorW.final ⟨1,by decide⟩ ⟨19,by decide⟩ StockWindowChainP.ExitPorts375 d x p out ∧
      ∀n,run (reverse45plus1 d) n out=start0 :=
  StockWindowChainP.strong d x good raw m stage

end ECDSAAdd.Entrant.StairPacket.StockStrongChain
end

section
namespace ECDSAAdd.Entrant.StairPacket.StockArchiveReference
open Arithmetic MappedCompressed WideReference
/-- The ship's stock reference (dadon's `common` at 225..270, now 120..270). -/
def common (d:Bool) (raw:State):State:=StockArchiveReferenceW.common 90 19 d raw
end ECDSAAdd.Entrant.StairPacket.StockArchiveReference

namespace ECDSAAdd.Entrant.StairPacket.StockArchiveBanks
open Arithmetic MappedCompressed Secp256k1 WideReference ArchivePortAction StairArchiveNativeRows CodecBitSliceVerify
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
attribute [local irreducible] run span
/-- The ship's banks: bank `b` is block `1+b`'s archive, bank 18 the exit archive. -/
abbrev Bank := Fin 19
def j1 : Fin 23 := ⟨1,by decide⟩
def jn : Fin 23 := ⟨19,by decide⟩
def ports (b:Bank):Ports:=ArchiveStockRows.bankPorts j1 jn StockWindowChainP.ExitPorts375 b.val
def siteAt (b:Bank) (j:Fin 16):Wire:=ports b ⟨j.val,by omega⟩
def tick (b:Bank):Nat:=90+15*b.val
def archives:List Wire:=StockWindowGeo.archives 90 19
def Same (a b:State):Prop:=ArchiveStockSuffixW.Same 90 19 a b
def nativeAt (d:Bool) (b:Bank) (r:Nat) (s:State):Prop:=StockArchiveBanksW.nativeAt (siteAt b) d r s

theorem exitCells : ∀j:Fin 16,StockWindowChainP.ExitPorts375 ⟨j.val,by omega⟩=
    (Partial.cellsRestoreP (start jn+15)).getD j 0 := by decide +kernel
theorem site_eq (b:Bank) (j:Fin 16) : siteAt b j=StockWindowGeo.bankSite 90 b.val j :=
  StockArchiveBanksW.site_eq j1 jn StockWindowChainP.ExitPorts375 exitCells b.val (by simp only [j1,jn]; omega) j
theorem mem (b:Bank) (j:Fin 16) : siteAt b j∈archives := by
  rw [site_eq]; exact StockWindowGeo.bank_mem 90 19 b.val b.isLt j
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
    (h:StockArchiveBanksW.Paired j1 jn StockWindowChainP.ExitPorts375 19 d x a s rows) :
    Paired d x a s (fun b=>rows b.val) :=
  ⟨h.equality,fun b=>h.labels b.val b.isLt,fun b=>h.custom b.val b.isLt,fun b=>h.stock b.val b.isLt⟩

theorem Paired.through {d x a s rows} (pair:Paired d x a s rows) (P:Program)
    (off:∀q∈archives,q∉wires P) (m:List Bool):Paired d x (run P m a) (run P m s) rows:=by
  have h:=ArchiveStockSuffixW.independent 90 19 P off m a s pair.equality
  refine ⟨h.1,pair.labels,?_,?_⟩
  · intro b j
    exact (h.2 (siteAt b j) (mem b j)).trans (pair.custom b j)
  · intro b j
    exact (run_preserves_outside P m s (siteAt b j) (off _ (mem b j))).trans (pair.stock b j)

/-- `ArchiveStockSuffix.safe` for the ship's banks. -/
theorem safe (d:Bool) (i n:Nat) (lo:376 ≤ i) (hi:i+n ≤ 512) (q:Wire) (mem:q∈archives) :
    q∉wires (Rolling1588TickGap.forward d i n) ∧ q∉wires (Rolling1588.reverse d i n) :=
  ArchiveStockSuffixW.safe 90 19 375 (by decide) rfl (by decide) (by decide) d i n lo hi q mem
end ECDSAAdd.Entrant.StairPacket.StockArchiveBanks

namespace ECDSAAdd.Entrant.StairPacket.StockRowVector
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks
/-- The ship's key-selected rows (bank `b` = block `3+b`). -/
noncomputable def rows (x p:Nat) (b:Bank):Nat:=StockRowVectorW.rows j1 x p b.val
theorem binding (d:Bool) (x:Nat) (good:Bounds x p) (raw a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis)
    (stored:StockRowVectorW.final j1 jn StockWindowChainP.ExitPorts375 d x p a)
    (same:Same a (run (Rolling1588TickGap.forward d 90 286) m (pullState (OB5.sig 89) raw))) :
    Paired d x a (run (Rolling1588TickGap.forward d 90 286) m (pullState (OB5.sig 89) raw)) (rows x p) :=
  Paired.ofW (StockRowVectorW.binding j1 jn StockWindowChainP.ExitPorts375 exitCells 19 rfl (by decide) d x good raw a m
    stage stored same)
end ECDSAAdd.Entrant.StairPacket.StockRowVector

namespace ECDSAAdd.Entrant.StairPacket.StockBaseline
open Arithmetic MappedCompressed WideReference Secp256k1 StockArchiveBanks
/-- dadon's `comparison` for the ship. -/
theorem comparison (d:Bool) (x:Nat) (good:Bounds x p) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 s.basis) (results:ArchiveStockRows.FinalW ⟨1,by decide⟩ ⟨19,by decide⟩ StockWindowChainP.ExitPorts375 d x p a) :
    Same (run (Rolling1588TickGap.forward d 90 286) m (pullState (OB5.sig 89) s)) (StockArchiveReference.common d s) :=
  StockBaselineW.comparison (j1:=⟨1,by decide⟩) (jn:=⟨19,by decide⟩) 19 rfl (by decide) d x good s a m stage results
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
private theorem hook (j:Nat) (hj:j∈[19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]) (op:Stage):GoodP (fieldHook j op):=by
  have span:j∈List.range' 1 83:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;apply List.mem_range'_1.mpr;omega
  have chk:(fieldSites j).all (fun q=>decide (16 ≤ q ∧ q < 2330))=true:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
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
private theorem pair (d:Bool) (j:Nat) (hj:j∈[19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]) (hi:j≤83):GoodP (ten j (!d)):=by
  have here:=singleton d j (by omega)
  have next:=singleton d (j+1) (by omega)
  have a:GoodP (first j (!d)):=by cases d <;> first | exact here | exact next
  have b:GoodP (second j (!d)):=by cases d <;> first | exact here | exact next
  exact app (hook j hj _) (app a (app (hook j hj _) (app b (hook j hj _))))
-- oddten:begin GOOD
theorem group84_good (d:Bool):GoodP (group84 d):=by
  have ord {a b:Program} (x:GoodP a) (y:GoodP b):GoodP (ordered d a b):=by cases d <;> first | exact app x y | exact app y x
  have og (j n:Nat) (hi:j+n≤102):GoodP (ogroup d j n):=
    Finset.Subset.trans (WindowFieldCosts.ot_ogroup_sub d j n) (ordinary d j n hi)
  have ot (j:Nat) (hj:j∈[19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]) (hi:j≤83):GoodP (oten j (!d)):=
    Finset.Subset.trans (WindowFieldCosts.ot_oten_sub j (!d)) (pair d j hj hi)
  exact ord (og 1 18 (by decide))
    (ord (ot 19 (by decide) (by decide))
    (ord (og 21 1 (by decide))
    (ord (ot 22 (by decide) (by decide))
    (ord (og 24 1 (by decide))
    (ord (ot 25 (by decide) (by decide))
    (ord (og 27 1 (by decide))
    (ord (ot 28 (by decide) (by decide))
    (ord (og 30 1 (by decide))
    (ord (ot 31 (by decide) (by decide))
    (ord (og 33 1 (by decide))
    (ord (ot 34 (by decide) (by decide))
    (ord (og 36 1 (by decide))
    (ord (ot 37 (by decide) (by decide))
    (ord (og 39 1 (by decide))
    (ord (ot 40 (by decide) (by decide))
    (ord (og 42 1 (by decide))
    (ord (ot 43 (by decide) (by decide))
    (ord (og 45 1 (by decide))
    (ord (ot 46 (by decide) (by decide))
    (ord (og 48 1 (by decide))
    (ord (ot 49 (by decide) (by decide))
    (ord (og 51 1 (by decide))
    (ord (ot 52 (by decide) (by decide))
    (ord (og 54 1 (by decide))
    (ord (ot 55 (by decide) (by decide))
    (ord (og 57 1 (by decide))
    (ord (ot 58 (by decide) (by decide))
    (ord (og 60 1 (by decide))
    (ord (ot 61 (by decide) (by decide))
    (ord (og 63 1 (by decide))
    (ord (ot 64 (by decide) (by decide))
    (ord (og 66 1 (by decide))
    (ord (ot 67 (by decide) (by decide))
    (ord (og 69 1 (by decide))
    (ord (ot 70 (by decide) (by decide))
    (ord (og 72 1 (by decide))
    (ord (ot 73 (by decide) (by decide))
    (og 75 10 (by decide)))))))))))))))))))))))))))))))))))))))
-- oddten:end GOOD

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
def divBefore:Program:=renameProgram phaseHost (openWalk true 49++checkpointPrimitives.firstPack)++WindowParityCaller.entryFieldHosted checkpointPrimitives
def divAfter:Program:=Stair44Outer.reverseEnd++(WindowWalkCosts.backward false 130++renameProgram first (FrontierEntry1591NativeH.inverse base))
def division:Program:=divBefore++renameProgram phaseHost divAfter
def mulBefore:Program:=(renameProgram phaseHost (openWalk false 129++Stair44Outer.forwardEnd)++WindowParityCaller.exitFieldHosted checkpointPrimitives)++renameProgram phaseHost checkpointPrimitives.firstUnpack
def mulAfter (k:Nat):Program:=WindowWalkCosts.backward true 49++renameProgram rawX (ParityXExitInverse23Kernel.x1N k)
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
  have bk:∀ j∈[19, 22, 25, 28, 31, 34, 37, 40, 43, 46, 49, 52, 55, 58, 61, 64, 67, 70, 73],StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330))
      (WindowFieldParity.bankCorrection j)=true:=by
    intro j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  have table:StairWireCheck.allSites (fun q=>decide (16 ≤ q ∧ q < 2330)) WindowFieldParity.correction=true:=by
    unfold WindowFieldParity.correction
    exact (app _ _ (bk 19 (by decide)) (app _ _ (bk 22 (by decide)) (app _ _ (bk 25 (by decide)) (app _ _ (bk 28 (by decide)) (app _ _ (bk 31 (by decide)) (app _ _ (bk 34 (by decide)) (app _ _ (bk 37 (by decide)) (app _ _ (bk 40 (by decide)) (app _ _ (bk 43 (by decide)) (app _ _ (bk 46 (by decide)) (app _ _ (bk 49 (by decide)) (app _ _ (bk 52 (by decide)) (app _ _ (bk 55 (by decide)) (app _ _ (bk 58 (by decide)) (app _ _ (bk 61 (by decide)) (app _ _ (bk 64 (by decide)) (app _ _ (bk 67 (by decide)) (app _ _ (bk 70 (by decide)) (bk 73 (by decide))))))))))))))))))))
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
    (stage:Rolling1588.Integer.Stage base d x p 90 s.basis) :
    (StockArchiveReferenceW.common 90 19 d s).phase=s.phase := by
  have final:=(StockWindowChainP.result d x good s [] stage).2.1
  have same:=StockBaselineW.comparison (j1:=⟨1,by decide⟩) (jn:=⟨19,by decide⟩) 19 rfl (by decide) d x good s _ [] stage final
  exact same.1.symm.trans (StockBaseline.forward_phase d x good 90 286 (by decide) (by decide) s [] stage)

theorem normalized (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) :
    ArchiveStockSuffixW.Same 90 19 (run (Partial.forward45plus1 d) m (pullState (OB5.sig 89) raw))
      (StockArchiveReferenceW.common 90 19 d raw) :=
  ⟨(StockWindowChainP.result d x good raw m stage).1.trans (common_phase d x good raw stage).symm,
    OrdinaryChainG.wiresShip d x good raw m stage⟩
end ECDSAAdd.Entrant.StairPacket.StockNativeCompare

end

section

namespace ECDSAAdd.Entrant.StairPacket.StockWalkWindow
open Arithmetic MappedCompressed Secp256k1 WideReference StockArchiveBanks StockWalkPrefix
set_option maxRecDepth 9500
set_option maxHeartbeats 3000000
attribute [local irreducible] run Rolling1588TickGap.forward Rolling1588.Integer.regularForward measurementCount Partial.forward45plus1
def NewNormalized (d:Bool) (x:Nat):Prop:=∀(raw:State)(m:List Bool),Rolling1588.Integer.Stage base d x p 90 raw.basis →
    Same (run (Partial.forward45plus1 d) m (pullState (OB5.sig 89) raw)) (StockArchiveReference.common d raw)

theorem steady (d:Bool) (x:Nat) (good:Bounds x p) (i n:Nat) (lo:0 < i) (hi:i+n≤512) (s:State) (u v:List Bool) (stage:Rolling1588.Integer.Stage base d x p i s.basis):
    run (Rolling1588TickGap.forward d i n) u (pullState (OB5.sig (i-1)) s)=run (Rolling1588TickGap.forward d i n) v (pullState (OB5.sig (i-1)) s):=
  (StockDelayed.window d x good.nonzero good.small i n lo hi s u stage).trans
    (StockDelayed.window d x good.nonzero good.small i n lo hi s v stage).symm
theorem suffix_independent (d:Bool) (n x:Nat) (good:Bounds x p) (bound:376+n≤512) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 90 s.basis) (u v y z:List Bool):
    let t:=pullState (OB5.sig 89) s
    let old:=Rolling1588TickGap.forward d 90 286
    let tail:=Rolling1588TickGap.forward d 376 n
    run tail u (run old v t)=run tail y (run old z t):=by
  let t:=pullState (OB5.sig 89) s
  let A:=Rolling1588TickGap.forward d 90 286
  let B:=Rolling1588TickGap.forward d 376 n
  let mix (v u:List Bool):=FlagEntry.pfx (measurementCount A) v++u
  have eq:=steady d x good 90 (286+n) (by decide) (by omega) s (mix v u) (mix z y) stage
  rw [StairRestSupport.forward_append d 286 90 n] at eq
  exact (Stair44PointSecond.joinRecords A B v u t).symm.trans (eq.trans (Stair44PointSecond.joinRecords A B z y t))

theorem window (d:Bool) (n x:Nat) (good:Bounds x p) (bound:376+n≤512) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) (m stockTape:List Bool) (norm:NewNormalized d x):
    let s:=pullState (OB5.sig 89) raw
    Paired d x (run (forwardEnd d n) m s) (run (Rolling1588TickGap.forward d 90 (286+n)) stockTape s) (StockRowVector.rows x p):=by
  let s:=pullState (OB5.sig 89) raw
  have result:=StockWindowChainP.result d x good raw m stage
  have old:=StockBaseline.comparison d x good raw _ m stage result.2.1
  have new:=norm raw m stage
  have eq:Same _ _:=⟨new.1.trans old.1.symm,fun q off=>(new.2 q off).trans (old.2 q off).symm⟩
  have h:=StockRowVector.binding d x good raw _ m stage (StockStrongChain.result d x good raw m stage).2.1 eq
  have onward:=h.through (Rolling1588TickGap.forward d 376 n) (fun q h=>(safe d 376 n (by decide) bound q h).1) (m.drop (measurementCount (Partial.forward45plus1 d)))
  simp only [forwardEnd,StairRestSupport.forward_append d 286 90 n,run_append,run_take]
  rw [←suffix_independent d n x good bound raw stage (m.drop (measurementCount (Partial.forward45plus1 d))) m (stockTape.drop (measurementCount (Rolling1588TickGap.forward d 90 286))) stockTape]
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

theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.forward d (360+n)=
    first d++renameProgram Stair44WalkMap.rest (Rolling1588TickGap.forward d 90 (286+n)):=by
  have e:=StairRestSupport.forward_append d 74 16 (286+n)
  change Rolling1588TickGap.forward d 16 (74+(286+n))=Rolling1588TickGap.forward d 16 74++Rolling1588TickGap.forward d 90 (286+n) at e
  rw [show 360+n=74+(286+n) by omega]
  simp only [Stair44WalkRun.forward,first,e,renameProgram,List.map_append,List.append_assoc]

theorem forward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:376+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s) (norm:NewNormalized d x):
    Paired d x (run (WindowWalkCosts.forward d n) m a) (run (Stair44WalkRun.forward d (360+n)) m a) (StockRowVector.rows x p):=by
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
def groupId (b:Bank):Nat:=19+3*b.val
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
def fieldRows (r:Bank→Nat) (j:Nat):Nat:=r ⟨((j-19)/3)%19,Nat.mod_lt _ (by decide)⟩
theorem rowsAt (r:Bank→Nat) (b:Bank):fieldRows r (groupId b)=r b:=by
  unfold fieldRows groupId
  congr 1
  apply Fin.ext
  have hb:=b.isLt
  show ((19+3*b.val-19)/3)%19=b.val
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

def real (d:Bool) (raw:State):State:=run (Partial.forward45plus1 d) [] (pullState (OB5.sig 89) raw)
def stock (d:Bool) (raw:State):State:=run (Rolling1588TickGap.forward d 90 286) [] (pullState (OB5.sig 89) raw)
theorem shadow (d:Bool) (x:Nat) (good:Bounds x p) (raw:State)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) (norm:NewNormalized d x):
    Paired d x (real d raw) (stock d raw) (StockRowVector.rows x p):=by
  have e:=norm raw [] stage
  have cmp:=StockBaseline.comparison d x good raw _ [] stage (StockWindowChainP.result d x good raw [] stage).2.1
  exact StockRowVector.binding d x good raw _ [] stage (StockStrongChain.result d x good raw [] stage).2.1
    ⟨e.1.trans cmp.1.symm,fun q off=>(e.2 q off).trans (cmp.2 q off).symm⟩
theorem candidate_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis):
    run (Partial.reverse45plus1 d) m (real d raw)=pullState (OB5.sig 89) raw:=
  (StockWindowChainP.result d x good raw [] stage).2.2 m
theorem stock_undo (d:Bool) (x:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis):
    run (Rolling1588.reverse d 90 286) m (stock d raw)=pullState (OB5.sig 89) raw:=
  reverse_forward d x good 90 286 (by decide) (by decide) raw [] m stage
attribute [local irreducible] real stock poolEq
theorem inner (d:Bool) (x:Nat) (good:Bounds x p) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (stock d raw)):
    run (Partial.reverse45plus1 d) m a=run (Rolling1588.reverse d 90 286) m ref:=by
  have ghost:=shadow d x good raw stage norm
  exact replay _ _ m a ref (real d raw) (stock d raw) _ (PartialSites.pool_partial d) (PartialSites.pool_old d 90 286 (by decide) (by decide))
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

def backwards (d:Bool) (n:Nat):Program:=Rolling1588.reverse d 376 n++Partial.reverse45plus1 d

theorem result (d:Bool) (n x:Nat) (good:Bounds x p) (bound:376+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 90 (286+n)) [] (pullState (OB5.sig 89) raw))):
    run (backwards d n) m a=run (Rolling1588.reverse d 90 (286+n)) m ref:=by
  have h:=pair.through (Rolling1588.reverse d 376 n) (fun q hq=>(safe d 376 n (by decide) bound q hq).2) m
  have pools:=pool_run (PartialSites.pool_old d 376 n (by decide) bound) agree m
  simp only [StairRestSupport.forward_append d 286 90 n,run_append,run_take,List.drop_nil] at pools
  rw [tail_cancel d x 90 286 n good (by decide) bound raw stage m] at pools
  simp only [backwards,StairRestSupport.reverse_append d 286 90 n,run_append,run_take]
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
def remaining (d:Bool):Program:=R (Rolling1588.reverse d 16 74)++renameProgram Stair44WalkMap.first (Rolling1588.reverse d 1 15)
theorem split (d:Bool) (n:Nat):WindowWalkCosts.backward d n=R (StockBackWindow.backwards d n)++remaining d:=by
  simp only [WindowWalkCosts.backward,StockBackWindow.backwards,R,remaining,renameProgram,List.map_append,List.append_assoc]
theorem old_split (d:Bool) (n:Nat):Stair44WalkRun.backward d (360+n)=R (Rolling1588.reverse d 90 (286+n))++remaining d:=by
  have e:=StairRestSupport.reverse_append d 74 16 (286+n)
  change Rolling1588.reverse d 16 (74+(286+n))=Rolling1588.reverse d 90 (286+n)++Rolling1588.reverse d 16 74 at e
  rw [show 360+n=74+(286+n) by omega]
  simp only [remaining,Stair44WalkRun.backward,e,R,renameProgram,List.map_append,List.append_assoc]

theorem backward (d:Bool) (n x:Nat) (good:Bounds x p) (bound:376+n≤512) (raw a ref:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 90 raw.basis) (norm:NewNormalized d x)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 90 (286+n)) [] (pullState (OB5.sig 89) raw))):
    ∃old,run (WindowWalkCosts.backward d n) m a=run (Stair44WalkRun.backward d (360+n)) old ref:=by
  let A:=R (StockBackWindow.backwards d n)
  let B:=R (Rolling1588.reverse d 90 (286+n))
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
theorem opened (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (bound:376+n≤512) (s a:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (input:pullState Stair44WalkMap.first a=s):
    Paired d x (run (WindowWalkCosts.forward d n) m a) (run (Stair44WalkRun.forward d (360+n)) m a) (StockRowVector.rows x p):=
  StockPlacedWindow.forward d n x (bounds x nz lt) bound s a m stage input (StockNativeCompare.normalized d x (bounds x nz lt))

theorem rest_pool (q:Wire) (h:q∈pool):Stair44WalkMap.rest q∈pool:=by
  simp only [Stair44WalkMap.rest,Stair44WalkMap.shared,Equiv.trans_apply,Equiv.swap_apply_def]
  split_ifs <;> first | exact h | exact List.mem_toFinset.mpr (OB5.base_pool _ (by decide))
theorem fixed_old (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:376+n∈[425,505,506]) (s:State)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (m:List Bool):
    let v:=run (Rolling1588TickGap.forward d 1 (375+n)) m s
    pullState Stair44WalkMap.rest v=v:=by
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have num:15+(360+n)=375+n:=by omega
  have cut:1+(15+(360+n))∈[425,505,506]:=by simpa only [show 1+(15+(360+n))=376+n by omega] using atCut
  have one:=Stair44WalkRun.forward_run d (360+n) x good.nonzero good.small s a m stage input
  have two:=Stair44WalkCuts.forward_done d (360+n) x cut good.nonzero good.small s a m stage input
  rw [two,num] at one
  exact one

theorem decompose (d:Bool) (x n:Nat) (good:Bounds x p) (s:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:376+n≤512):
    let raw:=regular d s []
    run (Rolling1588TickGap.forward d 1 (375+n)) m s=
      run (Rolling1588TickGap.forward d 90 (286+n)) [] (pullState (OB5.sig 89) raw):=by
  have init:pullState (OB5.sig 0) s=s:=by
    apply State.extensionality _ s
    · rfl
    · funext q;exact congrArg s.basis (OB5.sig_zero q)
  have same:=StockWalkWindow.steady d x good 1 (375+n) (by decide) (by omega) s m [] stage
  rw [show 1-1=0 from rfl,init] at same
  have cut:=Rolling1588TickGap.forward_gen d x good.nonzero good.small 89 1 (by decide) (by decide) s [] stage
  rw [show 1-1=0 from rfl,init] at cut
  have shape:375+n=89+(286+n):=by omega
  rw [same,shape,StairRestSupport.forward_append d 89 1 (286+n),run_append,run_take,List.drop_nil,cut]
  rfl

theorem move {f:Wire→Wire} (a b c:State) (mem:∀q∈pool,f q∈pool) (eq:poolEq a b)
    (fixed:pullState f b=b) (next:b=c):poolEq (pullState f a) c:=by
  intro q hq
  exact (eq _ (mem q hq)).trans ((congrArg (fun s:State=>s.basis q) fixed).trans (congrArg (fun s:State=>s.basis q) next))
theorem endpoint_stage (d:Bool) (x:Nat) (good:Bounds x p) (s:State) (stage:Rolling1588.Integer.Stage base d x p 1 s.basis):
    Rolling1588.Integer.Stage base d x p 90 (regular d s []).basis:=StockBackWindow.stageAt d x good 1 89 (by decide) s [] stage
theorem endpoint_pool (d:Bool) (n x:Nat) (good:Bounds x p) (atCut:376+n∈[425,505,506]) (s ref:State) (enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 s.basis) (bound:376+n≤512)
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (375+n)) enc s)):
    poolEq (pullState Stair44WalkMap.rest ref) (run (Rolling1588TickGap.forward d 90 (286+n)) [] (pullState (OB5.sig 89) (regular d s []))):=
  move _ _ _ rest_pool agree (fixed_old d n x good atCut s stage enc) (decompose d x n good s enc stage bound)
theorem closed (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:376+n∈[425,505,506]) (one a ref:State) (m enc:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p 1 one.basis)
    (pair:Paired d x a ref (StockRowVector.rows x p))
    (agree:poolEq ref (run (Rolling1588TickGap.forward d 1 (375+n)) enc one)):
    ∃old,run (WindowWalkCosts.backward d n) m a=run (Stair44WalkRun.backward d (360+n)) old ref:=by
  have good:=bounds x nz lt
  have bound:376+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
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
    (WindowWalkCosts.backward false 130++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [WindowKernelPrograms.division,divAfter,divHead,Six505.rename_append,List.append_assoc]
theorem old_div_head_split:Stair44Kernel.division=oldDivHead++renameProgram phaseHost
    (Stair44WalkRun.backward false 490++renameProgram Stair44WalkMap.first (FrontierEntry1591NativeH.inverse base)):=by
  simp only [Stair44Kernel.division,oldDivHead,Stair44DivTerm.routedClose,Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,Six505.rename_append,List.append_assoc]
theorem mul_head_split (k:Nat):WindowKernelPrograms.multiplication k=mulHead++renameProgram phaseHost
    (WindowWalkCosts.backward true 49++renameProgram Stair44Kernel.rawX (ParityXExitInverse23Kernel.x1N k)):=rfl
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
def original (d:Bool) (n:Nat):Program:=renameProgram phaseHost (openR d (360+n))

private theorem fixed (x y:Nat) (s:State) (h:SkywalkArithmeticInput base x y s.basis):
    pullState Stair44WalkMap.first s=s:=by
  let idx:List Nat:=[1026,514,1541,501,1542,500]
  have all:∀j∈idx,base j∈skywalkSharedWires base ∧ base j∉skywalkArithmeticDivisor base ∧ base j∉skywalkArithmeticNumerator base:=by decide +kernel
  have zero (j:Nat) (hj:j∈idx):s.basis (base j)=false:=h.2.2 _ (all j hj).1 (all j hj).2.1 (all j hj).2.2
  have a:=cleanWireRebind id s s _ _ rfl (zero 1026 (by decide)) (zero 514 (by decide))
  have b:=cleanWireRebind _ s s _ _ a (zero 1541 (by decide)) (zero 501 (by decide))
  exact cleanWireRebind _ s s _ _ b (zero 1542 (by decide)) (zero 500 (by decide))

theorem open_raw (d:Bool) (n x y:Nat) (nz:0 < x) (lt:x<p) (bound:376+n≤512)
    (hn:(skywalkSharedWires base).Nodup) (s:State) (input:SkywalkArithmeticInput base x y s.basis) (m:List Bool):
    Paired d x (run (openWalk d n) m s) (run (openR d (360+n)) m s) (StockRowVector.rows x p):=by
  let N:=FrontierEntry1591Native.forward base
  let t:=m.take (measurementCount firstR)
  have stage:=Rolling1588.Integer.stage_one base d x p _ (FrontierEntry1591Native.caller_first_stageW base hn x y nz lt s t input)
  have eq:=run_rename Stair44WalkMap.first Stair44WalkMap.first.injective N t s
  rw [fixed x y s input] at eq
  simp only [openWalk,openR,run_append]
  exact StockWalkEndpoints.opened d n x nz lt bound _ _ _ stage eq
theorem division {s:State} (F:EntryFrame s) (m:List Bool):
    Paired true F.x (pullState phaseHost (run (opening true 49) m s))
      (pullState phaseHost (run (original true 49) m s)) (StockRowVector.rows F.x p):=by
  rw [opening,original,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_entry F]
  exact open_raw true 49 F.x _ F.x_pos F.x_lt (by decide) F.sharedNodup s (StairField13V3Clean.entryInput F) m
theorem multiplication (k:Nat) {s:State} (F:ExitFrame k s) (m:List Bool):
    Paired false F.x (pullState phaseHost (run (opening false 129) m s))
      (pullState phaseHost (run (original false 129) m s)) (StockRowVector.rows F.x p):=by
  rw [opening,original,run_rename _ phaseHost.injective,run_rename _ phaseHost.injective,StairField13V3Clean.pull_phaseHost_exit F]
  exact open_raw false 129 F.x _ F.x_pos F.x_lt (by decide) F.sharedNodup s F.input m
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

theorem ofEndpoint (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (atCut:376+n∈[425,505,506]) (ref:State)
    (h:Endpoint d x (375+n) ref):Native d x ref:=by
  obtain ⟨s,enc,stage,eq⟩:=h
  let a:=pullState Stair44WalkMap.first.symm s
  have input:pullState Stair44WalkMap.first a=s:=Stair44PlacedHead.unpull Stair44WalkMap.first.symm s
  have bound:376+n≤512:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at atCut;omega
  have pair:=StockWalkEndpoints.opened d n x nz lt bound s a enc stage input
  have cut:1+(15+(360+n))∈[425,505,506]:=by simpa only [show 1+(15+(360+n))=376+n by omega] using atCut
  have same:=Stair44WalkCuts.forward_done d (360+n) x cut nz lt s a enc stage input
  rw [show 15+(360+n)=375+n by omega] at same
  refine ⟨pair.labels,?_⟩
  intro b j
  have loc:siteAt b j∈pool:=archives_pool _ (StockArchiveBanks.mem b j)
  exact (eq _ loc).trans ((congrArg (fun s:State=>s.basis (siteAt b j)) same.symm).trans (pair.stock b j))

theorem div_native {s:State} (F:StairConcreteAssembly.EntryFrame s) (m:List Bool):
    Native false F.x (pullState phaseHost (run oldDivHead m s)):=
  ofEndpoint false 130 F.x F.x_pos F.x_lt (by decide) _ (div_endpoint F m)
theorem mul_native (k:Nat) {s:State} (F:StairConcreteAssembly.ExitFrame k s) (m:List Bool):
    Native true F.x (pullState phaseHost (run oldMulHead m s)):=
  ofEndpoint true 49 F.x F.x_pos F.x_lt (by decide) _ (mul_endpoint k F m)

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

theorem divisionShape:divHead=opening true 49++divSpan ∧ oldDivHead=original true 49++oldDivSpan:=by
  simp only [divHead,WindowKernelPrograms.divBefore,divSpan,opening,oldDivHead,Stair44Kernel.divLead,Stair44Kernel.fieldD,original,oldDivSpan,Six505.rename_append,List.append_assoc]
  constructor <;> trivial
theorem multiplicationShape:mulHead=opening false 129++mulSpan ∧ oldMulHead=original false 129++oldMulSpan:=by
  simp only [mulHead,WindowKernelPrograms.mulBefore,mulSpan,opening,oldMulHead,Stair44Kernel.beforeX,Stair44Kernel.mulLead,original,oldMulSpan,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]
  constructor <;> trivial

def Related (d:Bool) (x:Nat) (a ref:State):Prop:=Paired d x (pullState phaseHost a) (pullState phaseHost ref) (StockRowVector.rows x p)

theorem division (H:∀{s:State} (F:EntryFrame s) (m t:List Bool),
    let a:=run (opening true 49) m s
    let b:=run (original true 49) m s
    Related true F.x a b → ∃old, Related false F.x (run divSpan t a) (run oldDivSpan old b)):
    WindowMiddleContract.entry:=by
  intro s F m
  let A:=opening true 49
  let B:=original true 49
  obtain ⟨old,rel⟩:=H F m (m.drop (measurementCount A)) (WindowStartStates.division F m)
  refine ⟨pfx (measurementCount B) m++old,?_⟩
  rw [divisionShape.1,divisionShape.2,Stair44PointSecond.joinRecords,run_append,run_take]
  exact rel

theorem multiplication (H:∀k {s:State} (F:ExitFrame k s) (m t:List Bool),
    let a:=run (opening false 129) m s
    let b:=run (original false 129) m s
    Related false F.x a b → ∃old, Related true F.x (run mulSpan t a) (run oldMulSpan old b)):
    WindowMiddleContract.exit:=by
  intro k s F m
  let A:=opening false 129
  let B:=original false 129
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

theorem forward (d:Bool) (n:Nat) (bound:375+n≤504):wires (WindowWalkCosts.forward d n)⊆callerDomain:=by
  have stock:=forward_own d (375+n) bound
  have shape:375+n=15+(74+(286+n)):=by omega
  rw [shape,tickGap_forward_split d 15 1 (74+(286+n)),tickGap_forward_split d 74 16 (286+n),tickGap_forward_split d 286 90 n] at stock
  simp only [wires_append,Finset.union_subset_iff] at stock
  apply wires_sub_of_parts _ _
  · exact rename_caller _ firstOK _ stock.1
  · apply rename_caller _ restOK
    exact wires_sub_of_parts _ _ (wires_sub_of_parts _ _ stock.2.1 (part d).1) stock.2.2.2

theorem backward (d:Bool) (n:Nat) (bound:375+n≤505):wires (WindowWalkCosts.backward d n)⊆callerDomain:=by
  have stock:=reverse_own d (375+n) bound
  have shape:375+n=15+(74+(286+n)):=by omega
  rw [shape,reverse_split d 15 1 (74+(286+n)),reverse_split d 74 16 (286+n),reverse_split d 286 90 n] at stock
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

theorem tail (d:Bool) (n x:Nat) (nz:0 < x) (lt:x<p) (cut:376+n∈[425,505,506])
    (a ref:State) (P:Program) (m:List Bool)
    (pair:Paired d x (pullState phaseHost a) (pullState phaseHost ref) (StockRowVector.rows x p))
    (known:Endpoint d x (375+n) (pullState phaseHost ref)):
    ∃old,run (renameProgram phaseHost (WindowWalkCosts.backward d n++P)) m a=
      run (renameProgram phaseHost (Stair44WalkRun.backward d (360+n)++P)) old ref:=by
  obtain ⟨s,enc,stage,ag⟩:=known
  obtain ⟨old,eq⟩:=StockWalkEndpoints.closed d n x nz lt cut s _ _ m enc stage pair ag
  let A:=WindowWalkCosts.backward d n
  let B:=Stair44WalkRun.backward d (360+n)
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
  exact compose (old:=head) (tail false 130 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (div_endpoint F head))

theorem mul_run (geometry:WindowMiddleContract.exit) (k:Nat) {t:State} (F:ExitFrame k t) (m:List Bool):
    ∃old,run (WindowKernelPrograms.multiplication k) m t=run (Stair44Kernel.multiplication k) old t:=by
  obtain ⟨head,v⟩:=geometry k F m
  rw [mul_head_split,old_mul_head_split]
  exact compose (old:=head) (tail true 49 F.x F.x_pos F.x_lt (by decide) _ _ _ _ v (mul_endpoint k F head))

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
def Active (j : Nat) := j=19 ∨ j=22 ∨ j=25 ∨ j=28 ∨ j=31 ∨ j=34 ∨ j=37 ∨ j=40 ∨ j=43 ∨ j=46 ∨ j=49 ∨ j=52 ∨ j=55 ∨ j=58 ∨ j=61 ∨ j=64 ∨ j=67 ∨ j=70 ∨ j=73
private theorem mesh : wires region⊆Finset.range 31 :=
  ECDSAAdd.Entrant.WSlimMain.wires_subset_range_of_all (by decide +kernel)
private theorem portDistinct : ∀ j∈([19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]:List Nat), ((List.range 31).map (port j)).Nodup := by decide +kernel
private theorem inj {j : Nat} (hj : Active j) :
    ∀a∈Finset.range 31,∀b∈Finset.range 31, port j a=port j b → a=b := by
  intro a ha b hb eq
  have mem : j∈([19,22,25,28,31,34,37,40,43,46,49,52,55,58,61,64,67,70,73]:List Nat) := by rcases hj with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h]
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
      ((((((((((((((((((delta (dirs 19) (rows 19) ^^ delta (dirs 22) (rows 22)) ^^ delta (dirs 25) (rows 25)) ^^ delta (dirs 28) (rows 28)) ^^ delta (dirs 31) (rows 31)) ^^ delta (dirs 34) (rows 34)) ^^ delta (dirs 37) (rows 37)) ^^ delta (dirs 40) (rows 40)) ^^ delta (dirs 43) (rows 43)) ^^ delta (dirs 46) (rows 46)) ^^ delta (dirs 49) (rows 49)) ^^ delta (dirs 52) (rows 52)) ^^ delta (dirs 55) (rows 55)) ^^ delta (dirs 58) (rows 58)) ^^ delta (dirs 61) (rows 61)) ^^ delta (dirs 64) (rows 64)) ^^ delta (dirs 67) (rows 67)) ^^ delta (dirs 70) (rows 70)) ^^ delta (dirs 73) (rows 73)) s := by
  have a0 : Active 19 := Or.inl rfl
  have a1 : Active 22 := Or.inr (Or.inl rfl)
  have a2 : Active 25 := Or.inr (Or.inr (Or.inl rfl))
  have a3 : Active 28 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have a4 : Active 31 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have a5 : Active 34 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have a6 : Active 37 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have a7 : Active 40 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have a8 : Active 43 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have a9 : Active 46 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have a10 : Active 49 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have a11 : Active 52 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have a12 : Active 55 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have a13 : Active 58 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))
  have a14 : Active 61 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))
  have a15 : Active 64 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))
  have a16 : Active 67 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))))))
  have a17 : Active 70 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))))))))
  have a18 : Active 73 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))))))))
  simp only [correction,run_append,run_take]
  rw [bank_run 19 a0 _ _ (hr _ a0) _ s (hd _ a0),
    bank_run 22 a1 _ _ (hr _ a1) _ _ (data_flip _ _ a1 (hd _ a1)),
    bank_run 25 a2 _ _ (hr _ a2) _ _ (data_flip _ _ a2 (data_flip _ _ a2 (hd _ a2))),
    bank_run 28 a3 _ _ (hr _ a3) _ _ (data_flip _ _ a3 (data_flip _ _ a3 (data_flip _ _ a3 (hd _ a3)))),
    bank_run 31 a4 _ _ (hr _ a4) _ _ (data_flip _ _ a4 (data_flip _ _ a4 (data_flip _ _ a4 (data_flip _ _ a4 (hd _ a4))))),
    bank_run 34 a5 _ _ (hr _ a5) _ _ (data_flip _ _ a5 (data_flip _ _ a5 (data_flip _ _ a5 (data_flip _ _ a5 (data_flip _ _ a5 (hd _ a5)))))),
    bank_run 37 a6 _ _ (hr _ a6) _ _ (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (data_flip _ _ a6 (hd _ a6))))))),
    bank_run 40 a7 _ _ (hr _ a7) _ _ (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (data_flip _ _ a7 (hd _ a7)))))))),
    bank_run 43 a8 _ _ (hr _ a8) _ _ (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (data_flip _ _ a8 (hd _ a8))))))))),
    bank_run 46 a9 _ _ (hr _ a9) _ _ (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (data_flip _ _ a9 (hd _ a9)))))))))),
    bank_run 49 a10 _ _ (hr _ a10) _ _ (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (data_flip _ _ a10 (hd _ a10))))))))))),
    bank_run 52 a11 _ _ (hr _ a11) _ _ (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (data_flip _ _ a11 (hd _ a11)))))))))))),
    bank_run 55 a12 _ _ (hr _ a12) _ _ (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (data_flip _ _ a12 (hd _ a12))))))))))))),
    bank_run 58 a13 _ _ (hr _ a13) _ _ (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (data_flip _ _ a13 (hd _ a13)))))))))))))),
    bank_run 61 a14 _ _ (hr _ a14) _ _ (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (data_flip _ _ a14 (hd _ a14))))))))))))))),
    bank_run 64 a15 _ _ (hr _ a15) _ _ (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (data_flip _ _ a15 (hd _ a15)))))))))))))))),
    bank_run 67 a16 _ _ (hr _ a16) _ _ (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (data_flip _ _ a16 (hd _ a16))))))))))))))))),
    bank_run 70 a17 _ _ (hr _ a17) _ _ (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (data_flip _ _ a17 (hd _ a17)))))))))))))))))),
    bank_run 73 a18 _ _ (hr _ a18) _ _ (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (data_flip _ _ a18 (hd _ a18)))))))))))))))))))]
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
  have f:=phaseHost_caller _ (WindowIntegerSites.forward true 49 (by decide))
  have b:=phaseHost_caller _ (WindowIntegerSites.backward false 130 (by decide))
  simp only [WindowKernelPrograms.division,WindowKernelPrograms.divBefore,WindowKernelPrograms.divAfter,
    WindowKernelPrograms.openWalk,Stair44Kernel.division,Stair44Kernel.divLead,Stair44Kernel.openR,
    Stair44DivTerm.routedClose,Stair44Outer.reverseEnd,Stair44DivTerm.head,Stair44DivTerm.P1,
    Six505.rename_append,wires_append,Finset.union_subset_iff] at original ⊢
  tauto
theorem multiplication (k:Nat) (g:wires (WindowParityCaller.exitFieldHosted checkpointPrimitives)⊆callerDomain):
    wires (WindowKernelPrograms.multiplication k)⊆callerDomain:=by
  have original:=Stair44CallerSupport.multiplication k
  have f:=phaseHost_caller _ (WindowIntegerSites.forward false 129 (by decide))
  have b:=phaseHost_caller _ (WindowIntegerSites.backward true 49 (by decide))
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
def free (q:Wire):Bool:=!(61304553945348964237221931932095858255062748130768273466802660760532528117005017558676085559699552555228033042571816605864214537499367467654214474441070118862372401464494352885166765411796817416992384954199706937039243183496673357464252411387134286873611067607066568284657373951681127866665137276076523684782922092683109946452520633667007482718594335536806833112985769939796471983058317025206379002508204676620119607980443481211914011381920858929676745375457777143121244534523486212325487103853743561863842069381225475617345432839202648268734464:Nat).testBit q
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
private def past (q:Wire):Bool:=(5142612124503089273200105140761209859177939527835786710375255706662668502397092779437320734953871967880315712228819557021840772208450033042882180980986568352253000233293739296813274699022398195304935374335018971270328507968605821084142487466291540993054988856410874227395780841497213419215651060279189918582580556365144380260418853330611861369792543883920529403979072458410764466228644638438790187740608783638581602391492132864:Nat).testBit q
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
def beginW := opening false 129 ++ endF
def beginR := original false 129 ++ endF

theorem refBegin : beginR = Stair44Kernel.mulLead := by
  simp only [beginR,original,endF,Stair44Kernel.mulLead,Stair44Kernel.finishM,Stair44Outer.forwardEnd,Six505.rename_append,List.append_assoc]

theorem begin_pair (k : Nat) {s : State} (F : ExitFrame k s) (m : List Bool) :
    ∃n, Paired false F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening false 129
  let B := original false 129
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
def beginW := opening true 49 ++ pack
def beginR := original true 49 ++ pack
def prefixW := (beginW ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group84 true)
def prefixR := (beginR ++ beforeGroup) ++ renameProgram fieldEquiv (WindowFieldCosts.group true 1 84)

theorem refBegin : beginR = Stair44Kernel.divLead := by
  simp only [beginR,original,pack,Stair44Kernel.divLead,Six505.rename_append]

theorem begin_pair {s : State} (F : EntryFrame s) (m : List Bool) :
    ∃n, Paired true F.x (run beginW m s) (run beginR n s) (StockRowVector.rows F.x p) := by
  let A := opening true 49
  let B := original true 49
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
