import ECDSAAdd.Submission.Entrant.FrontierEntry1591Inverse
import ECDSAAdd.Submission.Entrant.ParityHistoryResources

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.NewStackOB5
open Arithmetic Challenge Baselines MappedCompressed Secp256k1 OB5
attribute [local irreducible] reverse regularReverse StackOB5.reverse Stack5.reverse5

theorem unpackFirst_metrics (w : Nat → Wire) (i : Nat) :
    toffoliCount (unpackFirst w i)=toffoliCount (FirstNonzeroCodec.unpack9first w i) ∧
    measurementCount (unpackFirst w i)=measurementCount (FirstNonzeroCodec.unpack9first w i) ∧
    gateSlots (unpackFirst w i)=gateSlots (FirstNonzeroCodec.unpack9first w i)+
      2*(if History5.packDue i then 1 else 0) := by
  by_cases hi : i=5
  · subst i
    simpa only [unpackFirst,FirstNonzeroCodec.unpack9first,if_pos rfl,
      show History5.packDue 5=true from rfl,if_true,mul_one] using
      ParityCodec5New.first_decode_metrics (History5.historyMap w 0)
  · simpa only [unpackFirst,FirstNonzeroCodec.unpack9first,if_neg hi,
      FirstNonzeroCodec.unpack11] using NewHistory5.decodeBefore_metrics w i

theorem regularReverse_metrics (w : Nat → Wire) (i n : Nat) :
    toffoliCount (regularReverse w i n)=toffoliCount (Stack5.reverse5 w i n) ∧
    measurementCount (regularReverse w i n)=measurementCount (Stack5.reverse5 w i n) ∧
    gateSlots (regularReverse w i n)=gateSlots (Stack5.reverse5 w i n)+2*History5.packCount i n := by
  induction n generalizing i with
  | zero => simp [regularReverse,Stack5.reverse5,History5.packCount]
  | succ n ih =>
    have tail := ih (i+1)
    have step := NewHistory5.decodeBefore_metrics w i
    simp only [regularReverse,Stack5.reverse5,History5.packCount,toffoliCount_append,
      measurementCount_append,gateSlots_append]
    constructor
    · omega
    · constructor <;> omega

theorem reverse_metrics (i n : Nat) :
    toffoliCount (reverse i n)=toffoliCount (StackOB5.reverse i n) ∧
    measurementCount (reverse i n)=measurementCount (StackOB5.reverse i n) ∧
    gateSlots (reverse i n)=gateSlots (StackOB5.reverse i n)+2*History5.packCount i n := by
  induction n generalizing i with
  | zero => simp [reverse,StackOB5.reverse,History5.packCount]
  | succ n ih =>
    have tail := ih (i+1)
    have step := unpackFirst_metrics base i
    simp only [reverse,StackOB5.reverse,History5.packCount,toffoliCount_append,
      measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots]
    constructor
    · omega
    · constructor <;> omega

theorem stackReverse510_metrics_eq :
    toffoliCount stackReverse510=toffoliCount ECDSAAdd.Entrant.stackReverse510 ∧
    measurementCount stackReverse510=measurementCount ECDSAAdd.Entrant.stackReverse510 ∧
    gateSlots stackReverse510=gateSlots ECDSAAdd.Entrant.stackReverse510+204 := by
  have tail := reverse_metrics 1 509
  have step := NewHistory5.decodeBefore_metrics base 510
  have packets : History5.packCount 1 509=101 := by decide
  have due : History5.packDue 510=true := by decide
  rw [packets] at tail
  simp [due] at step
  simp only [stackReverse510,ECDSAAdd.Entrant.stackReverse510,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots]
  constructor
  · omega
  · constructor <;> omega

theorem stackReverseT_counts :
    toffoliCount stackReverseT=toffoliCount ECDSAAdd.Entrant.stackReverseT ∧
    measurementCount stackReverseT=measurementCount ECDSAAdd.Entrant.stackReverseT := by
  have h := stackReverse510_metrics_eq
  simp only [stackReverseT,ECDSAAdd.Entrant.stackReverseT,toffoliCount_append,
    measurementCount_append]
  exact ⟨by omega,by omega⟩

theorem stackReverseT_slots :
    gateSlots stackReverseT=gateSlots ECDSAAdd.Entrant.stackReverseT+204 := by
  have h := stackReverse510_metrics_eq
  simp only [stackReverseT,ECDSAAdd.Entrant.stackReverseT,gateSlots_append]
  omega

end ECDSAAdd.Entrant.NewStackOB5
