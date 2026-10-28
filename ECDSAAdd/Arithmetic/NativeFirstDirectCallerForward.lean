import ECDSAAdd.Arithmetic.NativeFirstDirectReferenceEq
import ECDSAAdd.Arithmetic.CompressedCompactFrame
import ECDSAAdd.Framework.RecordPadding

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run forward reference literalSkywalkSeed compactSkywalkTick
  compressedCompactForward compressedPackAfter

private theorem first_tick_count (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup) :
    measurementCount (compactSkywalkTick w 0)=257 := by
  have h := (compactSkywalkTick_counts w 0 (by omega) hn).2
  simpa only [compactSkywalkTickPostWidth,narrowSkywalkWidth] using h

private theorem first_forward_join (w : Nat → Wire) :
    compressedCompactForward w 0 512=
      compactSkywalkTick w 0++compressedCompactForward w 1 511 := by
  have zero : compressedPackAfter w 0=[] := by
    rw [compressedPackAfter,show compressedPackDue 0=false from rfl]
    rfl
  rw [compressedCompactForward,zero,List.append_nil]

/-- A first native tick takes only the fixed false prefix; the following
records remain an arbitrary independent stream, including an empty stream. -/
private theorem old_forward_eval (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (tail : List Bool) :
    run (compressedCompactForward w 0 512) (List.replicate 257 false++tail) s=
      run (compressedCompactForward w 1 511) tail (run (compactSkywalkTick w 0) [] s) := by
  rw [first_forward_join,run_append,first_tick_count w hn]
  have take : (List.replicate 257 false++tail).take 257=List.replicate 257 false := by
    rw [List.take_append_of_le_length (by simp [List.length_replicate])]
    simpa only [List.length_replicate] using List.take_length (l := List.replicate 257 false)
  have drop : (List.replicate 257 false++tail).drop 257=tail := by
    have nil : (List.replicate 257 false).drop 257=[] := by
      simpa only [List.length_replicate] using List.drop_length (l := List.replicate 257 false)
    rw [List.drop_append,List.length_replicate,nil,Nat.sub_self,List.drop_zero,List.nil_append]
  rw [take,drop,run_replicate_false]

/-- Exact terminal State equality for the entire 512-step compressed forward
schedule. Prefix and tail measurements are independently arbitrary. -/
theorem forward_terminal_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (first tail : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    run (compressedCompactForward w 1 511) tail (run (forward w) first s)=
      run (compressedCompactForward w 0 512) (List.replicate 257 false++tail)
        (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) := by
  have hpfx := forward_reference_eq w hn x hx s first [] hin ext
  have ref : run (reference w) [] s=
      run (compactSkywalkTick w 0) []
        (run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s) := by
    rw [reference,run_append]
    simp only [List.take_nil,List.drop_nil]
  have firstEq := hpfx.trans ref
  exact (congrArg (fun u : State => run (compressedCompactForward w 1 511) tail u) firstEq).trans
    (old_forward_eval w hn _ tail).symm

/-- Concrete old hs1/hs2 witnesses needed by compressedPreparation_facts.
No relationship between first and tail outcome values is required. -/
theorem forward_terminal_states (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s s1 s2 : State) (first tail : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false)
    (h1 : run (forward w) first s=s1)
    (h2 : run (compressedCompactForward w 1 511) tail s1=s2) :
    ∃ oldSeed : State,
      run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s=oldSeed ∧
      run (compressedCompactForward w 0 512) (List.replicate 257 false++tail) oldSeed=s2 := by
  refine ⟨run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) [] s,rfl,?_⟩
  have forward := forward_terminal_eq w hn x hx s first tail hin ext
  rw [h1,h2] at forward
  exact forward.symm

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.forward_terminal_eq
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.forward_terminal_states
