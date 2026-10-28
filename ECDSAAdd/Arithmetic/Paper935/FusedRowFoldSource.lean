import ECDSAAdd.Arithmetic.Paper935.FusedRowFold
import ECDSAAdd.Framework.WireRename

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.Arithmetic
attribute [local irreducible] fusedFoldBuild

private theorem copy_twice (src dst : List Wire) (len : src.length=dst.length)
    (nd : (src++dst).Nodup) (s : State) (m n : List Bool) :
    run (copyRegister none src dst) n (run (copyRegister none src dst) m s)=s := by
  let t := run (copyRegister none src dst) m s
  have f := copyRegister_correct none src dst len nd (by simp) s m
  have r := copyRegister_correct none src dst len nd (by simp) t n
  have srcSame : regValue src t.basis=regValue src s.basis := by
    apply regValue_congr
    intro q hq
    exact f.2.1 q (List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 hq)
  have dstSame : regValue dst (run (copyRegister none src dst) n t).basis=regValue dst s.basis := by
    rw [r.2.2]
    change (regValue dst t.basis) ^^^ regValue src t.basis=regValue dst s.basis
    rw [srcSame,f.2.2]
    simp [copyValue]
  apply State.extensionality
  · exact r.1.trans f.1
  · funext q
    by_cases hq : q∈dst
    · exact (regValue_eq_iff dst _ _).mp dstSame q hq
    · exact (r.2.1 q hq).trans (f.2.1 q hq)

private theorem copy_reverse (src dst : List Wire) (len : src.length=dst.length)
    (nd : (src++dst).Nodup) (s : State) (m n : List Bool) :
    run (copyRegister none src dst).reverse n s=run (copyRegister none src dst) m s := by
  have h := run_reverse_proper _ (copyRegister_none_proper src dst nd)
    (run (copyRegister none src dst) m s) m n
  rw [copy_twice src dst len nd s m m] at h
  exact h

/-- engine.py:2971–2988 emits the tap-zero CX loop in increasing order in
both sweeps. The normalized reverse stream differs only in that loop's order. -/
def fusedFoldSourceUnbuild : Program :=
  (fusedFoldTaps.flatMap fusedFoldTap).reverse ++
    copyRegister none fusedFoldHigh (fusedFoldWord.take 24)

theorem fusedFoldSourceUnbuild_run (s : State) (m : List Bool) :
    run fusedFoldSourceUnbuild m s=run fusedFoldBuild.reverse m s := by
  simp only [fusedFoldSourceUnbuild,fusedFoldBuild,List.reverse_append,run_append,run_take]
  symm
  apply copy_reverse
  · simp [fusedFoldHigh,fusedFoldWord]
  · decide

/-- The source-order row reducer, retaining the author's increasing tap-zero
copy order in the final unbuild. -/
def fusedRowFoldSource (inverse : Bool) : Program :=
  fusedFoldBuild ++
    (if inverse then (cuccaroAdd fusedFoldWord fusedFoldLow 536).reverse
      else cuccaroAdd fusedFoldWord fusedFoldLow 536) ++ fusedFoldSourceUnbuild

theorem fusedRowFoldSource_run (inverse : Bool) (s : State) (m : List Bool) :
    run (fusedRowFoldSource inverse) m s=run (fusedRowFold inverse) m s := by
  simp only [fusedRowFoldSource,fusedRowFold,run_append,run_take]
  rw [fusedFoldSourceUnbuild_run]

theorem fusedRowFoldSource_roundtrip (s : State) (m n : List Bool) :
    run (fusedRowFoldSource true) n (run (fusedRowFoldSource false) m s)=s := by
  rw [fusedRowFoldSource_run,fusedRowFoldSource_run]
  exact fusedRowFold_roundtrip s m n

theorem fusedRowFoldSource_proper (inverse : Bool) : ProperProgram (fusedRowFoldSource inverse) := by
  have hb := fusedFoldBuild_proper
  rw [fusedFoldBuild,properProgram_append] at hb
  have hu : ProperProgram fusedFoldSourceUnbuild :=
    (properProgram_append _ _).mpr ⟨properProgram_reverse _ hb.2,hb.1⟩
  have h := fusedRowFold_proper inverse
  rw [fusedRowFold,properProgram_append,properProgram_append] at h
  rw [fusedRowFoldSource,properProgram_append,properProgram_append]
  exact ⟨h.1,hu⟩

private theorem source_unbuild_resources :
    wires fusedFoldSourceUnbuild=wires fusedFoldBuild.reverse ∧
    toffoliCount fusedFoldSourceUnbuild=toffoliCount fusedFoldBuild.reverse ∧
    measurementCount fusedFoldSourceUnbuild=measurementCount fusedFoldBuild.reverse := by
  simp [fusedFoldSourceUnbuild,fusedFoldBuild,wires_reverse,toffoliCount_reverse,
    measurementCount_reverse]

theorem fusedRowFoldSource_resources (inverse : Bool) :
    wires (fusedRowFoldSource inverse) ⊆ Finset.range 537 ∧
    toffoliCount (fusedRowFoldSource inverse)=1086 ∧
    measurementCount (fusedRowFoldSource inverse)=0 := by
  have hw : wires (fusedRowFoldSource inverse)=wires (fusedRowFold inverse) := by
    simp only [fusedRowFoldSource,fusedRowFold,wires_append,source_unbuild_resources.1]
  have ht : toffoliCount (fusedRowFoldSource inverse)=toffoliCount (fusedRowFold inverse) := by
    simp only [fusedRowFoldSource,fusedRowFold,toffoliCount_append,source_unbuild_resources.2.1]
  have hm : measurementCount (fusedRowFoldSource inverse)=measurementCount (fusedRowFold inverse) := by
    simp only [fusedRowFoldSource,fusedRowFold,measurementCount_append,source_unbuild_resources.2.2]
  rw [hw,ht,hm]
  exact ⟨fusedRowFold_support inverse,fusedRowFold_counts inverse⟩

end ECDSAAdd.Arithmetic.Paper935
