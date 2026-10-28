import ECDSAAdd.Arithmetic.Paper935.AuthorWalkCompiler
import ECDSAAdd.Arithmetic.Paper935.BankFrame

namespace ECDSAAdd.Arithmetic.Paper935

/-- Only the retained one control needs an X; the allocator supplies all other
metadata sites clean, including the zero signed counter of zSeed. -/
def seedWalkMetadata : Program := [.X 774]

theorem seedWalkMetadata_run (s : State) (m : List Bool) (ready : seedArena.Ready s.basis)
    (p x : Int) :
    let t := run seedWalkMetadata m s
    t.phase=s.phase ∧ walkSeedArena.Ready t.basis ∧
    walkRegisters.Values t.basis ⟨ECDSAAdd.Divsteps.zSeed p x,false,0⟩ ∧
    (∀ q,q<774 → t.basis q=s.basis q) := by
  have clean (q : Wire) (hq : 774≤q ∧ q<794) : s.basis q=false :=
    ready q (by simp only [arenaWires,Finset.mem_range]; simp only [Wire] at *; omega)
      (by simp only [seedArena,Finset.mem_range]; simp only [Wire] at *; omega)
  have one : s.basis 774=false := clean 774 (by simp only [Wire] at *; omega)
  have run : run seedWalkMetadata m s=⟨s.phase,writeBit s.basis 774 true⟩ := by
    simp [seedWalkMetadata,ECDSAAdd.run,one]
  have keep (q : Wire) (hq : q≠774) : writeBit s.basis 774 true q=s.basis q :=
    Function.update_of_ne hq _ _
  have zero (q : Wire) (hq : 775≤q ∧ q<794) : writeBit s.basis 774 true q=false :=
    (keep q (by simp only [Wire] at *; omega)).trans (clean q (by simp only [Wire] at *; omega))
  dsimp only
  rw [run]
  dsimp only
  refine ⟨rfl,?_,?_,?_⟩
  · intro q hqa hq
    have neq : q≠774 := by
      simp only [walkSeedArena,Finset.mem_range] at hq
      simp only [Wire] at *; omega
    rw [keep q neq]
    exact ready q hqa (by simp only [seedArena,walkSeedArena,Finset.mem_range] at *; simp only [Wire] at *; omega)
  · constructor
    · simp [walkRegisters,writeBit]
    · exact zero 775 (by simp only [Wire] at *; omega)
    · exact zero 776 (by simp only [Wire] at *; omega)
    · exact zero 777 (by simp only [Wire] at *; omega)
    · exact zero 778 (by simp only [Wire] at *; omega)
    · exact zero 779 (by simp only [Wire] at *; omega)
    · exact zero 780 (by simp only [Wire] at *; omega)
    · change signedRegValue (List.range' 781 7) (writeBit s.basis 774 true)=0
      have hz : regValue (List.range' 781 7) (writeBit s.basis 774 true)=0 :=
        (regValue_zero _ _).mpr (by intro q hq; apply zero; simp only [List.mem_range'] at hq; simp only [Wire] at *; omega)
      norm_num [signedRegValue,signedDecode,hz]
    · change regValue (List.range' 788 6) (writeBit s.basis 774 true)=0
      exact (regValue_zero _ _).mpr (by intro q hq; apply zero; simp only [List.mem_range'] at hq; simp only [Wire] at *; omega)
  · intro q hq
    exact keep q (by simp only [Wire] at *; omega)


def seedWalk (p : Nat) : Program := seedRows p++seedWalkMetadata

theorem walkSeedBank_sites : ∀ q∈walkSeedBank.rows.flatMap WindowRow.wires,q<774 := by decide +kernel

/-- Concrete shared-host seed followed by metadata initialization supplies the
actual bank, metadata encoding and free-arena invariant used by the walk. -/
theorem seedWalk_run (p : Nat) (hp : p<2^256) (s : State) (m : List Bool)
    (ready : seedBefore.Ready s.basis) :
    let t := run (seedWalk p) m s
    let z := ECDSAAdd.Divsteps.zSeed p (regValue seedG s.basis)
    t.phase=s.phase ∧ walkSeedArena.Ready t.basis ∧
    walkRegisters.Values t.basis ⟨z,false,0⟩ ∧ walkSeedBank.Encodes t.basis z := by
  have seed := seed_run p hp s m ready
  have rows := seed_rows p hp s m ready
  have encoded : walkSeedBank.Encodes (run (seedRows p) m s).basis
      (ECDSAAdd.Divsteps.zSeed p (regValue seedG s.basis)) := by
    simpa only [walkSeedBank,WindowBank.Encodes,WindowRow.value,WindowRow.wires,ECDSAAdd.Divsteps.zSeed,List.cons_append,List.nil_append] using rows
  have metadata := seedWalkMetadata_run (run (seedRows p) m s) m seed.2.2.2.2
    p (regValue seedG s.basis)
  have finalRows := encoded.frame walkSeedBank _ _ _
    (fun q hq => metadata.2.2.2 q (walkSeedBank_sites q hq))
  dsimp only
  rw [seedWalk,run_append,run_take,(seed_counts p).2,List.drop_zero]
  exact ⟨metadata.1.trans seed.1,metadata.2.1,metadata.2.2.1,finalRows⟩

end ECDSAAdd.Arithmetic.Paper935
