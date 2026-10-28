import ECDSAAdd.Arithmetic.FusedSharedInput
import ECDSAAdd.Arithmetic.CompactGuardPackedInverse

namespace ECDSAAdd.Arithmetic

private theorem inverse_block_one (w : Nat → Wire) (s : Nat) :
    wireBlock w s 1=[w s] := by simp [wireBlock,List.range']

/-- The independent inverse endpoint on the actual shared workspace restores the
borrowed target guard, every original non-target wire, and the incoming phase. -/
theorem fusedSharedInverseKernel_correct (w : Nat → Wire) (g : Wire)
    (hn : (skywalkSharedWires w).Nodup) (hg : g∉fusedSharedIds.map w)
    (X Y : Nat) (hX : X<p) (hY : Y<p) (s : State) (record : List Bool)
    (hy : regValue (skywalkSharedField w).a s.basis=Y)
    (hx : regValue (skywalkSharedField w).z s.basis=X)
    (hk : regValue (skywalkSharedField w).work s.basis=0)
    (hu : regValue (skywalkSharedUnused w) s.basis=0) :
    (run (fusedSharedPorts w g).compactInverseProgram record s).phase=s.phase ∧
    (∀ q,q∉(skywalkSharedField w).z →
      (run (fusedSharedPorts w g).compactInverseProgram record s).basis q=s.basis q) ∧
    regValue (skywalkSharedField w).z
      (run (fusedSharedPorts w g).compactInverseProgram record s).basis=
      FusedSignedHalf.inverseValue (s.basis g) X Y := by
  have hi := fusedSharedPorts_input w g s.basis X Y hy hx hk hu
  have hfit : p+1<2^(fusedSharedPorts w g).A.length := by
    change p+1<2^(wireBlock w 512 256).length
    rw [wireBlock_length]
    norm_num [p]
  obtain ⟨out,hout⟩ : ∃ out : State,
      run (fusedSharedPorts w g).compactInverseProgram record s=out := ⟨_,rfl⟩
  have hc := (fusedSharedPorts w g).compactInverse_correct (fusedSharedPorts_widths w g)
    (fusedSharedPorts_nodup w g hn hg) (fusedSharedPorts_early w g) hfit
    X Y hX hY s record hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2
  rw [hout] at hc
  let Z := FusedSignedHalf.inverseValue (s.basis g) X Y
  have hz : Z<2^256 := by
    have hb := FusedSignedHalf.inverseValue_bound (s.basis g) X Y
    have hp : p<2^256 := by norm_num [p]
    exact hb.trans hp
  have ht : regValue ((fusedSharedPorts w g).targetLow++[w 2312,w 769])
      out.basis=Z := hc.2.2
  have hzlow : Z<2^(fusedSharedPorts w g).targetLow.length := by
    rw [fusedSharedPorts_targetLow,wireBlock_length]
    exact hz
  have guards := fusedCanonicalGuards (fusedSharedPorts w g).targetLow
    (w 2312) (w 769) out.basis Z hzlow ht
  have htarget : (skywalkSharedField w).z=
      (fusedSharedPorts w g).targetLow++[w 2312] := by
    rw [fusedSharedPorts_targetLow,skywalkShared_field_z]
    have hb := wireBlock_append w 2056 256 1
    simpa only [inverse_block_one,Nat.reduceAdd] using hb.symm
  rw [hout]
  refine ⟨hc.1,?_,?_⟩
  · intro q hq
    by_cases h769 : q=w 769
    · subst q
      have hzero : s.basis (w 769)=false :=
        (regValue_zero _ _).mp hu _ (by simp [skywalkSharedUnused])
      exact guards.2.2.trans hzero.symm
    · apply hc.2.1 q
      rw [(fusedSharedPorts_views w g).2.1]
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hq,h769⟩
  · rw [htarget,regValue_append,guards.1]
    simp [regValue,guards.2.1]
    rfl

end ECDSAAdd.Arithmetic
