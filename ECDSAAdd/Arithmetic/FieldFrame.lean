import ECDSAAdd.Arithmetic.FieldMultiply
import ECDSAAdd.Arithmetic.FieldAddSub
import ECDSAAdd.Arithmetic.ModularFrame
import ECDSAAdd.Arithmetic.InverseResources
import ECDSAAdd.Arithmetic.FieldMultiply

namespace ECDSAAdd.Arithmetic

theorem fieldSub_correct (L : ModLayout) (hnd : L.wires.Nodup) (hw : L.width=256)
    (s : State) (m : List Bool) (hx : regValue L.x s.basis<p)
    (hy : regValue L.y s.basis<p) (hz : regValue L.work s.basis=0) :
    (run (fieldSub L) m s).phase=s.phase ∧
    (∀ w∉L.out,(run (fieldSub L) m s).basis w=s.basis w) ∧
    regValue L.out (run (fieldSub L) m s).basis=regValue L.out s.basis ^^^
      ((regValue L.x s.basis+p-regValue L.y s.basis)%p) :=
  modSub_correct L hnd p (by norm_num [p]) (by rw [hw]; norm_num [p]) s m hx hy hz

/-- 将模乘的接口规格提升为逐线保持，以便复用共享工作区。 -/
theorem fieldMul_correct (L : MontLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (s : State) (m : List Bool)
    (hx : regValue L.x s.basis<p) (hz : regValue L.work s.basis=0) :
    (run (fieldMul L) m s).phase=s.phase ∧
    (∀ w∉L.out,(run (fieldMul L) m s).basis w=s.basis w) ∧
    regValue L.out (run (fieldMul L) m s).basis=regValue L.out s.basis ^^^
      ((regValue L.x s.basis*regValue L.y s.basis)%p) := by
  letI : Fact p.Prime := ⟨Secp256k1.p_prime⟩
  obtain ⟨hp,hpost⟩ := fieldMul_spec L hnd hw _ _ _ hx s m ⟨⟨⟨rfl,rfl⟩,rfl⟩,hz⟩
  simp only [fieldMul] at hp hpost ⊢
  refine ⟨hp,?_,hpost.1.2⟩
  intro w ho
  exact montMulXor_frame L p _ _ _ hw hnd (by norm_num [p]) secp256k1_mod_sixteen hx
    (by simpa only [hw.y] using regValue_lt L.y s.basis)
    s m rfl rfl rfl hz w ho

/-- 求逆只改变输出位，全部借用工作位逐线恢复；定义域仍要求正的规范输入。 -/
theorem fieldInverse_correct (L : InverseLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (s : State) (m : List Bool) (hx0 : 0<regValue L.x s.basis)
    (hx : regValue L.x s.basis<p) (hz : regValue L.work s.basis=0) :
    (run (fieldInverse L) m s).phase=s.phase ∧
    (∀ w∉L.out,(run (fieldInverse L) m s).basis w=s.basis w) ∧
    regValue L.out (run (fieldInverse L) m s).basis=regValue L.out s.basis ^^^
      (((regValue L.x s.basis : Fp)⁻¹).val) := by
  obtain ⟨hp,hpost⟩ := fieldInverse_xor_spec L hnd hw _ _ hx0 hx s m ⟨⟨rfl,rfl⟩,hz⟩
  refine ⟨hp,?_,hpost.1.2⟩
  intro w ho
  by_cases hm : w∈L.wires
  · simp only [InverseLayout.wires,List.mem_append] at hm
    rcases hm with (hi|hi)|hi
    · exact (regValue_eq_iff _ _ _).mp hpost.1.1 w hi
    · exact False.elim (ho hi)
    · exact (regValue_eq_iff _ _ _).mp (hpost.2.trans hz.symm) w hi
  · apply run_preserves_outside
    rw [fieldInverse_wires L hw]
    exact fun h => hm (L.usedWires_subset (List.mem_toFinset.mp h))

end ECDSAAdd.Arithmetic
