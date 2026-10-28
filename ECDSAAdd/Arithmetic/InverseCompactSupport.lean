import ECDSAAdd.Arithmetic.InverseCompute

namespace ECDSAAdd.Arithmetic
namespace InverseScaleLayout

/-- 变量乘法触及stage全区；十位查表触及九根scratch，因而只需另覆盖factor。 -/
theorem work_covered (L : InverseScaleLayout) (hw : L.Widths) (q : Nat) :
    L.work.toFinset ⊆ ECDSAAdd.wires (L.prepare q) ∪ L.factor.toFinset ∧
    L.work.toFinset ⊆ ECDSAAdd.wires (L.restore q) ∪ L.factor.toFinset := by
  have hm := montStage_wires L.stage L.factor (L.a.take 256) q hw.stage
    (by simp [hw.factor]) (by simp [hw.a])
  have hk := lookup10_core_wires (L.k.headD L.stage.flag) L.k.tail L.scratch L.factor
    (inverseScaleFactor q) (by simp [hw.k]) (by simp [scratch,hw.stage.scratch,hw.extraScratch])
  have hextra (w : Wire) (hh : w∈L.extraScratch) : w∈ECDSAAdd.wires (L.lookup q) := by
    exact hk (by simp [scratch,hh])
  have stage (w : Wire) (hh : w∈L.stage.work) : w∈L.stage.wires := by
    simp [MontStageLayout.wires,hh]
  constructor
  · intro w hh
    simp only [work,List.toFinset_append,Finset.mem_union,List.mem_toFinset] at hh
    rcases hh with (hh|hh)|hh
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hh)
    · apply Finset.mem_union_left
      rw [prepare,wires_append,wires_append,wires_append,hm.1]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (List.mem_toFinset.mpr (List.mem_append_right _ (stage w hh)))))
    · apply Finset.mem_union_left
      rw [prepare,wires_append]
      exact Finset.mem_union_right _ (hextra w hh)
  · intro w hh
    simp only [work,List.toFinset_append,Finset.mem_union,List.mem_toFinset] at hh
    rcases hh with (hh|hh)|hh
    · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hh)
    · apply Finset.mem_union_left
      rw [restore,wires_append,wires_append,hm.2]
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (List.mem_toFinset.mpr (List.mem_append_right _ (stage w hh))))
    · apply Finset.mem_union_left
      rw [restore,wires_append]
      exact Finset.mem_union_right _ (hextra w hh)

end InverseScaleLayout
namespace InverseLoopLayout

theorem compactBorrow_prefix (L : InverseLoopLayout) (hl : L.first.low.length=256) :
    L.compactBorrow.take 1054=(L.middle.u++L.middle.v++L.middle.s++(L.middle.data.reg .zero).drop 4)++
      L.arithmetic.wires.take 30 := by
  have hd (f : RoundField) : (L.middle.data.reg f).length=257 := by
    rw [middle,loopEnd_data,L.first.data_reg_length,hl]
  have hlen : (L.middle.u++L.middle.v++L.middle.s++(L.middle.data.reg .zero).drop 4).length=1024 := by
    simp [KaliskiRoundLayout.u,KaliskiRoundLayout.v,KaliskiRoundLayout.s,
      RoundDataLayout.u,RoundDataLayout.v,RoundDataLayout.s,hd]
  rw [compactBorrow,List.take_append,hlen,List.take_of_length_le (by omega)]
  simp only [compactBank,List.take_take]
  rfl

theorem compactNeg_core (L : InverseLoopLayout) (hm : L.arithmetic.width=256) (hl : L.first.low.length=256) :
    L.compactNeg.toModAddCoreLayout.work=L.compactBorrow.take 514 := by
  have hb := L.compactBorrow_length hl hm
  have he : (L.compactBorrow.drop 513).take 1=[L.compactBorrow.getD 513 L.first.done] := by
    apply List.ext_getElem
    · simp [hb]
    · intro i hi hi'
      have : i=0 := by simpa using hi'
      subst i
      simp [hb]
  simp only [compactNeg,ModAddCoreLayout.work]
  rw [←he,←List.take_add,←List.take_add]

end InverseLoopLayout
end ECDSAAdd.Arithmetic
