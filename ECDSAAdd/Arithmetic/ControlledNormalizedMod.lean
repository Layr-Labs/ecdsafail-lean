import ECDSAAdd.Arithmetic.CuccaroGateSupport
import ECDSAAdd.Framework.ExactControl

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace ECDSAAdd.Arithmetic

def controlledNormalizedModAdd (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (c p : Nat) : Program :=
  cuccaroNormalize L.normalize c++
    controlUnitary control scratch (cuccaroModAdd L.modular p)++
    cuccaroNormalizeClear L.normalize c

def controlledNormalizedModSub (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (c p : Nat) : Program :=
  cuccaroNormalize L.normalize c++
    controlUnitary control scratch (cuccaroModSub L.modular p)++
    cuccaroNormalizeClear L.normalize c

private theorem normalized_views_nodup (L : CuccaroNormalizedModLayout)
    (hn : L.wires.Nodup) : L.normalize.wires.Nodup ∧ L.modular.wires.Nodup := by
  constructor <;> apply List.nodup_iff_count.mpr <;> intro q
  all_goals
    have h := List.nodup_iff_count.mp hn q
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizedModLayout.modular,CuccaroModLayout.wires,CuccaroModLayout.z,
      CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.count_cons,
      List.count_append,List.count_nil] at h ⊢
    omega

private theorem normalized_views_away (L : CuccaroNormalizedModLayout)
    (q : Wire) (hq : q∉L.wires) : q∉L.normalize.wires ∧ q∉L.modular.wires := by
  constructor <;> intro h <;> apply hq
  all_goals
    simp only [CuccaroNormalizedModLayout.wires,CuccaroNormalizedModLayout.normalize,
      CuccaroNormalizeLayout.wires,CuccaroNormalizeLayout.a,CuccaroNormalizeLayout.scratch,
      CuccaroNormalizedModLayout.modular,CuccaroModLayout.wires,CuccaroModLayout.z,
      CuccaroModLayout.allWork,CuccaroModLayout.scratch,List.mem_cons,
      List.mem_append,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem controlledNormalizedMod_exact (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (n c p : Nat) (hw : L.Widths n)
    (hn : L.wires.Nodup) (hc : control∉L.wires) (ht : scratch∉L.wires)
    (hct : control≠scratch) :
    ExactControl control scratch (cuccaroNormalizedModAdd L c p)
      (controlledNormalizedModAdd control scratch L c p) ∧
    ExactControl control scratch (cuccaroNormalizedModSub L c p)
      (controlledNormalizedModSub control scratch L c p) := by
  have nd := normalized_views_nodup L hn
  have ca := normalized_views_away L control hc
  have ta := normalized_views_away L scratch ht
  have normProper := cuccaroNormalize_proper L.normalize c nd.1
  have normSupport := cuccaroNormalize_wires_subset L.normalize c
  have normC : control∉wires (cuccaroNormalize L.normalize c) := by
    intro h
    exact ca.1 (List.mem_toFinset.mp (normSupport h))
  have normT : scratch∉wires (cuccaroNormalize L.normalize c) := by
    intro h
    exact ta.1 (List.mem_toFinset.mp (normSupport h))
  have modProper := cuccaroMod_unitary L.modular p nd.2
  have modSupport := cuccaroMod_wires_subset L.modular n p (L.modular_widths n hw)
  have addC : control∉wires (cuccaroModAdd L.modular p) := by
    intro h
    exact ca.2 (List.mem_toFinset.mp (modSupport.1 h))
  have addT : scratch∉wires (cuccaroModAdd L.modular p) := by
    intro h
    exact ta.2 (List.mem_toFinset.mp (modSupport.1 h))
  have subC : control∉wires (cuccaroModSub L.modular p) := by
    intro h
    exact ca.2 (List.mem_toFinset.mp (modSupport.2 h))
  have subT : scratch∉wires (cuccaroModSub L.modular p) := by
    intro h
    exact ta.2 (List.mem_toFinset.mp (modSupport.2 h))
  have add := ExactControl.direct control scratch (cuccaroModAdd L.modular p)
    modProper.1 addC addT hct
  have sub := ExactControl.direct control scratch (cuccaroModSub L.modular p)
    modProper.2 subC subT hct
  exact ⟨ExactControl.sandwich normProper normC normT add,
    ExactControl.sandwich normProper normC normT sub⟩

theorem controlledNormalizedMod_counts (control scratch : Wire)
    (L : CuccaroNormalizedModLayout) (n c p : Nat) (hw : L.Widths n) :
    (toffoliCount (controlledNormalizedModAdd control scratch L c p)=
      2*(4*n-2)+3*(10*n-2)+cnotCount (cuccaroModAdd L.modular p) ∧
      measurementCount (controlledNormalizedModAdd control scratch L c p)=0) ∧
    (toffoliCount (controlledNormalizedModSub control scratch L c p)=
      2*(4*n-2)+3*(12*n-2)+cnotCount (cuccaroModSub L.modular p) ∧
      measurementCount (controlledNormalizedModSub control scratch L c p)=0) := by
  have norm := cuccaroNormalize_counts L.normalize n c (L.normalize_widths n hw)
  have add := cuccaroModAdd_counts L.modular n p (L.modular_widths n hw)
  have sub := cuccaroModSub_counts L.modular n p (L.modular_widths n hw)
  simp only [controlledNormalizedModAdd,controlledNormalizedModSub,
    toffoliCount_append,measurementCount_append,controlUnitary_toffoliCount,
    controlUnitary_measurementCount,norm.1.1,norm.1.2,norm.2.1,norm.2.2,
    add.1,sub.1]
  constructor
  · constructor
    · omega
    · trivial
  · constructor
    · omega
    · trivial

end ECDSAAdd.Arithmetic
