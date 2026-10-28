import ECDSAAdd.Arithmetic.PointCandidateLayout
import ECDSAAdd.Arithmetic.FieldFrame

namespace ECDSAAdd.Arithmetic

/-- 候选步骤的寄存器名；输入坐标带独立的零最高位。 -/
inductive CandidateField where
  | inputX | inputY | dx | dy | slope | square | offset | x | delta | product | y | constant | divisor | inverse
  deriving DecidableEq

def PointAddLayout.reg (L : PointAddLayout) : CandidateField → List Wire
  | .inputX => L.extendedX | .inputY => L.extendedY
  | .dx => L.dx | .dy => L.dy | .slope => L.slope | .square => L.square
  | .offset => L.offset | .x => L.candidateX | .delta => L.delta | .product => L.product
  | .y => L.candidateY | .constant => L.constant | .divisor => L.divisor | .inverse => L.inverse

def CandidateValues (L : PointAddLayout) (v : CandidateField → Nat) (G : Bool) (st : BasisState) : Prop :=
  (∀ f,regValue (L.reg f) st=v f) ∧ regValue L.pool st=0 ∧ st L.generic=G

theorem PointAddLayout.reg_pool_nodup (L : PointAddLayout) (h : L.wires.Nodup)
    (f : CandidateField) : (L.reg f++L.pool).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have hh := List.nodup_iff_count.mp h w
  cases f <;>
    simp only [PointAddLayout.reg,PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,
      PointAddLayout.flags,PointAddLayout.pointWires,PointAddLayout.extendedX,PointAddLayout.extendedY,
      List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at hh ⊢ <;>
    omega

theorem PointAddLayout.reg_disjoint (L : PointAddLayout) (h : L.wires.Nodup)
    (f g : CandidateField) (hfg : f≠g) : (L.reg f).Disjoint (L.reg g) := by
  have hn : (L.reg f++L.reg g).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp h w
    cases f <;> cases g <;> try contradiction
    all_goals
      simp only [PointAddLayout.reg,PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,
        PointAddLayout.flags,PointAddLayout.pointWires,PointAddLayout.extendedX,PointAddLayout.extendedY,
        List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at hh ⊢
      omega
  exact (List.nodup_append'.mp hn).2.2

theorem PointAddLayout.generic_not_reg (L : PointAddLayout) (h : L.wires.Nodup)
    (f : CandidateField) : L.generic∉L.reg f := by
  intro hm
  have hc := List.count_pos_iff.mpr hm
  have hh := List.nodup_iff_count.mp h L.generic
  cases f <;>
    simp only [PointAddLayout.reg,PointAddLayout.wires,PointAddLayout.work,PointAddLayout.words,
      PointAddLayout.flags,PointAddLayout.pointWires,PointAddLayout.extendedX,PointAddLayout.extendedY,
      List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil,
      beq_self_eq_true,if_true] at hh hc <;> omega

theorem CandidateValues.update (L : PointAddLayout) (hnd : L.wires.Nodup)
    (v : CandidateField → Nat) (G : Bool) (f : CandidateField) (N : Nat) (s t : BasisState)
    (hs : CandidateValues L v G s) (he : ∀ w∉L.reg f,t w=s w)
    (ho : regValue (L.reg f) t=N) : CandidateValues L (Function.update v f N) G t := by
  constructor
  · intro g
    by_cases hgf : g=f
    · subst g; simpa using ho
    · rw [Function.update_of_ne hgf]
      apply Eq.trans (regValue_congr _ _ _ ?_) (hs.1 g)
      intro w hw
      exact he w (List.disjoint_left.mp (L.reg_disjoint hnd g f hgf) hw)
  · constructor
    · apply Eq.trans (regValue_congr _ _ _ ?_) hs.2.1
      intro w hw
      exact he w (fun hf => List.disjoint_left.mp (List.nodup_append'.mp (L.reg_pool_nodup hnd f)).2.2 hf hw)
    · exact (he L.generic (L.generic_not_reg hnd f)).trans hs.2.2

end ECDSAAdd.Arithmetic
