import ECDSAAdd.Arithmetic.PointCandidateProof

namespace ECDSAAdd.Arithmetic

private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

private theorem field_sub_val (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [← Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

private theorem field_sub_cast (x y : Fp) : ((x.val+p-y.val : Nat) : Fp)=x-y := by
  have hy := ZMod.val_lt y
  rw [Nat.cast_sub (by omega : y.val≤x.val+p),Nat.cast_add,
    ZMod.natCast_zmod_val,ZMod.natCast_self,ZMod.natCast_zmod_val,add_zero]

/-- 逐模块得到的自然数代表元与域上的候选公式一致。 -/
theorem candidateResult_coordinates (G : Bool) (x y cx cy : Fp) :
    candidateResult G x.val y.val cx.val cy.val .x=(pointCandidateValues G x y cx cy).x.val ∧
    candidateResult G x.val y.val cx.val cy.val .y=(pointCandidateValues G x y cx cy).y.val := by
  cases G <;>
    simp [candidateResult,pointCandidateValues,pointSafeDivisor,field_sub_val,ZMod.val_mul,ZMod.val_one,field_sub_cast]

/-- 先展示候选工作寄存器全零时的命名接口。 -/
theorem pointCandidate_zero_spec (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (G : Bool) (X Y : Nat) (cx cy : Fp) (hX : X<p) (hY : Y<p)
    (hG : G=true → X≠cx.val) :
    let V := candidateResult G X Y cx.val cy.val
    {{ L.extendedX=X, L.extendedY=Y, L.dx=0, L.dy=0,
       L.slope=0, L.square=0, L.offset=0, L.candidateX=0,
       L.delta=0, L.product=0, L.candidateY=0, L.constant=0,
       L.divisor=0, L.inverse=0, L.pool=0, L.generic=G }} pointCandidateCompute L cx cy
    {{ L.extendedX=X, L.extendedY=Y, L.dx=V .dx, L.dy=V .dy,
       L.slope=V .slope, L.square=V .square, L.offset=V .offset, L.candidateX=V .x,
       L.delta=V .delta, L.product=V .product, L.candidateY=V .y, L.constant=0,
       L.divisor=V .divisor, L.inverse=V .inverse, L.pool=0, L.generic=G }} := by
  dsimp only
  intro st m hpre
  have hi : CandidateValues L (candidateInitial X Y) G st.basis := by
    refine ⟨?_,hpre.1.2,hpre.2⟩
    intro f
    cases f
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.2
    · exact hpre.1.1.1.1.2
    · exact hpre.1.1.1.2
    · exact hpre.1.1.2
  obtain ⟨hp,hpost⟩ := pointCandidate_compute_spec L h hnd G X Y cx cy hX hY hG st m hi
  exact ⟨hp,⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpost.1 .inputX,hpost.1 .inputY⟩,hpost.1 .dx⟩,hpost.1 .dy⟩,hpost.1 .slope⟩,hpost.1 .square⟩,hpost.1 .offset⟩,hpost.1 .x⟩,hpost.1 .delta⟩,hpost.1 .product⟩,hpost.1 .y⟩,hpost.1 .constant⟩,hpost.1 .divisor⟩,hpost.1 .inverse⟩,hpost.2.1⟩,hpost.2.2⟩⟩

/-- 恢复所有候选零寄存器的命名接口。 -/
theorem pointCandidate_cleanup_spec (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (G : Bool) (X Y : Nat) (cx cy : Fp) (hX : X<p) (hY : Y<p)
    (hG : G=true → X≠cx.val) :
    let V := candidateResult G X Y cx.val cy.val
    {{ L.extendedX=X, L.extendedY=Y, L.dx=V .dx, L.dy=V .dy,
       L.slope=V .slope, L.square=V .square, L.offset=V .offset, L.candidateX=V .x,
       L.delta=V .delta, L.product=V .product, L.candidateY=V .y, L.constant=0,
       L.divisor=V .divisor, L.inverse=V .inverse, L.pool=0, L.generic=G }} pointCandidateClear L cx cy
    {{ L.extendedX=X, L.extendedY=Y, L.dx=0, L.dy=0,
       L.slope=0, L.square=0, L.offset=0, L.candidateX=0,
       L.delta=0, L.product=0, L.candidateY=0, L.constant=0,
       L.divisor=0, L.inverse=0, L.pool=0, L.generic=G }} := by
  dsimp only
  intro st m hpre
  have hi : CandidateValues L (candidateResult G X Y cx.val cy.val) G st.basis := by
    refine ⟨?_,hpre.1.2,hpre.2⟩
    intro f
    cases f
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.1.2
    · exact hpre.1.1.1.1.1.2
    · exact hpre.1.1.1.1.2
    · exact hpre.1.1.1.2
    · exact hpre.1.1.2
  obtain ⟨hp,hpost⟩ := pointCandidate_clear_spec L h hnd G X Y cx cy hX hY hG st m hi
  exact ⟨hp,⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hpost.1 .inputX,hpost.1 .inputY⟩,hpost.1 .dx⟩,hpost.1 .dy⟩,hpost.1 .slope⟩,hpost.1 .square⟩,hpost.1 .offset⟩,hpost.1 .x⟩,hpost.1 .delta⟩,hpost.1 .product⟩,hpost.1 .y⟩,hpost.1 .constant⟩,hpost.1 .divisor⟩,hpost.1 .inverse⟩,hpost.2.1⟩,hpost.2.2⟩⟩

end ECDSAAdd.Arithmetic
