import ECDSAAdd.Arithmetic.PointCandidateBlocks

namespace ECDSAAdd.Arithmetic

def candidateInitial (X Y : Nat) : CandidateField → Nat
  | .inputX => X | .inputY => Y | _ => 0

/-- 候选计算的逐寄存器后置值；每个模运算对应一个实际算术调用。 -/
def candidateResult (G : Bool) (X Y cx cy : Nat) : CandidateField → Nat :=
  let dx := (X+p-cx)%p
  let dy := (Y+p-cy)%p
  let divisor := if G then dx else 1
  let inverse := ((divisor : Fp)⁻¹).val
  let slope := (dy*inverse)%p
  let square := (slope*slope)%p
  let offset := (square+p-X)%p
  let x := (offset+p-cx)%p
  let delta := (X+p-x)%p
  let product := (delta*slope)%p
  let y := (product+p-Y)%p
  fun f => match f with
    | .inputX => X | .inputY => Y | .dx => dx | .dy => dy
    | .slope => slope | .square => square | .offset => offset | .x => x
    | .delta => delta | .product => product | .y => y | .constant => 0
    | .divisor => divisor | .inverse => inverse

private theorem difference_pos (X C : Nat) (hX : X<p) (hC : C<p) (hne : X≠C) :
    0<(X+p-C)%p := by
  by_cases h : X<C
  · rw [Nat.mod_eq_of_lt (by omega : X+p-C<p)]
    omega
  · have he : X+p-C=(X-C)+p := by omega
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : X-C<p)]
    omega

/-- 给定已经确定的普通分支标志，完整候选程序保留输入、标志及共享工作池。
仅普通分支要求两横坐标不同；其他分支仍然执行定义良好的候选计算。 -/
theorem pointCandidate_compute_spec (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (G : Bool) (X Y : Nat) (cx cy : Fp) (hX : X<p) (hY : Y<p)
    (hG : G=true → X≠cx.val) :
    Triple (CandidateValues L (candidateInitial X Y) G) (pointCandidateCompute L cx cy)
      (CandidateValues L (candidateResult G X Y cx.val cy.val) G) := by
  letI : NeZero p := ⟨by norm_num [p]⟩
  have hp : 0<p := by norm_num [p]
  have hp1 : 1<p := by norm_num [p]
  have hpb : p<2^256 := by norm_num [p]
  have hcX : cx.val<p := ZMod.val_lt _
  have hcY : cy.val<p := ZMod.val_lt _
  obtain ⟨nDx,nDy,nOffset,nX,nDelta,nY,nSlope,nSquare,nProduct,nInverse⟩ := L.candidate_interfaces_nodup hnd
  have hdX : (L.reg .dx).length=257 := h.words L.dx (by simp [PointAddLayout.words])
  have hdY : (L.reg .dy).length=257 := h.words L.dy (by simp [PointAddLayout.words])
  have hS : (L.reg .slope).length=257 := h.words L.slope (by simp [PointAddLayout.words])
  have hSq : (L.reg .square).length=257 := h.words L.square (by simp [PointAddLayout.words])
  have hO : (L.reg .offset).length=257 := h.words L.offset (by simp [PointAddLayout.words])
  have hCX : (L.reg .x).length=257 := h.words L.candidateX (by simp [PointAddLayout.words])
  have hD : (L.reg .delta).length=257 := h.words L.delta (by simp [PointAddLayout.words])
  have hP : (L.reg .product).length=257 := h.words L.product (by simp [PointAddLayout.words])
  have hCY : (L.reg .y).length=257 := h.words L.candidateY (by simp [PointAddLayout.words])
  obtain ⟨heX,heY⟩ := L.extended_lengths h
  let v0 := candidateInitial X Y
  let v1 := Function.update v0 CandidateField.dx ((X+p-cx.val)%p)
  let v2 := Function.update v1 CandidateField.dy ((Y+p-cy.val)%p)
  let v3 := Function.update v2 CandidateField.divisor (if G then v2 .dx else 1)
  let v4 := Function.update v3 CandidateField.inverse ((v3 .divisor : Fp)⁻¹).val
  let v5 := Function.update v4 CandidateField.slope ((v4 .dy*v4 .inverse)%p)
  let v6 := Function.update v5 CandidateField.square ((v5 .slope*v5 .slope)%p)
  let v7 := Function.update v6 CandidateField.offset ((v6 .square+p-X)%p)
  let v8 := Function.update v7 CandidateField.x ((v7 .offset+p-cx.val)%p)
  let v9 := Function.update v8 CandidateField.delta ((X+p-v8 .x)%p)
  let v10 := Function.update v9 CandidateField.product ((v9 .delta*v9 .slope)%p)
  let v11 := Function.update v10 CandidateField.y ((v10 .product+p-Y)%p)
  have h1 : Triple (CandidateValues L v0 G) (pointSubConstant L L.extendedX L.dx cx.val) (CandidateValues L v1 G) := by
    simpa [v0,v1,candidateInitial] using CandidateValues.subConstant L h hnd v0 G .inputX .dx
      heX hdX (by decide) (by decide) nDx hX rfl cx.val hcX
  have h2 : Triple (CandidateValues L v1 G) (pointSubConstant L L.extendedY L.dy cy.val) (CandidateValues L v2 G) := by
    simpa [v0,v1,v2,candidateInitial] using CandidateValues.subConstant L h hnd v1 G .inputY .dy
      heY hdY (by decide) (by decide) nDy hY rfl cy.val hcY
  have h3 : Triple (CandidateValues L v2 G)
      (safeDivisor L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail) (CandidateValues L v3 G) := by
    simpa [v0,v1,v2,v3,candidateInitial] using CandidateValues.safe L h hnd v2 G
      (by simpa [v2,v1] using (Nat.mod_lt (X+p-cx.val) hp).trans hpb)
  have hDiv0 : 0<v3 .divisor := by
    cases hg : G <;> simp [v3,v2,v1,hg]
    exact difference_pos X cx.val hX hcX (hG hg)
  have hDiv : v3 .divisor<p := by
    cases hg : G <;> simp [v3,v2,v1,hg,hp1,Nat.mod_lt _ hp]
  have h4 : Triple (CandidateValues L v3 G)
      (fieldInverse (poolInverse L.poolWire L.divisor L.inverse)) (CandidateValues L v4 G) := by
    simpa [v0,v1,v2,v3,v4,candidateInitial] using CandidateValues.inverse L h hnd v3 G .divisor .inverse
      h.divisor h.inverse nInverse hDiv0 hDiv
  have h5 : Triple (CandidateValues L v4 G)
      (fieldMul (poolMul L.poolWire L.dy L.inverse L.slope)) (CandidateValues L v5 G) := by
    have hn : (L.reg .dy++(L.reg .inverse).take 256++L.reg .slope++L.pool).Nodup := by
      simpa [PointAddLayout.reg,List.take_of_length_le (show L.inverse.length≤256 by rw [h.inverse])] using nSlope
    simpa [PointAddLayout.reg,v0,v1,v2,v3,v4,v5,candidateInitial,
      List.take_of_length_le (show L.inverse.length≤256 by rw [h.inverse])] using
      CandidateValues.mul L h hnd v4 G .dy .inverse .slope hdY (by change 256≤L.inverse.length; rw [h.inverse]) hS hn
        (by simp [v4,v3,v2,Nat.mod_lt _ hp])
        (by simpa [v4] using (ZMod.val_lt ((v3 .divisor : Fp)⁻¹)).trans hpb)
  have h6 : Triple (CandidateValues L v5 G) (pointSquare L) (CandidateValues L v6 G) := by
    simpa [v0,v1,v2,v3,v4,v5,v6,candidateInitial] using CandidateValues.square L h hnd v5 G nSquare
      (by simp [v5,Nat.mod_lt _ hp]) rfl
  have h7 : Triple (CandidateValues L v6 G)
      (fieldSub (poolSub L.poolWire L.square L.extendedX L.offset)) (CandidateValues L v7 G) := by
    simpa [v0,v1,v2,v3,v4,v5,v6,v7,candidateInitial] using CandidateValues.sub L h hnd v6 G .square .inputX .offset
      hSq heX hO nOffset (by simp [v6,Nat.mod_lt _ hp]) hX
  have h8 : Triple (CandidateValues L v7 G)
      (pointSubConstant L L.offset L.candidateX cx.val) (CandidateValues L v8 G) := by
    simpa [v0,v1,v2,v3,v4,v5,v6,v7,v8,candidateInitial] using CandidateValues.subConstant L h hnd v7 G .offset .x
      hO hCX (by decide) (by decide) nX (by simp [v7,Nat.mod_lt _ hp]) rfl cx.val hcX
  have h9 : Triple (CandidateValues L v8 G)
      (fieldSub (poolSub L.poolWire L.extendedX L.candidateX L.delta)) (CandidateValues L v9 G) := by
    simpa [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,candidateInitial] using CandidateValues.sub L h hnd v8 G .inputX .x .delta
      heX hCX hD nDelta hX (by simp [v8,Nat.mod_lt _ hp])
  have h10 : Triple (CandidateValues L v9 G)
      (fieldMul (poolMul L.poolWire L.delta (L.slope.take 256) L.product)) (CandidateValues L v10 G) := by
    simpa [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,candidateInitial] using CandidateValues.mul L h hnd v9 G .delta .slope .product
      hD (by omega) hP nProduct (by simp [v9,Nat.mod_lt _ hp])
      (by simpa [v9,v8,v7,v6,v5] using (Nat.mod_lt (v4 .dy*v4 .inverse) hp).trans hpb)
  have h11 : Triple (CandidateValues L v10 G)
      (fieldSub (poolSub L.poolWire L.product L.extendedY L.candidateY)) (CandidateValues L v11 G) := by
    simpa [v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,candidateInitial] using CandidateValues.sub L h hnd v10 G .product .inputY .y
      hP heY hCY nY (by simp [v10,Nat.mod_lt _ hp]) hY
  have hf : v11=candidateResult G X Y cx.val cy.val := by
    funext f
    cases f <;> simp [v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1,v0,candidateInitial,candidateResult]
  rw [← hf]
  exact (((((((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11

/-- 候选寄存器按依赖逆序清零，输入、普通分支标志和共享池保持。 -/
private theorem candidateClear_of_values (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (G : Bool) (X Y : Nat) (cx cy : Fp) (hX : X<p) (hY : Y<p)
    (hG : G=true → X≠cx.val)
    (DX DY DV IV SL SQ OF CX DE PR CY : Nat)
    (eDX : (X+p-cx.val)%p=DX) (eDY : (Y+p-cy.val)%p=DY)
    (eDiv : (if G then DX else 1)=DV) (eInv : ((DV : Fp)⁻¹).val=IV)
    (eSlope : (DY*IV)%p=SL) (eSquare : (SL*SL)%p=SQ) (eOffset : (SQ+p-X)%p=OF)
    (eX : (OF+p-cx.val)%p=CX) (eDelta : (X+p-CX)%p=DE)
    (eProduct : (DE*SL)%p=PR) (eY : (PR+p-Y)%p=CY) :
    Triple (CandidateValues L (fun f => match f with
      | .inputX => X | .inputY => Y | .dx => DX | .dy => DY | .slope => SL
      | .square => SQ | .offset => OF | .x => CX | .delta => DE | .product => PR
      | .y => CY | .constant => 0 | .divisor => DV | .inverse => IV) G) (pointCandidateClear L cx cy)
      (CandidateValues L (candidateInitial X Y) G) := by
  rw [pointCandidateClear]
  letI : NeZero p := ⟨by norm_num [p]⟩
  have hp : 0<p := by norm_num [p]
  have hp1 : 1<p := by norm_num [p]
  have hpb : p<2^256 := by norm_num [p]
  have hcX : cx.val<p := ZMod.val_lt _
  have hcY : cy.val<p := ZMod.val_lt _
  obtain ⟨nDx,nDy,nOffset,nX,nDelta,nY,nSlope,nSquare,nProduct,nInverse⟩ := L.candidate_interfaces_nodup hnd
  have hdX : (L.reg .dx).length=257 := h.words L.dx (by simp [PointAddLayout.words])
  have hdY : (L.reg .dy).length=257 := h.words L.dy (by simp [PointAddLayout.words])
  have hS : (L.reg .slope).length=257 := h.words L.slope (by simp [PointAddLayout.words])
  have hSq : (L.reg .square).length=257 := h.words L.square (by simp [PointAddLayout.words])
  have hO : (L.reg .offset).length=257 := h.words L.offset (by simp [PointAddLayout.words])
  have hCX : (L.reg .x).length=257 := h.words L.candidateX (by simp [PointAddLayout.words])
  have hD : (L.reg .delta).length=257 := h.words L.delta (by simp [PointAddLayout.words])
  have hP : (L.reg .product).length=257 := h.words L.product (by simp [PointAddLayout.words])
  have hCY : (L.reg .y).length=257 := h.words L.candidateY (by simp [PointAddLayout.words])
  obtain ⟨heX,heY⟩ := L.extended_lengths h
  let v0 := candidateInitial X Y
  let v1 := Function.update v0 CandidateField.dx DX
  let v2 := Function.update v1 CandidateField.dy DY
  let v3 := Function.update v2 CandidateField.divisor DV
  let v4 := Function.update v3 CandidateField.inverse IV
  let v5 := Function.update v4 CandidateField.slope SL
  let v6 := Function.update v5 CandidateField.square SQ
  let v7 := Function.update v6 CandidateField.offset OF
  let v8 := Function.update v7 CandidateField.x CX
  let v9 := Function.update v8 CandidateField.delta DE
  let v10 := Function.update v9 CandidateField.product PR
  let v11 := Function.update v10 CandidateField.y CY
  have bDX : DX<p := by rw [← eDX]; exact Nat.mod_lt _ hp
  have bDY : DY<p := by rw [← eDY]; exact Nat.mod_lt _ hp
  have bSL : SL<p := by rw [← eSlope]; exact Nat.mod_lt _ hp
  have bSQ : SQ<p := by rw [← eSquare]; exact Nat.mod_lt _ hp
  have bOF : OF<p := by rw [← eOffset]; exact Nat.mod_lt _ hp
  have bCX : CX<p := by rw [← eX]; exact Nat.mod_lt _ hp
  have bDE : DE<p := by rw [← eDelta]; exact Nat.mod_lt _ hp
  have bPR : PR<p := by rw [← eProduct]; exact Nat.mod_lt _ hp
  have bCY : CY<p := by rw [← eY]; exact Nat.mod_lt _ hp
  have bIV : IV<p := by rw [← eInv]; exact ZMod.val_lt _
  have hDiv0 : 0<v3 .divisor := by
    change 0<DV
    rw [← eDiv]
    cases hg : G <;> simp only [Bool.false_eq_true,if_false,if_true]
    · omega
    · rw [← eDX]; exact difference_pos X cx.val hX hcX (hG hg)
  have hDiv : v3 .divisor<p := by
    change DV<p
    rw [← eDiv]
    split <;> assumption
  have c11 : Triple (CandidateValues L v11 G) (fieldSub (poolSub L.poolWire L.product L.extendedY L.candidateY)) (CandidateValues L v10 G) := by
    have hf : Function.update v11 CandidateField.y (v11 .y ^^^ ((v11 .product+p-v11 .inputY)%p))=v10 := by
      change Function.update (Function.update v10 CandidateField.y CY) CandidateField.y
        (CY ^^^ ((PR+p-Y)%p))=v10
      rw [eY,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.sub L h hnd v11 G .product .inputY .y hP heY hCY nY bPR hY)
    intro st hv
    simpa only [hf] using hv
  have c10 : Triple (CandidateValues L v10 G) (fieldMul (poolMul L.poolWire L.delta (L.slope.take 256) L.product)) (CandidateValues L v9 G) := by
    have hf : Function.update v10 CandidateField.product (v10 .product ^^^ ((v10 .delta*v10 .slope)%p))=v9 := by
      change Function.update (Function.update v9 CandidateField.product PR) CandidateField.product
        (PR ^^^ ((DE*SL)%p))=v9
      rw [eProduct,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.mul L h hnd v10 G .delta .slope .product hD (by omega) hP nProduct bDE (bSL.trans hpb))
    intro st hv
    simpa only [hf] using hv
  have c9 : Triple (CandidateValues L v9 G) (fieldSub (poolSub L.poolWire L.extendedX L.candidateX L.delta)) (CandidateValues L v8 G) := by
    have hf : Function.update v9 CandidateField.delta (v9 .delta ^^^ ((v9 .inputX+p-v9 .x)%p))=v8 := by
      change Function.update (Function.update v8 CandidateField.delta DE) CandidateField.delta
        (DE ^^^ ((X+p-CX)%p))=v8
      rw [eDelta,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.sub L h hnd v9 G .inputX .x .delta heX hCX hD nDelta hX bCX)
    intro st hv
    simpa only [hf] using hv
  have c8 : Triple (CandidateValues L v8 G) (pointSubConstant L L.offset L.candidateX cx.val) (CandidateValues L v7 G) := by
    have hf : Function.update v8 CandidateField.x (v8 .x ^^^ ((v8 .offset+p-cx.val)%p))=v7 := by
      change Function.update (Function.update v7 CandidateField.x CX) CandidateField.x
        (CX ^^^ ((OF+p-cx.val)%p))=v7
      rw [eX,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.subConstant L h hnd v8 G .offset .x hO hCX (by decide) (by decide) nX bOF rfl cx.val hcX)
    intro st hv
    simpa only [hf] using hv
  have c7 : Triple (CandidateValues L v7 G) (fieldSub (poolSub L.poolWire L.square L.extendedX L.offset)) (CandidateValues L v6 G) := by
    have hf : Function.update v7 CandidateField.offset (v7 .offset ^^^ ((v7 .square+p-v7 .inputX)%p))=v6 := by
      change Function.update (Function.update v6 CandidateField.offset OF) CandidateField.offset
        (OF ^^^ ((SQ+p-X)%p))=v6
      rw [eOffset,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.sub L h hnd v7 G .square .inputX .offset hSq heX hO nOffset bSQ hX)
    intro st hv
    simpa only [hf] using hv
  have c6 : Triple (CandidateValues L v6 G) (pointSquare L) (CandidateValues L v5 G) := by
    have hf : Function.update v6 CandidateField.square (v6 .square ^^^ ((v6 .slope*v6 .slope)%p))=v5 := by
      change Function.update (Function.update v5 CandidateField.square SQ) CandidateField.square
        (SQ ^^^ ((SL*SL)%p))=v5
      rw [eSquare,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.square L h hnd v6 G nSquare bSL rfl)
    intro st hv
    simpa only [hf] using hv
  have c5 : Triple (CandidateValues L v5 G) (fieldMul (poolMul L.poolWire L.dy L.inverse L.slope)) (CandidateValues L v4 G) := by
    have hn : (L.reg .dy++(L.reg .inverse).take 256++L.reg .slope++L.pool).Nodup := by
      simpa [PointAddLayout.reg,List.take_of_length_le (show L.inverse.length≤256 by rw [h.inverse])] using nSlope
    have hf : Function.update v5 CandidateField.slope (v5 .slope ^^^ ((v5 .dy*v5 .inverse)%p))=v4 := by
      change Function.update (Function.update v4 CandidateField.slope SL) CandidateField.slope
        (SL ^^^ ((DY*IV)%p))=v4
      rw [eSlope,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    have hc := CandidateValues.mul L h hnd v5 G .dy .inverse .slope hdY (by change 256≤L.inverse.length; rw [h.inverse]) hS hn bDY (bIV.trans hpb)
    have he : (L.reg .inverse).take 256=L.inverse := List.take_of_length_le (show L.inverse.length≤256 by rw [h.inverse])
    rw [he] at hc
    apply Triple.conseq (fun _ hv => hv) hc
    intro st hv
    simpa only [hf] using hv
  have c4 : Triple (CandidateValues L v4 G) (fieldInverse (poolInverse L.poolWire L.divisor L.inverse)) (CandidateValues L v3 G) := by
    have hf : Function.update v4 CandidateField.inverse (v4 .inverse ^^^ ((v4 .divisor : Fp)⁻¹).val)=v3 := by
      change Function.update (Function.update v3 CandidateField.inverse IV) CandidateField.inverse
        (IV ^^^ (((DV : Fp)⁻¹).val))=v3
      rw [eInv,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.inverse L h hnd v4 G .divisor .inverse h.divisor h.inverse nInverse hDiv0 hDiv)
    intro st hv
    simpa only [hf] using hv
  have c3 : Triple (CandidateValues L v3 G) (safeDivisor L.generic (L.dx.take 256) L.divisor.head! L.divisor.tail) (CandidateValues L v2 G) := by
    have hf : Function.update v3 CandidateField.divisor (v3 .divisor ^^^ (if G then v3 .dx else 1))=v2 := by
      change Function.update (Function.update v2 CandidateField.divisor DV) CandidateField.divisor
        (DV ^^^ ((if G then DX else 1)))=v2
      rw [eDiv,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.safe L h hnd v3 G (bDX.trans hpb))
    intro st hv
    simpa only [hf] using hv
  have c2 : Triple (CandidateValues L v2 G) (pointSubConstant L L.extendedY L.dy cy.val) (CandidateValues L v1 G) := by
    have hf : Function.update v2 CandidateField.dy (v2 .dy ^^^ ((v2 .inputY+p-cy.val)%p))=v1 := by
      change Function.update (Function.update v1 CandidateField.dy DY) CandidateField.dy
        (DY ^^^ ((Y+p-cy.val)%p))=v1
      rw [eDY,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.subConstant L h hnd v2 G .inputY .dy heY hdY (by decide) (by decide) nDy hY rfl cy.val hcY)
    intro st hv
    simpa only [hf] using hv
  have c1 : Triple (CandidateValues L v1 G) (pointSubConstant L L.extendedX L.dx cx.val) (CandidateValues L v0 G) := by
    have hf : Function.update v1 CandidateField.dx (v1 .dx ^^^ ((v1 .inputX+p-cx.val)%p))=v0 := by
      change Function.update (Function.update v0 CandidateField.dx DX) CandidateField.dx
        (DX ^^^ ((X+p-cx.val)%p))=v0
      rw [eDX,Nat.xor_self,Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    apply Triple.conseq (fun _ hv => hv) (CandidateValues.subConstant L h hnd v1 G .inputX .dx heX hdX (by decide) (by decide) nDx hX rfl cx.val hcX)
    intro st hv
    simpa only [hf] using hv
  have hf : v11=(fun f => match f with
      | .inputX => X | .inputY => Y | .dx => DX | .dy => DY | .slope => SL
      | .square => SQ | .offset => OF | .x => CX | .delta => DE | .product => PR
      | .y => CY | .constant => 0 | .divisor => DV | .inverse => IV) := by
    funext f
    cases f <;> simp [v11,v10,v9,v8,v7,v6,v5,v4,v3,v2,v1,v0,candidateInitial]
  rw [← hf]
  exact (((((((((c11.seq c10).seq c9).seq c8).seq c7).seq c6).seq c5).seq c4).seq c3).seq c2).seq c1

/-- 同一组前向 XOR 模块按依赖逆序清零所有候选寄存器。 -/
theorem pointCandidate_clear_spec (L : PointAddLayout) (h : L.Widths) (hnd : L.wires.Nodup)
    (G : Bool) (X Y : Nat) (cx cy : Fp) (hX : X<p) (hY : Y<p)
    (hG : G=true → X≠cx.val) :
    Triple (CandidateValues L (candidateResult G X Y cx.val cy.val) G) (pointCandidateClear L cx cy)
      (CandidateValues L (candidateInitial X Y) G) := by
  unfold candidateResult
  exact candidateClear_of_values L h hnd G X Y cx cy hX hY hG
    _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

end ECDSAAdd.Arithmetic
