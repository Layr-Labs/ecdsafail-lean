import ECDSAAdd.Submission.Entrant.FastE

/-! The infinity class shares the generic-flag wire.

For a set control the five input classes (infinity `O`, doubling `D`, inverse
`I`, exception `H`, generic `G`) are one-hot, and the generic flag is their
complement `G = b ⊕ O ⊕ D ⊕ I ⊕ H`.  So `O` never needs its own wire:

* on input, the infinity test `b ∧ ¬finite` is written straight into the
  generic wire, and `b ⊕ D ⊕ I ⊕ H` is then XORed on top, which leaves `G`;
* after the generic block, XORing `b ⊕ D ⊕ I ⊕ H` into the generic wire again
  leaves exactly `O` there; the infinity corner reads it from that wire, and
  the output comparison against `C` (which detected `O` on the old
  `infinitySelect` wire) now clears the generic wire.

The Toffoli and measurement counts are unchanged, and `infinitySelect` is never
touched, so the static site inventory loses one wire. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant
open Arithmetic MappedCompressed Secp256k1 ControlledPointLayout CompressedPointDialog

/-- `g ^= b ⊕ d ⊕ i ⊕ h` (four CX gates). -/
def genericFlagO (L : ControlledPointLayout) : Program :=
  [.CX L.control L.core.generic] ++ [.CX L.doubleSelect L.core.generic] ++
    [.CX L.genericSelect L.core.generic] ++ [.CX L.core.equalNegY L.core.generic]

/-- The six corner constants, the infinity corner read from the generic wire. -/
def cornersG (L : ControlledPointLayout) (C : Point) : Program :=
  maskedPointConstant L.core.generic L.point C ++
  (maskedPointConstant L.doubleSelect L.point C ++
  (maskedPointConstant L.doubleSelect L.point (C+C) ++
  (maskedPointConstant L.genericSelect L.point (-C) ++
  (maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C) ++
  maskedPointConstant L.core.equalNegY L.point (-C)))))

/-- The finite-addend program with the infinity class on the generic wire. -/
def finiteProgramO (L : ControlledPointLayout) (C : Point) (cy : Fp) (Gen : Program) : Program :=
  zeroFlag L.point.finite L.control L.core.generic ++
  pairEqual L L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C) ++
  gatedShort L (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C) ++
  genericFlagO L ++ Gen ++ genericFlagO L ++ cornersG L C ++
  pairEqual L L.core.generic L.core.equalNegY true (exceptionBit C) C (-C) ++
  gatedShort L (decide (cy≠-cy)) L.doubleSelect (C+C) ++
  zeroFlag L.point.finite L.control L.genericSelect

section Flags
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
include hn

theorem zeroFlag_equalG (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (zeroFlag L.point.finite L.control L.core.generic)
      (PointDialogBoundary L R b (dialogFlagState L O D I (G ^^ (b && pointEqual R 0)) E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := zeroFlag_boundary L hn R b (dialogFlagState L O D I G E H K) L.control L.core.generic
    (Or.inl rfl) (by simp [inPlaceFlags]) (by tauto) b (by simp)
  simp only [hr.2.2.2.1] at hh
  exact hh.conseq (fun _ h=>h) (fun _ h=>h.congrFlags
    (dialogFlagState_update L hn O D I G E H K _).2.2.2.1)

theorem genericFlagO_flag (R : Point) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L R b (dialogFlagState L O D I G E H K))
      (genericFlagO L)
      (PointDialogBoundary L R b (dialogFlagState L O D I ((((G ^^ b) ^^ D) ^^ I) ^^ H) E H K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags,List.nodup_cons,List.mem_cons,not_or] at sep
  have step (c : Wire) (hc : c = L.control ∨ c ∈ L.inPlaceFlags) (B X : Bool)
      (hb : (if c = L.control then b else dialogFlagState L O D I X E H K c) = B) :
      Triple (PointDialogBoundary L R b (dialogFlagState L O D I X E H K)) [.CX c L.core.generic]
        (PointDialogBoundary L R b (dialogFlagState L O D I (X ^^ B) E H K)) := by
    have h := dialogBoundary_cx L hn R b (dialogFlagState L O D I X E H K) c L.core.generic hc
      (by simp [inPlaceFlags]) B hb
    rw [(dialogFlagState_read L hn O D I X E H K).2.2.2.1] at h
    exact h.conseq (fun _ h => h) (fun _ h => h.congrFlags
      (dialogFlagState_update L hn O D I X E H K _).2.2.2.1)
  have h1 := step L.control (Or.inl rfl) b G (by simp)
  have h2 := step L.doubleSelect (Or.inr (by simp [inPlaceFlags])) D (G ^^ b)
    (by rw [if_neg (by tauto)]; exact (dialogFlagState_read L hn O D I _ E H K).2.1)
  have h3 := step L.genericSelect (Or.inr (by simp [inPlaceFlags])) I ((G ^^ b) ^^ D)
    (by rw [if_neg (by tauto)]; exact (dialogFlagState_read L hn O D I _ E H K).2.2.1)
  have h4 := step L.core.equalNegY (Or.inr (by simp [inPlaceFlags])) H (((G ^^ b) ^^ D) ^^ I)
    (by rw [if_neg (by tauto)]; exact (dialogFlagState_read L hn O D I _ E H K).2.2.2.2.2.1)
  exact ((h1.seq h2).seq h3).seq h4

include hw

theorem pairFlag_outputO (S C : Point) (en : Bool) (b O D I G E H K : Bool) :
    Triple (PointDialogBoundary L S b (dialogFlagState L O D I G E H K))
      (pairEqual L L.core.generic L.core.equalNegY true en C (-C))
      (PointDialogBoundary L S b
        (dialogFlagState L O D I (G ^^ (b && pointEqual S C)) E (H ^^ ((b && en) && pointEqual S (-C))) K)) := by
  have sep := dialogFlag_separation L hn
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have hr := dialogFlagState_read L hn O D I G E H K
  have hh := pairBoundary L hw hn S C b (dialogFlagState L O D I G E H K) L.core.generic L.core.equalNegY
    (by simp [inPlaceFlags]) (by simp [inPlaceFlags]) (by tauto)
    true en b (b && en) (by simp) rfl
  simp only [hr.2.2.2.1, hr.2.2.2.2.2.1] at hh
  refine hh.conseq (fun _ h => h) (fun _ h => h.congrFlags ?_)
  intro q hq
  have u1 := (dialogFlagState_update L hn O D I G E H K (G ^^ (b && pointEqual S C))).2.2.2.1
  have u2 := (dialogFlagState_update L hn O D I (G ^^ (b && pointEqual S C)) E H K
    (H ^^ ((b && en) && pointEqual S (-C)))).2.2.2.2.2.1
  rw [← u2 q hq]
  simp only [writeBit, Function.update_apply]
  rw [← u1 q hq]
  simp only [writeBit, Function.update_apply]

end Flags

section Corners

theorem masked_run_append (c : Wire) (r : PointReg) (P : Point) (Q : Program) (m : List Bool)
    (s : State) :
    run (maskedPointConstant c r P ++ Q) m s = run Q m (run (maskedPointConstant c r P) m s) := by
  rw [run_append, run_take, (maskedPointConstant_counts c r P).2, List.drop_zero]

theorem cornersG_effect (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (s : State) (m : List Bool) :
    PointEffect L.point
      ((((((s.basis L.core.generic && pointFinite C) ^^ (s.basis L.doubleSelect && pointFinite C)) ^^
        (s.basis L.doubleSelect && pointFinite (C+C))) ^^ (s.basis L.genericSelect && pointFinite (-C))) ^^
        (s.basis L.core.equalNegY && pointFinite (dialogExceptionPoint C))) ^^
        (s.basis L.core.equalNegY && pointFinite (-C)))
      ((((((if s.basis L.core.generic then pointX C else 0) ^^^ (if s.basis L.doubleSelect then pointX C else 0)) ^^^
        (if s.basis L.doubleSelect then pointX (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointX (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointX (-C) else 0))
      ((((((if s.basis L.core.generic then pointY C else 0) ^^^ (if s.basis L.doubleSelect then pointY C else 0)) ^^^
        (if s.basis L.doubleSelect then pointY (C+C) else 0)) ^^^ (if s.basis L.genericSelect then pointY (-C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (dialogExceptionPoint C) else 0)) ^^^
        (if s.basis L.core.equalNegY then pointY (-C) else 0))
      s (run (cornersG L C) m s) := by
  have hr : (PointAddLayout.pointWires L.point).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) q
    simp only [dialogUsedWires,List.count_append] at h
    omega
  have away (c : Wire) (hc : c ∈ L.inPlaceFlags) : c ∉ PointAddLayout.pointWires L.point := by
    intro hm
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) c
    have hf := List.count_pos_iff.mpr hc
    have hp := List.count_pos_iff.mpr hm
    simp only [dialogUsedWires,List.count_append,List.count_cons] at h
    omega
  have ag := away L.core.generic (by simp [inPlaceFlags])
  have ad := away L.doubleSelect (by simp [inPlaceFlags])
  have ai := away L.genericSelect (by simp [inPlaceFlags])
  have ah := away L.core.equalNegY (by simp [inPlaceFlags])
  simp only [cornersG, masked_run_append]
  let u := run (maskedPointConstant L.core.generic L.point C) m s
  have e0 := maskedPointConstant_correct _ _ C hr ag hw.inputX hw.inputY s m
  have ud : u.basis L.doubleSelect=s.basis L.doubleSelect := e0.outside _ ad
  let v := run (maskedPointConstant L.doubleSelect L.point C) m u
  have e1 := maskedPointConstant_correct _ _ C hr ad hw.inputX hw.inputY u m
  have vd : v.basis L.doubleSelect=s.basis L.doubleSelect := (e0.trans e1).outside _ ad
  let w := run (maskedPointConstant L.doubleSelect L.point (C+C)) m v
  have e2 := maskedPointConstant_correct _ _ (C+C) hr ad hw.inputX hw.inputY v m
  have wi : w.basis L.genericSelect=s.basis L.genericSelect := ((e0.trans e1).trans e2).outside _ ai
  let x := run (maskedPointConstant L.genericSelect L.point (-C)) m w
  have e3 := maskedPointConstant_correct _ _ (-C) hr ai hw.inputX hw.inputY w m
  have xh : x.basis L.core.equalNegY=s.basis L.core.equalNegY :=
    (((e0.trans e1).trans e2).trans e3).outside _ ah
  let y := run (maskedPointConstant L.core.equalNegY L.point (dialogExceptionPoint C)) m x
  have e4 := maskedPointConstant_correct _ _ (dialogExceptionPoint C) hr ah hw.inputX hw.inputY x m
  have yh : y.basis L.core.equalNegY=s.basis L.core.equalNegY :=
    ((((e0.trans e1).trans e2).trans e3).trans e4).outside _ ah
  have e5 := maskedPointConstant_correct _ _ (-C) hr ah hw.inputX hw.inputY y m
  have hh := ((((e0.trans e1).trans e2).trans e3).trans e4).trans e5
  simpa only [ud,vd,wi,xh,yh] using hh

theorem cornersG_boundary [DecidableEq Point] (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (R C : Point) (hc : C≠0) (b : Bool) (f : BasisState)
    (ho : f L.core.generic=dialogInfinity b R)
    (hd : f L.doubleSelect=dialogDouble b R C)
    (hi : f L.genericSelect=dialogInversePoint b R C)
    (hh : f L.core.equalNegY=dialogException b R C) :
    Triple (PointDialogBoundary L (if dialogOrdinary b R C then R+C else R) b f)
      (cornersG L C) (PointDialogBoundary L (if b then R+C else R) b f) := by
  intro s m v
  have he := cornersG_effect L hw hn C s m
  have vo := (v.flags _ (by simp [inPlaceFlags])).trans ho
  have vd := (v.flags _ (by simp [inPlaceFlags])).trans hd
  have vi := (v.flags _ (by simp [inPlaceFlags])).trans hi
  have vh := (v.flags _ (by simp [inPlaceFlags])).trans hh
  have hp := (point_holds _ _ _).mp v.point
  refine ⟨he.phase,v.withPoint hn ((point_holds _ _ _).mpr ⟨?_,?_,?_⟩) he.outside⟩
  · rw [he.finite,hp.1,vo,vd,vi,vh]
    have h := dialogCorners_bool b R C hc pointFinite (by rfl)
    have bool_if (a b : Bool) : (if a then b else false)=(a && b) := by cases a <;> rfl
    simpa only [bool_if,Bool.xor_assoc] using h
  · rw [he.x,hp.2.1,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointX (by rfl)
  · rw [he.y,hp.2.2,vo,vd,vi,vh]
    simpa only [Nat.xor_assoc] using dialogCorners_nat b R C hc pointY (by rfl)

end Corners

section Spec
attribute [local irreducible] run wires shortEqual pairEqual gatedShort genericFlagO cornersG
  pointCompressedDialogGeneric pointDialogGeneric MappedCompressed.pointCompressedArithmetic
  CompressedPointSquare.computableProgram

private theorem equal_simpO [DecidableEq Point] (R C : Point) : pointEqual R C=decide (R=C) := by
  simp only [pointEqual,pointCode_injective.eq_iff]

theorem finiteProgramO_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) :
    Triple (PointDialogBoundary L R b (fun _=>false)) (finiteProgramO L (.some hc) cy Gen)
      (PointDialogBoundary L (if b then R+.some hc else R) b (fun _=>false)) := by
  classical
  let C : Point := .some hc
  let O := dialogInfinity b R
  let D := dialogDouble b R C
  let I := dialogInversePoint b R C
  let H := dialogException b R C
  let G := dialogOrdinary b R C
  let E := b && decide (dialogExceptionEnabled C)
  let K := b && decide (cy≠-cy)
  let S := if b then R+C else R
  have hC : C≠0 := WeierstrassCurve.Affine.Point.some_ne_zero hc
  have hK : K=(b && decide (C≠-C)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [K,Bool.and_eq_true,decide_eq_true_eq]
    exact and_congr_right (fun _=>doubling_enabled_iff hc)
  have hE : exceptionBit C = decide (dialogExceptionEnabled C) := by
    simp [exceptionBit,equal_simpO,dialogExceptionEnabled,Bool.and_assoc]
  have hO : (b && pointEqual R 0)=O := by simp only [O,dialogInfinity,equal_simpO]
  have hD : ((b && decide (cy≠-cy)) && pointEqual R C)=D := by
    change (K && pointEqual R C) = D
    rw [hK]; simp only [D,dialogDouble,equal_simpO]
  have hI : (b && pointEqual R (-C))=I := by simp only [I,dialogInversePoint,equal_simpO]
  have hH : ((b && exceptionBit C) && pointEqual R (dialogExceptionPoint C))=H := by
    rw [hE]; simp [H,dialogException,dialogExceptionEnabled,equal_simpO]
  have h2 := zeroFlag_equalG L hn R b false false false false false false false
  rw [hO,Bool.false_xor] at h2
  have h3 := pairFlag_inputE L hw hn R C cy b false false false O false false false
  rw [hD,hI,Bool.false_xor,Bool.false_xor] at h3
  have h5 := gatedFlag_H L hw hn R (dialogExceptionPoint C) (exceptionBit C) b false D I O false false false
  rw [hH,Bool.false_xor] at h5
  have h6 := genericFlagO_flag L hn R b false D I O false H false
  have hg1 : ((((O ^^ b) ^^ D) ^^ I) ^^ H)=G := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hg1] at h6
  have read := dialogFlagState_read L hn false D I G false H false
  have h7 := hGen R b (dialogFlagState L false D I G false H false)
    (fun hg => ((dialogOrdinary_true b R C hC).mp (read.2.2.2.1.symm.trans hg)).2)
  rw [read.2.2.2.1] at h7
  have h8 := genericFlagO_flag L hn (if G then R+C else R) b false D I G false H false
  have hg2 : ((((G ^^ b) ^^ D) ^^ I) ^^ H)=O := by
    dsimp only [G,dialogOrdinary,O,D,I,H]
    generalize dialogInfinity b R=o,dialogDouble b R C=d,dialogInversePoint b R C=i,
      dialogException b R C=h
    cases b <;> cases o <;> cases d <;> cases i <;> cases h <;> rfl
  rw [hg2] at h8
  have read2 := dialogFlagState_read L hn false D I O false H false
  have h9 := cornersG_boundary L hw hn R C hC b (dialogFlagState L false D I O false H false)
    read2.2.2.2.1 read2.2.1 read2.2.2.1 read2.2.2.2.2.2.1
  have hf := dialogFlags_output b R C
  have heout : ((b && exceptionBit C) && pointEqual S (-C))=H := by
    rw [hE]
    simpa [E,H,S,dialogExceptionEnabled,equal_simpO] using hf.2.2.2
  have h10 := pairFlag_outputO L hw hn S C (exceptionBit C) b false D I O false H false
  rw [heout,Bool.xor_self] at h10
  simp only [equal_simpO] at h10
  rw [hf.1,Bool.xor_self] at h10
  have h11 := gatedFlag_D L hw hn S (C+C) (decide (cy≠-cy)) b false D I false false false false
  have hdo : ((b && decide (cy≠-cy)) && pointEqual S (C+C))=D := by
    change (K && pointEqual S (C+C)) = D
    rw [hK]; simpa only [equal_simpO] using hf.2.1
  rw [hdo,Bool.xor_self] at h11
  have h12 := zeroFlag_equalI L hn S b false false I false false false false
  simp only [equal_simpO] at h12
  rw [hf.2.2.1,Bool.xor_self] at h12
  have h := ((((((((h2.seq h3).seq h5).seq h6).seq h7).seq h8).seq h9).seq h10).seq h11).seq h12
  simpa only [finiteProgramO,List.append_assoc,dialogFlagState_zero] using h

end Spec

/-! ### Static sites: the point, the control, four flags and the pool inventory. -/

def flagsP (L : ControlledPointLayout) : List Wire :=
  [L.doubleSelect, L.genericSelect, L.core.generic, L.core.equalNegY]

def sitesP (L : ControlledPointLayout) : List Wire :=
  PointAddLayout.pointWires L.point ++ [L.control] ++ flagsP L ++ sharedPoolF L

theorem sitesP_length (L : ControlledPointLayout) (hw : L.Widths) : (sitesP L).length = 1894 := by
  simp [sitesP, flagsP, sharedPoolF, PointAddLayout.pointWires, wireBlock_length,
    show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]

section Support
attribute [local irreducible] wires shortEqual pairEqual controlled kernel pointMeasuredSquareCandidate
  CompressedPointSquare.computableProgram pointRecoveryConstantAdd pointRecoveryReflection
variable (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)

theorem point_P (q : Wire) (hq : q ∈ PointAddLayout.pointWires L.point) : q ∈ sitesP L := by
  simp [sitesP, hq]

theorem control_P : L.control ∈ sitesP L := by simp [sitesP]

theorem flag_P (t : Wire) (ht : t ∈ flagsP L) : t ∈ sitesP L := by
  simp only [sitesP, List.mem_append]; exact Or.inl (Or.inr ht)

theorem x_P (q : Wire) (hq : q ∈ L.point.x) : q ∈ sitesP L :=
  point_P L q (by simp [PointAddLayout.pointWires, hq])
theorem y_P (q : Wire) (hq : q ∈ L.point.y) : q ∈ sitesP L :=
  point_P L q (by simp [PointAddLayout.pointWires, hq])
theorem generic_P : L.core.generic ∈ sitesP L := flag_P L _ (by simp [flagsP])

theorem poolQ_P (q : Wire) (hq : q ∈ sharedPoolF L) : q ∈ sitesP L := by
  simp only [sitesP, List.mem_append]; exact Or.inr hq

include hw

theorem pool_lowP (k : Nat) (hk : k ≤ 515) (q : Wire) (hq : q ∈ L.dialogPool.take k) : q ∈ sitesP L := by
  rw [pool_block L hw k (by omega)] at hq
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range'_1] at hi
  apply poolQ_P
  simp only [sharedPoolF, List.mem_append, wireBlock, List.mem_map, List.mem_range'_1]
  exact Or.inl (Or.inl (Or.inl ⟨i, by omega, rfl⟩))

omit hw in
theorem P_of_sites (q : Wire) (hq : q ∈ CompressedPointSquare.residents L ++ CompressedPointSquare.sharedPool L)
    (h1 : q ≠ L.core.poolWire 1801) (h1' : q ≠ L.core.poolWire 1541)
    (h2 : q ≠ L.core.equalX) (h3 : q ≠ L.core.double)
    (h4 : q ≠ L.infinitySelect) : q ∈ sitesP L := by
  rcases List.mem_append.mp hq with hr | hp
  · simp only [CompressedPointSquare.residents, inPlaceFlags, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with (hp | hc) | hf
    · exact point_P L q hp
    · rw [hc]; exact control_P L
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl h4
      · exact flag_P L _ (by simp [flagsP])
      · exact flag_P L _ (by simp [flagsP])
      · exact flag_P L _ (by simp [flagsP])
      · exact absurd rfl h2
      · exact flag_P L _ (by simp [flagsP])
      · exact absurd rfl h3
  · exact poolQ_P L q (sharedPool_F L q hp h1 h1')

theorem pairP (t₁ t₂ : Wire) (h1 : t₁ ∈ flagsP L) (h2 : t₂ ∈ flagsP L) (e₁ e₂ : Bool) (C D : Point) :
    wires (pairEqual L t₁ t₂ e₁ e₂ C D) ⊆ (sitesP L).toFinset := by
  intro q hq
  have h := pairEqual_wires L hw t₁ t₂ e₁ e₂ C D hq
  have hy := yLow_mem L hw
  simp only [List.mem_toFinset, List.mem_cons, List.mem_append, pairSrc] at h
  apply List.mem_toFinset.mpr
  rcases h with rfl | rfl | rfl | rfl | h | h
  · exact control_P L
  · exact y_P L _ hy
  · exact flag_P L _ h1
  · exact flag_P L _ h2
  · exact x_P L _ h
  · exact pool_lowP L hw 256 (by omega) q h

theorem gatedP (en : Bool) (t : Wire) (ht : t ∈ flagsP L) (P : Point) :
    wires (gatedShort L en t P) ⊆ (sitesP L).toFinset := by
  cases en
  · simp [gatedShort, wires]
  · intro q hq
    simp only [gatedShort, if_true] at hq
    have h := shortEqual_wires_subset L hw L.control t P (pointCode P) hq
    rw [equalConstant_wires] at h
    have hp := (zeroPorts_perm (PointAddLayout.pointWires L.point) (L.dialogPool.take 513)
      (by simp [PointAddLayout.pointWires, L.dialogPool_length hw,
        show L.point.x.length = 256 from hw.inputX, show L.point.y.length = 256 from hw.inputY]))
    simp only [List.mem_toFinset, List.mem_cons] at h
    apply List.mem_toFinset.mpr
    rcases h with rfl | rfl | h
    · exact control_P L
    · exact flag_P L _ ht
    · rcases List.mem_append.mp (hp.mem_iff.mp (by simpa [dialogPointZero] using h)) with h' | h'
      · exact point_P L _ h'
      · exact pool_lowP L hw 513 (by omega) _ h'

omit hw in
theorem zeroFlagP (t : Wire) (ht : t ∈ flagsP L) :
    wires (zeroFlag L.point.finite L.control t) ⊆ (sitesP L).toFinset := by
  rw [zeroFlag_wires]
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl
  · exact point_P L _ (by simp [PointAddLayout.pointWires])
  · exact control_P L
  · exact flag_P L _ ht

omit hw in
theorem genericFlagOP : wires (genericFlagO L) ⊆ (sitesP L).toFinset := by
  intro q hq
  simp [genericFlagO, wires, Instr.wires] at hq
  apply List.mem_toFinset.mpr
  rcases hq with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact control_P L
    | exact flag_P L _ (by simp [flagsP])

omit hw in
theorem cornersGP (C : Point) : wires (cornersG L C) ⊆ (sitesP L).toFinset := by
  have m (c : Wire) (hc : c ∈ flagsP L) (P : Point) :
      wires (maskedPointConstant c L.point P) ⊆ (sitesP L).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (maskedPointConstant_support c L.point P hq)
    apply List.mem_toFinset.mpr
    rcases List.mem_cons.mp h with rfl | h
    · exact flag_P L _ hc
    · exact point_P L _ h
  simp only [cornersG, wires_append, Finset.union_subset_iff]
  exact ⟨m _ (by simp [flagsP]) _, m _ (by simp [flagsP]) _, m _ (by simp [flagsP]) _,
    m _ (by simp [flagsP]) _, m _ (by simp [flagsP]) _, m _ (by simp [flagsP]) _⟩

theorem finiteProgramO_support (C : Point) (cy : Fp) (Gen : Program)
    (hG : wires Gen ⊆ (sitesP L).toFinset) :
    wires (finiteProgramO L C cy Gen) ⊆ (sitesP L).toFinset := by
  have fS : flagsP L = [L.doubleSelect, L.genericSelect, L.core.generic, L.core.equalNegY] := rfl
  simp only [finiteProgramO, wires_append, Finset.union_subset_iff]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨zeroFlagP L _ (by simp [fS]), pairP L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _⟩,
    gatedP L hw _ _ (by simp [fS]) _⟩, genericFlagOP L⟩, hG⟩, genericFlagOP L⟩, cornersGP L _⟩,
    pairP L hw _ _ (by simp [fS]) (by simp [fS]) _ _ _ _⟩, gatedP L hw _ _ (by simp [fS]) _⟩,
    zeroFlagP L _ (by simp [fS])⟩

include hn

/-! The generic block's support is the frontier's `fastGenericE`: `sitesP` is the same list as
`sitesE`. -/

theorem fastGenericP (cx cy : Fp) : wires (fastGeneric2 L cx cy) ⊆ (sitesP L).toFinset :=
  fastGenericE L hw hn cx cy

omit hn in
theorem sitesP_used : (sitesP L).toFinset ⊆ L.dialogUsedWires.toFinset := by
  intro q hq
  have h := List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [sitesP, flagsP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [dialogUsedWires, inPlaceFlags, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  rcases h with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · tauto
  · exact Or.inr (sharedPool_Q_sub L hw q h)

end Support

section Frame
attribute [local irreducible] run wires

private theorem frame_valuesO (L : ControlledPointLayout) (P : Program)
    (hP : wires P⊆L.dialogUsedWires.toFinset) (R R' : Point) (b : Bool) (s : State) (m : List Bool)
    (hi : PointDialogBoundary L R b (fun _ => false) s.basis)
    (ho : PointDialogBoundary L R' b (fun _ => false) (run P m s).basis)
    (q : Wire) (hp : q∉PointAddLayout.pointWires L.point) : (run P m s).basis q=s.basis q := by
  by_cases hc : q=L.control
  · subst q; exact ho.control.trans hi.control.symm
  by_cases hf : q∈L.inPlaceFlags
  · exact (ho.flags q hf).trans (hi.flags q hf).symm
  by_cases hw : q∈L.dialogPool
  · exact (regValue_eq_iff _ _ _).mp (ho.clean.trans hi.clean.symm) q hw
  apply run_preserves_outside
  apply mt (@hP q)
  simp [dialogUsedWires,hp,hc,hf,hw]

private theorem work_subsetO (L : ControlledPointLayout) :
    L.inPlaceFlags++L.dialogPool ⊆ L.work := by
  intro q hq
  have h1 := List.count_pos_iff.mpr hq
  have ht := (List.take_sublist 2613 L.core.pool).count_le q
  apply List.count_pos_iff.mp
  simp only [dialogPool,List.count_append] at h1
  simp only [work,outWork,temporary,inPlaceFlags,selectors,PointAddLayout.work,PointAddLayout.words,
    PointAddLayout.flags,List.flatten_cons,List.flatten_nil,List.append_nil,List.count_append,List.count_cons,List.count_nil] at h1 ht ⊢
  omega

private theorem work_not_pointO (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.work) : q∉PointAddLayout.pointWires L.point := by
  intro hp
  have hh := List.nodup_iff_count.mp hn q
  have h1 := List.count_pos_iff.mpr hq
  have h2 := List.count_pos_iff.mpr hp
  simp only [ControlledPointLayout.wires,work,outWork,temporary,point,extras,selectors,PointAddLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at hh h1 h2
  omega

theorem finiteProgramO_full_spec (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Point) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) (b : Bool)
    (Gen : Program) (hGen : GenericOK L hc Gen) (hG : wires Gen ⊆ (sitesP L).toFinset) :
    {{ L.control=b,L.point=R,L.work=0 }} finiteProgramO L (.some hc) cy Gen
    {{ L.control=b,L.point=(if b then R+.some hc else R),L.work=0 }} := by
  intro s m hs
  have hz : regValue L.work s.basis=0 := hs.2
  have clean (q : Wire) (hq : q∈L.inPlaceFlags++L.dialogPool) : s.basis q=false :=
    (regValue_zero _ _).mp hz q (work_subsetO L hq)
  have hi : PointDialogBoundary L R b (fun _ => false) s.basis := by
    refine ⟨hs.1.2,hs.1.1,fun q hq => clean q (by simp [hq]),?_⟩
    · exact (regValue_zero _ _).mpr (fun q hq => clean q (by simp [hq]))
  obtain ⟨hp,ho⟩ := finiteProgramO_spec L hw hn R hc b Gen hGen s m hi
  refine ⟨hp,⟨ho.control,ho.point⟩,?_⟩
  apply (regValue_zero _ _).mpr
  intro q hq
  have hsup := (finiteProgramO_support L hw (.some hc) cy Gen hG).trans (sitesP_used L hw)
  rw [frame_valuesO L _ hsup R _ b s m hi ho q (work_not_pointO L hn q hq)]
  exact (regValue_zero _ _).mp hz q hq

end Frame

section Resources
open Challenge Baselines

theorem finiteProgramO_counts (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) (hc : curve.toAffine.Nonsingular cx cy) (hC : C = .some hc) :
    toffoliCount (finiteProgramO L C cy Gen) ≤ 1030 + toffoliCount Gen ∧
    measurementCount (finiteProgramO L C cy Gen) ≤ 1026 + measurementCount Gen := by
  have p1 := pairEqual_counts L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_counts L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)
  have c1 : tailCost (decide (cy≠-cy)) (yBit C) true (yBit (-C)) = 1 := by
    subst hC
    rw [cy_ne_neg hc, yBit_neg hc]
    cases yBit (.some hc) <;> decide
  have c2 : tailCost true (yBit C) (exceptionBit C) (yBit (-C)) ≤ 1 := by
    subst hC
    rw [yBit_neg hc]
    cases yBit (.some hc) <;> cases exceptionBit (.some hc) <;> decide
  have g1 := gatedShort_counts L hw (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C)
  have g2 := gatedShort_counts L hw (decide (cy≠-cy)) L.doubleSelect (C+C)
  have z1 := zeroFlag_counts L.point.finite L.control L.core.generic
  have z2 := zeroFlag_counts L.point.finite L.control L.genericSelect
  have f : toffoliCount (genericFlagO L) = 0 ∧ measurementCount (genericFlagO L) = 0 := by
    simp [genericFlagO, toffoliCount, measurementCount]
  have c : toffoliCount (cornersG L C) = 0 ∧ measurementCount (cornersG L C) = 0 := by
    simp only [cornersG, toffoliCount_append, measurementCount_append,
      (maskedPointConstant_counts _ _ _).1, (maskedPointConstant_counts _ _ _).2]
    decide
  simp only [finiteProgramO, toffoliCount_append, measurementCount_append]
  rw [c1] at p1
  omega

theorem finiteProgramO_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (C : Point) (cy : Fp) (Gen : Program) (hG : GatePhysical Gen) :
    GatePhysical (finiteProgramO L C cy Gen) := by
  have sep := dialogFlag_separation (L:=L) hn
  have hz (t : Wire) (ht : t∈L.inPlaceFlags) : GatePhysical (zeroFlag L.point.finite L.control t) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    have hnd := L.dialogPointZero_nodup hn L.control t hct (Or.inl rfl) ht
    simp only [PointAddLayout.pointWires, List.cons_append, List.nodup_cons, List.mem_cons,
      List.mem_append, not_or] at hnd
    exact zeroFlag_physical _ _ _ (fun h => hnd.2.1.1 h.symm) hct
  have hg (en : Bool) (t : Wire) (ht : t∈L.inPlaceFlags) (P : Point) : GatePhysical (gatedShort L en t P) := by
    have hct : L.control ≠ t := by
      intro h
      exact (List.nodup_cons.mp sep).1 (h ▸ ht)
    cases en
    · simp [gatedShort, GatePhysical]
    · simpa only [gatedShort, if_true] using shortEqual_physical L hw hn L.control t hct (Or.inl rfl) ht P
  have away (c : Wire) (hc : c ∈ L.inPlaceFlags) : c ∉ PointAddLayout.pointWires L.point := by
    intro hm
    have h := List.nodup_iff_count.mp (L.dialogUsed_nodup hn) c
    have hf := List.count_pos_iff.mpr hc
    have hp := List.count_pos_iff.mpr hm
    simp only [dialogUsedWires,List.count_append,List.count_cons] at h
    omega
  have mk (c : Wire) (hc : c ∈ L.inPlaceFlags) (D : Point) : GatePhysical (maskedPointConstant c L.point D) :=
    maskedPointConstant_physical c L.point D (away c hc)
  have co : GatePhysical (cornersG L C) := by
    simp only [cornersG, gatePhysical_append]
    exact ⟨mk _ (by simp [inPlaceFlags]) _, mk _ (by simp [inPlaceFlags]) _, mk _ (by simp [inPlaceFlags]) _,
      mk _ (by simp [inPlaceFlags]) _, mk _ (by simp [inPlaceFlags]) _, mk _ (by simp [inPlaceFlags]) _⟩
  have z1 := hz L.core.generic (by simp [inPlaceFlags])
  have z2 := hz L.genericSelect (by simp [inPlaceFlags])
  simp only [inPlaceFlags, List.nodup_cons, List.mem_cons, not_or] at sep
  have fl : GatePhysical (genericFlagO L) := by
    simp_all [genericFlagO, GatePhysical, RecordedQuantum.PhysicalInstr, ProperGate, ne_comm]
  have q3 := hg (exceptionBit C) L.core.equalNegY (by simp [inPlaceFlags]) (dialogExceptionPoint C)
  have q5 := hg (decide (cy≠-cy)) L.doubleSelect (by simp [inPlaceFlags]) (C+C)
  have p1 := pairEqual_physical L hw hn L.doubleSelect L.genericSelect (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) (decide (cy≠-cy)) true C (-C)
  have p2 := pairEqual_physical L hw hn L.core.generic L.core.equalNegY (by simp [inPlaceFlags])
    (by simp [inPlaceFlags]) (by tauto) true (exceptionBit C) C (-C)
  simp only [finiteProgramO, gatePhysical_append]
  tauto

theorem finiteProgramO_gateSlots (L : ControlledPointLayout) (hw : L.Widths) (C : Point) (cy : Fp)
    (Gen : Program) : gateSlots (finiteProgramO L C cy Gen) ≤ 20000 + gateSlots Gen := by
  have hx : L.point.x.length = 256 := hw.inputX
  have hy : L.point.y.length = 256 := hw.inputY
  have hm c P : gateSlots (maskedPointConstant c L.point P) ≤ 513 := by
    have h := maskedPoint_gateSlots_le c L.point P
    rw [hx,hy] at h; exact h
  have hf : gateSlots (genericFlagO L) = 4 := rfl
  have hzf (t : Wire) : gateSlots (zeroFlag L.point.finite L.control t) = 3 := rfl
  have hgs (en : Bool) (t : Wire) (P : Point) : gateSlots (gatedShort L en t P) ≤ 2314 := by
    cases en
    · simp [gatedShort]
    · simpa only [gatedShort, if_true] using shortEqual_gateSlots_le L hw L.control t P
  have z2 := pairEqual_gateSlots_le L hw L.doubleSelect L.genericSelect (decide (cy≠-cy)) true C (-C)
  have z4 := hgs (exceptionBit C) L.core.equalNegY (dialogExceptionPoint C)
  have z5 := pairEqual_gateSlots_le L hw L.core.generic L.core.equalNegY true (exceptionBit C) C (-C)
  have z6 := hgs (decide (cy≠-cy)) L.doubleSelect (C+C)
  have m1 := hm L.core.generic C
  have m2 := hm L.doubleSelect C
  have m3 := hm L.doubleSelect (C+C)
  have m4 := hm L.genericSelect (-C)
  have m5 := hm L.core.equalNegY (dialogExceptionPoint C)
  have m6 := hm L.core.equalNegY (-C)
  simp only [finiteProgramO, cornersG, gateSlots_append, hf, hzf]
  omega

end Resources

end ECDSAAdd.Entrant
