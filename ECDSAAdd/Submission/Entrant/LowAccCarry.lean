import ECDSAAdd.Submission.Entrant.LowAccLoop
namespace ECDSAAdd.Entrant.LowAccCarryDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop FourthASavedCarryDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
def fromLiteral (cm : ZeroSetDevelop.CheckedS hosts88 BData301.p0) :
 ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c) :=
 ⟨cm.out, Eq.mp (congrArg (fun p=>ZeroSetDevelop.SRewrites hosts88 p cm.out)
  (show BData301.p0=FullBTemp.middle L c from FullBReady.onePass_input_eq)) cm.proof⟩

open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
open LowBitCarryDevelop ParkCarry7Develop ParkCarry10Develop

def foldFor (L : CuccaroStreamedSquareWideLayout) (loop : Program) : Program :=
 eAddLo L ++ (loop ++ (ParkCarryDevelop.program (eU L) L.core.sumCarry ++ eSubK L))
def bodyFor (L : CuccaroStreamedSquareWideLayout) (c : Wire) (loop : Program) : Program :=
 measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++
  (foldFor L loop ++ (eFoldTq L c ++ ParkCarry10Develop.rebuild L)))

theorem body_frame_generic
 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hcw : c∉L.wires) (loopProgram : Program)
 (loopSpec : ∀ (base : BasisState) (clean : L.PairClean base) (hsum : base L.core.sumCarry=false)
  (O E O' : Nat),
  Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (FullBTemp.middle L c)
   (BState L base O' E (4294968272*regValue (hiReg L) base)) →
  Triple (BState L base O E 0) loopProgram (BState L base O' E 0))
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyFor L c loopProgram)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by

  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0


  let u := b1/2^96
  let d := W/2^128 - u
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  let kap:Bool:=decide (K=1)
  let baseK:=writeBit base L.core.sumCarry kap
  have kapNat:kap.toNat=K := by
    have kk:K=0 ∨ K=1 := by omega
    rcases kk with kk|kk <;> simp [kap,kk]
  have hcK:L.PairClean baseK := ParkCarryDevelop.base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply ParkCarryDevelop.sumCarry_away L hn;simp [ParkCarryDevelop.restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [ParkCarryDevelop.reg_update_off _ _ _ _ highOff]
    exact hb1
  have cq:c≠L.core.sumCarry := by
    intro h;apply hcw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have gc:baseK c=base c := by simp [baseK,writeBit,cq]
  have resetBase:writeBit baseK L.core.sumCarry false=base := by
    funext q
    by_cases hq:q=L.core.sumCarry
    · subst q;simp [writeBit,Function.update,hsum]
    · simp [baseK,writeBit,Function.update,hq]
  -- Park the completed low-window carry instead of recomputing it.
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have squareBit : (b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw[Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have loanFact : ((2^32*H+l'+2^128*K)/2%2==1)=
      ((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
        ((b1/2^96%2==1)&&((2^32*H+l'+2^128*K)%2==1))) := by
    have low0:(2^32*H+l'+2^128*K)%2=(b0%2^32+u)%2:=by dsimp[l'];omega
    have low1:(2^32*H+l'+2^128*K)/2%2=(b0%2^32+u)/2%2:=by dsimp[l'];omega
    rw[low0,low1]
    exact known_second_loan (b0%2^32) u squareBit
  let originalM:=regValue L.core.high base
  have source1:base (bit1 L.core.high)=digit originalM 1:=by
    simpa only[digit,pow_one]using bit1_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE:(2^32*H+l'+2^128*K)%16=lowSum (base c) originalM u%16:=by
    rw[lowSum,←hSource]
    exact folded_low_mod16 M u H l' K rfl rfl
  have loanFact2:=loan2_from_mod16 (base c) originalM u (2^32*H+l'+2^128*K) modE
  rw[←source1]at loanFact2
  have source0:base (L.core.high.headD 0)=digit originalM 0:=by
    simpa only[digit,pow_zero,Nat.div_one]using head_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE2:(2^32*H+l'+2^128*K)%2=lowSum (base c) originalM u%2:=by omega
  have loanFact0:=LowBitCarryNumbers.loan0_from_mod2 (base c) originalM u (2^32*H+l'+2^128*K)
    (by simpa only[lowSum]using modE2)
  rw[←source0]at loanFact0
  have wm := wMidFullCCC0_step L hw hn c hcw base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact loanFact2 loanFact0
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCCC0 L c)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    simpa only [hb1] using wm
  have loop := loopSpec base hc hsum
    O2 (2^32*H+l'+2^128*K) O3 wmBase
  have kc:=ParkCarryDevelop.park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (foldFor L loopProgram) (BState L baseK O3 E1 0) :=
    by simpa only [foldFor,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
  -- eFoldTq
  have f1 := eFlip_step L hw hn baseK c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn baseK hcK O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn baseK c hcw O4 (flipE g E1) 0
  rw [gc] at f1 f3
  rw [flipE_flipE] at f3
  have tf : Triple (BState L baseK O3 E1 0) (eFoldTq L c) (BState L baseK O4 E1 0) :=
    f1.seq (f2.seq f3)
  -- wRestoreT
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn baseK hcK O4 E1 0 b1 hb1K (by rw [bk]; omega)
  rw [bk] at r2
  have bit32:(b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have total:l'+2^32*(baseK L.core.sumCarry).toNat=b0%2^32+regValue (hiReg L) baseK/2^96 := by
    have atq:baseK L.core.sumCarry=kap := by simp [baseK,writeBit]
    rw [atq,kapNat,hb1K]
    show ((b0%2^32+u)%2^32)+2^32*((b0%2^32+u)/2^32)=b0%2^32+u
    exact Nat.mod_add_div _ _
  have r3:=ParkCarryDevelop.restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 744
  have tr : Triple (BState L baseK O4 E1 0) (ParkCarry10Develop.rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have conv0 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tf.seq tr)) conv0))
  rw [key] at all
  simpa only [bodyFor] using all




theorem body_frame
 (cm : ZeroSetDevelop.CheckedS hosts88 (FullBTemp.middle L c))
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0) :
 Triple (SquareFrame L.core.out base O) (bodyWith cm)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) :=
 by
  have hcw : c∉L.wires := control_outside
  simpa only [bodyWith,foldWith,bodyFor,foldFor] using
   body_frame_generic L layout_widths layout_nodup c hcw (loopWith cm) (loop_bstate_step cm)
    base M hM hP hc hsum O hO hg hSource



end ECDSAAdd.Entrant.LowAccCarryDevelop
namespace ECDSAAdd.Entrant.FullB88OptTemp
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.Arithmetic.GatePhysical
attribute [local irreducible] ZeroSetDevelop.compileS? ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots ECDSAAdd.regValue
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem option_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hf : P fallback) (hb : ∀a,P (body a)) (result : Option α) : P (result.elim fallback body) := by
 cases result with
 | none => exact hf
 | some a => exact hb a

theorem option_some_property {α : Type} (P : Program → Prop) (fallback : Program) (body : α → Program)
 (hb : ∀a,P (body a)) (result : Option α) (success : result.isSome=true) : P (result.elim fallback body) := by
 cases result with
 | none => simp only [Option.isSome_none,Bool.false_eq_true] at success
 | some a => exact hb a

theorem option_map_success {α β : Type} (result : Option α) (f : α → β) :
 (result.map f).isSome=result.isSome := by
 cases result <;> rfl

theorem actual_resources :
 toffoliCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)+88≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 measurementCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 Challenge.gateSlots (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)+264≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_some_property (fun p=>
  toffoliCount p+88≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  measurementCount p=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
  Challenge.gateSlots p+264≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith LowAccCarryDevelop.body_resources ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)
  ((option_map_success (ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0) LowAccCarryDevelop.fromLiteral).trans LowAccCarryDevelop.success_literal)

theorem actual_subset : wires (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 exact option_property (fun p=>wires p⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))
  (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith (Finset.Subset.refl (wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c))) LowAccCarryDevelop.body_support ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_physical : GatePhysical (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := by
 exact option_property GatePhysical (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith
  (ParkCarry10Develop.body_physical LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.c LowAccCarryDevelop.layout_control_nodup)
  LowAccCarryDevelop.body_physical ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

theorem actual_frame (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue LowAccCarryDevelop.L.core.product base=M^2) (hc : LowAccCarryDevelop.L.PairClean base)
 (hsum : base LowAccCarryDevelop.L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base LowAccCarryDevelop.c=false → M=0)
 (hSource : M=if base LowAccCarryDevelop.c then regValue LowAccCarryDevelop.L.core.high base else 0) :
 Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O)) := by
 exact option_property (fun p=>Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) p
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O))) (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith
  (ParkCarry10Develop.body_frame LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths
   LowAccCarryDevelop.layout_nodup LowAccCarryDevelop.c LowAccCarryDevelop.control_outside
   base M hM hP hc hsum O hO hg hSource)
  (fun cm=>LowAccCarryDevelop.body_frame cm base M hM hP hc hsum O hO hg hSource) ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral)

def selectedBody (K : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 match FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse _ => ParkCarry10Develop.body K g
 | isTrue _ => if g=LowAccCarryDevelop.c then (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) else ParkCarry10Develop.body K g

theorem selected_body_transport (K K' : CuccaroStreamedSquareWideLayout) (g g' : Wire)
 (he : K=K') (hg : g=g') : selectedBody K g=selectedBody K' g' := by
 cases he
 cases hg
 rfl

def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem selected_subset (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 wires (selectedBody K g)⊆wires (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact Finset.Subset.refl _
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_subset
  · exact Finset.Subset.refl _

theorem selected_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) : wires (selectedBody L c)⊆(c::L.wires).toFinset :=
 (selected_subset L hw c).trans (ParkCarry10Develop.body_support L hw hn c)

theorem selected_physical (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths)
 (g : Wire) (nd : (g::K.wires).Nodup) : GatePhysical (selectedBody K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ParkCarry10Develop.body_physical K hw g nd
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_physical
  · exact ParkCarry10Develop.body_physical K hw g nd

theorem selected_frame (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (hn : K.wires.Nodup)
 (g : Wire) (hcw : g∉K.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue K.core.product base=M^2) (hc : K.PairClean base)
 (hsum : base K.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base g=false → M=0) (hSource : M=if base g then regValue K.core.high base else 0) :
 Triple (SquareFrame K.core.out base O) (selectedBody K g)
  (SquareFrame K.core.out base (bO4 (M^2) (base g) O)) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hne => exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource
 | isTrue hl =>
  dsimp only
  split
  · rename_i hgc;subst K;subst g;exact actual_frame base M hM hP hc hsum O hO hg hSource
  · exact ParkCarry10Develop.body_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource

theorem selected_resources (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 toffoliCount (selectedBody K g)≤toffoliCount (ParkCarry10Develop.body K g) ∧
 measurementCount (selectedBody K g)=measurementCount (ParkCarry10Develop.body K g) ∧
 Challenge.gateSlots (selectedBody K g)≤Challenge.gateSlots (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g
    have h:=actual_resources
    exact ⟨by omega,h.2.1,by omega⟩
  · exact ⟨Nat.le_refl _,rfl,Nat.le_refl _⟩

theorem hostedSelectedBody_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
 (c : Wire) (fixed : rho L.core.sumCarry=L.core.sumCarry) :
 hostedSelectedBody L rho c=selectedBody L c :=
 congrArg (fun K=>selectedBody K c) (ParkCarryDevelop.host_eq L rho fixed)

theorem hosted_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedSelectedBody L rho c)≤toffoliCount (ParkCarry10Develop.hostedBody L rho c) ∧
 measurementCount (hostedSelectedBody L rho c)=measurementCount (ParkCarry10Develop.hostedBody L rho c) ∧
 Challenge.gateSlots (hostedSelectedBody L rho c)≤Challenge.gateSlots (ParkCarry10Develop.hostedBody L rho c) :=
 selected_resources (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 wires (hostedSelectedBody L rho c)⊆wires (ParkCarry10Develop.hostedBody L rho c) :=
 selected_subset (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen : 300≤ext.length)
 (away : ∀q∈ext,q∉L.wires) :
 wires (hostedSelectedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
 rw [hostedSelectedBody_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact selected_support L hw hn c

abbrev actualLayout := FullBOptTemp.actualLayout
abbrev actualControl := FullBOptTemp.actualControl
abbrev actualExt := FullBOptTemp.actualExt
abbrev actualFoldPerm := FullBOptTemp.actualFoldPerm

theorem selected_actual : selectedBody LowAccCarryDevelop.L LowAccCarryDevelop.c=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq LowAccCarryDevelop.L LowAccCarryDevelop.L with
 | isFalse hn => exact False.elim (hn rfl)
 | isTrue hl => exact if_pos rfl

theorem ranked_selected_exact : hostedSelectedBody actualLayout actualFoldPerm actualControl=(((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := by
 have he : ParkCarryDevelop.hostLayout actualLayout actualFoldPerm=actualLayout :=
  FullBOptTemp.actualHostedLayout_eq
 exact (congrArg (fun K=>selectedBody K actualControl) he).trans
  ((selected_body_transport actualLayout LowAccCarryDevelop.L actualControl LowAccCarryDevelop.c rfl rfl).trans selected_actual)

theorem ranked_certified_gain :
 toffoliCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)+88≤4762 ∧
 measurementCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)=5924 := by
 rw [ranked_selected_exact]
 have h:=actual_resources
 have old:=ParkCarry10Develop.body_counts LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.c
 exact ⟨h.1.trans old.1.le,h.2.1.trans old.2⟩

end ECDSAAdd.Entrant.FullB88OptTemp
