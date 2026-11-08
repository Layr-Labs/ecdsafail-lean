-- Includes selected declarations adapted from public submission 752224eb-97a1-4267-9d0f-5b34615ef093.
import ECDSAAdd.Submission.Entrant.SecondCarryLoan
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
namespace ECDSAAdd.Entrant.ParkCarry5Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open CarryWindowCache SecondCarryLoan ParkCarryDevelop
abbrev restWires:=ParkCarryDevelop.restWires
abbrev sumCarry_away:=@ParkCarryDevelop.sumCarry_away
abbrev sumCarry_off_regs:=@ParkCarryDevelop.sumCarry_off_regs
abbrev hostLayout:=ParkCarryDevelop.hostLayout
abbrev host_widths:=@ParkCarryDevelop.host_widths
abbrev host_eq:=@ParkCarryDevelop.host_eq
abbrev ExtraLe:=ParkCarryDevelop.ExtraLe

def fold (L:CuccaroStreamedSquareWideLayout):Program:=
 eAddLo L++(InverseCarryDevelop.buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
  (wMidFullCC L++(InverseCarryDevelop.unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
  (program (eU L) L.core.sumCarry++eSubK L))))
def rebuild (L:CuccaroStreamedSquareWideLayout):Program:=eAddB L++(restore L++padM L 748)
def body (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(fold L++(eFoldTq L c++rebuild L)))
theorem middle_delta (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 toffoliCount (wMidFullCC L)+5=toffoliCount (wFwdK L++(wCoreK L++wInvK L)) ∧
 measurementCount (wMidFullCC L)=measurementCount (wFwdK L++(wCoreK L++wInvK L))+3 ∧
 Challenge.gateSlots (wMidFullCC L)+13=Challenge.gateSlots (wFwdK L++(wCoreK L++wInvK L)):=by
 have a:=SecondCarryLoan.midCC_counts L hw
 have b:=CarryWindowCache.mid_counts L hw
 exact ⟨by omega,by omega,by omega⟩

theorem cached_loop_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 toffoliCount (InverseCarryDevelop.buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)=
   toffoliCount (wBuild L) ∧
 measurementCount (InverseCarryDevelop.buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)=
   measurementCount (wBuild L) ∧
 Challenge.gateSlots (InverseCarryDevelop.buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)=
   Challenge.gateSlots (wBuild L)+1 ∧
 toffoliCount (InverseCarryDevelop.unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)+1=
   toffoliCount (wUnbuildKnown L) ∧
 measurementCount (InverseCarryDevelop.unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)=
   measurementCount (wUnbuildKnown L) ∧
 Challenge.gateSlots (InverseCarryDevelop.unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)+4=
   Challenge.gateSlots (wUnbuildKnown L):=by
 have lens:=acc_lengths L hw
 have wb:=InverseCarryDevelop.buildCached_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
   lens.1 (hiReg_length L hw) (by omega) (by omega)
 have wu:=InverseCarryDevelop.unbuildConsumed_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
   lens.1 (hiReg_length L hw) (by omega)
 exact ⟨wb.1,wb.2.1,wb.2.2,wu.1,wu.2.1,wu.2.2⟩

theorem body_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 toffoliCount (body L c)=4765 ∧ measurementCount (body L c)=5924:=by
 have base:=ParkCarryDevelop.body_counts L hw c
 have mid:=middle_delta L hw
 have p:=padM_counts L 748
 have q:=padM_counts L 751
 have lc:=cached_loop_counts L hw
 simp only[toffoliCount_append,measurementCount_append]at mid
 simp only[body,fold,rebuild,ParkCarryDevelop.body,ParkCarryDevelop.fold,ParkCarryDevelop.rebuild,
  toffoliCount_append,measurementCount_append]at base ⊢
 exact ⟨by omega,by omega⟩

theorem body_slots (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 Challenge.gateSlots (body L c)+19=Challenge.gateSlots (ParkCarryDevelop.body L c):=by
 have lc:=cached_loop_counts L hw
 have m:=(middle_delta L hw).2.2
 have p:=padM_slots L 748
 have q:=padM_slots L 751
 simp only[Challenge.gateSlots_append]at m
 simp only[body,fold,rebuild,ParkCarryDevelop.body,ParkCarryDevelop.fold,ParkCarryDevelop.rebuild,
  Challenge.gateSlots_append]
 omega

theorem body_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (hn:(c::L.wires).Nodup):GatePhysical (body L c):=by
 have h:=ParkCarryDevelop.body_physical L hw c hn
 have nd:=(List.nodup_cons.mp hn).2
 have hcw:=(List.nodup_cons.mp hn).1
 have off:=b_wloop_sumCarry_free L hw nd c hcw
 have lens:=acc_lengths L hw
 simp only[ParkCarryDevelop.body,ParkCarryDevelop.fold,ParkCarryDevelop.rebuild,gatePhysical_append]at h
 have wbNew:=InverseCarryDevelop.buildCached_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
   lens.1 (hiReg_length L hw) (by omega) (by omega) off.1 h.2.2.1.2.1
 have wuNew:=InverseCarryDevelop.unbuildConsumed_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
   lens.1 (hiReg_length L hw) (by omega) off.2.2 (wUnbuildKnown_physical L hw nd)
 simp only[body,fold,rebuild,gatePhysical_append]
 exact ⟨h.1,h.2.1,⟨h.2.2.1.1,wbNew,SecondCarryLoan.midCC_physical L hw nd,
  wuNew,h.2.2.1.2.2.2.2⟩,h.2.2.2.1,⟨h.2.2.2.2.1,h.2.2.2.2.2.1,padM_physical L 748⟩⟩
theorem body_le_extra (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
    ExtraLe L.core.sumCarry (body L c) (bBody L c) := by
  have tailWires : wires (fold L ++ (eFoldTq L c ++ rebuild L)) ⊆
      insert L.core.sumCarry (wires (wFold L ++ (eFold L c ++ wRestore L))) := by
    have wc := (QRel.qprog_le (rotWCore L) 256 SquareReduction.p (rotWCore_widths L hw) (by decide)).1
    have ef := (QRel.eFold_le L hw c).1
    have sk := eSubK_wires L hw
    have ab := eAddB_wires L hw
    have ml {A B : Program} {q : Wire} (h : q ∈ wires A) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_left _ h
    have mr {A B : Program} {q : Wire} (h : q ∈ wires B) : q ∈ wires (A ++ B) := by
      rw [wires_append]; exact Finset.mem_union_right _ h
    have hOE {q : Wire} (h : q ∈ oldE L) : q ∈ wires (wFold L ++ (eFold L c ++ wRestore L)) := by
      rcases Finset.mem_union.mp h with h|h
      · exact ml (mr (mr (ml h)))
      · exact ml (mr (mr (mr (ml h))))
    have lens:=acc_lengths L hw
    have wbSupport:=InverseCarryDevelop.buildCached_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
      lens.1 (hiReg_length L hw) (by omega) (by omega)
    have wuSupport:=InverseCarryDevelop.unbuildConsumed_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
      lens.1 (hiReg_length L hw) (by omega)
    change wires (InverseCarryDevelop.buildCached _ _ _ _ _ _)⊆insert L.core.sumCarry (wires (wBuild L)) at wbSupport
    change wires (InverseCarryDevelop.unbuildConsumed _ _ _ _ _ _)⊆insert L.core.sumCarry (wires (wUnbuildKnown L)) at wuSupport
    intro q hq
    by_cases spare:q=L.core.sumCarry
    · exact Finset.mem_insert.mpr (Or.inl spare)
    apply Finset.mem_insert_of_mem
    simp only [fold, wMidFullCC, wCoreK, rebuild, wires_append, Finset.mem_union] at hq
    rcases hq with (h | h | (h | ((h | (h | h | h) | h) | h)) | h | h | h) | h | h | h | h
    · exact hOE (eAddLo_oldE L hw h)
    · have hh:=Finset.mem_insert.mp (wbSupport h)
      rcases hh with hh|hh
      · exact False.elim (spare hh)
      · exact ml (ml hh)
    · exact hOE ((endsCC_oldE L hw).1 h)
    · exact hOE ((armsCC_oldE L hw).1 h)
    · exact hOE (kw_oldE L hw h)
    · exact ml (mr (ml (wc h)))
    · exact hOE (kw_oldE L hw h)
    · exact hOE ((armsCC_oldE L hw).2 h)
    · exact hOE ((endsCC_oldE L hw).2 h)
    · have hh:=Finset.mem_insert.mp (wuSupport h)
      rcases hh with hh|hh
      · exact False.elim (spare hh)
      · exact ml (mr (mr (mr (mr (wUnbuildKnown_wires L hw hh)))))
    · have hh:q=eU L ∨ q=L.core.sumCarry := by simpa [ParkCarryDevelop.program,wires,Instr.wires,or_comm] using h
      rcases hh with hh|hh
      · apply hOE
        exact oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl (hh ▸ (eK_mem L hw).2.1)))))
      · exact False.elim (spare hh)
    · exact ml (mr (mr (ml (sk h))))
    · exact mr (ml (ef h))
    · exact mr (mr (mr (mr (ml (ab h)))))
    · have hh:=(restore_resources L hw).2.2.1 h
      rcases Finset.mem_insert.mp hh with hh|hh
      · exact False.elim (spare hh)
      · exact hOE hh
    · exact hOE (padM_oldE L hw 748 h)
  refine ⟨?_, ?_⟩
  · have a := (QRel.measuredFoldQ_le L hw (negP L)).1
    have b := (QRel.measuredFoldQ_le L hw (rot128F L)).1
    intro q hq
    change q ∈ wires (measuredFoldQTq L (negP L) ++ (measuredFoldQTq L (rot128F L) ++ (fold L ++ (eFoldTq L c ++ rebuild L)))) at hq
    rw [wires_append] at hq
    rcases Finset.mem_union.mp hq with h|h
    · apply Finset.mem_insert_of_mem
      change q ∈ wires (measuredFoldQ L (negP L) ++ (measuredFoldQ L (rot128F L) ++ (wFold L ++ (eFold L c ++ wRestore L))))
      rw [wires_append];exact Finset.mem_union_left _ (a h)
    · rw [wires_append] at h
      rcases Finset.mem_union.mp h with h|h
      · apply Finset.mem_insert_of_mem
        change q ∈ wires (measuredFoldQ L (negP L) ++ (measuredFoldQ L (rot128F L) ++ (wFold L ++ (eFold L c ++ wRestore L))))
        rw [wires_append];apply Finset.mem_union_right
        rw [wires_append];exact Finset.mem_union_left _ (b h)
      · have t := tailWires h
        rcases Finset.mem_insert.mp t with t|t
        · exact Finset.mem_insert.mpr (Or.inl t)
        · apply Finset.mem_insert_of_mem
          change q ∈ wires (measuredFoldQ L (negP L) ++ (measuredFoldQ L (rot128F L) ++ (wFold L ++ (eFold L c ++ wRestore L))))
          rw [wires_append];apply Finset.mem_union_right
          rw [wires_append];exact Finset.mem_union_right _ t
  · have delta:=body_slots L hw c
    have old:=(ParkCarryDevelop.body_le_extra L hw c).2
    omega

theorem body_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (c : Wire) : wires (body L c)⊆(c::L.wires).toFinset := by
  intro q hq
  have h:=(body_le_extra L hw c).1 hq
  rcases Finset.mem_insert.mp h with h|h
  · simp only [List.mem_toFinset,List.mem_cons]
    right
    rw [h]
    simp [Arithmetic.CuccaroStreamedSquareWideLayout.wires,Arithmetic.CuccaroStreamedSquareLayout.wires]
  · exact (bBody_support L hw hn c) h

theorem mid_replace (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    wMidFullCC {L with core:={L.core with sumCarry:=q} }=wMidFullCC L := by rfl

theorem mid_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn:L.wires.Nodup) (c : Wire) (hc:c∉L.wires) : L.core.sumCarry∉wires (wMidFullCC L) := by
  let N:CuccaroStreamedSquareWideLayout:={L with core:={L.core with sumCarry:=c} }
  have zm:L.core.sumCarry∈L.wires := by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
  have cz:c≠L.core.sumCarry := by intro h;apply hc;simpa [h] using zm
  have cw:(L.wires).count c=0 := List.count_eq_zero.mpr hc
  have nd:N.wires.Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro q
    have old:=List.nodup_iff_count_le_one.mp hn q
    simp only [N,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_iff_eq] at cw old ⊢
    by_cases h:q=c
    · subst q
      simp only [if_true] at cw ⊢
      omega
    · simp only [if_neg (Ne.symm h)]
      omega
  have nw: L.core.sumCarry∉N.wires := by
    intro hm
    have pos:=List.count_pos_iff.mpr hm
    have old:=List.nodup_iff_count_le_one.mp hn L.core.sumCarry
    simp only [N,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil,beq_iff_eq] at pos old
    simp only [if_true,if_neg cz] at pos old
    omega
  have wn:N.Widths := ⟨⟨hw.core.y,hw.core.out,hw.core.product,hw.core.pad,hw.core.work⟩,hw.overflowPad⟩
  have support:=body_support N wn nd c
  intro hm
  rw [←mid_replace L c] at hm
  have hb:L.core.sumCarry∈wires (body N c) := by
    show L.core.sumCarry∈wires (measuredFoldQTq N (negP N)++(measuredFoldQTq N (rot128F N)++(fold N++(eFoldTq N c++rebuild N))))
    rw [wires_append];apply Finset.mem_union_right
    rw [wires_append];apply Finset.mem_union_right
    rw [wires_append];apply Finset.mem_union_left
    unfold ParkCarry5Develop.fold
    rw [wires_append];apply Finset.mem_union_right
    rw [wires_append];apply Finset.mem_union_right
    rw [wires_append];apply Finset.mem_union_left
    exact hm
  have h:=support hb
  simp only [List.mem_toFinset,List.mem_cons] at h
  exact h.elim (fun h=>cz h.symm) nw

theorem body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (body L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
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
  have hcK:L.PairClean baseK := base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply sumCarry_away L hn;simp [restWires,ParkCarryDevelop.restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [reg_update_off _ _ _ _ highOff]
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
  have wm := wMidFullCC_step L hw hn base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCC L)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    rw [hb1]; exact wm
  have off:=b_wloop_sumCarry_free L hw hn c hcw
  have loop:=InverseCarryDevelop.cached_wloop_bstate_step L hw hn base hc hsum O2 (2^32*H+l'+2^128*K) O3
    (wMidFullCC L) wmBase off.1 (mid_sumCarry_free L hw hn c hcw) off.2.2
  have kc:=park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (fold L) (BState L baseK O3 E1 0) :=
    by simpa only [fold,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
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
  have r3:=restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 748
  have tr : Triple (BState L baseK O4 E1 0) (rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have conv2 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
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
    (tf.seq tr)) conv2))
  rw [key] at all
  exact all

theorem body_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c : Wire) :
    toffoliCount (body L c)+1058=toffoliCount (bBody L c) ∧
    measurementCount (body L c)+4=measurementCount (bBody L c) ∧
    ExtraLe L.core.sumCarry (body L c) (bBody L c) := by
  have current:=body_counts L hw c
  have preceding:=bBody_countsTq L hw c
  have old:=QRel.bBody_rel L hw c
  exact ⟨by omega,by omega,body_le_extra L hw c⟩

def hostedBody (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire):Program:=body (hostLayout L rho) c

theorem hosted_rel (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 toffoliCount (hostedBody L rho c)+1058=toffoliCount (bBody L c) ∧
 measurementCount (hostedBody L rho c)+4=measurementCount (bBody L c) ∧
 ExtraLe (rho.symm L.core.sumCarry) (hostedBody L rho c) (bBody L c):=by
 have h:=body_rel (hostLayout L rho) (host_widths L hw rho) c
 simpa only[hostedBody,ParkCarryDevelop.oldBody_host,ParkCarryDevelop.hostLayout]using h

theorem hosted_eq (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire)
 (h:rho L.core.sumCarry=L.core.sumCarry):hostedBody L rho c=body L c:=by
 change body (ParkCarryDevelop.hostLayout L rho) c=body L c
 rw[ParkCarryDevelop.host_eq L rho h]

theorem hosted_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 toffoliCount (hostedBody L rho c)=4765 ∧ measurementCount (hostedBody L rho c)=5924:=
 body_counts (hostLayout L rho) (host_widths L hw rho) c
#print axioms body_frame
#print axioms body_counts
#print axioms body_physical
#print axioms body_le_extra
#print axioms hosted_rel
end ECDSAAdd.Entrant.ParkCarry5Develop
