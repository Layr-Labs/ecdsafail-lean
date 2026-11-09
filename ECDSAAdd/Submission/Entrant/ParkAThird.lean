import ECDSAAdd.Submission.Entrant.MainPart04Base

-- Third retained inverse W carry, using the always-zero square product bit 1 in the A leaf.
-- The old first two retained carries and A body are inherited from our published nine-host source.
-- New symbolic protocols, lifetime proofs, resource statements and A-body integration are proved below.

section
-- ThirdSavedCarryNumbers
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

def spare (L:CuccaroStreamedSquareWideLayout):Wire := L.core.product.getD 1 0

theorem square_bit1 (x:Nat):(x^2/2%2==1)=false := by
 have hx:x%4=0 ∨ x%4=1 ∨ x%4=2 ∨ x%4=3:=by omega
 have hm:(x^2)%4=(x%4)^2%4:=Nat.pow_mod x 2 4
 rcases hx with hx|hx|hx|hx <;> rw[hx]at hm <;> norm_num at hm
 all_goals
  have h:x^2/2%2=0:=by omega
  simp[h]

theorem spare_zero (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (base:BasisState)
 (M:Nat) (hP:regValue L.core.product base=M^2):base (spare L)=false := by
 unfold spare
 rw[RawClearCarryProbe.register_bit _ 1 base (by simp[hw.core.product]),hP]
 exact square_bit1 M


def cacheBit7 (H:Nat):Bool:=decide ((1040*H/64)%128<H%128)
theorem cacheBit7_value (H:Nat):(cacheBit7 H).toNat=(if (1040*H/64)%128<H%128 then 1 else 0):=by
 by_cases h:(1040*H/64)%128<H%128 <;> simp[cacheBit7,h]
theorem carry_return128 (X A:Nat) (hX:X<128) (hA:A<128):
 (X+(A+128-X)%128)/128=(if A<X then 1 else 0):=by split_ifs <;> omega
theorem carry_return7_w64 (H:Nat):
 (H%128+(976*H/64)%128)/128=(if (1040*H/64)%128<H%128 then 1 else 0):=by
 have sum:H+976*H/64=1040*H/64:=by omega
 have back:((1040*H/64)%128+128-H%128)%128=(976*H/64)%128:=by omega
 rw[←back]
 exact carry_return128 _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
theorem sub_add_carry7_w64 (H:Nat):
 (H%128+(127-(1040*H/64)%128))/128=(H%128+(976*H/64)%128)/128:=by
 have sub:(H%128+(127-(1040*H/64)%128))/128=(if (1040*H/64)%128<H%128 then 1 else 0):=by split_ifs <;> omega
 exact sub.trans (carry_return7_w64 H).symm
#print axioms carry_return7_w64
#print axioms sub_add_carry7_w64

#print axioms square_bit1
#print axioms spare_zero
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryGeometry
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem spare_mem_eReg (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):spare L∈eReg L:=by
 have he:(L.core.product.take 128).getD 1 0=spare L:=by
  simp[spare,List.getD_eq_getElem?_getD]
 have hp:spare L∈L.core.product.take 128:=by
  rw[←he,List.getD_eq_getElem _ _ (by simp[hw.core.product])]
  exact List.getElem_mem _
 exact List.mem_append_left _ hp

theorem spare_mem_product (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):spare L∈L.core.product:=
 eReg_product L _ (spare_mem_eReg L hw)

theorem spare_off_aux (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (q : Wire) (hq:q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,L.core.workHigh,
      L.core.cin,L.core.normFlag,L.core.modFlag]) : spare L≠q := by
  intro eq
  have off:=(L.pairAuxAway hn q hq).1
  exact off (eq ▸ spare_mem_product L hw)

theorem spare_fresh_domain (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    spare L∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L) := by
  have off:=spare_off_aux L hw hn
  intro h
  simp only [List.mem_cons,List.mem_append] at h
  rcases h with h|(((h|h)|h)|h)
  · exact off _ (by simp) h
  · exact (eReg_away L hn _ (spare_mem_eReg L hw)).2.2 h
  · exact off _ (by simp [accReg_work L _ h]) rfl
  · rcases accZ_mem L _ h with h|h
    · exact off _ (by simp [h]) rfl
    · exact off _ (by simp [List.mem_of_mem_drop h]) rfl
  · exact off _ (by simp [List.mem_of_mem_take h]) rfl

theorem spare_ne_sumCarry (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    spare L≠L.core.sumCarry := by
  intro eq
  apply ParkCarryDevelop.sumCarry_away L hn
  have h:=spare_mem_product L hw
  simp [ParkCarryDevelop.restWires,←eq,h]

theorem spare_off_acore (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
    spare L∉wires (qprogTq L.measuredCore SquareReduction.p) := by
  intro h
  have old:=(QRel.qprog_le L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)).1 h
  have hh:=List.mem_toFinset.mp (QCore.qprog_support L.measuredCore SquareReduction.p old)
  simp only [measuredCore,MeasuredCanonicalModLayout.wires,foldCarry,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
  have flat : spare L∈L.core.work ∨ spare L∈L.core.out ∨ spare L∈L.foldPad ∨
      spare L=L.core.productHigh ∨ spare L=L.core.workHigh ∨ spare L=L.core.outHigh ∨ spare L=L.core.cin ∨ spare L=L.core.modFlag := by
    simpa only [or_assoc] using hh
  have off:=spare_off_aux L hw hn
  rcases flat with h|h|h|h|h|h|h|h
  · exact off _ (by simp [h]) rfl
  · exact (eReg_away L hn _ (spare_mem_eReg L hw)).1 h
  · exact off _ (by simp [h]) rfl
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h
  · exact off _ (by simp) h

theorem spare_off_amiddle (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) : spare L∉wires (aMiddle L g) := by
  have ne:spare L≠g := by
    intro e
    apply hg
    have h:=spare_mem_product L hw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,←e,h]
  have away:spare L∉accReg L := (eReg_away L hn _ (spare_mem_eReg L hw)).2.1
  have masks:spare L∉wires (maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK) := by
    intro h
    have mem:=maskedConstant_wires_subset g (accReg L) OwnDiagAll12Square.cFlipK h
    simp only [List.mem_toFinset,List.mem_cons] at mem
    exact mem.elim ne away
  simp only [aMiddle,wires_append,Finset.mem_union,not_or]
  exact ⟨masks,spare_off_acore L hw hn,masks⟩

#print axioms spare_off_acore
#print axioms spare_off_amiddle
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryPrefix
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem shape7 (xs:List Wire) (h:7≤xs.length):∃a b c d e f g tail,xs=a::b::c::d::e::f::g::tail:=by
 obtain ⟨a,b,c,d,e,f,tail,rfl⟩:=shape6 xs (by omega)
 cases tail with
 | nil=>simp at h
 | cons g tail=>exact ⟨a,b,c,d,e,f,g,tail,rfl⟩
def word7 (a0 a1 a2 a3 a4 a5 a6:Bool):Nat:=word6 a0 a1 a2 a3 a4 a5+64*a6.toNat
def carry7 (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6:Bool):Bool:=carryBit a6 b6 (carry6 a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5)
theorem carry_bit_nat : ∀a b c:Bool,(carryBit a b c).toNat=(a.toNat+b.toNat+c.toNat)/2 :=by decide +kernel
theorem carry7_value (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6:Bool):
 (carry7 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6).toNat=(word7 a0 a1 a2 a3 a4 a5 a6+word7 b0 b1 b2 b3 b4 b5 b6)/128:=by
 rw[carry7,carry_bit_nat,carry6_value]
 unfold word7
 omega
theorem carryPrefix_seven (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6 cin:Wire) (as bs cs:List Wire)
 (hn:(cin::(([a0,a1,a2,a3,a4,a5,a6]++as)++([b0,b1,b2,b3,b4,b5,b6]++bs)++([c0,c1,c2,c3,c4,c5,c6]++cs))).Nodup) (s:State) (m:List Bool)
 (hz:∀q∈[c0,c1,c2,c3,c4,c5,c6],s.basis q=false) (hi:s.basis cin=false):
 (run (carryPrefix 7 ([a0,a1,a2,a3,a4,a5,a6]++as) ([b0,b1,b2,b3,b4,b5,b6]++bs) ([c0,c1,c2,c3,c4,c5,c6]++cs) cin) m s).basis c6=carry7 (s.basis a0) (s.basis a1) (s.basis a2) (s.basis a3) (s.basis a4) (s.basis a5) (s.basis a6) (s.basis b0) (s.basis b1) (s.basis b2) (s.basis b3) (s.basis b4) (s.basis b5) (s.basis b6) :=by
 rw[carryPrefix_run 7 ([a0,a1,a2,a3,a4,a5,a6]++as) ([b0,b1,b2,b3,b4,b5,b6]++bs) ([c0,c1,c2,c3,c4,c5,c6]++cs) cin hn s m]
 have hzc0:s.basis c0=false:=hz c0 (by simp)
 have hzc1:s.basis c1=false:=hz c1 (by simp)
 have hzc2:s.basis c2=false:=hz c2 (by simp)
 have hzc3:s.basis c3=false:=hz c3 (by simp)
 have hzc4:s.basis c4=false:=hz c4 (by simp)
 have hzc5:s.basis c5=false:=hz c5 (by simp)
 have hzc6:s.basis c6=false:=hz c6 (by simp)
 have small:[a0,a1,a2,a3,a4,a5,a6,b0,b1,b2,b3,b4,b5,b6,c0,c1,c2,c3,c4,c5,c6,cin].Nodup:=by
  apply List.nodup_iff_count_le_one.mpr
  intro w
  have h:=List.nodup_iff_count_le_one.mp hn w
  simp only[List.count_cons,List.count_append,List.count_nil]at h ⊢
  omega
 have getNe (i j:Nat) (hi:i<22) (hj:j<22) (hne:i≠j):
  ([a0,a1,a2,a3,a4,a5,a6,b0,b1,b2,b3,b4,b5,b6,c0,c1,c2,c3,c4,c5,c6,cin][i]'hi)≠([a0,a1,a2,a3,a4,a5,a6,b0,b1,b2,b3,b4,b5,b6,c0,c1,c2,c3,c4,c5,c6,cin][j]'hj):=by
  intro e
  exact hne ((List.Nodup.getElem_inj_iff small).mp e)
 have ne0_14:a0≠c0:=getNe 0 14 (by decide) (by decide) (by decide)
 have ne0_15:a0≠c1:=getNe 0 15 (by decide) (by decide) (by decide)
 have ne0_16:a0≠c2:=getNe 0 16 (by decide) (by decide) (by decide)
 have ne0_17:a0≠c3:=getNe 0 17 (by decide) (by decide) (by decide)
 have ne0_18:a0≠c4:=getNe 0 18 (by decide) (by decide) (by decide)
 have ne0_19:a0≠c5:=getNe 0 19 (by decide) (by decide) (by decide)
 have ne0_20:a0≠c6:=getNe 0 20 (by decide) (by decide) (by decide)
 have ne1_14:a1≠c0:=getNe 1 14 (by decide) (by decide) (by decide)
 have ne1_15:a1≠c1:=getNe 1 15 (by decide) (by decide) (by decide)
 have ne1_16:a1≠c2:=getNe 1 16 (by decide) (by decide) (by decide)
 have ne1_17:a1≠c3:=getNe 1 17 (by decide) (by decide) (by decide)
 have ne1_18:a1≠c4:=getNe 1 18 (by decide) (by decide) (by decide)
 have ne1_19:a1≠c5:=getNe 1 19 (by decide) (by decide) (by decide)
 have ne1_20:a1≠c6:=getNe 1 20 (by decide) (by decide) (by decide)
 have ne2_14:a2≠c0:=getNe 2 14 (by decide) (by decide) (by decide)
 have ne2_15:a2≠c1:=getNe 2 15 (by decide) (by decide) (by decide)
 have ne2_16:a2≠c2:=getNe 2 16 (by decide) (by decide) (by decide)
 have ne2_17:a2≠c3:=getNe 2 17 (by decide) (by decide) (by decide)
 have ne2_18:a2≠c4:=getNe 2 18 (by decide) (by decide) (by decide)
 have ne2_19:a2≠c5:=getNe 2 19 (by decide) (by decide) (by decide)
 have ne2_20:a2≠c6:=getNe 2 20 (by decide) (by decide) (by decide)
 have ne3_14:a3≠c0:=getNe 3 14 (by decide) (by decide) (by decide)
 have ne3_15:a3≠c1:=getNe 3 15 (by decide) (by decide) (by decide)
 have ne3_16:a3≠c2:=getNe 3 16 (by decide) (by decide) (by decide)
 have ne3_17:a3≠c3:=getNe 3 17 (by decide) (by decide) (by decide)
 have ne3_18:a3≠c4:=getNe 3 18 (by decide) (by decide) (by decide)
 have ne3_19:a3≠c5:=getNe 3 19 (by decide) (by decide) (by decide)
 have ne3_20:a3≠c6:=getNe 3 20 (by decide) (by decide) (by decide)
 have ne4_14:a4≠c0:=getNe 4 14 (by decide) (by decide) (by decide)
 have ne4_15:a4≠c1:=getNe 4 15 (by decide) (by decide) (by decide)
 have ne4_16:a4≠c2:=getNe 4 16 (by decide) (by decide) (by decide)
 have ne4_17:a4≠c3:=getNe 4 17 (by decide) (by decide) (by decide)
 have ne4_18:a4≠c4:=getNe 4 18 (by decide) (by decide) (by decide)
 have ne4_19:a4≠c5:=getNe 4 19 (by decide) (by decide) (by decide)
 have ne4_20:a4≠c6:=getNe 4 20 (by decide) (by decide) (by decide)
 have ne5_14:a5≠c0:=getNe 5 14 (by decide) (by decide) (by decide)
 have ne5_15:a5≠c1:=getNe 5 15 (by decide) (by decide) (by decide)
 have ne5_16:a5≠c2:=getNe 5 16 (by decide) (by decide) (by decide)
 have ne5_17:a5≠c3:=getNe 5 17 (by decide) (by decide) (by decide)
 have ne5_18:a5≠c4:=getNe 5 18 (by decide) (by decide) (by decide)
 have ne5_19:a5≠c5:=getNe 5 19 (by decide) (by decide) (by decide)
 have ne5_20:a5≠c6:=getNe 5 20 (by decide) (by decide) (by decide)
 have ne6_14:a6≠c0:=getNe 6 14 (by decide) (by decide) (by decide)
 have ne6_15:a6≠c1:=getNe 6 15 (by decide) (by decide) (by decide)
 have ne6_16:a6≠c2:=getNe 6 16 (by decide) (by decide) (by decide)
 have ne6_17:a6≠c3:=getNe 6 17 (by decide) (by decide) (by decide)
 have ne6_18:a6≠c4:=getNe 6 18 (by decide) (by decide) (by decide)
 have ne6_19:a6≠c5:=getNe 6 19 (by decide) (by decide) (by decide)
 have ne6_20:a6≠c6:=getNe 6 20 (by decide) (by decide) (by decide)
 have ne7_14:b0≠c0:=getNe 7 14 (by decide) (by decide) (by decide)
 have ne7_15:b0≠c1:=getNe 7 15 (by decide) (by decide) (by decide)
 have ne7_16:b0≠c2:=getNe 7 16 (by decide) (by decide) (by decide)
 have ne7_17:b0≠c3:=getNe 7 17 (by decide) (by decide) (by decide)
 have ne7_18:b0≠c4:=getNe 7 18 (by decide) (by decide) (by decide)
 have ne7_19:b0≠c5:=getNe 7 19 (by decide) (by decide) (by decide)
 have ne7_20:b0≠c6:=getNe 7 20 (by decide) (by decide) (by decide)
 have ne8_14:b1≠c0:=getNe 8 14 (by decide) (by decide) (by decide)
 have ne8_15:b1≠c1:=getNe 8 15 (by decide) (by decide) (by decide)
 have ne8_16:b1≠c2:=getNe 8 16 (by decide) (by decide) (by decide)
 have ne8_17:b1≠c3:=getNe 8 17 (by decide) (by decide) (by decide)
 have ne8_18:b1≠c4:=getNe 8 18 (by decide) (by decide) (by decide)
 have ne8_19:b1≠c5:=getNe 8 19 (by decide) (by decide) (by decide)
 have ne8_20:b1≠c6:=getNe 8 20 (by decide) (by decide) (by decide)
 have ne9_14:b2≠c0:=getNe 9 14 (by decide) (by decide) (by decide)
 have ne9_15:b2≠c1:=getNe 9 15 (by decide) (by decide) (by decide)
 have ne9_16:b2≠c2:=getNe 9 16 (by decide) (by decide) (by decide)
 have ne9_17:b2≠c3:=getNe 9 17 (by decide) (by decide) (by decide)
 have ne9_18:b2≠c4:=getNe 9 18 (by decide) (by decide) (by decide)
 have ne9_19:b2≠c5:=getNe 9 19 (by decide) (by decide) (by decide)
 have ne9_20:b2≠c6:=getNe 9 20 (by decide) (by decide) (by decide)
 have ne10_14:b3≠c0:=getNe 10 14 (by decide) (by decide) (by decide)
 have ne10_15:b3≠c1:=getNe 10 15 (by decide) (by decide) (by decide)
 have ne10_16:b3≠c2:=getNe 10 16 (by decide) (by decide) (by decide)
 have ne10_17:b3≠c3:=getNe 10 17 (by decide) (by decide) (by decide)
 have ne10_18:b3≠c4:=getNe 10 18 (by decide) (by decide) (by decide)
 have ne10_19:b3≠c5:=getNe 10 19 (by decide) (by decide) (by decide)
 have ne10_20:b3≠c6:=getNe 10 20 (by decide) (by decide) (by decide)
 have ne11_14:b4≠c0:=getNe 11 14 (by decide) (by decide) (by decide)
 have ne11_15:b4≠c1:=getNe 11 15 (by decide) (by decide) (by decide)
 have ne11_16:b4≠c2:=getNe 11 16 (by decide) (by decide) (by decide)
 have ne11_17:b4≠c3:=getNe 11 17 (by decide) (by decide) (by decide)
 have ne11_18:b4≠c4:=getNe 11 18 (by decide) (by decide) (by decide)
 have ne11_19:b4≠c5:=getNe 11 19 (by decide) (by decide) (by decide)
 have ne11_20:b4≠c6:=getNe 11 20 (by decide) (by decide) (by decide)
 have ne12_14:b5≠c0:=getNe 12 14 (by decide) (by decide) (by decide)
 have ne12_15:b5≠c1:=getNe 12 15 (by decide) (by decide) (by decide)
 have ne12_16:b5≠c2:=getNe 12 16 (by decide) (by decide) (by decide)
 have ne12_17:b5≠c3:=getNe 12 17 (by decide) (by decide) (by decide)
 have ne12_18:b5≠c4:=getNe 12 18 (by decide) (by decide) (by decide)
 have ne12_19:b5≠c5:=getNe 12 19 (by decide) (by decide) (by decide)
 have ne12_20:b5≠c6:=getNe 12 20 (by decide) (by decide) (by decide)
 have ne13_14:b6≠c0:=getNe 13 14 (by decide) (by decide) (by decide)
 have ne13_15:b6≠c1:=getNe 13 15 (by decide) (by decide) (by decide)
 have ne13_16:b6≠c2:=getNe 13 16 (by decide) (by decide) (by decide)
 have ne13_17:b6≠c3:=getNe 13 17 (by decide) (by decide) (by decide)
 have ne13_18:b6≠c4:=getNe 13 18 (by decide) (by decide) (by decide)
 have ne13_19:b6≠c5:=getNe 13 19 (by decide) (by decide) (by decide)
 have ne13_20:b6≠c6:=getNe 13 20 (by decide) (by decide) (by decide)
 have ne14_15:c0≠c1:=getNe 14 15 (by decide) (by decide) (by decide)
 have ne14_16:c0≠c2:=getNe 14 16 (by decide) (by decide) (by decide)
 have ne14_17:c0≠c3:=getNe 14 17 (by decide) (by decide) (by decide)
 have ne14_18:c0≠c4:=getNe 14 18 (by decide) (by decide) (by decide)
 have ne14_19:c0≠c5:=getNe 14 19 (by decide) (by decide) (by decide)
 have ne14_20:c0≠c6:=getNe 14 20 (by decide) (by decide) (by decide)
 have ne15_14:c1≠c0:=getNe 15 14 (by decide) (by decide) (by decide)
 have ne15_16:c1≠c2:=getNe 15 16 (by decide) (by decide) (by decide)
 have ne15_17:c1≠c3:=getNe 15 17 (by decide) (by decide) (by decide)
 have ne15_18:c1≠c4:=getNe 15 18 (by decide) (by decide) (by decide)
 have ne15_19:c1≠c5:=getNe 15 19 (by decide) (by decide) (by decide)
 have ne15_20:c1≠c6:=getNe 15 20 (by decide) (by decide) (by decide)
 have ne16_14:c2≠c0:=getNe 16 14 (by decide) (by decide) (by decide)
 have ne16_15:c2≠c1:=getNe 16 15 (by decide) (by decide) (by decide)
 have ne16_17:c2≠c3:=getNe 16 17 (by decide) (by decide) (by decide)
 have ne16_18:c2≠c4:=getNe 16 18 (by decide) (by decide) (by decide)
 have ne16_19:c2≠c5:=getNe 16 19 (by decide) (by decide) (by decide)
 have ne16_20:c2≠c6:=getNe 16 20 (by decide) (by decide) (by decide)
 have ne17_14:c3≠c0:=getNe 17 14 (by decide) (by decide) (by decide)
 have ne17_15:c3≠c1:=getNe 17 15 (by decide) (by decide) (by decide)
 have ne17_16:c3≠c2:=getNe 17 16 (by decide) (by decide) (by decide)
 have ne17_18:c3≠c4:=getNe 17 18 (by decide) (by decide) (by decide)
 have ne17_19:c3≠c5:=getNe 17 19 (by decide) (by decide) (by decide)
 have ne17_20:c3≠c6:=getNe 17 20 (by decide) (by decide) (by decide)
 have ne18_14:c4≠c0:=getNe 18 14 (by decide) (by decide) (by decide)
 have ne18_15:c4≠c1:=getNe 18 15 (by decide) (by decide) (by decide)
 have ne18_16:c4≠c2:=getNe 18 16 (by decide) (by decide) (by decide)
 have ne18_17:c4≠c3:=getNe 18 17 (by decide) (by decide) (by decide)
 have ne18_19:c4≠c5:=getNe 18 19 (by decide) (by decide) (by decide)
 have ne18_20:c4≠c6:=getNe 18 20 (by decide) (by decide) (by decide)
 have ne19_14:c5≠c0:=getNe 19 14 (by decide) (by decide) (by decide)
 have ne19_15:c5≠c1:=getNe 19 15 (by decide) (by decide) (by decide)
 have ne19_16:c5≠c2:=getNe 19 16 (by decide) (by decide) (by decide)
 have ne19_17:c5≠c3:=getNe 19 17 (by decide) (by decide) (by decide)
 have ne19_18:c5≠c4:=getNe 19 18 (by decide) (by decide) (by decide)
 have ne19_20:c5≠c6:=getNe 19 20 (by decide) (by decide) (by decide)
 have ne20_14:c6≠c0:=getNe 20 14 (by decide) (by decide) (by decide)
 have ne20_15:c6≠c1:=getNe 20 15 (by decide) (by decide) (by decide)
 have ne20_16:c6≠c2:=getNe 20 16 (by decide) (by decide) (by decide)
 have ne20_17:c6≠c3:=getNe 20 17 (by decide) (by decide) (by decide)
 have ne20_18:c6≠c4:=getNe 20 18 (by decide) (by decide) (by decide)
 have ne20_19:c6≠c5:=getNe 20 19 (by decide) (by decide) (by decide)
 have ne21_14:cin≠c0:=getNe 21 14 (by decide) (by decide) (by decide)
 have ne21_15:cin≠c1:=getNe 21 15 (by decide) (by decide) (by decide)
 have ne21_16:cin≠c2:=getNe 21 16 (by decide) (by decide) (by decide)
 have ne21_17:cin≠c3:=getNe 21 17 (by decide) (by decide) (by decide)
 have ne21_18:cin≠c4:=getNe 21 18 (by decide) (by decide) (by decide)
 have ne21_19:cin≠c5:=getNe 21 19 (by decide) (by decide) (by decide)
 have ne21_20:cin≠c6:=getNe 21 20 (by decide) (by decide) (by decide)
 clear hn small getNe hz
 simp_all[prefixState,writeBit,Function.update,carry7,carry6]

theorem carryPrefix_value7 (xs ys cs : List Wire) (cin : Wire)
    (hx:7≤xs.length) (hy:7≤ys.length) (hc:7≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State) (m : List Bool)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (carryPrefix 7 xs ys cs cin) m s).basis (cs.getD 6 0)).toNat=
      (regValue (xs.take 7) s.basis+regValue (ys.take 7) s.basis)/128 := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,as,rfl⟩:=shape7 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,bs,rfl⟩:=shape7 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,cs,rfl⟩:=shape7 cs hc
  have zeros:∀q∈[c0,c1,c2,c3,c4,c5,c6],s.basis q=false := by
    intro q hq
    apply hz q
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have v:=congrArg Bool.toNat (carryPrefix_seven a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 c0 c1 c2 c3 c4 c5 c6 cin as bs cs hn s m zeros hi)
  rw [carry7_value] at v
  simpa [regValue,word7,word6,Bool.toNat,Bool.cond_eq_ite,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using v

def subPre7 (xs ys cs : List Wire) (cin : Wire) : Program :=
  notRegister ys++carryPrefix 7 xs ys cs cin

theorem subPre7_value7 (xs ys cs : List Wire) (cin : Wire)
    (hx:7≤xs.length) (hy:7≤ys.length) (hc:7≤cs.length)
    (hn:(cin::(xs++ys++cs)).Nodup) (s : State)
    (hz:∀q∈cs,s.basis q=false) (hi:s.basis cin=false) :
    ((run (subPre7 xs ys cs cin) [] s).basis (cs.getD 6 0)).toNat=
      (regValue (xs.take 7) s.basis+(127-regValue (ys.take 7) s.basis))/128 := by
  have nd:=List.nodup_cons.mp hn
  have split:=List.nodup_append'.mp nd.2
  have xy:=List.nodup_append'.mp split.1
  have xAway:∀q∈xs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp xy.2.2 hq bad
  have cAway:∀q∈cs,q∉ys := by
    intro q hq bad
    exact List.disjoint_left.mp split.2.2 (List.mem_append_right _ bad) hq
  have cinAway:cin∉ys := by
    intro bad
    exact nd.1 (List.mem_append_left _ (List.mem_append_right _ bad))
  let t:=run (notRegister ys) [] s
  have nr:=notRegister_correct ys xy.2.1 s []
  have zt:∀q∈cs,t.basis q=false := by
    intro q hq
    change (run (notRegister ys) [] s).basis q=false
    rw [nr]
    simpa [cAway q hq] using hz q hq
  have it:t.basis cin=false := by
    change (run (notRegister ys) [] s).basis cin=false
    rw [nr]
    simpa [cinAway] using hi
  have xv:regValue (xs.take 7) t.basis=regValue (xs.take 7) s.basis := by
    apply regValue_congr
    intro q hq
    change (run (notRegister ys) [] s).basis q=s.basis q
    rw [nr]
    simp [xAway q (List.mem_of_mem_take hq)]
  have yv:regValue (ys.take 7) t.basis=127-regValue (ys.take 7) s.basis := by
    have e:regValue (ys.take 7) t.basis=regValue (ys.take 7) (fun q=>!s.basis q) := by
      apply regValue_congr
      intro q hq
      change (run (notRegister ys) [] s).basis q= !s.basis q
      rw [nr]
      simp [List.mem_of_mem_take hq]
    rw [e,regValue_complement]
    have len:(ys.take 7).length=7 := by simp [hy]
    rw [len]
    norm_num
  have val:=carryPrefix_value7 xs ys cs cin hx hy hc hn t [] zt it
  rw [xv,yv] at val
  have count:measurementCount (notRegister ys)=0 := (notRegister_counts ys).2
  simpa only [subPre7,run_append,count,List.take_zero,List.drop_zero] using val

#print axioms carry7_value
#print axioms carryPrefix_value7
#print axioms subPre7_value7
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarrySplits
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def seventhMajority (xs ys cs:List Wire):Program:=
 majority (xs.getD 6 0) (ys.getD 6 0) (cs.getD 5 0) (cs.getD 6 0)
def subPost7 (xs ys cs:List Wire) (cin:Wire):Program:=addKTSuffix true 7 xs ys cs cin++notRegister ys

theorem carryPrefix_split7 (xs ys cs:List Wire) (cin:Wire) (hx:7≤xs.length) (hy:7≤ys.length) (hc:7≤cs.length):
 carryPrefix 7 xs ys cs cin=carryPrefix 6 xs ys cs cin++seventhMajority xs ys cs:=by
 obtain ⟨a0,a1,a2,a3,a4,a5,a6,as,rfl⟩:=shape7 xs hx
 obtain ⟨b0,b1,b2,b3,b4,b5,b6,bs,rfl⟩:=shape7 ys hy
 obtain ⟨c0,c1,c2,c3,c4,c5,c6,cs,rfl⟩:=shape7 cs hc
 simp[carryPrefix,seventhMajority,List.append_assoc]
theorem subPre7_split (xs ys cs:List Wire) (cin:Wire) (hx:7≤xs.length) (hy:7≤ys.length) (hc:7≤cs.length):
 subPre7 xs ys cs cin=subPre6 xs ys cs cin++seventhMajority xs ys cs:=by
 simp only[subPre7,subPre6,carryPrefix_split7 xs ys cs cin hx hy hc,List.append_assoc]
theorem subPost6_split7 (xs ys cs:List Wire) (cin:Wire) (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length):
 subPost6 xs ys cs cin=seventhMajority xs ys cs++subPost7 xs ys cs cin:=by
 have a:=addKT_split true 6 xs ys cs cin hx hc (by omega)
 have b:=addKT_split true 7 xs ys cs cin hx hc hy
 rw[carryPrefix_split7 xs ys cs cin (by omega) (by omega) (by omega),List.append_assoc]at b
 have eq:carryPrefix 6 xs ys cs cin++addKTSuffix true 6 xs ys cs cin=
  carryPrefix 6 xs ys cs cin++(seventhMajority xs ys cs++addKTSuffix true 7 xs ys cs cin):=a.symm.trans b
 have tail:=List.append_cancel_left eq
 simp only[subPost6,subPost7,tail,List.append_assoc]

def cachedSubTriple (xs ys cs:List Wire) (cin q r t:Wire):Program:=
 insertCopy (secondCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs)
  (cs.getD 4 0) (cs.getD 5 0) q r) (subPost7 xs ys cs cin) (cs.getD 6 0) t

theorem cachedSubDual_split7 (xs ys cs:List Wire) (cin q r:Wire) (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length):
 cachedSubDual xs ys cs cin q r=
 secondCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs) (cs.getD 4 0) (cs.getD 5 0) q r++subPost7 xs ys cs cin:=by
 rw[cachedSubDual,subPost6_split7 xs ys cs cin hx hc hy]
 simp only[secondCopy,insertCopy,List.append_assoc]

theorem source_suffix_three_heads (src Z ys carry:List Wire) (cin:Wire)
 (hs:9≤src.length) (hy:ys.length=src.length+5) (hc:7≤carry.length):
 (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).take 18=
 majority ((src++Z.take 5).getD 4 0) (ys.getD 4 0) (carry.getD 3 0) (carry.getD 4 0)++
 sixthMajority (src++Z.take 5) ys carry++seventhMajority (src++Z.take 5) ys carry:=by
 obtain ⟨a0,a1,a2,a3,a4,a5,a6,as,rfl⟩:=shape7 src (by omega)
 cases as with
 | nil=>simp only[List.length_cons,List.length_nil]at hs;omega
 | cons a7 as=>
  cases as with
  | nil=>simp only[List.length_cons,List.length_nil]at hs;omega
  | cons a8 as=>
   obtain ⟨b0,b1,b2,b3,b4,b5,b6,bs,rfl⟩:=shape7 ys (by simp only[List.length_cons]at hy;omega)
   cases bs with
   | nil=>simp only[List.length_cons,List.length_nil]at hy;omega
   | cons b7 bs=>
    cases bs with
    | nil=>simp only[List.length_cons,List.length_nil]at hy;omega
    | cons b8 bs=>
     obtain ⟨c0,c1,c2,c3,c4,c5,c6,cs,rfl⟩:=shape7 carry hc
     change _=majority a4 b4 c3 c4++majority a5 b5 c4 c5++majority a6 b6 c5 c6
     simp[knownSuffix,desired,mappedRead,mappedAdd,mappedMajority,majority,List.append_assoc]

def addPost3 (src Z ys carry:List Wire) (cin:Wire):Program:=
 (knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin).drop 18

theorem addPost2_split7 (src Z ys carry:List Wire) (cin:Wire)
 (hs:9≤src.length) (hy:ys.length=src.length+5) (hc:7≤carry.length):
 addPost2 src Z ys carry cin=seventhMajority (src++Z.take 5) ys carry++addPost3 src Z ys carry cin:=by
 let suffix:=knownSuffix (src.getD 0 0) (mappedRead (src++Z.take 5) false) ys (desired src) carry cin
 have split:=List.take_append_drop 18 suffix
 rw[source_suffix_three_heads src Z ys carry cin hs hy hc]at split
 have eq:=congrArg (List.drop 12) split.symm
 simpa only[addPost2,addPost3,seventhMajority,sixthMajority,majority,List.append_assoc,List.drop_succ_cons,List.drop_zero,List.nil_append]using eq

def consumedAddTriple (src Z ys carry:List Wire) (cin q r t:Wire):Program:=
 ((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0)++addPost3 src Z ys carry cin

theorem consumedAddDual_split7 (src Z ys carry:List Wire) (cin q r:Wire)
 (hs:9≤src.length) (hy:ys.length=src.length+5) (hc:7≤carry.length):
 consumedAddDual src Z ys carry cin q r=
 ((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++seventhMajority (src++Z.take 5) ys carry++addPost3 src Z ys carry cin:=by
 rw[consumedAddDual,addPost2_split7 src Z ys carry cin hs hy hc]
 simp only[List.append_assoc]
#print axioms cachedSubDual_split7
#print axioms consumedAddDual_split7
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryCopy
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem secondCopy_value (pre next post:Program) (c d q r w:Wire)
 (hqpre:q∉wires pre) (hqnext:q∉wires next) (hqpost:q∉wires post)
 (hrpre:r∉wires (insertCopy pre next c q)) (hrpost:r∉wires post)
 (mp:measurementCount pre=0) (mn:measurementCount next=0) (dq:d≠q)
 (wq:w≠q) (wr:w≠r) (s:State) (hq:s.basis q=false) (hr:s.basis r=false):
 (run (secondCopy pre next post c d q r) [] s).basis w=(run (pre++next++post) [] s).basis w:=by
 have hp:q∉wires (next++post):=by simp only[wires_append,Finset.mem_union,not_or];exact ⟨hqnext,hqpost⟩
 rw[secondCopy_correct pre next post c d q r hqpre hqnext hrpre hrpost mp mn dq s [] hq hr]
 change (writeBit (run (insertCopy pre (next++post) c q) [] s).basis r _ ) w=_
 rw[show (writeBit (run (insertCopy pre (next++post) c q) [] s).basis r _ ) w=(run (insertCopy pre (next++post) c q) [] s).basis w by simp[writeBit,Function.update_apply,wr]]
 rw[insertCopy_correct pre (next++post) c q hqpre hp s [] hq]
 simp only[writeBit,Function.update_of_ne wq,List.append_assoc]

theorem cachedSubTriple_frame (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length)
 (off:t∉wires (cachedSubDual xs ys cs cin q r))
 (s:State) (m:List Bool) (ht:s.basis t=false):
 run (cachedSubTriple xs ys cs cin q r t) m s=
 ⟨(run (cachedSubDual xs ys cs cin q r) m s).phase,
 writeBit (run (cachedSubDual xs ys cs cin q r) m s).basis t
 ((run (secondCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs)
  (cs.getD 4 0) (cs.getD 5 0) q r) [] s).basis (cs.getD 6 0))⟩:=by
 have split:=cachedSubDual_split7 xs ys cs cin q r hx hc hy
 rw[split,wires_append,Finset.mem_union,not_or]at off
 have mp:measurementCount (secondCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs)
  (cs.getD 4 0) (cs.getD 5 0) q r)=0:=by
  simp[secondCopy,insertCopy,subPre,sixthMajority,seventhMajority,majority,measurementCount_append,
   (notRegister_counts ys).2,carryPrefix_measurements,measurementCount]
 rw[cachedSubTriple,insertCopy_correct _ _ _ _ off.1 off.2 s m ht,mp,List.take_zero,←split]

#print axioms secondCopy_value
#print axioms cachedSubTriple_frame
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryKnown
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem cachedSubTriple_known_frame (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length)
 (hn:(cin::(xs++ys++cs)).Nodup) (s:State) (m:List Bool)
 (hz:∀w∈cs,s.basis w=false) (hi:s.basis cin=false)
 (qoff:q∉wires (CodexNarrowSub.program xs ys cs cin))
 (roff:r∉wires (CodexNarrowSub.program xs ys cs cin)) (rq:r≠q)
 (off:t∉wires (cachedSubDual xs ys cs cin q r))
 (hq:s.basis q=false) (hr:s.basis r=false) (ht:s.basis t=false)
 (H:Nat) (source:regValue xs s.basis=H) (target:regValue ys s.basis=1040*H/64):
 run (cachedSubTriple xs ys cs cin q r t) m s=
 ⟨(run (cachedSubDual xs ys cs cin q r) m s).phase,
 writeBit (run (cachedSubDual xs ys cs cin q r) m s).basis t (cacheBit7 H)⟩:=by
 have split:subPre xs ys cs cin++(sixthMajority xs ys cs++(seventhMajority xs ys cs++subPost7 xs ys cs cin))=
  CodexNarrowSub.program xs ys cs cin:=by
  rw[←subPost6_split7 xs ys cs cin hx hc hy,←subPost_split6 xs ys cs cin hx hc (by omega)]
  exact sub_split xs ys cs cin hx hc (by omega)
 have qo:=qoff
 rw[←split]at qo
 simp only[wires_append,Finset.mem_union,not_or]at qo
 have ro:=roff
 rw[←split]at ro
 simp only[wires_append,Finset.mem_union,not_or]at ro
 have rfirst:r∉wires (cachedSub xs ys cs cin q):=by
  intro h
  have h:=Finset.mem_insert.mp (cachedSub_support xs ys cs cin q hx hc (by omega) h)
  exact h.elim rq roff
 rw[cachedSub_first_split xs ys cs cin q hx hc (by omega),firstCopy_split,wires_append,Finset.mem_union,not_or]at rfirst
 have dq:cs.getD 5 0≠q:=by
  intro e
  apply qo.2.1
  simp[sixthMajority,majority,wires,Instr.wires,←e]
 have wq:cs.getD 6 0≠q:=by
  intro e
  apply qo.2.2.1
  simp[seventhMajority,majority,wires,Instr.wires,←e]
 have wr:cs.getD 6 0≠r:=by
  intro e
  apply ro.2.2.1
  simp[seventhMajority,majority,wires,Instr.wires,←e]
 have mp:measurementCount (subPre xs ys cs cin)=0:=by
  simp only[subPre,measurementCount_append,(notRegister_counts ys).2,carryPrefix_measurements,Nat.zero_add]
 have value:=secondCopy_value (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs)
  (cs.getD 4 0) (cs.getD 5 0) q r (cs.getD 6 0) qo.1 qo.2.1 qo.2.2.1 rfirst.1 ro.2.2.1 mp rfl dq wq wr s hq hr
 have pref:subPre xs ys cs cin++sixthMajority xs ys cs++seventhMajority xs ys cs=subPre7 xs ys cs cin:=by
  rw[←subPre6_split xs ys cs cin (by omega) (by omega) (by omega),←subPre7_split xs ys cs cin (by omega) (by omega) (by omega)]
 rw[pref]at value
 have v:=subPre7_value7 xs ys cs cin (by omega) (by omega) (by omega) hn s hz hi
 rw[Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod xs 7 (by omega) s.basis,Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod ys 7 (by omega) s.basis,source,target]at v
 norm_num only[show 2^7=128 by decide]at v
 rw[sub_add_carry7_w64 H,carry_return7_w64 H]at v
 have known:(run (subPre7 xs ys cs cin) [] s).basis (cs.getD 6 0)=cacheBit7 H:=
  bool_nat_injective _ _ (v.trans (cacheBit7_value H).symm)
 rw[cachedSubTriple_frame xs ys cs cin q r t hx hc hy off s m ht,value,known]
#print axioms cachedSubTriple_known_frame
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop SourceAddFourDevelop
set_option maxHeartbeats 3000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem cachedSubTriple_counts (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length):
 toffoliCount (cachedSubTriple xs ys cs cin q r t)=toffoliCount (cachedSubDual xs ys cs cin q r) ∧
 measurementCount (cachedSubTriple xs ys cs cin q r t)=measurementCount (cachedSubDual xs ys cs cin q r) ∧
 Challenge.gateSlots (cachedSubTriple xs ys cs cin q r t)=Challenge.gateSlots (cachedSubDual xs ys cs cin q r)+1:=by
 rw[cachedSubDual_split7 xs ys cs cin q r hx hc hy]
 simp[cachedSubTriple,insertCopy,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots] <;> omega

theorem consumedAddTriple_counts (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:9≤src.length) (hy:ys.length=src.length+5) (hc:7≤carry.length):
 toffoliCount (consumedAddTriple src Z ys carry cin q r t)+1=toffoliCount (consumedAddDual src Z ys carry cin q r) ∧
 measurementCount (consumedAddTriple src Z ys carry cin q r t)=measurementCount (consumedAddDual src Z ys carry cin q r) ∧
 Challenge.gateSlots (consumedAddTriple src Z ys carry cin q r t)+4=Challenge.gateSlots (consumedAddDual src Z ys carry cin q r):=by
 rw[consumedAddDual_split7 src Z ys carry cin q r hs hy hc]
 simp[consumedAddTriple,move,seventhMajority,majority,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots] <;> omega

#print axioms cachedSubTriple_counts
#print axioms consumedAddTriple_counts
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryNext
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem carryPrefix_next_value7 (xs ys carry : List Wire) (cin : Wire)
    (hx:7≤xs.length) (hy:7≤ys.length) (hc:7≤carry.length)
    (hn:(cin::(xs++ys++carry)).Nodup) (s : State)
    (hz:∀q∈carry,s.basis q=false) (hi:s.basis cin=false) :
    (carryBit
      ((run (carryPrefix 6 xs ys carry cin) [] s).basis (xs.getD 6 0))
      ((run (carryPrefix 6 xs ys carry cin) [] s).basis (ys.getD 6 0))
      ((run (carryPrefix 6 xs ys carry cin) [] s).basis (carry.getD 5 0))).toNat=
      (regValue (xs.take 7) s.basis+regValue (ys.take 7) s.basis)/128 := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,as,rfl⟩:=shape7 xs hx
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,bs,rfl⟩:=shape7 ys hy
  obtain ⟨c0,c1,c2,c3,c4,c5,c6,cs,rfl⟩:=shape7 carry hc
  let xs:=a0::a1::a2::a3::a4::a5::a6::as
  let ys:=b0::b1::b2::b3::b4::b5::b6::bs
  let carry:=c0::c1::c2::c3::c4::c5::c6::cs
  let t:=run (carryPrefix 6 xs ys carry cin) [] s
  have nd4:[a6,b6,c5,c6].Nodup := by
    apply List.nodup_iff_count_le_one.mpr
    intro w
    have h:=List.nodup_iff_count_le_one.mp hn w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndcs:carry.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
  have off:c6∉carry.take 6 := by
    change c6∉[c0,c1,c2,c3,c4,c5]
    intro mem
    have pos:=List.count_pos_iff.mpr mem
    have bound:=List.nodup_iff_count_le_one.mp ndcs c6
    simp only [carry,List.count_cons,List.count_nil] at pos bound
    simp only [beq_self_eq_true,if_true] at bound
    omega
  have clean:t.basis c6=false :=
    (carryPrefix_preserves 6 xs ys carry cin hn s [] c6 off).trans (hz c6 (by simp))
  have split:carryPrefix 7 xs ys carry cin=carryPrefix 6 xs ys carry cin++majority a6 b6 c5 c6 := by
    simp [xs,ys,carry,carryPrefix,List.append_assoc]
  have run7:run (carryPrefix 7 xs ys carry cin) [] s=run (majority a6 b6 c5 c6) [] t := by
    rw [split,run_append]
    simp only [List.take_nil,List.drop_nil,t]
  have v:=carryPrefix_value7 xs ys carry cin hx hy hc hn s [] hz hi
  rw [run7,majority_correct a6 b6 c5 c6 nd4 t [],clean] at v
  change (carryBit (t.basis a6) (t.basis b6) (t.basis c5)).toNat=_
  have get:carry.getD 6 0=c6 := rfl
  rw [get] at v
  simpa only [writeBit,Function.update_self,Bool.false_xor] using v

#print axioms carryPrefix_next_value7
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryConsumePrefix
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem source_prefix_consumed_eq6 (src Z ys carry:List Wire) (cin q r:Wire)
 (hs:8≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
 (s:State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
 (hcin:s.basis cin=false) (H:Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
 (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉carry) (rq:r≠q)
 (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H):
 run ((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0)) [] s=
 setWire (setWire (run (carryPrefix 6 (src++Z.take 5) ys carry cin) [] s) q false) r false:=by
 let xs:=src++Z.take 5
 let pre:=addPre src Z ys carry cin++move q (carry.getD 4 0)
 have xlen:6≤xs.length:=by dsimp[xs];simp only[List.length_append];omega
 have enough:6≤carry.length:=by omega
 have nd:=sixth_majority_nd xs ys carry cin xlen (by omega) enough hn
 have ne:r≠carry.getD 5 0:=by
  intro e
  exact rfresh (e.symm ▸ DiagSq.getD_in carry 5 (by omega))
 have ready:=source_second_consume_ready src Z ys carry cin q r hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh rfresh rq saved savedR
 have qcarry:q∉carry:=by intro h;exact fresh (by simp[h])
 have eq5:run pre [] s=setWire (run (carryPrefix 5 xs ys carry cin) [] s) q false:=
  source_prefix_consumed_eq5 src Z ys carry cin q (by omega) hzl hy hc hn s hz hclean hcin H hsrc hys qcarry saved
 have preM:measurementCount pre=0:=by
  have h:=(knownPrefix_counts (src.getD 0 0) (mappedRead (src++Z.take 5) false) (desired src) ys carry cin).2
  change measurementCount (addPre src Z ys carry cin)=0 at h
  simp only[pre,measurementCount_append,h,show measurementCount (move q (carry.getD 4 0))=0 from rfl,Nat.zero_add]
 have result:=secondConsume_correct pre [] (xs.getD 5 0) (ys.getD 5 0) (carry.getD 4 0) (carry.getD 5 0) r
  nd ne (by simp[wires]) s []
  (by simpa only[List.take_nil]using ready.1) (by simpa only[List.take_nil]using ready.2)
 simp only[List.append_nil]at result
 have qx:q∉xs:=by intro h;exact fresh (List.mem_append_left _ (List.mem_append_left _ h))
 have qy:q∉ys:=by intro h;exact fresh (by simp[h])
 have nX:q≠xs.getD 5 0:=by intro e;exact qx (e.symm ▸ DiagSq.getD_in xs 5 (by omega))
 have nY:q≠ys.getD 5 0:=by intro e;exact qy (e.symm ▸ DiagSq.getD_in ys 5 (by omega))
 have nC4:q≠carry.getD 4 0:=by intro e;exact qcarry (e.symm ▸ DiagSq.getD_in carry 4 (by omega))
 have nC5:q≠carry.getD 5 0:=by intro e;exact qcarry (e.symm ▸ DiagSq.getD_in carry 5 (by omega))
 have qo:q∉wires (sixthMajority xs ys carry):=by
  simp only[List.getD_eq_getElem?_getD]at nX nY nC4 nC5
  simp[sixthMajority,majority,wires,Instr.wires,nX,nY,nC4,nC5]
 have old6:run (pre++sixthMajority xs ys carry) [] s=
  setWire (run (carryPrefix 6 xs ys carry cin) [] s) q false:=by
  rw[run_append,List.take_nil,List.drop_nil,eq5]
  simp only[setWire]
  rw[run_update_outside _ q false qo]
  have ce:carryPrefix 6 xs ys carry cin=carryPrefix 5 xs ys carry cin++sixthMajority xs ys carry:=
   carryPrefix_split6 xs ys carry cin xlen (by omega) enough
  rw[ce,run_append,List.take_nil,List.drop_nil]
 change run (pre++move r (carry.getD 5 0)) [] s=setWire (setWire (run (carryPrefix 6 xs ys carry cin) [] s) q false) r false
 rw[result]
 change setWire (run (pre++sixthMajority xs ys carry) [] s) r false=_
 rw[old6]
#print axioms source_prefix_consumed_eq6
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryReady
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem seventh_not_take6 (carry:List Wire) (hc:7≤carry.length) (hn:carry.Nodup):
 carry.getD 6 0∉carry.take 6:=by
 obtain ⟨c0,c1,c2,c3,c4,c5,c6,cs,rfl⟩:=shape7 carry hc
 change c6∉[c0,c1,c2,c3,c4,c5]
 intro mem
 have pos:=List.count_pos_iff.mpr mem
 have bound:=List.nodup_iff_count_le_one.mp hn c6
 simp only[List.count_cons,List.count_nil]at pos bound
 simp only[beq_self_eq_true,if_true]at bound
 omega

theorem seventh_majority_nd (xs ys carry:List Wire) (cin:Wire)
 (hx:7≤xs.length) (hy:7≤ys.length) (hc:7≤carry.length)
 (hn:(cin::(xs++ys++carry)).Nodup):
 [xs.getD 6 0,ys.getD 6 0,carry.getD 5 0,carry.getD 6 0].Nodup:=by
 obtain ⟨a0,a1,a2,a3,a4,a5,a6,as,rfl⟩:=shape7 xs hx
 obtain ⟨b0,b1,b2,b3,b4,b5,b6,bs,rfl⟩:=shape7 ys hy
 obtain ⟨c0,c1,c2,c3,c4,c5,c6,cs,rfl⟩:=shape7 carry hc
 change [a6,b6,c5,c6].Nodup
 apply List.nodup_iff_count_le_one.mpr
 intro w
 have h:=List.nodup_iff_count_le_one.mp hn w
 simp only[List.count_cons,List.count_append,List.count_nil]at h ⊢
 omega

theorem source_third_consume_ready (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:9≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
 (s:State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
 (hcin:s.basis cin=false) (H:Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
 (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉(src++Z.take 5)++ys++carry) (rq:r≠q)
 (tfresh:t∉carry) (tq:t≠q) (tr:t≠r)
 (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) (savedT:s.basis t=cacheBit7 H):
 let v:=run ((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0)) [] s
 v.basis (carry.getD 6 0)=false ∧
 v.basis t=carryBit (v.basis ((src++Z.take 5).getD 6 0)) (v.basis (ys.getD 6 0)) (v.basis (carry.getD 5 0)):=by
 let xs:=src++Z.take 5
 let u:=run (carryPrefix 6 xs ys carry cin) [] s
 let v:=run ((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0)) [] s
 have enough:7≤carry.length:=by omega
 have xlen:7≤xs.length:=by dsimp[xs];simp only[List.length_append];omega
 have rf:r∉carry:=by intro h;exact rfresh (by simp[h])
 have eq:v=setWire (setWire u q false) r false:=
  source_prefix_consumed_eq6 src Z ys carry cin q r (by omega) hzl hy hc hn s hz hclean hcin H hsrc hys fresh rf rq saved savedR
 have outside (w:Wire) (hw:w∈xs++ys++carry):v.basis w=u.basis w:=by
  have wq:w≠q:=by intro e;exact fresh (e ▸ hw)
  have wr:w≠r:=by intro e;exact rfresh (e ▸ hw)
  rw[eq]
  simp only[setWire,writeBit,Function.update_of_ne wr,Function.update_of_ne wq]
 have ndcs:carry.Nodup:=(List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
 have clean:v.basis (carry.getD 6 0)=false:=
  (outside _ (List.mem_append_right _ (DiagSq.getD_in carry 6 (by omega)))).trans
  ((carryPrefix_preserves 6 xs ys carry cin hn s [] _ (seventh_not_take6 carry enough ndcs)).trans
   (hclean _ (DiagSq.getD_in carry 6 (by omega))))
 have kept:v.basis t=cacheBit7 H:=by
  rw[eq]
  simp only[setWire,writeBit,Function.update_of_ne tr,Function.update_of_ne tq]
  exact (carryPrefix_preserves 6 xs ys carry cin hn s [] t (fun h=>tfresh (List.mem_of_mem_take h))).trans savedT
 have val:=carryPrefix_next_value7 xs ys carry cin xlen (by omega) enough hn s hclean hcin
 have xvalue:regValue xs s.basis=H:=by
  have zv:regValue (Z.take 5) s.basis=0:=(regValue_zero _ _).mpr (fun w hw=>hz w (List.mem_of_mem_take hw))
  simp only[xs,regValue_append,zv,hsrc,Nat.mul_zero,Nat.add_zero]
 rw[Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod xs 7 xlen s.basis,
  Arithmetic.CuccaroStreamedSquareWideLayout.regValue_take_mod ys 7 (by omega) s.basis,xvalue,hys]at val
 norm_num only[show 2^7=128 by decide]at val
 rw[carry_return7_w64 H]at val
 have known:carryBit (u.basis (xs.getD 6 0)) (u.basis (ys.getD 6 0)) (u.basis (carry.getD 5 0))=cacheBit7 H:=
  bool_nat_injective _ _ (val.trans (cacheBit7_value H).symm)
 refine ⟨clean,?_⟩
 change v.basis t=carryBit (v.basis (xs.getD 6 0)) (v.basis (ys.getD 6 0)) (v.basis (carry.getD 5 0))
 rw[outside _ (List.mem_append_left _ (List.mem_append_left _ (DiagSq.getD_in xs 6 (by omega)))),
  outside _ (List.mem_append_left _ (List.mem_append_right _ (DiagSq.getD_in ys 6 (by omega)))),
  outside _ (List.mem_append_right _ (DiagSq.getD_in carry 5 (by omega))),known]
 exact kept
#print axioms source_third_consume_ready
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryConsume
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem consumedAddTriple_frame (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:9≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
 (hcin:s.basis cin=false) (H:Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
 (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉(src++Z.take 5)++ys++carry) (rq:r≠q)
 (tfresh:t∉carry) (tq:t≠q) (tr:t≠r)
 (off:t∉wires (consumedAddDual src Z ys carry cin q r))
 (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) (savedT:s.basis t=cacheBit7 H):
 run (consumedAddTriple src Z ys carry cin q r t) m s=
 setWire (run (consumedAddDual src Z ys carry cin q r) m s) t false:=by
 have enough:7≤carry.length:=by omega
 have xlen:7≤(src++Z.take 5).length:=by simp only[List.length_append];omega
 have nd:=seventh_majority_nd (src++Z.take 5) ys carry cin xlen (by omega) enough hn
 have ne:t≠carry.getD 6 0:=by intro e;exact tfresh (e.symm ▸ DiagSq.getD_in carry 6 (by omega))
 have off':=off
 rw[consumedAddDual_split7 src Z ys carry cin q r hs hy enough]at off'
 simp only[wires_append,Finset.mem_union,not_or]at off'
 have ready:=source_third_consume_ready src Z ys carry cin q r t hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh rfresh rq tfresh tq tr saved savedR savedT
 let pre:=((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))
 have preM:measurementCount pre=0:=by
  have h:=(knownPrefix_counts (src.getD 0 0) (mappedRead (src++Z.take 5) false) (desired src) ys carry cin).2
  change measurementCount (addPre src Z ys carry cin)=0 at h
  simp only[pre,measurementCount_append,h,show measurementCount (move q (carry.getD 4 0))=0 from rfl,
   show measurementCount (move r (carry.getD 5 0))=0 from rfl,Nat.zero_add]
 have result:=secondConsume_correct pre (addPost3 src Z ys carry cin)
  ((src++Z.take 5).getD 6 0) (ys.getD 6 0) (carry.getD 5 0) (carry.getD 6 0) t
  nd ne off'.2 s m (by simpa only[preM,List.take_zero]using ready.1)
  (by simpa only[preM,List.take_zero]using ready.2)
 have split:=consumedAddDual_split7 src Z ys carry cin q r hs hy enough
 rw[seventhMajority]at split
 rw[←split]at result
 simpa only[consumedAddTriple,pre]using result
#print axioms consumedAddTriple_frame
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryBuild
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def buildTriple (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire):Program:=
 buildPre acc Z bank cin src++cachedSubTriple (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p++buildPost acc Z bank cin src
theorem buildTriple_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false) (hr:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (NarrowAcc.build8 acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (rq:r≠q)
    (hp:s.basis p=false) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (buildDual acc Z bank cin src q r)) :
    run (buildTriple acc Z bank cin src q r p) m s=
      setWire (run (buildDual acc Z bank cin src q r) m s) p (cacheBit7 (regValue src s.basis)) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=false := (preFrame.2.2 r racc).trans hr
  have piecesR:=offR
  rw [build_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=false:=(preFrame.2.2 p pacc).trans hp
  have piecesP:=offP
  rw[buildDual]at piecesP
  simp only[wires_append,Finset.mem_union,not_or]at piecesP
  have count:=cachedSubTriple_counts (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p lens.1 lens.2.1 (by omega)
  have changed:=cachedSubTriple_known_frame (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p
   lens.1 lens.2.1 (by omega) nd t
   ((m.drop (measurementCount (buildPre acc Z bank cin src))).take
    (measurementCount (cachedSubDual (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r)))
   clean iv pieces.1.2 piecesR.1.2 rq piecesP.1.2 qt rt pt H xv yv
  have result:=modify_inside (buildPre acc Z bank cin src)
   (cachedSubDual (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r)
   (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p)
   (buildPost acc Z bank cin src) p (cacheBit7 H) count.2.1 piecesP.2 s m changed
  simpa only[buildTriple,buildDual,f]using result
#print axioms buildTriple_frame
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryUnbuild
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def unbuildTriple (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire):Program:=
 unbuildPre acc Z bank cin src++consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p++unbuildPost acc Z bank cin src
theorem unbuildTriple_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (hacc:acc.length=163) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis)) (savedR:s.basis r=cacheBit6 (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src)) (rq:r≠q)
    (savedP:s.basis p=cacheBit7 (regValue src s.basis)) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (unbuildDual acc Z bank cin src q r)) (pq:p≠q) (pr:p≠r) :
    run (unbuildTriple acc Z bank cin src q r p) m s=
      setWire (run (unbuildDual acc Z bank cin src q r) m s) p false := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 163 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=cacheBit6 H := (preFrame.2.2 r racc).trans savedR
  have rbank:r∉bank.take 132 := by intro bad;exact freshR (by simp [List.mem_of_mem_take bad])
  have freshQ:q∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132 := by
    intro bad
    simp only [List.mem_append] at bad
    rcases bad with ((h|h)|h)|h
    · exact fresh (by simp [h])
    · exact fresh (by simp [List.mem_of_mem_take h])
    · exact fresh (by simp [List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact fresh (by simp [List.mem_of_mem_take h])
  have piecesR:=offR
  rw [unbuild_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=cacheBit7 H:=(preFrame.2.2 p pacc).trans savedP
  have pbank:p∉bank.take 132:=by intro bad;exact freshP (by simp[List.mem_of_mem_take bad])
  have freshR':r∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshR (by simp[h])
   · exact freshR (by simp[List.mem_of_mem_take h])
   · exact freshR (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshR (by simp[List.mem_of_mem_take h])
  have piecesP:=offP
  rw[unbuildDual]at piecesP
  simp only[wires_append,Finset.mem_union,not_or]at piecesP
  have count:=consumedAddTriple_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p
   (by omega) hy (by simp[Nat.min_eq_left bankLen])
  have changed:=consumedAddTriple_frame src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p
   (by omega) zlen hy hc nd t
   ((m.drop (measurementCount (unbuildPre acc Z bank cin src))).take
    (measurementCount (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r)))
   zt clean iv H sv yv freshQ freshR' rq pbank pq pr piecesP.1.2 qt rt pt
  have result:=modify_inside (unbuildPre acc Z bank cin src)
   (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r)
   (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) (unbuildPost acc Z bank cin src)
   p false count.2.1 piecesP.2 s m changed
  simpa only[unbuildTriple,unbuildDual]using result
#print axioms unbuildTriple_frame
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryLoopCounts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem buildTriple_counts (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length):
 toffoliCount (buildTriple acc Z bank cin src q r p)=toffoliCount (buildDual acc Z bank cin src q r) ∧
 measurementCount (buildTriple acc Z bank cin src q r p)=measurementCount (buildDual acc Z bank cin src q r) ∧
 Challenge.gateSlots (buildTriple acc Z bank cin src q r p)=Challenge.gateSlots (buildDual acc Z bank cin src q r)+1:=by
 have len:=sub6_lengths acc Z bank src ha hs hz hb
 have count:=cachedSubTriple_counts (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p
  (by omega) (by omega) (by omega)
 simp only[buildTriple,buildDual,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

theorem unbuildTriple_counts (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length):
 toffoliCount (unbuildTriple acc Z bank cin src q r p)+1=toffoliCount (unbuildDual acc Z bank cin src q r) ∧
 measurementCount (unbuildTriple acc Z bank cin src q r p)=measurementCount (unbuildDual acc Z bank cin src q r) ∧
 Challenge.gateSlots (unbuildTriple acc Z bank cin src q r p)+4=Challenge.gateSlots (unbuildDual acc Z bank cin src q r):=by
 have hy:((acc.take 139).drop 6).length=src.length+5:=by simp[ha,hs]
 have hc:7≤(bank.take 132).length:=by simp[Nat.min_eq_left hb]
 have count:=consumedAddTriple_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) hy hc
 simp only[unbuildTriple,unbuildDual,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩
#print axioms buildTriple_counts
#print axioms unbuildTriple_counts
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryLoop
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem cached_wloop_triple_eq (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=163) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (NarrowAcc.build8 acc Z bank cin src) middle s m)):
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s=
 run (buildDual acc Z bank cin src q r++middle++unbuildDual acc Z bank cin src q r) m s:=by
 let H:=regValue src s.basis
 have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hsrc]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have bc:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
 have dc:=buildDual_counts acc Z bank cin src q r hacc hsrc zl bl
 have tc:=buildTriple_counts acc Z bank cin src q r p hacc hsrc zl bl
 let u:=middleState (NarrowAcc.build8 acc Z bank cin src) middle s m
 let t1:=middleState (buildCached acc Z bank cin src q) middle s m
 let t2:=middleState (buildDual acc Z bank cin src q r) middle s m
 let t3:=setWire t2 p (cacheBit7 H)
 have eq1:t1=setWire u q (cacheBit H):=
  middleState_frame_copy _ _ middle q (cacheBit H) bc.2.1 offM s m
   (fun tape=>buildCached_frame acc Z bank cin src q hacc hsrc hf s tape hz hb hi ha zero fresh offF)
 have eq2:t2=setWire t1 r (cacheBit6 H):=
  middleState_frame_copy _ _ middle r (cacheBit6 H) dc.2.1 offMR s m
   (fun tape=>buildDual_frame acc Z bank cin src q r hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq)
 have ready1:WReady acc Z bank cin src H t1:=by
  rw[eq1]
  exact WReady.setWire acc Z bank cin src H u q (cacheBit H) fresh good
 have ready2:WReady acc Z bank cin src H t2:=by
  rw[eq2]
  exact WReady.setWire acc Z bank cin src H t1 r (cacheBit6 H) freshR ready1
 have ready3:WReady acc Z bank cin src H t3:=
  WReady.setWire acc Z bank cin src H t2 p (cacheBit7 H) freshP ready2
 have atq:t2.basis q=cacheBit H:=by
  rw[eq2]
  rw[setWire_basis_outside t1 r q (cacheBit6 H) (Ne.symm rq)]
  rw[eq1]
  simp only[setWire,writeBit,Function.update_self]
 have atr:t2.basis r=cacheBit6 H:=by
  rw[eq2]
  simp only[setWire,writeBit,Function.update_self]
 have saved1:t3.basis q=cacheBit (regValue src t3.basis):=by
  rw[ready3.2.1]
  exact (setWire_basis_outside t2 p q (cacheBit7 H) (Ne.symm pq)).trans atq
 have saved2:t3.basis r=cacheBit6 (regValue src t3.basis):=by
  rw[ready3.2.1]
  exact (setWire_basis_outside t2 p r (cacheBit7 H) (Ne.symm pr)).trans atr
 have saved3:t3.basis p=cacheBit7 (regValue src t3.basis):=by
  rw[ready3.2.1]
  simp only[t3,setWire,writeBit,Function.update_self]
 have av:regValue acc t3.basis=4294968272*regValue src t3.basis:=by rw[ready3.2.1];exact ready3.1
 have forward:=buildTriple_frame acc Z bank cin src q r p hacc hsrc hf s
  (m.take (measurementCount (buildDual acc Z bank cin src q r))) hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP
 have inverse:=unbuildTriple_frame acc Z bank cin src q r p hacc hsrc hf t3
  (m.drop (measurementCount (buildDual acc Z bank cin src q r)+measurementCount middle))
  ready3.2.2.1 ready3.2.2.2.1 ready3.2.2.2.2 av saved1 saved2 fresh offI freshR offIR rq saved3 freshP offIP pq pr
 exact cached_pair_eq (buildDual acc Z bank cin src q r) (buildTriple acc Z bank cin src q r p) middle
  (unbuildDual acc Z bank cin src q r) (unbuildTriple acc Z bank cin src q r p) p (cacheBit7 H)
  tc.2.1 offFP offMP offIP s m zeroP forward inverse
#print axioms cached_wloop_triple_eq
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryDomain
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

theorem spare_ne_product_i (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (i:Nat) (hi:i<258) (h1:1≠i):spare L≠L.core.product.getD i 0:=by
 have nd:L.core.product.Nodup:=by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h:=lay_pos L hn q
  omega
 unfold spare
 rw[List.getD_eq_getElem _ _ (by simp[hw.core.product]),List.getD_eq_getElem _ _ (by simpa[hw.core.product]using hi)]
 intro e
 exact h1 ((List.Nodup.getElem_inj_iff nd).mp e)

theorem spare_ne_eV (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):spare L≠eV L:=by
 have he:eV L=L.core.product.getD 257 0:=by simp[eV,List.getD_eq_getElem?_getD]
 rw[he]
 exact spare_ne_product_i L hw hn 257 (by decide) (by decide)

theorem spare_off_dual (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 spare L∉wires (buildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)) ∧
 spare L∉wires (unbuildDual (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)):=by
 have lens:=acc_lengths L hw
 have fresh:=spare_fresh_domain L hw hn
 have off:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (spare L)
  lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) fresh
 have bc:=buildCached_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
  lens.1 (hiReg_length L hw) (by omega) (by omega)
 have uc:=unbuildConsumed_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
  lens.1 (hiReg_length L hw) (by omega)
 have bd:=buildDual_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
  lens.1 (hiReg_length L hw) (by omega) (by omega)
 have ud:=unbuildDual_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L)
  lens.1 (hiReg_length L hw) (by omega)
 constructor
 · intro h
   rcases Finset.mem_insert.mp (bd h)with e|h
   · exact spare_ne_eV L hw hn e
   · exact (Finset.mem_insert.mp (bc h)).elim (spare_ne_sumCarry L hw hn) off.1
 · intro h
   rcases Finset.mem_insert.mp (ud h)with e|h
   · exact spare_ne_eV L hw hn e
   · exact (Finset.mem_insert.mp (uc h)).elim (spare_ne_sumCarry L hw hn) off.2
#print axioms spare_ne_eV
#print axioms spare_off_dual
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryAFold
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def aFoldTriple (L:CuccaroStreamedSquareWideLayout) (g:Wire):Program:=
 buildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)++aMiddle L g++
 unbuildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
theorem aFoldTriple_eq (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false) (hV:base (eV L)=false) (hP:base (spare L)=false)
    (O : Nat) (hO:O<SquareReduction.p) (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    run (aFoldTriple L g) m s=run (aFoldDual L g) m s := by
  have clean:=L.squareFrame_clean hn base s.basis O hf hc
  have lens:=acc_lengths L hw
  have hz:∀q∈accZ L,s.basis q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact (regValue_zero _ _).mp clean.pad q h
    · exact (regValue_zero _ _).mp clean.work q (List.mem_of_mem_drop h)
  have hb:∀q∈accBank L,s.basis q=false := fun q hq =>
    (regValue_zero _ _).mp clean.pad q (List.mem_of_mem_take hq)
  have ha:regValue (accReg L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp clean.work q (accReg_work L q hq))
  have away:=ParkCarryDevelop.sumCarry_off_regs L hn
  have zero:s.basis L.core.sumCarry=false := (hf.2 _ away.1).trans hsum
  have off:=a_wloop_sumCarry_free L hw hn g hg
  have zeroR:s.basis (eV L)=false :=
    (hf.2 _ (eReg_away L hn _ (eK_mem L hw).2.2.1).1).trans hV
  have freshR:=eV_fresh_domain L hw hn
  have offR:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (eV L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) freshR
  have zeroP:s.basis (spare L)=false:=
   (hf.2 _ (eReg_away L hn _ (spare_mem_eReg L hw)).1).trans hP
  have offP:=spare_off_dual L hw hn
  have eq:=cached_wloop_triple_eq (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
   L.core.sumCarry (eV L) (spare L) (aMiddle L g)
   lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) s m hz hb clean.cin ha zero zeroR zeroP
   (sumCarry_fresh_domain L hn) freshR (eV_ne_sumCarry L hw hn)
   (spare_fresh_domain L hw hn) (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
   off.1 off.2.1 off.2.2 offR.1 (eV_off_amiddle L hw hn g hg) offR.2
   offP.1 (spare_off_amiddle L hw hn g hg) offP.2 (a_middle_good L hw hn g hg base hc O hO s m hf)
  simpa only[aFoldTriple,aFoldDual]using eq

theorem aFoldTriple_frame (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false) (O:Nat) (hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (aFoldTriple L g)
  (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
   else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hs
 rw[aFoldTriple_eq L hw hn g hg base hc hsum hV hP O hO s m hs]
 exact aFoldDual_frame L hw hn g hg base hc hsum hV O hO s m hs
#print axioms aFoldTriple_eq
#print axioms aFoldTriple_frame
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryABody
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def aBodyTriple (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFoldTriple L c)
theorem aBodyTriple_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodyTriple L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have vZero:base (eV L)=false := eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
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
  have hAeq : Acc.accVal base 0 (aAcc L).spec=4294968272*regValue (hiReg L) base := by
    rw [show (aAcc L).spec=earlyHTerms (L.core.product.drop 128) from rfl,accVal_earlyH]
    congr 1
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb,hP]
  have t3 := aFoldTriple_frame L hw hn c hcw base hc hzero vZero (spare_zero L hw base M hP) O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  -- value
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

#print axioms aBodyTriple_frame
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryPrimitiveSupport
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem cachedSubTriple_used (xs ys cs:List Wire) (cin q r:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length):
 cs.getD 6 0∈wires (cachedSubDual xs ys cs cin q r):=by
 rw[cachedSubDual_split7 xs ys cs cin q r hx hc hy]
 simp[secondCopy,insertCopy,seventhMajority,majority,wires_append,wires,Instr.wires]

theorem cachedSubTriple_support (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length):
 wires (cachedSubTriple xs ys cs cin q r t)⊆insert t (wires (cachedSubDual xs ys cs cin q r)):=by
 have split:=cachedSubDual_split7 xs ys cs cin q r hx hc hy
 have used:=cachedSubTriple_used xs ys cs cin q r hx hc hy
 rw[split]at used ⊢
 exact insertCopy_support _ _ _ _ used

theorem cachedSubTriple_physical (xs ys cs:List Wire) (cin q r t:Wire)
 (hx:xs.length=ys.length) (hc:cs.length+1=ys.length) (hy:9≤ys.length)
 (off:t∉wires (cachedSubDual xs ys cs cin q r)) (physical:GatePhysical (cachedSubDual xs ys cs cin q r)):
 GatePhysical (cachedSubTriple xs ys cs cin q r t):=by
 have split:=cachedSubDual_split7 xs ys cs cin q r hx hc hy
 have used:=cachedSubTriple_used xs ys cs cin q r hx hc hy
 have ne:cs.getD 6 0≠t:=by intro e;exact off (e ▸ used)
 rw[split,gatePhysical_append]at physical
 exact insertCopy_physical _ _ _ _ physical.1 physical.2 ne

theorem consumedAddTriple_support (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:9≤src.length) (hy:ys.length=src.length+5) (hc:7≤carry.length):
 wires (consumedAddTriple src Z ys carry cin q r t)⊆insert t (wires (consumedAddDual src Z ys carry cin q r)):=by
 intro w hw
 by_cases eq:w=t
 · exact Finset.mem_insert.mpr (Or.inl eq)
 apply Finset.mem_insert_of_mem
 simp only[consumedAddTriple,wires_append,Finset.mem_union]at hw
 simp only[consumedAddDual_split7 src Z ys carry cin q r hs hy hc,wires_append,Finset.mem_union]
 rcases hw with ((hw|hw)|hw)|hw
 · exact Or.inl (Or.inl (Or.inl hw))
 · exact Or.inl (Or.inl (Or.inr hw))
 · have h:=Finset.mem_insert.mp (consume_support ((src++Z.take 5).getD 6 0) (ys.getD 6 0) (carry.getD 5 0) (carry.getD 6 0) t hw)
   exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
 · exact Or.inr hw

theorem consumedAddTriple_physical (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:9≤src.length) (hy:ys.length=src.length+5) (hc:7≤carry.length)
 (off:t∉wires (consumedAddDual src Z ys carry cin q r)) (physical:GatePhysical (consumedAddDual src Z ys carry cin q r)):
 GatePhysical (consumedAddTriple src Z ys carry cin q r t):=by
 have split:=consumedAddDual_split7 src Z ys carry cin q r hs hy hc
 have used:carry.getD 6 0∈wires (consumedAddDual src Z ys carry cin q r):=by
  rw[split]
  simp[seventhMajority,majority,wires_append,wires,Instr.wires]
 have ne:t≠carry.getD 6 0:=by intro e;exact off (e.symm ▸ used)
 rw[split,gatePhysical_append,gatePhysical_append]at physical
 rw[consumedAddTriple,gatePhysical_append,gatePhysical_append]
 refine ⟨⟨physical.1.1,?_⟩,physical.2⟩
 simp only[move,GatePhysical,List.mem_cons,List.not_mem_nil,or_false]
 intro i hi
 rcases hi with rfl|rfl
 · exact ne
 · exact Ne.symm ne
#print axioms cachedSubTriple_support
#print axioms cachedSubTriple_physical
#print axioms consumedAddTriple_support
#print axioms consumedAddTriple_physical
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryLoopSupport
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem buildTriple_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    wires (buildTriple acc Z bank cin src q r p)⊆insert p (wires (buildDual acc Z bank cin src q r)) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have sub:=cachedSubTriple_support (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p
    (by omega) (by omega) (by omega)
  intro w hw
  by_cases eq:w=p
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [buildTriple,wires_append,Finset.mem_union] at hw
  simp only [buildDual,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem unbuildTriple_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length) :
    wires (unbuildTriple acc Z bank cin src q r p)⊆insert p (wires (unbuildDual acc Z bank cin src q r)) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:7≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have sub:=consumedAddTriple_support src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) hy hc
  intro w hw
  by_cases eq:w=p
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [unbuildTriple,wires_append,Finset.mem_union] at hw
  simp only [unbuildDual,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

theorem buildTriple_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
    (off:p∉wires (buildDual acc Z bank cin src q r)) (physical:GatePhysical (buildDual acc Z bank cin src q r)) :
    GatePhysical (buildTriple acc Z bank cin src q r p) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  rw [buildDual,gatePhysical_append,gatePhysical_append] at physical
  have midOff:p∉wires (cachedSubDual (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r) := by
    intro h;apply off
    simp only [buildDual,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=cachedSubTriple_physical _ _ _ cin q r p (by omega) (by omega) (by omega) midOff physical.1.2
  simp only [buildTriple,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

theorem unbuildTriple_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=163) (hs:src.length=128) (hb:132≤bank.length)
    (off:p∉wires (unbuildDual acc Z bank cin src q r)) (physical:GatePhysical (unbuildDual acc Z bank cin src q r)) :
    GatePhysical (unbuildTriple acc Z bank cin src q r p) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:7≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  rw [unbuildDual,gatePhysical_append,gatePhysical_append] at physical
  have midOff:p∉wires (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r) := by
    intro h;apply off
    simp only [unbuildDual,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=consumedAddTriple_physical src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) hy hc midOff physical.1.2
  simp only [unbuildTriple,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

#print axioms buildTriple_support
#print axioms unbuildTriple_support
#print axioms buildTriple_physical
#print axioms unbuildTriple_physical
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryABodyResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

theorem aBodyTriple_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 toffoliCount (aBodyTriple L c)=2915 ∧ measurementCount (aBodyTriple L c)=3077:=by
 have old:=aBodyDual_counts L hw c
 have lens:=acc_lengths L hw
 have b:=buildTriple_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega) (by omega)
 have u:=unbuildTriple_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega)
 simp only[aBodyTriple,aFoldTriple,aBodyDual,aFoldDual,toffoliCount_append,measurementCount_append]at old ⊢
 omega

theorem aBodyTriple_slots (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 Challenge.gateSlots (aBodyTriple L c)+3=Challenge.gateSlots (aBodyDual L c):=by
 have lens:=acc_lengths L hw
 have b:=buildTriple_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega) (by omega)
 have u:=unbuildTriple_counts (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega)
 simp only[aBodyTriple,aFoldTriple,aBodyDual,aFoldDual,Challenge.gateSlots_append]
 omega

theorem aBodyTriple_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (hn:(c::L.wires).Nodup):GatePhysical (aBodyTriple L c):=by
 have nd:=(List.nodup_cons.mp hn).2
 have lens:=acc_lengths L hw
 have off:=spare_off_dual L hw nd
 have old:=aBodyDual_physical L hw c hn
 simp only[aBodyDual,aFoldDual,gatePhysical_append]at old
 rcases old with ⟨p1,p2,⟨⟨wb,mid⟩,wu⟩⟩
 have bp:=buildTriple_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega) (by omega) off.1 wb
 have up:=unbuildTriple_physical (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega) off.2 wu
 simp only[aBodyTriple,aFoldTriple,gatePhysical_append]
 exact ⟨p1,p2,⟨⟨bp,mid⟩,up⟩⟩

theorem aBodyTriple_refined (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 wires (aBodyTriple L c)⊆insert (spare L) (wires (aBodyDual L c)):=by
 have lens:=acc_lengths L hw
 have b:=buildTriple_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega) (by omega)
 have u:=unbuildTriple_support (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
  lens.1 (hiReg_length L hw) (by omega)
 intro q hq
 by_cases eq:q=spare L
 · exact Finset.mem_insert.mpr (Or.inl eq)
 apply Finset.mem_insert_of_mem
 simp only[aBodyTriple,aFoldTriple,wires_append,Finset.mem_union]at hq
 simp only[aBodyDual,aFoldDual,wires_append,Finset.mem_union]
 rcases hq with h|(h|((h|h)|h))
 · exact Or.inl h
 · exact Or.inr (Or.inl h)
 · have h:=Finset.mem_insert.mp (b h)
   exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inr (Or.inr (Or.inl (Or.inl h))))
 · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
 · have h:=Finset.mem_insert.mp (u h)
   exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inr (Or.inr (Or.inr h)))

#print axioms aBodyTriple_counts
#print axioms aBodyTriple_slots
#print axioms aBodyTriple_physical
#print axioms aBodyTriple_refined
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryDomainExtras
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem spare_ne_eU (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):spare L≠eU L:=by
 have he:eU L=(L.core.product.drop 256).getD 0 0:=by
  unfold eU
  cases h:L.core.product.drop 256 <;> rfl
 have he2:(L.core.product.drop 256).getD 0 0=L.core.product.getD 256 0:=by
  simp[List.getD_eq_getElem?_getD]
 rw[he,he2]
 exact spare_ne_product_i L hw hn 256 (by decide) (by decide)
#print axioms spare_ne_eU
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryHosting
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold ParkCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def hostedATriple (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire):Program:=aBodyTriple (hostLayout L rho) c

theorem hostedATriple_eq (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire)
 (h:rho L.core.sumCarry=L.core.sumCarry):hostedATriple L rho c=aBodyTriple L c:=by
 rw[hostedATriple,host_eq L rho h]

theorem hostedATriple_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 toffoliCount (hostedATriple L rho c)+1=toffoliCount (hostedADual L rho c) ∧
 measurementCount (hostedATriple L rho c)=measurementCount (hostedADual L rho c) ∧
 Challenge.gateSlots (hostedATriple L rho c)+3=Challenge.gateSlots (hostedADual L rho c):=by
 have new:=aBodyTriple_counts (hostLayout L rho) (host_widths L hw rho) c
 have old:=aBodyDual_counts (hostLayout L rho) (host_widths L hw rho) c
 have slots:=aBodyTriple_slots (hostLayout L rho) (host_widths L hw rho) c
 exact ⟨by simp only[hostedATriple,hostedADual,new.1,old.1],by simp only[hostedATriple,hostedADual,new.2,old.2],slots⟩

theorem hostedATriple_refined (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 wires (hostedATriple L rho c)⊆insert (spare L) (wires (hostedADual L rho c)):=by
 have h:=aBodyTriple_refined (hostLayout L rho) (host_widths L hw rho) c
 simpa only[hostedATriple,hostedADual,spare,hostLayout]using h
#print axioms hostedATriple_eq
#print axioms hostedATriple_counts
#print axioms hostedATriple_refined
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarryGlobalSupport
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem aBodyTriple_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (c:Wire):
 wires (aBodyTriple L c)⊆(c::L.wires).toFinset:=by
 intro q hq
 rcases Finset.mem_insert.mp (aBodyTriple_refined L hw c hq)with e|h
 · subst q
   have hp:=spare_mem_product L hw
   simp[CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hp]
 · exact aBodyDual_support L hw hn c h
#print axioms aBodyTriple_support
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

section
-- ThirdSavedCarrySubset
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ThirdSavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold ParkCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem spare_mem_oldA (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 spare L∈wires (aBodyDual L c):=by
 have hs:(negP L).src.length=256:=by simp[negP,hw.core.product]
 have hd:(L.foldDestination (negP L)).length=256:=by simp[foldDestination,negP,hw.core.product,hw.core.work]
 have he:(L.core.product.take 256).getD 1 0=spare L:=by simp[spare,List.getD_eq_getElem?_getD]
 have hp:spare L∈(negP L).src:=by
  change spare L∈L.core.product.take 256
  rw[←he,List.getD_eq_getElem _ _ (by simp[hw.core.product])]
  exact List.getElem_mem _
 have hn:(negP L).src.isEmpty=false:=by
  apply List.isEmpty_eq_false_iff.mpr
  intro h
  have h0:=congrArg List.length h
  rw[hs]at h0
  simp at h0
 have copy:spare L∈wires (copyRegister none (negP L).src (L.foldDestination (negP L))):=by
  rw[copyRegister_wires _ _ _ (hs.trans hd.symm)]
  simp only[hn,Bool.false_eq_true,if_false,Option.toList_none,List.nil_append,List.mem_toFinset,List.mem_append]
  exact Or.inl hp
 simp only[aBodyDual,measuredFoldQTq,wires_append,Finset.mem_union]
 exact Or.inl (Or.inl (Or.inl copy))

theorem aBodyTriple_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 wires (aBodyTriple L c)⊆wires (aBodyDual L c):=by
 intro q h
 rcases Finset.mem_insert.mp (aBodyTriple_refined L hw c h)with e|h
 · exact e ▸ spare_mem_oldA L hw c
 · exact h

theorem hostedATriple_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 wires (hostedATriple L rho c)⊆wires (hostedADual L rho c):=
 aBodyTriple_subset (hostLayout L rho) (host_widths L hw rho) c
#print axioms spare_mem_oldA
#print axioms aBodyTriple_subset
#print axioms hostedATriple_subset
end ThirdSavedCarryDevelop

end -- isolated ParkAThird component

