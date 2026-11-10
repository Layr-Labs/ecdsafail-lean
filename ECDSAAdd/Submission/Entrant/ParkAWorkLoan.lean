import ECDSAAdd.Submission.Entrant.MainPart04Base
import ECDSAAdd.Submission.Entrant.ParkAData

section

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

                                                                                                               
                                                                                 
                                                                        
                                                              
#print axioms hostedATriple_eq
#print axioms hostedATriple_counts
                                   
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

end

section

                           


       
                                                  
                         
                                
                                      
                                       

                                           
               
                            

                                                                                                

                                                                                   
                                                   
                                 
           
                 
              
         
                 
            
                                                                   
                                                          
                                          
            
                  
            
                                                                   
                  
            
                                                                   
                                                              
                                                         

                                                                
                                              
                                                         
                                    
                      

                                                               
                                              
                                                         
                                    
                      
                           
                                  
                   

   

       
                                                  
                         
                                
                            
                                      
                                       

                       
          
             
                
                     

                                     
               
                                         
                                                     
                                                                                   

                                                                     

                                                          

                                                                                                  
                                              
                        

                                                                 
                                        
                                         
             
           
           
                
                                            
                      
              
                 
                                            
                 
                                            
                          
                     
                                                 
                   
                                     
                                             
                                         

                                                                                             
                                    
                                         
                                                 

                                                                                                  
                 
           
                
                                                                       
                                                                 
        
                                    

                                                      
                                                                   
                        

                                                                                      
                                                            
                                  
           
                
                                      
                                                                   
                                                                  
                                                               
                                                                 
                            
                          
                   

   

       
                                                  
                         
                                
                            
                                      
                                       

                                                
                       
                                                                          
                                        
                                                                                      
                                                          

                                                                                         
                                             
                                  
           
                            
                                                     
                                                               
                                                              
                                      
                                            
                                                                                   
                        
                                            
                                            
                                                                         

                                                                        
                                          
                 
           
                            
                                             
                                    
                                      
                                                                  

                                                   
            
                       

                                                                                 
                                   
                        
                                                                                
          
                             
                                   
                   

   

       
                                                  
                         
                                
                            
                                      
                                       

                                                                    
            
                                 
                                                       
                                                 
                         
                                                                  
                                         
                             
                                   
                
                                          
                                              
            
                                                                           
                                                
                                                                
                              
                
               
                                                          

                                                                                           

                                            
                        
          
                

                                                                                        
                                      
                 
      
      
                
                                        

                                                                                                
                 
      
      
                
                                       
                           
                         
                   

   

       
                                                  
                         
                                
                            
                                      
                                       
                                           

                                                    
                                                                           
                  
                                              
                 
            
                                                                                      
                                             
              
         
                     
                                                                         
            
                                          
                                                                         

                                                                                          
                                  
                                                                      

                                                                
                                             
             
                                                            
           
                
                            
                                                                        
              
                 
                             
                 
                             
                                                                        
                     
                             
                             
                                                            
            
                                                       
                            
                           
                         
                         

                                                                   
                                  
                 
           
                            
                           
                         
                                                                                                
              
                                      
                                      

                                                                   
                              
                 
                   
                            
                                    
                               
            
                                          
                         
                         
                                      
                                                              
            
                                                                            
                                      
       
                              
                              
                   

   

       
                                                                           
                         
                                
                                      
                                       
                                           

                                                                           
                                  
                                  
                
                                                               
                                                   

                                                                   
                                       
                 
                          
                            
                                                 
                                                      
                         
                                          
                                      
                                                                     
                         
             
                                               
                                                                                  
         
               
                               
                   

   

       
                                                  
                         
                                
                            
                                      
                                       
                                           

                                                     
                                      
                                                                     
                                                      

                                                                                
                                                                           
                 
           
                                 
                                       
                                              

                                                                                       
                                          
                 
           
                                                                         

                                                                                  
                                  
                 
           
                                                                    

                                                                                  
                                      
                 
            
                                 
                             
             
                                                                 
              
                                          
                                                                             
                     

                                                                                  
                                       
                 
                
                                                                  

                                                      
            
                            

                                                                       
              
                                  
            
                        
                                    
                                                                                    
                                 
                                  
                                   
                   

   

       
                                                  
                         
                                
                            
                                      
                                       
                                           

                                                                                              
                               
                 
                      
                            
                                                                                             
                                      
                                                                                      

                                                                  
            
          
                                    
         
                                 
                                    
                        
                                                                                     
                                             

                                                                                                

                                                                              
              
                                  
            
                               
                                           
                                                                                    
                             
                   

   

       
                                                  
                         
                        
                                
                                      
                                       
                                           

                                                                                           
                                                                 
                                                                            
                   
                              
               
           
                                                                   

                                                                                             
                                                                      
                                                                                  
                                                    
                                                                              
                                    
                                                                                                                        
                
            
                                                                    
       
                                    
                                      
                   

   

       
                                                  
                         
                                
                                      
                                       
                                           

                                                                                                                      

                                                                                                            
             
           
                                                                                               
                                                                                                  
                     
                            
                            
                                                                                                                                         
       

                                                                                                                
                 
           
                            
                               
                                
                                                                                                                
              
                                      
                                           
                                                                                                                    
                                                         
                 

                                                                                                                               
                 
           
                                                                  
                                
                   

   

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
                                                          
                                                                                                
                                                       
                                                        
                                                                     
                                  
                                                                        
                                        
                                                                   
          
                                                                                
                                   
                                                                 
                                                                                                            
                                           
                               
                                


end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                                                          
                                                      
                
                    
                                                
                                                                                     
                                                                                                                                         
                                                                            
                                                                                                                                     
                                      
             
      
                                                                                                                                 
                                                                                                                                              
                                                                          
                                                                                                                                                                                                                                                                                                                                                                   
                                                                                                                                 
                                            
                                            
                                            
                                            
                                            
                                            
                                            
                                            
                                                                                                   
                                       
         
                                             
                                                                   
       
                                                    
                                                                                                                                                                                 
         
                                                     
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                  
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                     
                                                                     
                                                                     
                                                                     
                                                                     
                                                                     
                                                                     
                                                                     
                        
                                                                    
                                                              
                                                      
                                                              
                                                       
                                                                       
                                                                           
                                                       
                                                       
                                                       
                                                               
              
              
                                                               
         
                                                                                                                                                      
                        
                                                                                                                

                                                            
                                            

                                                          
                                                      
                                              
                                                       
                                                                  
                                                                                 
                                
                                        
                                        
                             
                  
                                             
                             
                  
                                                                          
                           
             
                                                                     
                                  
                                             
                                     
              
                                                    
           
                                    
                                 
                                                      
           
                            
                                                                         
                        
              
                                                        
           
                                            
                                                                             
                                                                                      
                          
                
                                                            
             
                                    
                              
                                                 
            
            
                                                                  
                   
                                                                             
                                                                               

                                
                            
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                 
                                                                 
                                                                                                     

                                                                                                              
                                                                                   
                                                      
                                                      
                                                      
                                                   

                                                                                                         
                                                                       
                                                                                      

                                                                                                                              
                                                                         
                                                         
                                                 
                                                                                           
                                                                     
                                                                                                        
                                      
                                                    

def preTriple (xs ys cs:List Wire) (cin q r t:Wire):Program:=
 secondCopy (subPre xs ys cs cin) (sixthMajority xs ys cs) (seventhMajority xs ys cs)
  (cs.getD 4 0) (cs.getD 5 0) q r++[.CX (cs.getD 6 0) t]

                                                                   
                                                                                                           

                                                                    
                                                                       
                                    
                                                                                   
                                                          
                                                  

                                                                      
                                                                    
                                                                                                    
                                                                                      
                                                                                                                              
                                                               
              
                                                              
               
               
                                                               
                
                                                                                                 
                
                                                                
                 
                 
                                                                 
                  
                                                             
                                                                                                    
                                                                                             

                                                            
                                                                                                   

                                                             
                                                                    
                                                                                                     
                                                                                                     
                                            
                                                                 
                                            
                                                                                                                                                                 

                                                                           
                                                                                                                                                                 

                                                                            
                                                                    
                                            
                                                                                                                                                                                     
                                                                  
                             
                                    
                                      
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem thirdCopy_value (pre next next2 post:Program) (c d e q r t w:Wire)
 (hqpre:q∉wires pre) (hqnext:q∉wires next) (hqnext2:q∉wires next2) (hqpost:q∉wires post)
 (hrpre:r∉wires (insertCopy pre next c q)) (hrnext2:r∉wires next2) (hrpost:r∉wires post)
 (htpre:t∉wires (secondCopy pre next next2 c d q r)) (htpost:t∉wires post)
 (mp:measurementCount pre=0) (mn:measurementCount next=0)
 (dq:d≠q) (wq:w≠q) (wr:w≠r) (wt:w≠t)
 (s:State) (hq:s.basis q=false) (hr:s.basis r=false) (ht:s.basis t=false):
 (run (insertCopy (secondCopy pre next next2 c d q r) post e t) [] s).basis w=
 (run (pre++next++next2++post) [] s).basis w:=by
 rw[insertCopy_correct _ _ _ _ htpre htpost s [] ht]
 simp only[writeBit,Function.update_of_ne wt]
 have hqp:q∉wires (next2++post):=by simp only[wires_append,Finset.mem_union,not_or];exact ⟨hqnext2,hqpost⟩
 have hrp:r∉wires (next2++post):=by simp only[wires_append,Finset.mem_union,not_or];exact ⟨hrnext2,hrpost⟩
 have h:=secondCopy_value pre next (next2++post) c d q r w hqpre hqnext hqp hrpre hrp mp mn dq wq wr s hq hr
 simpa only[secondCopy,insertCopy,List.append_assoc]using h

                                                                   
                                                                      
                                                   
                                              
                                              
                                                       
                                                                
                                                                                              
                                                               
                                                     
                                                                                       
                                                                                                                            
                                                                       
                                                                                         
#print axioms thirdCopy_value
                                 
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                         
                                                                      
                                                       
                                                  
                                                     
                                                              
                                                
                                                   
                                                                                    
                                                                               
                                              
                                                       
                                                                                   
                                                                                                                                        
                                         
                                                                                                                                         
                                               
              
              
                   
                                                        
                                                   
         
                                                                                    
                      
                                                                                                                        
                 
                                                                                                         
                                                        
                          
                      
                                                   
                          
                          
                                                    
                          
                          
                                                    
                          
                         
                                                    
                                                     
                                                                                                           
                                                                                                                                
                                                               
                                                                                                              
                                                                                                                                  
                                                                                                                                                                                            
                 
                                                                                
                                                                                                                                                                                                
                                          
                                                 
                                                                               
                                                           
                                                                                                                   
                                                                           
                                                                        
                                       
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
                                                                      
                                                         
                                                 
                                                          
             
                                                                      
                                                                      
                                                                                 
                                                                           
                                                       
                                                       
                                                          
                                            
                                            
                                               
                                                 
                                    
                                         
           
                                               
                                                                       
         
                                                                                
                                
                                    
             
                                        
                                                      
                                                                 
                                                 
         
                                
                                                                                    
                                                                                                    
                                                    
                                                                                          
                         
                                             
                                                                   
                                                            
                                                                  
                                   
               
                                                                   

                                     
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem source_prefix_consumed_eq7 (src Z ys carry:List Wire) (cin q r t:Wire)
 (hs:9≤src.length) (hzl:5≤Z.length) (hy:ys.length=src.length+5) (hc:carry.length+1=ys.length)
 (hn:(cin::((src++Z.take 5)++ys++carry)).Nodup)
 (s:State) (hz:∀w∈Z,s.basis w=false) (hclean:∀w∈carry,s.basis w=false)
 (hcin:s.basis cin=false) (H:Nat) (hsrc:regValue src s.basis=H) (hys:regValue ys s.basis=976*H/64)
 (fresh:q∉(src++Z.take 5)++ys++carry) (rfresh:r∉(src++Z.take 5)++ys++carry) (rq:r≠q)
 (tfresh:t∉carry) (tq:t≠q) (tr:t≠r)
 (saved:s.basis q=cacheBit H) (savedR:s.basis r=cacheBit6 H) (savedT:s.basis t=cacheBit7 H):
 run (((addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0))++move t (carry.getD 6 0)) [] s=
 setWire (setWire (setWire (run (carryPrefix 7 (src++Z.take 5) ys carry cin) [] s) q false) r false) t false:=by
 let xs:=src++Z.take 5
 let pre:=(addPre src Z ys carry cin++move q (carry.getD 4 0))++move r (carry.getD 5 0)
 have xlen:7≤xs.length:=by dsimp[xs];simp only[List.length_append];omega
 have enough:7≤carry.length:=by omega
 have nd:=seventh_majority_nd xs ys carry cin xlen (by omega) enough hn
 have ne:t≠carry.getD 6 0:=by intro e;exact tfresh (e.symm ▸ DiagSq.getD_in carry 6 (by omega))
 have ready:=source_third_consume_ready src Z ys carry cin q r t hs hzl hy hc hn s hz hclean hcin H hsrc hys fresh rfresh rq tfresh tq tr saved savedR savedT
 have rf:r∉carry:=by intro h;exact rfresh (by simp[h])
 have eq6:run pre [] s=setWire (setWire (run (carryPrefix 6 xs ys carry cin) [] s) q false) r false:=
  source_prefix_consumed_eq6 src Z ys carry cin q r (by omega) hzl hy hc hn s hz hclean hcin H hsrc hys fresh rf rq saved savedR
 have result:=secondConsume_correct pre [] (xs.getD 6 0) (ys.getD 6 0) (carry.getD 5 0) (carry.getD 6 0) t
  nd ne (by simp[wires]) s []
  (by simpa only[List.take_nil]using ready.1) (by simpa only[List.take_nil]using ready.2)
 simp only[List.append_nil]at result
 have away (w:Wire) (hw:w∉xs++ys++carry):w∉wires (seventhMajority xs ys carry):=by
  have na:w≠xs.getD 6 0:=by intro e;exact hw (e.symm ▸ List.mem_append_left _ (List.mem_append_left _ (DiagSq.getD_in xs 6 (by omega))))
  have nb:w≠ys.getD 6 0:=by intro e;exact hw (e.symm ▸ List.mem_append_left _ (List.mem_append_right _ (DiagSq.getD_in ys 6 (by omega))))
  have nc:w≠carry.getD 5 0:=by intro e;exact hw (e.symm ▸ List.mem_append_right _ (DiagSq.getD_in carry 5 (by omega)))
  have nd:w≠carry.getD 6 0:=by intro e;exact hw (e.symm ▸ List.mem_append_right _ (DiagSq.getD_in carry 6 (by omega)))
  simp only[List.getD_eq_getElem?_getD]at na nb nc nd
  simp[seventhMajority,majority,wires,Instr.wires,na,nb,nc,nd]
 have qo:=away q fresh
 have ro:=away r rfresh
 have old7:run (pre++seventhMajority xs ys carry) [] s=
  setWire (setWire (run (carryPrefix 7 xs ys carry cin) [] s) q false) r false:=by
  rw[run_append,List.take_nil,List.drop_nil,eq6]
  have commute (w:Wire) (hw:w∉wires (seventhMajority xs ys carry)) (v:State):
   run (seventhMajority xs ys carry) [] (setWire v w false)=setWire (run (seventhMajority xs ys carry) [] v) w false:=by
   exact run_update_outside _ w false hw v []
  rw[commute r ro,commute q qo]
  have ce:=carryPrefix_split7 xs ys carry cin xlen (by omega) enough
  rw[ce,run_append,List.take_nil,List.drop_nil]
 change run (pre++move t (carry.getD 6 0)) [] s=_
 rw[result]
 change setWire (run (pre++seventhMajority xs ys carry) [] s) t false=_
 rw[old7]
#print axioms source_prefix_consumed_eq7
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

                                                                                
                                
                                                         
                                 
          
                                     
                                                 
                                                      
                                            
      

                                                             
                                                      
                                   
                                                                  
                                                      
                                                      
                                                         
                           
                                      
        
                                            
                                                                  
      

                                                                                 
                                                                                              
                                               
                                                                      
                                                                                                  
                                                                                    
                                                        
                                            
                                                                                                                           
                                                                                                                           
                                 
                                                                                                               
                      
                                                   
                                                                                                                           
                                     
                                                                        
                                                      
                                                                     
                                                                                                                                                      
                                                                      
                                              
                                               
                                               
        
                                                                                                        
                                                                             
                                            
                                                                                 
                                                                                                 
                                                  
                                    
        
                                                                                                        
                                                                                                                 
                                                                                          
                                      
                                                                                                           
                                                                 
                                                                                   
                                                                                                        
                                            
                              
                                                                                                                      
                                                             
                  
                                                                                                     
                                                                                                 
                                                                                                
                                                                                
           
                                         
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                    
                                                                       
                                                                                                      
                                                                                                              
                                                                                                                        
                                                       
                                                                                                                                                                                             

                                                                            
                                                                    
                                                                                                                        
                                                                                                                              
                                                                                                                                        
                                                               
                                                                                                                                                                                                                 
                                  
                                    
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop SourceAddFourDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                           
                                                                                              
                                               
                                                                                    
                                                                                                  
                                                                                    
                                                        
                                            
                                                           
                                                                                                                           
                                                      
                                                                           
                                     
                                                                           
                                                                                   
                                                                                               
               
                                                                          
                                                       
                                                                                                                                                                                       
                                                                                                                    
                                     
                                                                                                             
                                                            
                                                                                                     
                                                                                                                                      
                                                                     
                                                                              
                                                                    
                                                   
                                                                           
                           
                    
                                            
                                   
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

                                                                                        
                                                                                     
                                                                                                                                           
                                                                                                
                                               
                                                         
                                                                                      
                                                                                                
                                                                                          
                                                                                                     
                                                            
                                                     
                                                            
                                                           
                                                   
                                                                                                         
                             
                                 
                                                                                                      
                                                                                         
                                                                               
                                                                    
                                                
                                                                                        
                                                
                                                                
             
                 
                                      
                         
                                       
                                                          
                          
                                                                                 
           
                                                                                                      
                                                                                                     
                                                      
                                                                               
                                                             
                                                                                               
                                                   
                                                                                                   
                
                                                                                                         
                                                                                                       
                                                              
                                                                 
                                                            
                                                                                                                  
                                                                    
                                                                            
                          
                                                       
              
                                                 
                                                                  
                                                               
                                                             
                                                           
                  
                            
                                                            
                                                              
                                                           
                    
                             
                                                             
                                                           
                                                         
                    
                         
                                                           
                                                           
                                                         
                    
                           
                                                           
                                                                                                                                        
                                                                                                                    
                                  
                                                                  
                                                                                                                  
                                                                                 
                                                          
                                                                                             
                                                                                             
                                                                                 
                                                 
                             
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop ControlLoan1589BFFold Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

                                                                                          
                                                                                                                                         
                                                                                                  
                                               
                                                         
                                                                                      
                                                                                    
                                                                                                         
                                                                                                      
                                                                                                                 
                                                                                           
                                                                         
                                                                                           
                                                                                        
                                                     
                                                                              
                             
                                 
                                                                                                          
                                                                                     
                                                                                 
                                                                    
                                                
                                                                                        
                                                
                                                                
             
                 
                                      
                         
                                       
                                                          
                          
                                                                                 
           
                                                                                                      
                                                                                                     
                                                              
                                                                                    
                                                                    
                                    
                       
                                   
         
                            
                    
                                        
         
                                                                                                   
                                                                                                                 
                                                                 
                                                      
            
                                    
              
                                                          
                                                   
              
                                                 
                                                                  
                                                               
                                                             
                                                                   
                                                                                             
                  
                              
                                                            
                                                                            
                                                                                                           
                                                              
                                                                     
                                                                                              
                                                                           
             
                                      
                               
                               
                                                    
                                                                           
                                                    
                    
                               
                                                             
                                                           
                                                                   
                                                                          
            
                                   
                              
                              
                                                   
                                                                          
                                                   
                                                           
                                                                   
                                                                                           
                                                                          
            
                                   
                              
                              
                                                   
                                                                          
                                                   
                    
                             
                                                           
                                                                                              
                                                   
                                                                                               
                             
                                                                    
                                                                                                   
                                                                                             
                                                            
                                                                              
                                                                                                               
                                          
                                                   
                               
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

                                                                                         
                                                                              
                                                                                                          
                                                                                                                  
                                                                                                                            
                                                  
                                                                           
                                                                                                             
                                  
                                                                                                        
                                   

                                                                                           
                                                              
                                                                                                                
                                                                                                                      
                                                                                                                                
                                                                    
                                                              
                                                                                                              
                                                                                                            
                                   
                              
                                
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                                                              
                                            
                                                      
                                                                               
                                                                                                                                                  
                                                                                
                                                      
                                                               
                                                                                                                      
                                                                                                                        
                                                                                                        
                                                                              
                                                         
                                                                                                                        
                                                                                                                 
                                                                                                                  
                                                                                                                   
                                                                                                
                                                                                                   
                            
                                               
                                                                               
                                                                                  
                                                                     
                                                                      
                                   
                                                                                                               
                                                            
                
                                                                              
                                                             
                
                                                                              
                                                             
                
                                                                              
                                                             
                
                                                     
                                                                                                 
                                                                        
                                                                                                                                                            
                                                                           
                                                                                            
                                                                                                                                               
                                                                                                          
                                                                                                   
                                                    
                                  
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                
                                                                       
                                                           
                                                       
                                                             

                                                                     
                                                                       
                                                                                                     
                                                               
                                                          
                   
                                      

                                                                      
                                                                      
                                                                                                                 
                                                      
                                                               
                                                          
                                                       
                                         
                                                           

                                                                             
                                                                    
                                                                                                                     
                                                                                                                    
                                                                       
          
                                                                                                                                                                          
           
                
                                          
                               
                                                
                          
                           
                                                                                                                                 
                                                                     
                  

                                                                              
                                                                   
                                                                                                                                 
                                                              
                                                                       
                                                                                
           
                                                              
                                                               
                                                             
                                                            
                                      
                                                                     
           
                       
           
                   
                                   
                                    
                                     
                                      
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop InverseCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
                                                                                                  
                                                                                  
                                                                                                              
                                                   
                                                                           
                                                                                                               
                                    
            
                 
                                           
                                
                                                           
                                                       
                           
                            
                                         
                                                                      
                   

                                                                                                    
                                                                  
                                                                                                                  
                                                                        
                                                                  
                                                                                                              
            
                 
                                           
                                
                                                             
                                                         
                           
                            
                                         
                                                                      
                   

                                                                                                   
                                                                                
                                                                                                                         
                                                             
                                                   
                                                                      
                                                                                
                                                                                                                      
                     
                                                         
                           
                                                                                                         
                                           
                                       

                                                                                                     
                                                                
                                                                                                                             
                                                               
                                                                        
                                                                  
                                                                        
                                                                                                       
                     
                                                           
                           
                                                                                                                                   
                                             
                                       

                               
                                 
                                
                                  
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem triple_middle_ready (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire) (middle:Program)
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
 let t:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 WReady acc Z bank cin src (regValue src s.basis) t ∧
 t.basis q=cacheBit (regValue src s.basis) ∧ t.basis r=cacheBit6 (regValue src s.basis) ∧ t.basis p=cacheBit7 (regValue src s.basis):=by
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
 let t3:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 have eq1:t1=setWire u q (cacheBit H):=
  middleState_frame_copy _ _ middle q (cacheBit H) bc.2.1 offM s m
   (fun tape=>buildCached_frame acc Z bank cin src q hacc hsrc hf s tape hz hb hi ha zero fresh offF)
 have eq2:t2=setWire t1 r (cacheBit6 H):=
  middleState_frame_copy _ _ middle r (cacheBit6 H) dc.2.1 offMR s m
   (fun tape=>buildDual_frame acc Z bank cin src q r hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq)
 have eq3:t3=setWire t2 p (cacheBit7 H):=
  middleState_frame_copy _ _ middle p (cacheBit7 H) tc.2.1 offMP s m
   (fun tape=>buildTriple_frame acc Z bank cin src q r p hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP)
 have ready1:WReady acc Z bank cin src H t1:=by
  rw[eq1]
  exact WReady.setWire acc Z bank cin src H u q (cacheBit H) fresh good
 have ready2:WReady acc Z bank cin src H t2:=by
  rw[eq2]
  exact WReady.setWire acc Z bank cin src H t1 r (cacheBit6 H) freshR ready1
 have ready3:WReady acc Z bank cin src H t3:=by
  rw[eq3]
  exact WReady.setWire acc Z bank cin src H t2 p (cacheBit7 H) freshP ready2
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
  rw[eq3]
  exact (setWire_basis_outside t2 p q (cacheBit7 H) (Ne.symm pq)).trans atq
 have saved2:t3.basis r=cacheBit6 (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  exact (setWire_basis_outside t2 p r (cacheBit7 H) (Ne.symm pr)).trans atr
 have saved3:t3.basis p=cacheBit7 (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  simp only[setWire,writeBit,Function.update_self]
 exact ⟨ready3,by simpa only[ready3.2.1]using saved1,by simpa only[ready3.2.1]using saved2,by simpa only[ready3.2.1]using saved3⟩
#print axioms triple_middle_ready
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

                                                                                                                          
                                            
                                                      
                                                                               
                                                                                                                          
                                                                                
                                                      
                                                                           
                                                                 
                                                                             
                                                                  
                                                                          
                                                     
                                                                                       
                                                       
                                                         
                                         
                                                                                                                        
                                                                                                   
                                                                                                   
                                                                                                              
                                                                                      
                                                                                              
                                                                                                                                                 
                      
                                                                                  
                                                                                                                       
                                                                                                   
                                           
                                                                                                                                         
                                                                                                                                                 
                        
                                    
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                                                                   
                                                                             
                                          
                                                                                                          
                                                                                                      
                                                                                                            
                                                                                                            
                                                                
                                                               
                                          
                                               
                                                       
                          

                                                                                                                    
                                                                             
                                          
                                                                                                 
                                                                                                            
                                                                 
                                                                
                                                
           
                                                
                          
                                      
                      
         
                                                                                       
                                                                                            
                                      
                      
         
                                                                              

                                                                                                                     
                                                                             
                                         
                                                                                                              
                                                                                                                
                                                                                                           
                                                         
                                                                                     
                                                  
                                                                          
                             
                              
                               
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] ECDSAAdd.wires

theorem fresh_off_triple (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (fresh:u∉cin::(src++acc++Z++bank)) (uq:u≠q) (ur:u≠r) (up:u≠p):
 u∉wires (buildTriple acc Z bank cin src q r p) ∧ u∉wires (unbuildTriple acc Z bank cin src q r p):=by
 have hf6:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hs]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have off:=wloop_original_off acc Z bank cin src u ha hs hf fresh
 have bc:=buildCached_support acc Z bank cin src q ha hs zl bl
 have uc:=unbuildConsumed_support acc Z bank cin src q ha hs bl
 have bd:=buildDual_support acc Z bank cin src q r ha hs zl bl
 have ud:=unbuildDual_support acc Z bank cin src q r ha hs bl
 have bt:=buildTriple_support acc Z bank cin src q r p ha hs zl bl
 have ut:=unbuildTriple_support acc Z bank cin src q r p ha hs bl
 constructor
 · intro h
   rcases Finset.mem_insert.mp (bt h)with e|h
   · exact up e
   rcases Finset.mem_insert.mp (bd h)with e|h
   · exact ur e
   exact (Finset.mem_insert.mp (bc h)).elim uq off.1
 · intro h
   rcases Finset.mem_insert.mp (ut h)with e|h
   · exact up e
   rcases Finset.mem_insert.mp (ud h)with e|h
   · exact ur e
   exact (Finset.mem_insert.mp (uc h)).elim uq off.2
#print axioms fresh_off_triple
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop ZeroReadDevelop Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

                                                                                       
                                                                                                            
                                                                                                    
                                                                                           
                                                   
                                                                                      
                                                     
                                                                                                                                                                                
                                                                                                               
                                                                       
                                                         
                             
                                         
              
                                   
                                                
                                                                        
                                                     
                                                                
                                          
                                                                                                
                                                    
                                                                       
                                              
                                    
                                                              
                                      
                                                                                           
                                                           
                                      
                                                               
                                   
                                                                      
                                                                                  
                                                                                                      
                                                                                      
                                                             
                                                                                           
                                                               
                                                                                 
                                                                    
                                                                                                                                           
                                           

                          
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def loan (L:CuccaroStreamedSquareWideLayout):Wire:=L.core.work.getD 163 0

def hasWire (p:Program) (q:Wire):Bool:=p.any (fun i=>decide (q∈i.wires))
theorem hasWire_iff (p:Program) (q:Wire):hasWire p q=true ↔ q∈wires p:=by
 induction p with
 | nil=>simp[hasWire,ECDSAAdd.wires]
 | cons i p ih=>simp_all[hasWire,ECDSAAdd.wires]

def LoanReady (L:CuccaroStreamedSquareWideLayout) (g u:Wire):Prop:=
 u∈L.core.work ∧ u∉L.core.cin::(hiReg L++accReg L++accZ L++accBank L) ∧
 u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L ∧ hasWire (aBodyTriple L g) u=true
instance (L:CuccaroStreamedSquareWideLayout) (g u:Wire):Decidable (LoanReady L g u):=by
 unfold LoanReady
 infer_instance

                                                                        
              
                           
                                                  
                         
                                   
                     

                                                                                             
                                                                                                  
                                                                                  
                                                                    
                                                          
                     
           
      
              
                                                           
              
              
                                                                                                                                        
      
                              
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
                                                                                                
                                                                                                  
                                                                                   
                                                           
                                                                                                             
                                                                                            
             
                                                                 
                                                                    

                                 
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open ThirdSavedCarryDevelop Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

                                                                        
                                                                               
                                                                                                      
                                                                             
                                                                                                                                           
                               
                                                                                                                           
                                                                                                        
                                                             
                                                                                       
              
                                                         
                                                                                        
                                                      
                                                      
                                            
                                                                                         
                                                                                               
                                                                                     
                                                       
                                                             
                                                                                 
                                                                                        
                                                                
                                             
                                                                                                                      
                                                                        
                   
                                                                                   
                                            
                                                                             
                   
                                                                                      
                                                                                        
           
                                                                  
                                                          
                                                                                  
                                                                                                     
                   
                                
                                        
            
                             
                                          
                                                                                        
                                                                                  
                                                            
                                                         
                                                        
                                                                          
                
                                                                                                            
                      
                                                                             
                                                                                  
                                                                                     
                                                                                                                                    
                     
                                                                           
                                                                                                                      
                                                                                                                               
                                                                         
                                         
                                           
                                           
                                                                                                              
                                                   
                                                                                                             
                                              
                                                                                                      
                                       
                                             
                    
                     
                                                     
                                                                                                      
                      
                                           
              
                                                                           
            
                  
                            
                       
                                                                                              
                                                                                                                                    
                                          
                            
             
                           

                                 
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                                                         
                                              
                                                                         
                                                                               
                                                                                         
                            
                                                                                                                
                                                                            
                                                                                                                 
                                                  
                                                                                                                   
                                       
                                              
                    
                                                            
      

                                                                                           
                                                                  
                                                                          
                                                                                  
                     
           
      
              
                                                           
                                    
              
              
                                                               
                                   
                            
                                 
                                     
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                                         
                                                                        
                     
           
      
              
                                                           
                                         
              
                               
                                                                                                                         
                                                                                   
                                 

                                                                                                            
                                                                               
                     
           
      
              
                                                           
                         
              
                               
                                                                                   
                                                                                               
                                            
                                                                                                                          
                                                                                                        
                 

                                                                                        
                                                      
                                                                 
            
                                                      
                          
                                                                
                                    
                                                                               
                 
                                                                            
                    
                     
                                                     
           
                                                            
                          
                                                                       
                                                                                
                

                                                                                           
                                                                                    
                                                                                  
                                    
                                       
                                                                                                                    
                                   

                                                                                         
                                                             
                                         
                                                 
                                                                           
                                             
                           
                                  
                                     
                                    
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ParkCarryDevelop
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                                                                                  

                                                                                             
                                                                                      
                                    

                                                                                                                
                                                                
                                                                 

                                                                                                                   
                                                                              
                                                                                      
                                                                                              
                                                                            
                                                                       
                                                                  
                                                              
                                    
                                       
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop
set_option linter.unusedSimpArgs false

                                                                                         
                                                                                         
                                                                 

                                                                                                            
                                                  
                                                                    
end FourthASavedCarryDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace FourthASavedCarryDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 6000000
attribute [local irreducible] ECDSAAdd.toffoliCount

                                                                                                                          
                                        
                                                  
                                                     
                                                 
      
                             
end FourthASavedCarryDevelop

end


end

section

-- Fourth cached carry extending the published 52bbcfbf third-carry package.

section
-- FourthCarryArithmetic
namespace FourthCarryArithmetic
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

                                                

                                                                   

                                                               
                         
                                                                                     
                                                           
                                                                     

                                                                           
             
                                       
                                        

                                             
                                                
                                                  

                                         
                         
                                                                                     
                                                           
                                                                                     
                                                                                             
                                                          
                                                                
                                                                                      
                                      

                    
                      
end FourthCarryArithmetic

end -- isolated Carry9 component

section
-- FourthCachedMapped
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def cachedMapped4 (cache0 cache1 cache2 cache3 : Wire) (bits : List MappedBit) (ys cs : List Wire) (cin : Wire) : Program :=
 match bits,ys,cs with
 | b0::b1::b2::b3::b4::bs,y0::y1::y2::y3::y4::ys,k0::k1::k2::k3::ks =>
  [.CX cache0 k0]++cachedMapped3 cache1 cache2 cache3 (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (k1::k2::k3::ks) k0++
   mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_=>cachedMapped3 cache0 cache1 cache2 bits ys cs cin

theorem cachedMapped4_eq (cache0 cache1 cache2 cache3 : Wire) (b0 b1 b2 b3 b4 : MappedBit) (bs : List MappedBit)
 (y0 y1 y2 y3 y4 : Wire) (ys : List Wire) (k0 k1 k2 k3 : Wire) (ks : List Wire) (cin : Wire)
 (hn : [y3,k2,k3].Nodup) (ha : ∀q∈b3.wire,q∉[y3,k2,k3]) (s : State) (m : List Bool)
 (ready : (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis cache3=
  carryBit (b3.value (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis y3)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis k2)) :
 run (cachedMapped4 cache0 cache1 cache2 cache3 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin) m s := by
 have hl : cachedMapped4 cache0 cache1 cache2 cache3 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMapped3 cache1 cache2 cache3 (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMapped4,List.append_assoc]
 have hr : cachedMapped3 cache0 cache1 cache2 (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMapped2 cache1 cache2 (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMapped3,List.append_assoc]
 rw [hl,hr,prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMapped3_counts cache1 cache2 cache3 b1 b2 b3 b4 bs y1 y2 y3 y4 ys k1 k2 k3 ks k0).2
 intro r
 exact cachedMapped3_eq cache1 cache2 cache3 b1 b2 b3 b4 bs y1 y2 y3 y4 ys k1 k2 k3 ks k0 hn ha _ r ready

                                                                                                                    
                                                                                              
                                                                                                                                       
                                                                                                                                
                                                                                                                                         
                                                                                                                                        
                                                                                               
                                                                                         
                          
#print axioms cachedMapped4_eq
                                  
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedMixed
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def cachedMixed4 (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (bits : List MappedBit) (ys : List Wire) (flags : List Bool) (cs : List Wire) (cin : Wire) : Program :=
 match bits,ys,flags,cs with
 | b0::b1::b2::b3::b4::bs,y0::y1::y2::y3::y4::ys,_::false::false::false::false::fs,k0::k1::k2::k3::ks =>
  [.CX cache0 k0]++cachedMixed3 cache1 cache2 cache3 expected (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (false::false::false::false::fs) (k1::k2::k3::ks) k0++
   mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin
 | _,_,_,_=>cachedMixed3 cache0 cache1 cache2 expected bits ys flags cs cin

theorem cachedMixed4_eq (cache0 cache1 cache2 cache3 : Wire) (expected d : Bool) (b0 b1 b2 b3 b4 : MappedBit) (bs : List MappedBit)
 (y0 y1 y2 y3 y4 : Wire) (ys : List Wire) (fs : List Bool) (k0 k1 k2 k3 : Wire) (ks : List Wire) (cin : Wire)
 (hn : [y3,k2,k3].Nodup) (ha : ∀q∈b3.wire,q∉[y3,k2,k3]) (s : State) (m : List Bool)
 (ready : (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis cache3=
  carryBit (b3.value (run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis y3)
   ((run [.CX cache2 k2] [] (run [.CX cache1 k1] [] (run [.CX cache0 k0] [] s))).basis k2)) :
 run (cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s := by
 have hl : cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMixed3 cache1 cache2 cache3 expected (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (false::false::false::false::fs) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMixed4,List.append_assoc]
 have hr : cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin=
  [.CX cache0 k0]++(cachedMixed2 cache1 cache2 expected (b1::b2::b3::b4::bs) (y1::y2::y3::y4::ys) (false::false::false::false::fs) (k1::k2::k3::ks) k0++
   (mappedEraseCarry b0 y0 cin k0++mappedSum b0 y0 cin)) := by simp only [cachedMixed3,List.append_assoc]
 rw [hl,hr,prepend_zero [.CX cache0 k0] _ (by rfl),prepend_zero [.CX cache0 k0] _ (by rfl)]
 apply append_equal _ _ _ (cachedMixed3_counts cache1 cache2 cache3 expected false b1 b2 b3 b4 bs y1 y2 y3 y4 ys fs k1 k2 k3 ks k0).2
 intro r
 exact cachedMixed3_eq cache1 cache2 cache3 expected false b1 b2 b3 b4 bs y1 y2 y3 y4 ys fs k1 k2 k3 ks k0 hn ha _ r ready

theorem cachedMixed4_counts (cache0 cache1 cache2 cache3 : Wire) (expected d : Bool) (b0 b1 b2 b3 b4 : MappedBit) (bs : List MappedBit)
 (y0 y1 y2 y3 y4 : Wire) (ys : List Wire) (fs : List Bool) (k0 k1 k2 k3 : Wire) (ks : List Wire) (cin : Wire) :
 toffoliCount (cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin)+1=
  toffoliCount (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) ∧
 measurementCount (cachedMixed4 cache0 cache1 cache2 cache3 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin)=
  measurementCount (cachedMixed3 cache0 cache1 cache2 expected (b0::b1::b2::b3::b4::bs) (y0::y1::y2::y3::y4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) := by
 have h:=cachedMixed3_counts cache1 cache2 cache3 expected false b1 b2 b3 b4 bs y1 y2 y3 y4 ys fs k1 k2 k3 ks k0
 simp only [cachedMixed4,cachedMixed3,toffoliCount_append,measurementCount_append] at *
 exact ⟨by omega,by omega⟩
#print axioms cachedMixed4_eq
#print axioms cachedMixed4_counts
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedRead
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def bit3 (xs : List Wire) : Wire := (xs.drop 3).headD 0

theorem split_five {α : Type} (xs : List α) (h : 5 ≤ xs.length) :
 ∃ a b c d e rest, xs = a::b::c::d::e::rest := by
 obtain ⟨a,b,c,d,rest,rfl⟩ := split_four xs (by omega)
 obtain ⟨e,rest,rfl⟩ := split_one rest (by simpa using h)
 exact ⟨a,b,c,d,e,rest,rfl⟩

theorem fourth_geometry (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire) (xs ys ks : List Wire)
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup) :
 [a3,b3,k0,k1,k2,k3].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h := List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
 omega

theorem mapped4_read_eq (cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire)
 (xs ys ks : List Wire)
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup)
 (away20 : cache2 ≠ k0) (away21 : cache2 ≠ k1)
 (away30 : cache3 ≠ k0) (away31 : cache3 ≠ k1) (away32 : cache3 ≠ k2)
 (s : State) (m : List Bool) (hi : s.basis k2 = false)
 (hk : s.basis cache3 = carryBit (s.basis a3) (s.basis b3) (s.basis cache2)) :
 run (cachedMapped4 cache0 cache1 cache2 cache3 (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMapped3 cache0 cache1 cache2 (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s := by
 have hg := fourth_geometry a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin xs ys ks nd
 have hn : [b3,k2,k3].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hg q
  simp only [List.count_cons,List.count_nil] at h ⊢
  omega
 have ha : a3 ∉ [b3,k2,k3] := by
  have h := List.nodup_cons.mp hg
  intro bad
  apply h.1
  simp only [List.mem_cons,List.mem_singleton] at bad ⊢
  tauto
 apply cachedMapped4_eq cache0 cache1 cache2 cache3 ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩ ⟨some a4,false⟩
  (mappedRead xs false) b0 b1 b2 b3 b4 ys k0 k1 k2 k3 ks cin hn (by simpa using ha) s m
 simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
  not_false_eq_true,not_or,ne_eq,and_true] at hg
 have hax : a3 ≠ k0 ∧ a3 ≠ k1 ∧ a3 ≠ k2 ∧ b3 ≠ k0 ∧ b3 ≠ k1 ∧ b3 ≠ k2 ∧ k2 ≠ k0 ∧ k2 ≠ k1 := by aesop
 rcases hax with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
 simpa [MappedBit.value,run,writeBit,Function.update_apply,away20,away21,away30,away31,away32,
  h0,h1,h2,h3,h4,h5,h6,h7,hi] using hk
#print axioms mapped4_read_eq

theorem mixed4_read_eq (cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire)
 (expected d : Bool) (xs ys ks : List Wire) (fs : List Bool)
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup)
 (away20 : cache2 ≠ k0) (away21 : cache2 ≠ k1)
 (away30 : cache3 ≠ k0) (away31 : cache3 ≠ k1) (away32 : cache3 ≠ k2)
 (s : State) (m : List Bool) (hi : s.basis k2 = false)
 (hk : s.basis cache3 = carryBit (s.basis a3) (s.basis b3) (s.basis cache2)) :
 run (cachedMixed4 cache0 cache1 cache2 cache3 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s=
 run (cachedMixed3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) m s := by
 have hg := fourth_geometry a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin xs ys ks nd
 have hn : [b3,k2,k3].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hg q
  simp only [List.count_cons,List.count_nil] at h ⊢
  omega
 have ha : a3 ∉ [b3,k2,k3] := by
  have h := List.nodup_cons.mp hg
  intro bad
  apply h.1
  simp only [List.mem_cons,List.mem_singleton] at bad ⊢
  tauto
 apply cachedMixed4_eq cache0 cache1 cache2 cache3 expected d ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩ ⟨some a4,false⟩
  (mappedRead xs false) b0 b1 b2 b3 b4 ys fs k0 k1 k2 k3 ks cin hn (by simpa using ha) s m
 simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
  not_false_eq_true,not_or,ne_eq,and_true] at hg
 have hax : a3 ≠ k0 ∧ a3 ≠ k1 ∧ a3 ≠ k2 ∧ b3 ≠ k0 ∧ b3 ≠ k1 ∧ b3 ≠ k2 ∧ k2 ≠ k0 ∧ k2 ≠ k1 := by aesop
 rcases hax with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
 simpa [MappedBit.value,run,writeBit,Function.update_apply,away20,away21,away30,away31,away32,
  h0,h1,h2,h3,h4,h5,h6,h7,hi] using hk
#print axioms mixed4_read_eq
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedSub
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def cachedSub4 (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (bits : List MappedBit) (flags : List Bool)
 (ys cs : List Wire) (cin : Wire) : Program :=
 notRegister ys ++ cachedMixed4 cache0 cache1 cache2 cache3 expected bits ys flags cs cin ++ notRegister ys

theorem sub4_read_eq (cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin : Wire)
 (expected d : Bool) (xs ys ks : List Wire) (fs : List Bool)
 (nd : (cin::(a0::a1::a2::a3::a4::xs)++(b0::b1::b2::b3::b4::ys)++(k0::k1::k2::k3::ks)).Nodup)
 (away2 : cache2 ∉ b0::b1::b2::b3::b4::ys) (away3 : cache3 ∉ b0::b1::b2::b3::b4::ys)
 (away20 : cache2 ≠ k0) (away21 : cache2 ≠ k1)
 (away30 : cache3 ≠ k0) (away31 : cache3 ≠ k1) (away32 : cache3 ≠ k2)
 (s : State) (m : List Bool) (hi : s.basis k2 = false)
 (hk : s.basis cache3 = carryBit (s.basis a3) (!s.basis b3) (s.basis cache2)) :
 run (cachedSub4 cache0 cache1 cache2 cache3 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (d::false::false::false::false::fs) (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s =
 run (cachedSub3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
  (d::false::false::false::false::fs) (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin) m s := by
 have geo := MixedLiteralAdderDevelop.read_geometry (a0::a1::a2::a3::a4::xs) (b0::b1::b2::b3::b4::ys) (k0::k1::k2::k3::ks) cin nd
 have hnd : (b0::b1::b2::b3::b4::ys).Nodup := (List.nodup_append.mp (List.nodup_cons.mp geo.1).2).1
 have hay : a3 ∉ b0::b1::b2::b3::b4::ys := by
  intro h; exact geo.2 a3 (by simp) (List.mem_cons_of_mem _ (List.mem_append_left _ h))
 have hcy : k2 ∉ b0::b1::b2::b3::b4::ys := by
  intro bad
  have hn := List.nodup_append.mp (List.nodup_cons.mp geo.1).2
  exact hn.2.2 k2 bad k2 (by simp) rfl
 have h : ∀ r, run (cachedMixed4 cache0 cache1 cache2 cache3 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
   (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) r
   (run (notRegister (b0::b1::b2::b3::b4::ys)) [] s) =
  run (cachedMixed3 cache0 cache1 cache2 expected (mappedRead (a0::a1::a2::a3::a4::xs) false)
   (b0::b1::b2::b3::b4::ys) (d::false::false::false::false::fs) (k0::k1::k2::k3::ks) cin) r
   (run (notRegister (b0::b1::b2::b3::b4::ys)) [] s) := by
  intro r
  apply mixed4_read_eq cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin
   expected d xs ys ks fs nd away20 away21 away30 away31 away32 _ r
  · rw [notRegister_correct _ hnd]; simpa [hcy] using hi
  · rw [notRegister_correct _ hnd]; simpa [hay,away2,away3] using hk
 have hm := (cachedMixed4_counts cache0 cache1 cache2 cache3 expected d
   ⟨some a0,false⟩ ⟨some a1,false⟩ ⟨some a2,false⟩ ⟨some a3,false⟩ ⟨some a4,false⟩
   (mappedRead xs false) b0 b1 b2 b3 b4 ys fs k0 k1 k2 k3 ks cin).2
 simp only [cachedSub4,cachedSub3,List.append_assoc]
 rw [prepend_zero (notRegister _) _ ((notRegister_counts _).2),prepend_zero (notRegister _) _ ((notRegister_counts _).2)]
 exact append_equal _ _ _ hm _ m h
#print axioms sub4_read_eq
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedGeneral
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem mapped4_read_general (cache0 cache1 cache2 cache3 : Wire) (x y cs : List Wire) (cin : Wire)
 (nd : (cin::x++y++cs).Nodup) (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length)
 (away2 : cache2 ∉ cs) (away3 : cache3 ∉ cs) (s : State) (m : List Bool)
 (hi : s.basis (bit2 cs) = false)
 (hk : s.basis cache3 = carryBit (s.basis (bit3 x)) (s.basis (bit3 y)) (s.basis cache2)) :
 run (cachedMapped4 cache0 cache1 cache2 cache3 (mappedRead x false) y cs cin) m s =
 run (cachedMapped3 cache0 cache1 cache2 (mappedRead x false) y cs cin) m s := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 apply mapped4_read_eq cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin xs ys ks nd
  (by intro he; apply away2; simp [he]) (by intro he; apply away2; simp [he])
  (by intro he; apply away3; simp [he]) (by intro he; apply away3; simp [he])
  (by intro he; apply away3; simp [he]) s m (by simpa [bit2] using hi)
 simpa [bit3] using hk

theorem sub4_read_general (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (x y cs : List Wire)
 (flags : List Bool) (cin : Wire) (nd : (cin::x++y++cs).Nodup)
 (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length) (hf : 5 ≤ flags.length)
 (hf1 : flags.getD 1 false = false) (hf2 : flags.getD 2 false = false)
 (hf3 : flags.getD 3 false = false) (hf4 : flags.getD 4 false = false)
 (away2 : cache2 ∉ y) (away3 : cache3 ∉ y) (awayk2 : cache2 ∉ cs) (awayk3 : cache3 ∉ cs)
 (s : State) (m : List Bool) (hi : s.basis (bit2 cs) = false)
 (hk : s.basis cache3 = carryBit (s.basis (bit3 x)) (!s.basis (bit3 y)) (s.basis cache2)) :
 run (cachedSub4 cache0 cache1 cache2 cache3 expected (mappedRead x false) flags y cs cin) m s =
 run (cachedSub3 cache0 cache1 cache2 expected (mappedRead x false) flags y cs cin) m s := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 obtain ⟨f0,f1,f2,f3,f4,fs,rfl⟩ := split_five flags hf
 have h1 : f1 = false := by simpa using hf1
 have h2 : f2 = false := by simpa using hf2
 have h3 : f3 = false := by simpa using hf3
 have h4 : f4 = false := by simpa using hf4
 subst f1; subst f2; subst f3; subst f4
 apply sub4_read_eq cache0 cache1 cache2 cache3 a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 k0 k1 k2 k3 cin expected f0 xs ys ks fs
  nd away2 away3 (by intro he; apply awayk2; simp [he]) (by intro he; apply awayk2; simp [he])
  (by intro he; apply awayk3; simp [he]) (by intro he; apply awayk3; simp [he])
  (by intro he; apply awayk3; simp [he]) s m (by simpa [bit2] using hi)
 simpa [bit3] using hk

theorem bit3_append (a b : List Wire) (h : 4 ≤ a.length) : bit3 (a++b) = bit3 a := by
 obtain ⟨a0,a1,a2,a3,as,rfl⟩ := split_four a h
 simp [bit3]

theorem bit3_take (a : List Wire) (n : Nat) (h : 4 ≤ n) : bit3 (a.take n) = bit3 a := by
 cases a with
 | nil => simp [bit3]
 | cons a0 as =>
  cases as with
  | nil => simp [bit3]
  | cons a1 as =>
   cases as with
   | nil => simp [bit3]
   | cons a2 as =>
    cases as with
    | nil => simp [bit3]
    | cons a3 as =>
     obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le h
     subst n
     simp [bit3,Nat.add_comm,List.take_succ_cons]

theorem bit3_parity (r : List Wire) (t : BasisState) (hr : 4 ≤ r.length) :
 t (bit3 r) = digit (regValue r t) 3 := by
 obtain ⟨a,b,c,d,rs,rfl⟩ := split_four r hr
 cases ha:t a <;> cases hb:t b <;> cases hc:t c <;> cases hd:t d <;>
  simp [bit3,digit,regValue,ha,hb,hc,hd] <;> omega
#print axioms mapped4_read_general
#print axioms sub4_read_general
#print axioms bit3_parity
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedNarrow
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def sub33CCCC (cache0 cache1 cache2 cache3:Wire) (R Z cs U:List Wire) (cin:Wire):Program :=
 cachedSub4 cache0 cache1 cache2 cache3 true (mappedRead (U++Z.take 1) false)
  MixedLiteralAdderDevelop.upper33 (R.take 33) (cs.take 32) cin

def sub43CCCC (cache0 cache1 cache2 cache3:Wire) (R Z cs U:List Wire) (cin:Wire):Program :=
 cachedSub4 cache0 cache1 cache2 cache3 true (mappedRead (U++Z) false)
  MixedLiteralAdderDevelop.mask43 (R.take 43) (cs.take 42) cin

def addCCCC (cache0 cache1 cache2 cache3:Wire) (x y cs:List Wire) (cin:Wire):Program :=
 cachedMapped4 cache0 cache1 cache2 cache3 (mappedRead x false) y cs cin

theorem sub33CCCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2 cache3:Wire) (h2R:cache2∉R) (h2C:cache2∉cs) (h3R:cache3∉R) (h3C:cache3∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache3=carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2)):
 run (sub33CCCC cache0 cache1 cache2 cache3 R Z cs U cin) m s=
 run (sub33CCC cache0 cache1 cache2 R Z cs U cin) m s := by
 unfold sub33CCCC sub33CCC
 apply sub4_read_general cache0 cache1 cache2 cache3 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simpa using g.ndU 1 0 33 32)
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c]) (by decide) (by decide) (by decide) (by decide) (by decide)
  (fun h=>h2R (List.mem_of_mem_take h)) (fun h=>h3R (List.mem_of_mem_take h))
  (fun h=>h2C (List.mem_of_mem_take h)) (fun h=>h3C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit2_mem;simp[g.c]
 · simpa[bit3_append U _ (by rw[g.u];decide),bit3_take R 33 (by decide)]using hk

theorem sub43CCCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2 cache3:Wire) (h2R:cache2∉R) (h2C:cache2∉cs) (h3R:cache3∉R) (h3C:cache3∉cs)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache3=carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2)):
 run (sub43CCCC cache0 cache1 cache2 cache3 R Z cs U cin) m s=
 run (sub43CCC cache0 cache1 cache2 R Z cs U cin) m s := by
 unfold sub43CCCC sub43CCC
 apply sub4_read_general cache0 cache1 cache2 cache3 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simpa using g.ndUZ 0 43 42)
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c]) (by decide) (by decide) (by decide) (by decide) (by decide)
  (fun h=>h2R (List.mem_of_mem_take h)) (fun h=>h3R (List.mem_of_mem_take h))
  (fun h=>h2C (List.mem_of_mem_take h)) (fun h=>h3C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit2_mem;simp[g.c]
 · simpa[bit3_append U _ (by rw[g.u];decide),bit3_take R 43 (by decide)]using hk

theorem addCCCC_eq {R S Z cs U:List Wire} {cin:Wire} (g:Geo R S Z cs U cin)
 (cache0 cache1 cache2 cache3:Wire) (h2C:cache2∉cs) (h3C:cache3∉cs)
 (j n i:Nat) (hn: 5 ≤ n) (hc: 4 ≤ i)
 (s:State) (m:List Bool) (hi:∀q∈cs,s.basis q=false)
 (hk:s.basis cache3=carryBit (s.basis (bit3 U)) (s.basis (bit3 R)) (s.basis cache2)):
 run (addCCCC cache0 cache1 cache2 cache3 (U++Z.take j) (R.take n) (cs.take i) cin) m s=
 run (addCCC cache0 cache1 cache2 (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 apply mapped4_read_general cache0 cache1 cache2 cache3 (U++Z.take j) (R.take n) (cs.take i) cin
  (by simpa using g.ndU j 0 n i) (by simp[g.u];omega) (by simp[g.r];omega)
  (by simp[g.c];omega) (fun h=>h2C (List.mem_of_mem_take h)) (fun h=>h3C (List.mem_of_mem_take h)) s m
 · apply hi;apply List.mem_of_mem_take;apply bit2_mem;simp[g.c];omega
 · simpa[bit3_append U _ (by rw[g.u];decide),bit3_take R n (by omega)]using hk

#print axioms sub33CCCC_eq
#print axioms sub43CCCC_eq
#print axioms addCCCC_eq
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryNumbers
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

def carryLow4 (u d : Nat) : Bool := carryBit (digit u 3) (digit d 3) (carryLow3 u d)

theorem carryLow3_mod16 (u d : Nat) : carryLow3 (u%16) (d%16) = carryLow3 u d := by
 simp only [carryLow3,carryLow2_mod16,digit_mod16 u ⟨2,by decide⟩,digit_mod16 d ⟨2,by decide⟩]

theorem sub_fourth_fin16 : ∀ (u d : Fin 16),
 carryBit (digit u.val 3) (!(digit (u.val+d.val) 3)) (carryLow3 u.val d.val) = carryLow4 u.val d.val := by decide +kernel

theorem sub_fourth (u d k : Nat) (hk : k%16 = 1) :
 carryBit (digit u 3) (!(digit (u+k*d) 3)) (carryLow3 u d) = carryLow4 u d := by
 have h := sub_fourth_fin16 ⟨u%16,by omega⟩ ⟨d%16,by omega⟩
 have hs : (u%16+d%16)%16 = (u+k*d)%16 := by simp [Nat.add_mod,Nat.mul_mod,hk]
 have de := digit_congr16 _ _ hs ⟨3,by decide⟩
 have du := digit_mod16 u ⟨3,by decide⟩
 have dd := digit_mod16 d ⟨3,by decide⟩
 simpa only [carryLow4,carryLow3_mod16,de,du,dd] using h

theorem digit3_mul_one (d k : Nat) (hk : k%16 = 1) : digit (k*d) 3 = digit d 3 := by
 apply digit_congr16 _ _ _ ⟨3,by decide⟩
 simp [Nat.mul_mod,hk]
#print axioms sub_fourth
#print axioms digit3_mul_one
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedSpecs
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem ps_fourth {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
 (cache3 : Wire) (hR : cache3 ∉ R) (hS : cache3 ∉ S) (t : BasisState)
 (u V D : Nat) (hu : regValue U t = u) (s : State) (h : PS R S t V D s.basis) :
 s.basis (bit3 U) = digit u 3 ∧ s.basis (bit3 R) = digit V 3 ∧ s.basis cache3 = t cache3 := by
 have uv : regValue U s.basis = u :=
  (regValue_congr U _ _ (fun q hq => h.2.2 q (g.UR q hq) (g.US q hq))).trans hu
 refine ⟨?_,?_,h.2.2 cache3 hR hS⟩
 · simpa only [uv] using bit3_parity U s.basis (by rw [g.u]; decide)
 · simpa only [h.1] using bit3_parity R s.basis (by rw [g.r]; decide)

theorem sub33CCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
 (cache : Wire) (hR : cache ∉ R) (hS : cache ∉ S) {t : BasisState}
 (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
 (hk : t cache = ((u%2==1)&&(d%2==1)))
 (cache1 : Wire) (h1R : cache1 ∉ R) (h1S : cache1 ∉ S) (h1C : cache1 ∉ cs) (hk1 : t cache1 = carryLow2 u d)
 (cache2 : Wire) (h2R : cache2 ∉ R) (h2S : cache2 ∉ S) (h2C : cache2 ∉ cs) (hk2 : t cache2 = carryLow3 u d)
 (cache3 : Wire) (h3R : cache3 ∉ R) (h3S : cache3 ∉ S) (h3C : cache3 ∉ cs) (hk3 : t cache3 = carryLow4 u d) :
 Triple (PS R S t (u+d) 0) (sub33CCCC cache cache1 cache2 cache3 R Z cs U cin) (PS R S t d 0) := by
 intro s m h
 obtain ⟨bu,br,b3⟩ := ps_fourth g cache3 h3R h3S t u (u+d) 0 hu s h
 have b2 : s.basis cache2 = t cache2 := h.2.2 cache2 h2R h2S
 have ready : s.basis cache3 = carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2) := by
  rw [bu,br,b3,b2,hk2,hk3]
  simpa only [Nat.one_mul] using (sub_fourth u d 1 (by decide)).symm
 rw [sub33CCCC_eq g cache cache1 cache2 cache3 h2R h2C h3R h3C s m (ps_cs g cl.c _ _ s h) ready]
 exact sub33CCC_spec g cache hR hS cl u d hu hu32 hd hk cache1 h1R h1S h1C hk1 cache2 h2R h2S h2C hk2 s m h

theorem addCCCC_ps_loose {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin)
 (cache : Wire) (hR : cache ∉ R) (hS : cache ∉ S) {t : BasisState}
 (hcin : t cin = false) (u d V D : Nat) (hu : regValue U t = u)
 (hk : t cache = ((u%2==1)&&(d%2==1))) (hV : V%2 = d%2)
 (j n i : Nat) (hn : 5 ≤ n) (hc : 4 ≤ i)
 (cache1 : Wire) (h1R : cache1 ∉ R) (h1S : cache1 ∉ S) (h1C : cache1 ∉ cs)
 (hk1 : t cache1 = carryLow2 u d) (hV1 : V/2%2 = d/2%2) (hcs : ∀ q ∈ cs, t q = false)
 (cache2 : Wire) (h2R : cache2 ∉ R) (h2S : cache2 ∉ S) (h2C : cache2 ∉ cs)
 (hk2 : t cache2 = carryLow3 u d) (hV2 : digit V 2 = digit d 2)
 (cache3 : Wire) (h3R : cache3 ∉ R) (h3S : cache3 ∉ S) (h3C : cache3 ∉ cs)
 (hk3 : t cache3 = carryLow4 u d) (hV3 : digit V 3 = digit d 3)
 (s : State) (m : List Bool) (h : PS R S t V D s.basis) :
 run (addCCCC cache cache1 cache2 cache3 (U++Z.take j) (R.take n) (cs.take i) cin) m s =
 run (addInPlace (U++Z.take j) (R.take n) (cs.take i) cin) m s := by
 obtain ⟨bu,br,b3⟩ := ps_fourth g cache3 h3R h3S t u V D hu s h
 have b2 : s.basis cache2 = t cache2 := h.2.2 cache2 h2R h2S
 have ready : s.basis cache3 = carryBit (s.basis (bit3 U)) (s.basis (bit3 R)) (s.basis cache2) := by
  rw [bu,br,b3,b2,hk2,hk3,hV3]
  rfl
 rw [addCCCC_eq g cache cache1 cache2 cache3 h2C h3C j n i hn hc s m (ps_cs g hcs V D s h) ready]
 exact addCCC_ps_loose g cache hR hS hcin u d V D hu hk hV j n i (by omega) (by omega)
  cache1 h1R h1S h1C hk1 hV1 hcs cache2 h2R h2S h2C hk2 hV2 s m h
#print axioms sub33CCCC_spec
#print axioms addCCCC_ps_loose
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCachedSub43Spec
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem sub43CCCCK_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
 (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
 (cache : Wire) (hR : cache ∉ R) (hS : cache ∉ S) (hZ : cache ∉ Z)
 (hk : t cache = ((u%2==1)&&(d%2==1))) (k : Wire) (hkZ : k ∉ Z)
 (cache1 : Wire) (h1R : cache1 ∉ R) (h1S : cache1 ∉ S) (h1Z : cache1 ∉ Z) (h1C : cache1 ∉ cs)
 (hk1 : t cache1 = carryLow2 u d)
 (cache2 : Wire) (h2R : cache2 ∉ R) (h2S : cache2 ∉ S) (h2Z : cache2 ∉ Z) (h2C : cache2 ∉ cs)
 (hk2 : t cache2 = carryLow3 u d)
 (cache3 : Wire) (h3R : cache3 ∉ R) (h3S : cache3 ∉ S) (h3Z : cache3 ∉ Z) (h3C : cache3 ∉ cs)
 (hk3 : t cache3 = carryLow4 u d) :
 Triple (PS R S (kz t k Z) (u+4294968273*d+2^32*(976*(if t k then 1 else 0))) 0)
  (sub43CCCC cache cache1 cache2 cache3 R Z cs U cin) (PS R S (kz t k Z) (4294968273*d) 0) := by
 intro s m h
 obtain ⟨bu,br,b3⟩ := ps_fourth g cache3 h3R h3S (kz t k Z) u _ 0 ((kz_u g t k).trans hu) s h
 have b2 : s.basis cache2 = t cache2 :=
  (h.2.2 cache2 h2R h2S).trans (kz_out t k Z g.z cache2 h2Z)
 have b33 : s.basis cache3 = t cache3 := b3.trans (kz_out t k Z g.z cache3 h3Z)
 have hcs : ∀ q ∈ cs, kz t k Z q = false := by
  intro q hq
  have qZ : q ∉ Z := fun bad => g.away cs Z q hq bad (by simp only [List.count_cons,List.count_append,List.count_nil]; omega)
  exact (kz_out t k Z g.z q qZ).trans (cl.c q hq)
 have ready : s.basis cache3 = carryBit (s.basis (bit3 U)) (!s.basis (bit3 R)) (s.basis cache2) := by
  rw [bu,br,b33,b2,hk2,hk3]
  have hp : digit (u+4294968273*d+2^32*(976*(if t k then 1 else 0))) 3 = digit (u+4294968273*d) 3 := by
   cases t k <;> norm_num [digit] <;> omega
  rw [hp]
  exact (sub_fourth u d 4294968273 (by decide)).symm
 rw [sub43CCCC_eq g cache cache1 cache2 cache3 h2R h2C h3R h3C s m (ps_cs g hcs _ _ s h) ready]
 exact sub43CCCK_spec g cl u d hu hu32 hd cache hR hS hZ hk k hkZ
  cache1 h1R h1S h1Z h1C hk1 cache2 h2R h2S h2Z h2C hk2 s m h
#print axioms sub43CCCCK_spec
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryArms
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop WinArith
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
def fwdCCCC (R S Z cs U : List Wire) (cin k cache cache1 cache2 cache3 : Wire) : Program :=
  sub33CCCC cache cache1 cache2 cache3 R Z cs U cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  (WinArithAux3SmallDevelop.smallF R S cs cin ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (kpat k Z ++ (addCCCC cache cache1 cache2 cache3 (U ++ Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin ++ kpat k Z))))))

theorem fwdCCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d)
    (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2Z:cache2∉Z) (h2C:cache2∉cs)
    (hcache2:t cache2=carryLow3 u d)
    (cache3:Wire) (h3R:cache3∉R) (h3S:cache3∉S) (h3Z:cache3∉Z) (h3C:cache3∉cs)
    (hcache3:t cache3=carryLow4 u d) :
    Triple (PS R S t (u+d) 0) (fwdCCCC R S Z cs U cin k cache cache1 cache2 cache3)
      (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) := by
  have s1 := sub33CCCC_spec g cache hR hS cl u d hu hu32 hd hcache cache1 h1R h1S h1C hcache1 cache2 h2R h2S h2C hcache2 cache3 h3R h3S h3C hcache3
  have s2 := tcopy_in R S 0 t d 0 (by rw [g.r]; omega) g.s (g.ndIn 0) g.SR
  have s3 := WinArithAux3SmallDevelop.smallF_spec g cl d hd
  have s4 := tcopy_out R S 32 t (977*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s5 := tcopy_in R S 32 t (977*d + 2^32*d) d (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have p1 := kpat_PS g k hkR hkS hkZ t (977*d + 2^32*d) 0
  have cinZ : cin ∉ Z := fun h => g.away [cin] Z cin (by simp) h
    (by simp only [List.count_cons, List.count_append, List.count_nil]; omega)
  have csZ : ∀ q ∈ cs, q ∉ Z := fun q h1 h2 => g.away cs Z q h1 h2
    (by simp only [List.count_cons, List.count_append]; omega)
  have kzc : kz t k Z cin = false := by
    have : cin ∉ zpat Z := fun h => cinZ (zpat_sub Z g.z cin h)
    simp [kz, this, cl.cin]
  have kzs : ∀ q ∈ cs.take 42, kz t k Z q = false := by
    intro q hq
    have hq' := List.mem_of_mem_take hq
    have : q ∉ zpat Z := fun h => csZ q hq' (zpat_sub Z g.z q h)
    simp [kz, this, cl.c q hq']
  have s6old := tstep_add R S (U ++ Z.take 11) (cs.take 42) cin 0 43 (kz t k Z) (977*d + 2^32*d) 0
    (u + 2^32*(976*(if t k then 1 else 0))) g.rnd (by simp [g.r])
    (g.ndU 11 0 43 42) (by simp [g.u, g.z]) (by simp [g.c]) g.SR g.cinR g.cinS (g.csR 42) (g.csS 42) kzc
    kzs (valK g cl u hu k hkZ _ _) (by
      have hv : 977*d + 2^32*d < 2^42 := by omega
      rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt (by omega : 977*d + 2^32*d < 2^43)]
      cases t k <;> simp <;> omega)
  have s6 : Triple (PS R S (kz t k Z) (977*d+2^32*d) 0)
      (addCCCC cache cache1 cache2 cache3 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin)
      (PS R S (kz t k Z) (977*d+2^32*d+2^0*(u+2^32*(976*(if t k then 1 else 0)))) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCCCC_ps_loose g cache hR hS kzc u d (977*d+2^32*d) 0
      ((kz_u g t k).trans hu) ((kz_out t k Z g.z cache hZ).trans hcache)
      (by omega) 11 43 42 (by decide) (by decide)
      cache1 h1R h1S h1C ((kz_out t k Z g.z cache1 h1Z).trans hcache1)
      (by
        have hsum:977*d+2^32*d=4294968273*d:=by norm_num;omega
        rw[hsum]
        simpa only[Nat.zero_add] using low2_mul 0 d 4294968273 (by decide)) (by
        intro q hq
        exact (kz_out t k Z g.z q (csZ q hq)).trans (cl.c q hq))
      cache2 h2R h2S h2C ((kz_out t k Z g.z cache2 h2Z).trans hcache2) (by
        have hsum:977*d+2^32*d=4294968273*d:=by norm_num;omega
        rw[hsum]
        exact digit_mul_one d 4294968273 (by decide))
      cache3 h3R h3S h3C ((kz_out t k Z g.z cache3 h3Z).trans hcache3) (by
        have hsum:977*d+2^32*d=4294968273*d:=by norm_num;omega
        rw[hsum]
        exact digit3_mul_one d 4294968273 (by decide)) s m hs]
    exact s6old s m hs
  have p2 := kpat_PS g k hkR hkS hkZ (kz t k Z) (977*d + 2^32*d + 2^0*(u + 2^32*(976*(if t k then 1 else 0)))) 0
  rw [kz_kz t k Z g.z hkZ] at p2
  have a4 : 977*d % 2^32 + 2^32*((((977*d) / 2^32) % 2^10 ^^^ d) + 2^10*(977*d / 2^(32+10))) =
      977*d + 2^32*d := by
    have a : 977*d % 2^32 = 977*d := Nat.mod_eq_of_lt (by omega)
    have b : (977*d / 2^32) % 2^10 = 0 := by rw [Nat.div_eq_of_lt (by omega), Nat.zero_mod]
    have c : 977*d / 2^(32+10) = 0 := Nat.div_eq_of_lt (by norm_num <;> omega)
    rw [a, b, c, Nat.zero_xor]; ring
  have a5 : d ^^^ (((977*d + 2^32*d) / 2^32) % 2^10) = 0 := by
    have a : ((977*d + 2^32*d) / 2^32) % 2^10 = d := by
      rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), Nat.zero_add,
        Nat.mod_eq_of_lt (by omega)]
    rw [a, Nat.xor_self]
  have a2 : 0 ^^^ ((d / 2^0) % 2^10) = d := by
    rw [Nat.zero_xor]; norm_num; omega
  unfold fwdCCCC
  exact seqv s1 (PS_val (by omega)) (seqv s2 (PS_dval a2)
    (seqv s3 (fun _ h => h) (seqv s4 (PS_val a4) (seqv s5 (PS_dval a5)
    (seqv p1 (fun _ h => h) (seqv s6 (fun _ h => h)
    (Triple.conseq (fun s h => h) p2 (PS_val (by cases t k <;> simp <;> omega)))))))))


def invCCCC (R S Z cs U : List Wire) (cin k cache cache1 cache2 cache3 : Wire) : Program :=
  kpat k Z ++ (sub43CCCC cache cache1 cache2 cache3 R Z cs U cin ++ (kpat k Z ++
  (copyRegister none ((R.drop 32).take 10) S ++
  (copyRegister none S ((R.drop 32).take 10) ++
  (WinArithAux3SmallDevelop.smallI R S cs cin ++
  (copyRegister none ((R.drop 0).take 10) S ++
  addCCCC cache cache1 cache2 cache3 (U ++ Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin))))))

theorem invCCCC_spec {R S Z cs U : List Wire} {cin : Wire} (g : Geo R S Z cs U cin) {t : BasisState}
    (cl : Clean Z cs cin t) (u d : Nat) (hu : regValue U t = u) (hu32 : u < 2^32) (hd : d ≤ 976)
    (cache : Wire) (hR : cache∉R) (hS : cache∉S) (hZ : cache∉Z)
    (hcache : t cache=((u%2==1) && (d%2==1))) (k : Wire) (hkR : k ∉ R) (hkS : k ∉ S) (hkZ : k ∉ Z) (_h35 : u + d < 2^35)
    (cache1 : Wire) (h1R : cache1∉R) (h1S : cache1∉S) (h1Z : cache1∉Z) (h1C : cache1∉cs)
    (hcache1 : t cache1=carryLow2 u d)
    (cache2:Wire) (h2R:cache2∉R) (h2S:cache2∉S) (h2Z:cache2∉Z) (h2C:cache2∉cs)
    (hcache2:t cache2=carryLow3 u d)
    (cache3:Wire) (h3R:cache3∉R) (h3S:cache3∉S) (h3Z:cache3∉Z) (h3C:cache3∉cs)
    (hcache3:t cache3=carryLow4 u d) :
    Triple (PS R S t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0) (invCCCC R S Z cs U cin k cache cache1 cache2 cache3)
      (PS R S t (u+d) 0) := by
  have p1 := kpat_PS g k hkR hkS hkZ t (u + 4294968273*d + 2^32*(976*(if t k then 1 else 0))) 0
  have s1 := sub43CCCCK_spec g cl u d hu hu32 hd cache hR hS hZ hcache k hkZ cache1 h1R h1S h1Z h1C hcache1 cache2 h2R h2S h2Z h2C hcache2 cache3 h3R h3S h3Z h3C hcache3
  have p2 := kpat_PS g k hkR hkS hkZ (kz t k Z) (4294968273*d) 0
  rw [kz_kz t k Z g.z hkZ] at p2
  have s2 := tcopy_in R S 32 t (977*d + 2^32*d) 0 (by rw [g.r]; omega) g.s (g.ndIn 32) g.SR
  have s3 := tcopy_out R S 32 t (977*d + 2^32*d) d g.rnd (by rw [g.r]; omega) g.s (g.ndOut 32) g.SR
  have s4 := WinArithAux3SmallDevelop.smallI_spec g cl d hd
  have s5 := tcopy_in R S 0 t d d (by rw [g.r]; omega) g.s (g.ndIn 0) g.SR
  have s6old := tstep_add R S (U ++ Z.take 1) (cs.take 32) cin 0 33 t d 0 u g.rnd (by rw [g.r];omega)
    (g.ndU 1 0 33 32) (by simp [g.u,g.z]) (by simp [g.c]) g.SR g.cinR g.cinS (g.csR 32) (g.csS 32) cl.cin
    (fun q h=>cl.c q (List.mem_of_mem_take h)) (valUZ g cl u hu 1 _ _) (by norm_num at _h35 ⊢; omega)
  have s6 : Triple (PS R S t d 0)
      (addCCCC cache cache1 cache2 cache3 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin)
      (PS R S t (d+2^0*u) 0) := by
    intro s m hs
    simp only [List.drop_zero]
    rw [addCCCC_ps_loose g cache hR hS cl.cin u d d 0 hu hcache rfl
      1 33 32 (by decide) (by decide) cache1 h1R h1S h1C hcache1 rfl cl.c cache2 h2R h2S h2C hcache2 rfl cache3 h3R h3S h3C hcache3 rfl s m hs]
    exact s6old s m hs
  have a : ((977*d + 2^32*d) / 2^32) % 2^10 = d := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), Nat.zero_add,
      Nat.mod_eq_of_lt (by omega)]
  have a2 : 0 ^^^ (((977*d + 2^32*d) / 2^32) % 2^10) = d := by rw [a, Nat.zero_xor]
  have a3 : (977*d + 2^32*d) % 2^32 + 2^32*((((977*d + 2^32*d) / 2^32) % 2^10 ^^^ d) +
      2^10*((977*d + 2^32*d) / 2^(32+10))) = 977*d := by
    have b : (977*d + 2^32*d) % 2^32 = 977*d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have c : (977*d + 2^32*d) / 2^(32+10) = 0 := Nat.div_eq_of_lt (by norm_num <;> omega)
    rw [a, b, c, Nat.xor_self]; ring
  have a5 : d ^^^ ((d / 2^0) % 2^10) = 0 := by
    rw [show (d / 2^0) % 2^10 = d by norm_num; omega, Nat.xor_self]
  unfold invCCCC
  exact seqv p1 (fun _ h => h) (seqv s1 (fun _ h => h) (seqv p2 (PS_val (by ring))
    (seqv s2 (PS_dval a2) (seqv s3 (PS_val a3)
    (seqv s4 (fun _ h => h) (seqv s5 (PS_dval a5)
    (Triple.conseq (fun s h => h) s6 (PS_val (by omega)))))))))

#print axioms fwdCCCC_spec
#print axioms invCCCC_spec
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryMiddle
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
def wFwdCCCC (L:CuccaroStreamedSquareWideLayout) (cache cache1 cache2 cache3:Wire):Program :=
 fwdCCCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1 cache2 cache3
def wInvCCCC (L:CuccaroStreamedSquareWideLayout) (cache cache1 cache2 cache3:Wire):Program :=
 invCCCC (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (eU L) cache cache1 cache2 cache3
theorem wMidCCCC_step (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cache : Wire) (cacheE : cache∈eReg L) (cache1 : Wire) (cache1E : cache1∈eReg L) (cache2:Wire) (cache2E:cache2∈eReg L) (cache3:Wire) (cache3E:cache3∈eReg L)
    (base : BasisState) (hc : L.PairClean base) (O E b1 : Nat) (hb1 : regValue (hiReg L) base = b1)
    (hb1lt : b1 < 2^128) (hO : O < SquareReduction.p)
    (K : Nat) (hK : K ≤ 1) :
    Triple (fun x=> BState L base O E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache2=carryLow3 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache3=carryLow4 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3))
      (fun x=> BState L base (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 4294968272*2^32*K +
        2^128*((4294968272*b1)%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p) E (4294968272*b1) x ∧
      x cache=((b1/2^96%2==1) && ((4294968272*b1/2^128-b1/2^96)%2==1)) ∧
      x cache1=carryLow2 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache2=carryLow3 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      x cache3=carryLow4 (b1/2^96) (4294968272*b1/2^128-b1/2^96) ∧
      (if x (eU L) then 1 else 0)=K) := by
  intro s m input
  obtain ⟨h,hCache,hCache1,hCache2,hCache3,key⟩:=input
  have cr : cache∉mR L := fun hr=>(m_away L hn cache (Or.inl hr)).2 cacheE
  have cS : cache∉mS L := fun hs=>(m_away L hn cache (Or.inr hs)).2 cacheE
  have cZ : cache∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache
    have ps:=productSplit L cache
    have ec:=eReg_count L cache
    have ce:=List.count_pos_iff.mpr cacheE
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache hz)
    omega
  have co : cache∉L.core.out := (eReg_away L hn cache cacheE).1
  have cr1 : cache1∉mR L := fun hr=>(m_away L hn cache1 (Or.inl hr)).2 cache1E
  have cS1 : cache1∉mS L := fun hs=>(m_away L hn cache1 (Or.inr hs)).2 cache1E
  have cZ1 : cache1∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache1
    have ps:=productSplit L cache1
    have ec:=eReg_count L cache1
    have ce:=List.count_pos_iff.mpr cache1E
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache1 hz)
    omega
  have cC1 : cache1∉mC L := by
    intro hz
    have lc:=layoutCount L hn cache1
    have ps:=productSplit L cache1
    have ec:=eReg_count L cache1
    have ce:=List.count_pos_iff.mpr cache1E
    have cz:=List.count_pos_iff.mpr (mC_pad L cache1 hz)
    omega
  have co1 : cache1∉L.core.out := (eReg_away L hn cache1 cache1E).1
  have cr2 : cache2∉mR L := fun hr=>(m_away L hn cache2 (Or.inl hr)).2 cache2E
  have cS2 : cache2∉mS L := fun hs=>(m_away L hn cache2 (Or.inr hs)).2 cache2E
  have cZ2 : cache2∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache2
    have ps:=productSplit L cache2
    have ec:=eReg_count L cache2
    have ce:=List.count_pos_iff.mpr cache2E
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache2 hz)
    omega
  have cC2 : cache2∉mC L := by
    intro hz
    have lc:=layoutCount L hn cache2
    have ps:=productSplit L cache2
    have ec:=eReg_count L cache2
    have ce:=List.count_pos_iff.mpr cache2E
    have cz:=List.count_pos_iff.mpr (mC_pad L cache2 hz)
    omega
  have co2 : cache2∉L.core.out := (eReg_away L hn cache2 cache2E).1
  have cr3 : cache3∉mR L := fun hr=>(m_away L hn cache3 (Or.inl hr)).2 cache3E
  have cS3 : cache3∉mS L := fun hs=>(m_away L hn cache3 (Or.inr hs)).2 cache3E
  have cZ3 : cache3∉mZ L := by
    intro hz
    have lc:=layoutCount L hn cache3
    have ps:=productSplit L cache3
    have ec:=eReg_count L cache3
    have ce:=List.count_pos_iff.mpr cache3E
    have cz:=List.count_pos_iff.mpr (mZ_pad L cache3 hz)
    omega
  have cC3 : cache3∉mC L := by
    intro hz
    have lc:=layoutCount L hn cache3
    have ps:=productSplit L cache3
    have ec:=eReg_count L cache3
    have ce:=List.count_pos_iff.mpr cache3E
    have cz:=List.count_pos_iff.mpr (mC_pad L cache3 hz)
    omega
  have co3 : cache3∉L.core.out := (eReg_away L hn cache3 cache3E).1
  obtain ⟨ws1, ws2, ws3⟩ := whi_split b1 hb1lt
  generalize hW : 4294968272*b1 = W at h hCache hCache1 hCache2 hCache3 ws1 ws2 ws3 ⊢
  generalize hu : b1/2^96 = u at hCache hCache1 hCache2 hCache3 ws1 ws2 ⊢
  generalize hd : W/2^128 - u = d at hCache hCache1 hCache2 hCache3 ws2 ⊢
  have hWlt : W < 2^163 := by rw [← hW]; norm_num at hb1lt ⊢; omega
  obtain ⟨hz, hb, hi, padZ, workZ⟩ := zero_regs L hn base hc O E W s.basis h
  have g := mGeo L hw hn
  have hRv := mR_value L hw hn base hc O E W s.basis h
  have Rv : regValue (mR L) s.basis = u + d := by rw [hRv.1, Nat.mod_eq_of_lt (by omega)]; omega
  have Sv : regValue (mS L) s.basis = 0 := (regValue_zero _ _).mpr (fun q hq => padZ q (mS_pad L q hq))
  have P0 : WinArith.PS (mR L) (mS L) s.basis (u+d) 0 s.basis := ⟨Rv, Sv, fun _ _ _ => rfl⟩
  have cl : WinArith.Clean (mZ L) (mC L) L.core.cin s.basis :=
    ⟨hi, fun q hq => padZ q (mZ_pad L q hq), fun q hq => padZ q (mC_pad L q hq)⟩
  have hU : regValue (mU L) s.basis = u := by
    rw [hi96 L hw, regValue_congr _ _ _ (fun q hq => bstate_other L hn base O E W s.basis h q (Or.inl hq)), hb1, hu]
  have hu32 : u < 2^32 := by rw [← hu]; norm_num at hb1lt ⊢; omega
  have eA := eU_away L hw hn
  have heR : eU L ∉ mR L := fun hr => eA.2.1 (mR_work L _ hr)
  have heS : eU L ∉ mS L := fun hs => eA.1 (mS_pad L _ hs)
  have heZ : eU L ∉ mZ L := fun hz => eA.1 (mZ_pad L _ hz)
  have wf := w192_facts L hw hn
  have hkU : s.basis (eU L) = decide (K = 1) := by
    cases e : s.basis (eU L) <;> simp only [e, Bool.false_eq_true, if_false, if_true] at key <;> simp <;> omega
  have T1 : Triple (WinArith.PS (mR L) (mS L) s.basis (u+d) 0) (wFwdCCCC L cache cache1 cache2 cache3)
      (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) := by
    have := fwdCCCC_spec g cl u d hU hu32 ws2 cache cr cS cZ hCache (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache1 cache2 cr2 cS2 cZ2 cC2 hCache2 cache3 cr3 cS3 cZ3 cC3 hCache3
    rw [key] at this; exact this
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hX : (u + 4294968273*d + 4294968272*2^32*K) + 2^128*(W%2^128) < SquareReduction.p := by
    have b := Nat.mod_lt W (show 2^128>0 by positivity)
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c] at b hu32 ws2 ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hK with hk | hk <;> subst hk <;> omega
  -- frame facts of the start state
  have wnd : L.core.work.Nodup := by
    apply List.nodup_iff_count_le_one.mpr; intro q; have := lay_pos L hn q; omega
  have keepS (q : Wire) (h1 : q ∉ L.core.out) (h2 : q ∉ eReg L) (h3 : q ∉ accReg L) : s.basis q = base q :=
    h.2.2.2 q h1 h2 h3
  let O' := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O)) % SquareReduction.p
  let Q2 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + 4294968273*d + 2^32*(976*K) ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T2 : Triple (WinArith.PS (mR L) (mS L) s.basis (u + 4294968273*d + 2^32*(976*K)) 0) (wCoreK L) Q2 := by
    intro s1 m1 h1
    have keep0 (q : Wire) (a : q ∉ mR L) (b : q ∉ mS L) : s1.basis q = s.basis q := h1.2.2 q a b
    have w0 : s1.basis (w192 L) = false := (keep0 _ wf.2.2.1 wf.2.2.2.1).trans (workZ _ wf.2.1)
    have ek1 : s1.basis (eU L) = decide (K = 1) := (keep0 _ heR heS).trans hkU
    let s1' : State := ⟨s1.phase, writeBit s1.basis (w192 L) (s1.basis (w192 L) ^^ s1.basis (eU L))⟩
    have r1 : ∀ mm, run (kw L) mm s1 = s1' := by intro mm; simp [kw, run, s1']
    have b1' : ∀ q, q ≠ w192 L → s1'.basis q = s1.basis q := by
      intro q hq; simp [s1', writeBit, Function.update_apply, hq]
    have bw : s1'.basis (w192 L) = decide (K = 1) := by simp [s1', writeBit, w0, ek1]
    have keep (q : Wire) (a : q ∉ mR L) (b : q ∉ mS L) (c : q ≠ w192 L) : s1'.basis q = s.basis q :=
      (b1' q c).trans (keep0 q a b)
    have nw_out (q : Wire) (hq : q ∈ L.core.out) : q ≠ w192 L := fun e => wf.2.2.2.2.1 (e ▸ hq)
    have nw_pad (q : Wire) (hq : q ∈ L.foldPad) : q ≠ w192 L := fun e => work_pad L hn _ wf.1 (e ▸ hq)
    have nw_lo (q : Wire) (hq : q ∈ L.core.work.take 128) : q ≠ w192 L := by
      intro e
      have c := List.nodup_iff_count_le_one.mp wnd q
      have sp := congrArg (List.count q) (List.take_append_drop 128 L.core.work)
      have a1 := List.count_pos_iff.mpr hq
      have a2 : 0 < (L.core.work.drop 128).count q := by
        rw [e]; exact List.count_pos_iff.mpr (List.mem_of_mem_drop (w192_tail L hw))
      simp only [List.count_append] at sp; omega
    have nw_R (q : Wire) (hq : q ∈ mR L) : q ≠ w192 L := fun e => wf.2.2.1 (e ▸ hq)
    have outv : regValue L.core.out s1'.basis = O :=
      (regValue_congr _ _ _ (fun q hq => keep q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq) (nw_out q hq))).trans h.1
    have sg (q : Wire) (hq : q ∈ [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
        L.core.modFlag,L.core.sumCarry]) : s1'.basis q = s.basis q :=
      keep q (fun hr => (sing_away L hn q hq).1 (mR_work L q hr)) (fun hs => (sing_away L hn q hq).2.1 (mS_pad L q hs))
        (fun e => (sing_away L hn q hq).1 (e ▸ wf.1))
    have bo (q : Wire) (hq : q = L.core.productHigh ∨ q = L.core.outHigh ∨ q = L.core.workHigh ∨ q = L.core.cin ∨
        q = L.core.modFlag) : s.basis q = base q :=
      bstate_other L hn base O E W s.basis h q (Or.inr (Or.inr (Or.inr (by rcases hq with rfl|rfl|rfl|rfl|rfl <;> simp))))
    have padS (q : Wire) (hq : q ∈ L.foldPad) : s1'.basis q = false := by
      rw [b1' q (nw_pad q hq)]
      by_cases hs : q ∈ mS L
      · exact (regValue_zero _ _).mp h1.2.1 q hs
      · exact (keep0 q (fun hr => work_pad L hn q (mR_work L q hr) hq) hs).trans (padZ q hq)
    have carryZ : ∀q∈(rotWCore L).carry,s1'.basis q=false := by
      intro q hq
      simp only [rotWCore,measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with hq|rfl|rfl
      · exact padS q hq
      · exact ((sg _ (by simp)).trans (bo _ (Or.inl rfl))).trans hc.productHigh
      · exact ((sg _ (by simp)).trans (bo _ (Or.inr (Or.inr (Or.inl rfl))))).trans hc.workHigh
    have srcv : regValue (rotWCore L).src s1'.basis = (u + 4294968273*d + 4294968272*2^32*K) + 2^128*(W%2^128) := by
      show regValue (rotWork L) s1'.basis = _
      rw [rotWork, regValue_append]
      have l128 : (L.core.work.drop 128).length = 128 := by simp [hw.core.work]
      have hlo : regValue (L.core.work.take 128) s1'.basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => keep q
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs)) (nw_lo q hq)),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hhi : regValue (L.core.work.drop 128) s1'.basis = u + 4294968273*d + 4294968272*2^32*K := by
        have sp := regValue_append ((L.core.work.drop 128).take 43) ((L.core.work.drop 128).drop 43) s1'.basis
        rw [List.take_append_drop] at sp
        have z : regValue ((L.core.work.drop 128).drop 43) s1'.basis = 2^21 * K := by
          apply tail_value L hw hn s1'.basis K hK bw
          intro q hq hne
          have hq0 := hq
          rw [List.drop_drop] at hq
          have hq' : q ∈ L.core.work.drop (128+43) := hq
          rw [keep q (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq') hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq') (mS_pad L q hs)) hne]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq'
          exact List.mem_of_mem_drop hq'
        have rv : regValue ((L.core.work.drop 128).take 43) s1'.basis = u + 4294968273*d + 2^32*(976*K) := by
          show regValue (mR L) s1'.basis = _
          rw [regValue_congr _ _ s1.basis (fun q hq => b1' q (nw_R q hq))]
          exact h1.1
        rw [sp, z, rv]
        have : ((L.core.work.drop 128).take 43).length = 43 := by simp [hw.core.work]
        rw [this]; ring
      rw [hhi, hlo, l128]
    have mk0 : measurementCount (kw L) = 0 := by simp [kw, measurementCount]
    rw [wCoreK, run_append, r1, mk0, List.drop_zero, run_append]
    rw [show wCoreTq L = qprogTq (rotWCore L) SquareReduction.p from rfl]
    have ek := QCore.qprog_correctTq (rotWCore L) 256 SquareReduction.c SquareReduction.p (rotWCore_widths L hw)
      (rotWCore_nodup L hn) (by decide) hp (by norm_num [SquareReduction.c]) _ O hX hO s1'
      (m1.take (measurementCount (qprogTq (rotWCore L) SquareReduction.p))) srcv outv
      (show s1'.basis L.core.outHigh = false from
        (sg L.core.outHigh (by simp)).trans ((bo _ (Or.inr (Or.inl rfl))).trans hc.outHigh))
      (show s1'.basis L.core.modFlag = false from
        (sg L.core.modFlag (by simp)).trans ((bo _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).trans hc.modFlag)) carryZ
      (show s1'.basis L.core.cin = false from (sg L.core.cin (by simp)).trans hi)
    generalize hr : run (qprogTq (rotWCore L) SquareReduction.p)
      (m1.take (measurementCount (qprogTq (rotWCore L) SquareReduction.p))) s1' = r at ek ⊢
    have rw' : r.basis (w192 L) = decide (K = 1) := (ek.2.2 _ wf.2.2.2.2.1).trans bw
    have re : r.basis (eU L) = decide (K = 1) := by
      rw [ek.2.2 _ eA.2.2, b1' _ (fun e => wf.2.2.2.2.2.1 e.symm), ek1]
    have fin : ∀ mm, run (kw L) mm r = ⟨r.phase, writeBit r.basis (w192 L) false⟩ := by
      intro mm; simp [kw, run, rw', re]
    rw [fin]
    have fb : ∀ q, q ≠ w192 L → (writeBit r.basis (w192 L) false) q = r.basis q := by
      intro q hq; simp [writeBit, Function.update_apply, hq]
    refine ⟨ek.1, ?_, ?_, ?_, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => fb q (nw_out q hq))).trans ek.2.1
    · rw [regValue_congr _ _ r.basis (fun q hq => fb q (nw_R q hq))]
      exact (regValue_congr _ _ _ (fun q hq => (ek.2.2 q (m_away L hn q (Or.inl hq)).1).trans
        (b1' q (nw_R q hq)))).trans h1.1
    · rw [regValue_congr _ _ r.basis (fun q hq => fb q (fun e => wf.2.2.2.1 (e ▸ hq)))]
      exact (regValue_congr _ _ _ (fun q hq => (ek.2.2 q (m_away L hn q (Or.inr hq)).1).trans
        (b1' q (fun e => wf.2.2.2.1 (e ▸ hq))))).trans h1.2.1
    · intro q a b c
      by_cases hq : q = w192 L
      · subst hq; simp [writeBit]; exact workZ _ wf.2.1
      · show writeBit r.basis (w192 L) false q = s.basis q
        rw [fb q hq, ek.2.2 q a, b1' q hq]; exact keep0 q b c
  let Q3 : BasisState → Prop := fun x => regValue L.core.out x = O' ∧ regValue (mR L) x = u + d ∧
    regValue (mS L) x = 0 ∧ ∀ q, q ∉ L.core.out → q ∉ mR L → q ∉ mS L → x q = s.basis q
  have T3 : Triple Q2 (wInvCCCC L cache cache1 cache2 cache3) Q3 := by
    intro s2 m2 h2
    have k2 (q : Wire) (a : q ∉ L.core.out) (b : q ∉ mR L) (c : q ∉ mS L) : s2.basis q = s.basis q := h2.2.2.2 q a b c
    have cl2 : WinArith.Clean (mZ L) (mC L) L.core.cin s2.basis := by
      refine ⟨?_, fun q hq => ?_, fun q hq => ?_⟩
      · exact (k2 _ (sing_away L hn _ (by simp)).2.2 (fun hr => (sing_away L hn _ (by simp)).1 (mR_work L _ hr))
          (fun hs => (sing_away L hn _ (by simp)).2.1 (mS_pad L _ hs))).trans hi
      · exact (k2 q (pad_out L hn q (mZ_pad L q hq)) (fun hr => work_pad L hn q (mR_work L q hr) (mZ_pad L q hq))
          (fun hs => g.ZS q hq hs)).trans (padZ q (mZ_pad L q hq))
      · exact (k2 q (pad_out L hn q (mC_pad L q hq)) (fun hr => work_pad L hn q (mR_work L q hr) (mC_pad L q hq))
          (fun hs => (g.csS 42) q (by rwa [List.take_of_length_le (by rw [g.c])]) hs)).trans (padZ q (mC_pad L q hq))
    have hU2 : regValue (mU L) s2.basis = u := by
      rw [regValue_congr (mU L) _ (s.basis) (fun q hq => k2 q
        (fun ho => (other_away L hn q (Or.inl (List.mem_of_mem_drop hq))).1 ho) (g.UR q hq) (g.US q hq)), hU]
    have ke : (if s2.basis (eU L) = true then 1 else 0) = K := by
      rw [k2 _ eA.2.2 heR heS]; exact key
    have P2 : WinArith.PS (mR L) (mS L) s2.basis
        (u + 4294968273*d + 2^32*(976*(if s2.basis (eU L) = true then 1 else 0))) 0 s2.basis :=
      ⟨by rw [ke]; exact h2.2.1, h2.2.2.1, fun _ _ _ => rfl⟩
    have hCache0at2 : s2.basis cache=((u%2==1) && (d%2==1)) :=
      (k2 cache co cr cS).trans hCache
    have hCache12 : s2.basis cache1=carryLow2 u d :=
      (k2 cache1 co1 cr1 cS1).trans hCache1
    have hCache22 : s2.basis cache2=carryLow3 u d :=
      (k2 cache2 co2 cr2 cS2).trans hCache2
    have hCache32 : s2.basis cache3=carryLow4 u d :=
      (k2 cache3 co3 cr3 cS3).trans hCache3
    obtain ⟨ph, h3⟩ := invCCCC_spec g cl2 u d hU2 hu32 ws2 cache cr cS cZ hCache0at2 (eU L) heR heS heZ (by omega) cache1 cr1 cS1 cZ1 cC1 hCache12 cache2 cr2 cS2 cZ2 cC2 hCache22 cache3 cr3 cS3 cZ3 cC3 hCache32 s2 m2 P2
    refine ⟨ph, ?_, h3.1, h3.2.1, ?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => h3.2.2 q (fun hr => (m_away L hn q (Or.inl hr)).1 hq)
        (fun hs => (m_away L hn q (Or.inr hs)).1 hq))).trans h2.1
    · intro q a b c; exact (h3.2.2 q b c).trans (k2 q a b c)
  obtain ⟨ph, f⟩ := (T1.seq (T2.seq T3)) s m P0
  refine ⟨ph, ⟨f.1, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => f.2.2.2 q (eReg_away L hn q hq).1
      (fun hr => (m_away L hn q (Or.inl hr)).2 hq) (fun hs => (m_away L hn q (Or.inr hs)).2 hq))).trans h.2.1
  · -- the work register is `W` again
    have wv : regValue L.core.work (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W := by
      rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
      have lo : regValue (L.core.work.take 128) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W % 2^128 := by
        rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
          WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
      have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = 0 := by
        apply (regValue_zero _ _).mpr
        intro q hq
        rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
          (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
          (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
        apply workZ
        have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
        rw [this] at hq
        exact List.mem_of_mem_drop hq
      have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = u + d :=
        f.2.1
      rw [lo, mr, hi0]
      omega
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis
    rw [List.take_append_drop] at sp
    rw [accReg, WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), wv, Nat.mod_eq_of_lt hWlt]
  · intro q h1 h2 h3
    by_cases hr : q ∈ mR L
    · -- bits 163..170 of work are clear again
      have wq : q ∈ L.core.work := mR_work L q hr
      have hd163 : q ∈ L.core.work.drop 163 := by
        have e := L.core.work.take_append_drop 163
        rw [← e] at wq
        rcases List.mem_append.mp wq with a|a
        · exact absurd a h3
        · exact a
      have wv : regValue L.core.work (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W := by
        rw [WinArith.split3 L.core.work 128 43 (by simp [hw.core.work])]
        have lo : regValue (L.core.work.take 128) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = W % 2^128 := by
          rw [regValue_congr _ _ (s.basis) (fun q hq => f.2.2.2 q (work_out L hn q (List.mem_of_mem_take hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inl hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_take hq) (mS_pad L q hs))),
            WinArith.regValue_take_mod _ _ (by simp [hw.core.work]), hRv.2]
        have hi0 : regValue (L.core.work.drop (128+43)) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = 0 := by
          apply (regValue_zero _ _).mpr
          intro q hq
          rw [f.2.2.2 q (work_out L hn q (List.mem_of_mem_drop hq))
            (fun hr => WinArith.win_away L.core.work wnd 128 43 q (Or.inr hq) hr)
            (fun hs => work_pad L hn q (List.mem_of_mem_drop hq) (mS_pad L q hs))]
          apply workZ
          have : L.core.work.drop (128+43) = (L.core.work.drop 163).drop 8 := by rw [List.drop_drop]
          rw [this] at hq
          exact List.mem_of_mem_drop hq
        have mr : regValue ((L.core.work.drop 128).take 43) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = u + d :=
          f.2.1
        rw [lo, mr, hi0]
        omega
      have z : regValue (L.core.work.drop 163) (run (wFwdCCCC L cache cache1 cache2 cache3 ++ (wCoreK L ++ wInvCCCC L cache cache1 cache2 cache3)) m s).basis = 0 := by
        rw [WinArith.drop_div _ _ (by simp [hw.core.work]), wv, Nat.div_eq_of_lt hWlt]
      rw [(regValue_zero _ _).mp z q hd163]
      exact ((regValue_zero _ _).mp hc.work q wq).symm
    by_cases hs : q ∈ mS L
    · rw [(regValue_zero _ _).mp f.2.2.1 q hs]
      exact ((regValue_zero _ _).mp hc.pad q (mS_pad L q hs)).symm
    · exact (f.2.2.2 q h1 hr hs).trans (keepS q h1 h2 h3)



  · exact (f.2.2.2 cache co cr cS).trans hCache
  · exact (f.2.2.2 cache1 co1 cr1 cS1).trans hCache1
  · exact (f.2.2.2 cache2 co2 cr2 cS2).trans hCache2
  · exact (f.2.2.2 cache3 co3 cr3 cS3).trans hCache3
  · rw [f.2.2.2 (eU L) eA.2.2 heR heS]
    exact key

#print axioms wMidCCCC_step
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryLoanCore
open ECDSAAdd
namespace FourthCarryLoan
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem get_ne (r : List Wire) (hn : r.Nodup) (i j : Nat)
 (hi : i<r.length) (hj : j<r.length) (hij : i≠j) : r.getD i 0≠r.getD j 0 := by
 intro h
 rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at h
 exact hij ((List.Nodup.getElem_inj_iff hn).mp h)

def loan3 (v1 v2 u0 u2 u3 e0 e2 host : Wire) : Program :=
 [.measureX host [] [.Z u3,.CZ v1 e0,.CZ v2 e0,.CZ v1 u0,.CZ v2 u0,.CZ u2 e2,.Z u2]]
def restore3 (v1 v2 u0 u2 u3 e0 e2 host : Wire) : Program :=
 [.CX u0 e0,.CX v2 v1,.CCX v1 e0 host,.CX v2 v1,.CX u0 e0,
  .CCX u2 e2 host,.CX u2 host,.CX u3 host]

def value (s : BasisState) (v1 v2 u0 u2 u3 e0 e2 : Wire) : Bool :=
 s u3 ^^ ((s e0 ^^ s u0) && (s v1 ^^ s v2)) ^^ (s u2 && s e2) ^^ s u2

                                                                                             
                                                                                     
                                                                                      
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                      
                                                                    
                                                                      
                                                                      
             
                                                    
                 
                                                               
                                                                          
                                                  
                                                                                     
                                                                   
                                                                   
                                                                   
                                                                   
                                                                   
                                                                   
                                                                                        

                                                                                                
                              
                                              
                                                                                           
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                      
                                                                    
                                                                      
                                                                      
                                       
                                  
         
                   
          
                                                  
                                                                           
                                                   
                                                            
                                                                    
                                                                   
                                                                   
                                                                   
                                                                   
                                                                   
                                                                                        
                 
          
                                                  
                                                                                                                            
                                                                   
                                                                   
                                                                   
                                                                   
                                                                   
                                                                         
                 
          
                                                  
                                                                                                                            
                                                                   
                                                                   
                                                                   
                                                                   
                                                                   
                                                                         
                                                                  

                                                   
                                                   
                                                       
                                                          
                                                      
                                                          
                                                                 
                                

                                                   
                                           
                                                            
                                                                   
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                    
                                                                      
                                                                    
                                                                    
                                                                      
                                                                    
                                                                      
                                                                      
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       

theorem support (v1 v2 u0 u2 u3 e0 e2 host : Wire) :
 wires (loan3 v1 v2 u0 u2 u3 e0 e2 host)⊆[v1,v2,u0,u2,u3,e0,e2,host].toFinset ∧
 wires (restore3 v1 v2 u0 u2 u3 e0 e2 host)⊆[v1,v2,u0,u2,u3,e0,e2,host].toFinset := by
 constructor <;> intro q h <;>
  simp [loan3,restore3,ECDSAAdd.wires,Instr.wires,correctionWires] at h ⊢ <;> tauto
                      
#print axioms support

                       
                          
                    
end FourthCarryLoan

end -- isolated Carry9 component

section
-- FourthCarryEnds
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

                                                                                             
                                                       
                                                                                   

                                                                                            
                            
                                                                                                                

                                                                                         
                                                                            
                                                          
                                      
        
                                              
                                                  
      

                                                                                        
                                                                            
                                            
                                      
        
                                              
                                                  
      

                                                                                        
                                                                                                      
                             
                                                                                 
                                                                  
                                                                                
                                    
                                                 
                                                 
                                                 
                                                                                
                                                                                                      
                
                                                                                   
                                                                                         
                                                                                       
                                    
                                                 
                                                 
                                                 
                                                         
                                                                                               
                                                                                       
         
                                                                           
                                                                                         
         
                                                                         
                                                                               
                                                                          
                                                   
                                                                                
                                                                       
                                                                                    
                                                                                  
                                                                         
                                                                          
                                         
                                                    
                                                                                                        
         
                                                                                                          
                                   
          
                       
           
                                                  
                                                                                                 
                                                                                                 
                                                                                   
                                                         
                                                  
           
                                          

                                                                                       
                                                                                                      
                                                    
                                                                            
                                                                            
                                                                              
                                                                                        
                                                                       
                                                                 
                                                                               
                                                                                     
                
                                                                                   
                                                                                         
                                                                                       
                                                         
                                                                  
                                                                       
                                                                 
                               
                                                            
         
                                                                             
                                                                                        
         
                                                                        
                                                                           
                                                   
                                                                       
                                                             
                                                                       
                                                                                       
                                                                       
                                                                                       
                                                                                  
                                                                                       
         
                                                                          
                                        
                                                   
                                                                                  
                               
     
           
                                         
                          
                         
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryGeometry
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem bit3_mem (xs : List Wire) (h : 4 ≤ xs.length) : bit3 xs ∈ xs := by
 obtain ⟨a,b,c,d,ys,rfl⟩ := split_four xs h
 simp [bit3]

theorem head4_count (xs : List Wire) (h : 4 ≤ xs.length) (q : Wire) :
 [xs.headD 0,bit1 xs,bit2 xs,bit3 xs].count q ≤ xs.count q := by
 obtain ⟨a,b,c,d,ys,rfl⟩ := split_four xs h
 simp only [bit1,bit2,bit3,List.headD_cons,List.drop_succ_cons,List.drop_zero]
 simp only [List.count_cons,List.count_nil]
 omega

def host3Wire (L : CuccaroStreamedSquareWideLayout) : Wire := bit3 (eReg L)

                                                                                                 
                                        

                                                                                             
                                
                                                                                         
                                                                      
                                                             
                         
                                      
        
                                                        
                                                        
                                                                          
                                                                                             
                                                                               
                                                                                 
                                                                                 
                                  
                                                       
                                                                                   
                                                  
                                                                    
                                                                                         
                                        
                                                       
                             
                                                             
                                                                                             
                                                    
       
                            
                          
                                                                          
                                                                                            
                                                                          
      
                        
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryBits
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem bstate_heads4 (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (base s:BasisState) (hc:L.PairClean base) (O E b1:Nat) (hb1:regValue (hiReg L) base=b1)
 (hb1lt:b1<2^128) (h:BState L base O E (4294968272*b1) s):
 s (bit3 (mU L))=digit (b1/2^96) 3 ∧
 s (bit3 (mR L))=digit (b1/2^96+(4294968272*b1/2^128-b1/2^96)) 3 := by
 have g:=mGeo L hw hn
 obtain ⟨h1,h2,h3⟩:=whi_split b1 hb1lt
 have hr:=mR_value L hw hn base hc O E (4294968272*b1) s h
 have hv:regValue (mR L) s=b1/2^96+(4294968272*b1/2^128-b1/2^96):=by
  rw[hr.1,Nat.mod_eq_of_lt (by omega)]
  omega
 have hu:=bstate_u L hw hn base s O E b1 hb1 h
 constructor
 · rw[bit3_parity (mU L) s (by rw[g.u];decide),hu]
 · rw[bit3_parity (mR L) s (by rw[g.r];decide),hv]

                                                                                          
                       
                            
                                                              
                                
                  
                                               
                                      
                         
               
                                                     

#print axioms bstate_heads4
                          
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryEndsResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ECDSAAdd.RecordedQuantum
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

                                                                                    
                                                                                
                                                                                    
                                                                                            
                    
                                                                                                        
                                                 

                                                                                   
                                                                               
                                                                                   
                                                                                           
                    
                                                                                                     
                                                 

                             
                            
                                                                                 
                                                                   
                                                                            
                                                                               
                                                                                
                                                                              
                                     
                                       
         
                                               
                                                   
       
                                                               
                                                                    
                                                                                     
                                                                                   
                                                                     
       
                                                 
                                  

                                                                                  
                                                                     
                                                               
                                                                    
                                                                   
                                                          
                                                              
                                                               
                                                            
                               
                                                                                            
                          
                                                          
                      
                                                                                                  
                                                                                                  
                                                                                                  
                                                         
                      
                                                                                                  
                                                                                                  
                                                                                                  
                             
                            
                            
                           
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryPatches
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem add4_patch (cache0 cache1 cache2 cache3 : Wire) (x y cs : List Wire) (cin : Wire)
 (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length) :
 Patch cache3 1 (addCCCC cache0 cache1 cache2 cache3 x y cs cin) (addCCC cache0 cache1 cache2 x y cs cin) := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 have p := add3_patch cache1 cache2 cache3 (a1::a2::a3::a4::xs) (b1::b2::b3::b4::ys) (k1::k2::k3::ks) k0
  (by simp) (by simp) (by simp)
 have h := (Patch.refl cache3 [.CX cache0 k0]).app
  (p.app (Patch.refl cache3 (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0 ++ mappedSum ⟨some a0,false⟩ b0 cin)))
 simpa only [addCCCC,addCCC,addCC,cachedMapped4,cachedMapped3,cachedMapped2,mappedRead,List.map_cons,
  Nat.zero_add,Nat.add_zero,List.append_assoc] using h

theorem sub4_patch (cache0 cache1 cache2 cache3 : Wire) (expected : Bool) (x y cs : List Wire)
 (flags : List Bool) (cin : Wire) (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) (hc : 4 ≤ cs.length)
 (hf : 5 ≤ flags.length) (hf1 : flags.getD 1 false = false) (hf2 : flags.getD 2 false = false)
 (hf3 : flags.getD 3 false = false) (hf4 : flags.getD 4 false = false) :
 Patch cache3 1 (cachedSub4 cache0 cache1 cache2 cache3 expected (mappedRead x false) flags y cs cin)
  (cachedSub3 cache0 cache1 cache2 expected (mappedRead x false) flags y cs cin) := by
 obtain ⟨a0,a1,a2,a3,a4,xs,rfl⟩ := split_five x hx
 obtain ⟨b0,b1,b2,b3,b4,ys,rfl⟩ := split_five y hy
 obtain ⟨k0,k1,k2,k3,ks,rfl⟩ := split_four cs hc
 obtain ⟨f0,f1,f2,f3,f4,fs,rfl⟩ := split_five flags hf
 have h1 : f1=false := by simpa using hf1
 have h2 : f2=false := by simpa using hf2
 have h3 : f3=false := by simpa using hf3
 have h4 : f4=false := by simpa using hf4
 subst f1; subst f2; subst f3; subst f4
 have inner := (majority_patch cache3 a3 b3 k2 k3).app (Patch.refl cache3
  (MixedLiteralAdderDevelop.program expected (mappedRead (a4::xs) false) (b4::ys) (false::fs) ks k3 ++
   mappedEraseCarry ⟨some a3,false⟩ b3 k2 k3 ++ mappedSum ⟨some a3,false⟩ b3 k2))
 have third := (Patch.refl cache3 [.CX cache2 k2]).app (inner.app (Patch.refl cache3
  (mappedEraseCarry ⟨some a2,false⟩ b2 k1 k2 ++ mappedSum ⟨some a2,false⟩ b2 k1)))
 have middle := (Patch.refl cache3 [.CX cache1 k1]).app (third.app (Patch.refl cache3
  (mappedEraseCarry ⟨some a1,false⟩ b1 k0 k1 ++ mappedSum ⟨some a1,false⟩ b1 k0)))
 have outer := (Patch.refl cache3 [.CX cache0 k0]).app (middle.app (Patch.refl cache3
  (mappedEraseCarry ⟨some a0,false⟩ b0 cin k0 ++ mappedSum ⟨some a0,false⟩ b0 cin)))
 have h := (Patch.refl cache3 (notRegister (b0::b1::b2::b3::b4::ys))).app
  (outer.app (Patch.refl cache3 (notRegister (b0::b1::b2::b3::b4::ys))))
 simpa only [cachedSub4,cachedSub3,cachedMixed4,cachedMixed3,cachedMixed2,cachedMixed,
  MixedLiteralAdderDevelop.program,MixedLiteralAdderDevelop.head,mappedRead,List.map_cons,mappedMajority,
  Bool.false_eq_true,if_false,Nat.add_zero,Nat.zero_add,List.append_assoc] using h
#print axioms add4_patch
#print axioms sub4_patch
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryArmPatches
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem sub33CCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3:Wire):
 Patch cache3 1 (sub33CCCC cache0 cache1 cache2 cache3 R Z cs U cin) (sub33CCC cache0 cache1 cache2 R Z cs U cin):=by
 exact sub4_patch cache0 cache1 cache2 cache3 true (U++Z.take 1) (R.take 33) (cs.take 32)
  MixedLiteralAdderDevelop.upper33 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide) (by decide) (by decide)

theorem sub43CCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3:Wire):
 Patch cache3 1 (sub43CCCC cache0 cache1 cache2 cache3 R Z cs U cin) (sub43CCC cache0 cache1 cache2 R Z cs U cin):=by
 exact sub4_patch cache0 cache1 cache2 cache3 true (U++Z) (R.take 43) (cs.take 42)
  MixedLiteralAdderDevelop.mask43 cin (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
  (by decide) (by decide) (by decide) (by decide) (by decide)

theorem fwdCCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3 k:Wire):
 Patch cache3 2 (fwdCCCC R S Z cs U cin k cache0 cache1 cache2 cache3) (fwdCCC R S Z cs U cin k cache0 cache1 cache2):=by
 have a:=add4_patch cache0 cache1 cache2 cache3 (U++Z.take 11) ((R.drop 0).take 43) (cs.take 42) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache3 (WinArith.kpat k Z)
 exact (sub33CCCC_patch (cin:=cin) g cache0 cache1 cache2 cache3).app
  ((Patch.refl cache3 (copyRegister none ((R.drop 0).take 10) S)).app
   ((Patch.refl cache3 (WinArithAux3SmallDevelop.smallF R S cs cin)).app
    ((Patch.refl cache3 (copyRegister none S ((R.drop 32).take 10))).app
     ((Patch.refl cache3 (copyRegister none ((R.drop 32).take 10) S)).app (kp.app (a.app kp))))))

theorem invCCCC_patch {R S Z cs U:List Wire} {cin:Wire} (g:WinArith.Lens R S Z cs U)
 (cache0 cache1 cache2 cache3 k:Wire):
 Patch cache3 2 (invCCCC R S Z cs U cin k cache0 cache1 cache2 cache3) (invCCC R S Z cs U cin k cache0 cache1 cache2):=by
 have a:=add4_patch cache0 cache1 cache2 cache3 (U++Z.take 1) ((R.drop 0).take 33) (cs.take 32) cin
  (by simp[g.u,g.z]) (by simp[g.r]) (by simp[g.c])
 have kp:=Patch.refl cache3 (WinArith.kpat k Z)
 exact kp.app ((sub43CCCC_patch (cin:=cin) g cache0 cache1 cache2 cache3).app (kp.app
  ((Patch.refl cache3 (copyRegister none ((R.drop 32).take 10) S)).app
   ((Patch.refl cache3 (copyRegister none S ((R.drop 32).take 10))).app
    ((Patch.refl cache3 (WinArithAux3SmallDevelop.smallI R S cs cin)).app
     ((Patch.refl cache3 (copyRegister none ((R.drop 0).take 10) S)).app a))))))

theorem midCCCC_patch (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 Patch (host3Wire L) 4
  (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) ++
   (wCoreK L ++ wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L)))
  (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L) ++
   (wCoreK L ++ wInvCCC L (cacheWire L) (hostWire L) (host2Wire L))) :=
 (fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)).app
  ((Patch.refl _ (wCoreK L)).app
   (invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (host3Wire L) (eU L)))
#print axioms fwdCCCC_patch
#print axioms invCCCC_patch
#print axioms midCCCC_patch
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryFull
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                              
                                                                                                            
                                                                               
                                                           
                                                                       
                                                                                     
                                                                                                           
                                                                               
                                                         

                                                                                              
                                                                              
                                                                           
                                                                     
                                                         
                               
                                         
                                                                               
                                                  
                                                        
                                            
                                                                                               
                                                           
                                                              
                                                                                       
                                                                                                     
            
                            
                         
                         
                         
                            
                         
                         
                         
                              
                             
                              
                            
                          
                            
                            
               
                             
                                
                           
                           
                           
                                                                                                   
              
                                                                                 
                                                                                          
                                                                                        
                                                                                        
                                                                                          
                                                                                          
                                                                                          
                                                                                          
                                                                                          
                                                                                          
                                                                                          
                                                                                           
                                                                                           
                                                                                                 
                                                                                               
                                                                                                 
                                     
                                   
                                      
                                      
                               
                                                               
                                                                                                                                                 
                               
                                                                       
                                                                                
                                    
                                                       
                                                       
                                                                    
                                                                                 
                                                                 
                                                                   
                                                                  
                                                                  
                                
                                                                                                                                                                                                                  
                                    
                                                                                                                                                                                                                             
                                     
                                                                                                                                                                                                                               
                                           
                                                                                               
                                                                                   
                                  
                                                                      
         
                   
                                 
                                                              
                                                                                         
          
                              
                                   
                                                           
                                             
                                                                           
                                                          
                                                                           
                                                          
                                                                        
                                                                
                                                                             
                                                                                                       
                                
                                                                                                               
          
                                                                                                                                      
                                                               
                                                                         
                                                          
                                                                                              
                                                                             
                                               
                                                                      
                                                                                                 
                                                                                                   
                                   
                             
                                                                                                                                                                                                                                                                                           
                                                                                                                                                                                                   
                                                                                                            
                                                                                      
                                                              
                                                                                          
                                                                                                                                                              
                                                                                          
                                                                                                        
                                           
                                                
                                                                                                      
                              
                                                         
                                                                        
                                                                         
                                                                         
                                                                         
                                                                       
                                   
                                                                                                                      
                                                                                                                                                                                                                                                                                                                                                                        
                                                      
                                                       
                                                      
                                                      
                                                       
                                                      
                                                            
                                                            
                                                                                             
                                                                               
                                                                               
                                                    
                                   
                                                                              
                                              
                                                                              
                                                  
                                                                                     
                                                        
                                                                                      
                                  
                                                                                               
           
             
                                                                                                                  
                                                                    
                                                                                        
                                           
                                                                                                                                                                                                                                                           
                                                                                                                                                                                                                                                           
                                                                                                                                                                                                                                                              
                                                                                                                                                                                                                                                              
                                                                                                                                                                                                                                                              
                                                                                                                                                                                                                                                                 
                                                                                                                                                                                                     
                   
                                                                 
                                                                                       
                 
                
                                  
                                            
                                                                                                                                                                                                                                                              
                                                                                                                                                                                                                                                                  
                                                                                                                                                                                                                                                                  
                                                                                                                                                                                                                                                                  
                                                                                                                                                                                                                                                                  
                                                                                                                                                                                                                                                                     
                                             
                   
                 
                                                                           
                                                                                
                                                                
                                                                                                     
                                                                                                
                                                                                                                                     
                                                                                                                      
                                                                                                                      
                                                                                                                                   
                                                                                                            
                
                 
                
                        
                      
            
                       
                            
                       
                                                         
                      
                                                                                                                                                                                                                                         
                       
                                                                                                                                                       
                                                                       
                
                                                       
                          
                               
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryModLoan
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

                                                         
                                        
                                                                                                    
                                              
                                                       
                                        
                                                                                                              
                                                                   
                                                                   
                                                                   
                                                                   
                      
        
                              
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryOldE
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
                                                                        
                                                                                   
                                                                                     
                                                                                                 
                                                                                                                             
                                                                                                                             
            
                                                      
                 
                                  
                                                      
                 
                                  

                                                                                   
                                                                                  
                                                                               
                                                                                                    
                                                                                 
                                                                               
                                                                                                      
                      
                                                                                                   
                                                                                                            
                                                                                                
                                                     
                                                     
                                                     
                                                     
                                                     
                                                     
                                                     
                                                     
                                                          
                                     
                                 
                                  
                                  
                                                                          
                                                                        
                                                                                                                    
           
                                                                          
                                                                                   
                                         
                                                                                          
                                                                                
                                                         
                                                

                                                                                           
                                                                              
                        
                                                      
                                        
         
                                 
                                                                                               
                                                                                              
        
                                                            
                                                       
                                                      
                                                      
                                                      

                           
                        
                           
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryMiddleCounts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

                                                                                        
                                                                     
                                                                             
                                                                                        
                             
                                                   
                                                                                               
                                                                                                                                                                         
                                                                                                                                                                               
                                                                                                                                                                                   
                                                                                                                                                                      
                                                                                                                                                                            
                                                                                                                                                                                
                                                                                                         
                                                                                                             
                                                                                                                                                                                                                                        
                                                                                                        
                                                                                                            
                                                                                                                                                                                                                                  
                                                                                                            
                                                                       
                                   
                           
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- FourthCarryPhysical
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

                                                                                                  
                                                                      
                                                              
                                                  
                                    
                                                                                                          
                                                                                                         
                                                                                                          
                                                                                         
         
                                                                                                                                                 
               
                                                                                                                                  
               
                                                                                                                    
               
                                                              
                                  
                                 
                                                                                         
         
                                                                                                                                                 
               
                                                                                                                                  
               
                                                                                                                    
               
                                                              
                                  
                                 
                                                                                                                                         
                                                                                                                                           
                                                                
                                             
                                         
                             
end ECDSAAdd.Entrant.FourthCarryLoanDevelop

end -- isolated Carry9 component

section
-- ParkCarry9Core
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry9Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ParkCarry7Develop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

                                                                                                    
                                                                                 
                                                             
                                    
                   
                                                                                   
                                                   
         
                                           
                                                   
               
                                      
                                                    
         
                                           
                                                                                     
                                                                       
               
                                      
                                                                     
                                
                                                   
                                                      
                                                         
               
                                                                                                                       
                                  
         
                                              
              
                                        
              
                                        
               
              
        
                                                            
                              
                       
                      
             
                      
                       

                                                               
                                                                                              
                                                                                                            
                                                                
                                                                                         
                                                              
                                                                                                  

                                                                                             
                                                                             
                                                                                                                                          
                                                                                           
                                                                                                                
                                                             
                                                                                                        
              
                   
                   
                        
                 
                                                         
                                                                                        
                                                      
                                                      
                             
                      
                                              
                      
                                    
                           
                            
                       
         
                                            
                                                                                         
                                                                                               
                                                       
                                                             
                                                                                 
                                                                                        
                                                                
                                             
                                                                                                                      
                                                                        
                   
                                                                                   
                                            
                                                                             
                   
                                                                     
                                         
                                                                                               
                                             
                                                                  
                                                                               
                                                                                  
              
                                                 
                                                                                        
                                                                                       


                  
                      
                  
                              
                             
                                                                                                                     
                                              
                                                                                  
                                                      
                                                     
                            
                       
                                              
                          
                                  
                                                     
                                                      
                                                          
                                                 
                                                                       
                                         
                            
                            
                            
                                              
                               
                                 
                                          
                                                           
                                                      
                                                       
                                            
                                                                            
                                             
                      
                                       
             
                                 
                     
                                                                                    
                                                       
                                                                
            
                                 
                                                  
                                              
                                                                   
                                                    
                
                                        
                                   
                                                       
                                                 
                                               
                                            
                                                           
                                                                     
                                                                         
                 
                                                 
                                          
                                                            
                                                               
                                                           
                                                                     
                       
                                             
                                                                                
                          
                                                                  
                                                                                             
                                                                                  
                                     
                                                                                            
                                                     
                                                                                                  
                        
                                                                                       
                             
                                               
                                                                                    
                                                                             
                                                                      
                   
                                                                               
                                                                                 
                                                                              
            
                                                   
                                                               
                                                             
                  
                        
                                                                                     
                      
              
                                                                                                               
                                                                             
               
                                  
                                   
                                                        
                                                 
                                                                                              
                                                                  
                        
                                                             
                             
                                                                    
                                              
                                                 
                         
                                                  
                                                                                  
                      
                                                                                  
              
                                
                          
                                                                  
                            
                                                                    
                             
                                            
                                                
              
                           
                
                      
                                                                                                              
                                                                                                      
                                
                   
                                                                                                         
                                                                                                                         
                                                                                                                             
                                                                                     
             
                                               
                                            
                                                                                                       
                        
                 
           

                               
                        
end ECDSAAdd.Entrant.ParkCarry9Develop

end -- isolated Carry9 component

section
-- ParkCarry9Metrics
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry9Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
                                                                               
                                                                    
                                                
                                                      
                          
                          
                                                                                                     
                                                       
                          

                                                                              
                                                                                      
                                                            
                         
                         
                                                                                                     
                             
      

                                                                                
                                                    
                                                   
                                   
                                                                                     
                              
                                                                                                            
                                                 
      

                         
                        
                           
end ECDSAAdd.Entrant.ParkCarry9Develop

end -- isolated Carry9 component

section
-- ParkCarry9Hosting
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry9Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

                                                                                                    
                          

                                                                                          
                                                                                  
                                                 

                                                                                                                
                                                                                           
                                                        

                                                                                                               
                                                                                
                                                      
                                                                                                           
                                                                                                                          
                                                         
                                                                 
                            
                                                                                        
      
                       
                           
                          
end ECDSAAdd.Entrant.ParkCarry9Develop

end -- isolated Carry9 component

section
-- Carry9BodySubset
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry9BodySubset
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem old_copy (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 (L.core.product.take 256++L.core.work.take 256).toFinset ⊆ wires (ParkCarry8Develop.body L c) := by
 have pl : (L.core.product.take 256).length=256 := by simp [hw.core.product]
 have wl : (L.core.work.take 256).length=256 := by simp [hw.core.work]
 have nonempty : (L.core.product.take 256).isEmpty=false := by
  rw [List.isEmpty_eq_false_iff]
  intro e
  rw [e] at pl
  contradiction
 have cp : wires (copyRegister none (L.core.product.take 256) (L.core.work.take 256))=
  (L.core.product.take 256++L.core.work.take 256).toFinset := by
  rw [copyRegister_wires none _ _ (pl.trans wl.symm),nonempty]
  rfl
 intro q h
 have used : q∈wires (copyRegister none (L.core.product.take 256) (L.core.work.take 256)) := cp.symm ▸ h
 have foldUsed : q∈wires (measuredFoldQTq L (negP L)) := by
  simp only [measuredFoldQTq,negP,foldDestination,List.drop_zero,pl,wires_append,Finset.mem_union]
  tauto
 simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union]
 tauto

theorem old_prepare (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 [c,bit1 L.core.high,(mU L).headD 0,bit1 (mU L),bit2 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset
 ⊆ wires (ParkCarry8Develop.body L c) := by
 have roles (g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2 : Wire) :
  [g,v,u0,u1,u2,r0,r1,r2,e0,cache,h1,h2].toFinset ⊆ wires (prepare3 g v u0 u1 u2 r0 r1 r2 e0 cache h1 h2) := by
  intro q h
  simp [prepare3,loan2,SecondCarryLoan.prepare,SecondCarryLoan.loan,prime,prime2,majority,wires,Instr.wires,correctionWires] at h ⊢
  tauto
 intro q h
 have used := roles c (bit1 L.core.high) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) h
 have hm : q ∈ wires (wMidFullCCC L c) := by
  rw [wMidFullCCC,wires_append]
  exact Finset.mem_union_left _ used
 have hf : q ∈ wires (ParkCarry8Develop.fold L c) := by
  rw [ParkCarry8Develop.fold,wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  exact Finset.mem_union_left _ hm
 rw [ParkCarry8Develop.body,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_left _ hf

                                                                                      
                                           
                           
                          
         
             
               
                                                 
                                       
                                      
                                                                         
                                                             
                                                                         
      

theorem new_roles (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 bit3 (mU L)∈wires (ParkCarry8Develop.body L c) ∧
 bit3 (mR L)∈wires (ParkCarry8Develop.body L c) ∧
 host3Wire L∈wires (ParkCarry8Develop.body L c) := by
 have cp:=old_copy L hw c
 have u : bit3 (mU L)∈L.core.product.take 256 := by
  have hu:=bit3_mem (mU L) (by rw [mU_length L hw];decide)
  change bit3 (mU L)∈(hiReg L).drop 96 at hu
  have hh:=List.mem_of_mem_drop hu
  change bit3 (mU L)∈(L.core.product.take 256).drop 128 at hh
  exact List.mem_of_mem_drop hh
 have r : bit3 (mR L)∈L.core.work.take 256 := by
  have hr:=bit3_mem (mR L) (by rw [(mLens L hw).r];decide)
  exact win_take (l:=L.core.work) (a:=128) (b:=43) (n:=256) (by simpa only [mR] using hr) (by decide)
 have h : host3Wire L∈L.core.product.take 256 := by
  unfold host3Wire eReg
  rw [bit3_append _ _ (by simp [hw.core.product])]
  have mem:=bit3_mem (L.core.product.take 128) (by simp [hw.core.product])
  have eq : (L.core.product.take 256).take 128=L.core.product.take 128 := by simp [List.take_take]
  have mem' : bit3 (L.core.product.take 128)∈(L.core.product.take 256).take 128 := by
   rw [eq]
   exact mem
  exact List.mem_of_mem_take mem'
 exact ⟨cp (by simp [u]),cp (by simp [r]),cp (by simp [h])⟩

#print axioms old_copy
#print axioms old_prepare
                         
#print axioms new_roles
end ECDSAAdd.Entrant.Carry9BodySubset

end -- isolated Carry9 component

section
-- Carry9OldParts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry9OldParts
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem old_mid (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wMidFullCCC L c) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q hm
 have hf : q ∈ wires (ParkCarry8Develop.fold L c) := by
  rw [ParkCarry8Develop.fold,wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  apply Finset.mem_union_right
  rw [wires_append]
  exact Finset.mem_union_left _ hm
 rw [ParkCarry8Develop.body,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_left _ hf

theorem old_fwd (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q h
 apply old_mid L c
 rw [wMidFullCCC,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_left
 rw [wires_append]
 exact Finset.mem_union_left _ h

theorem old_inv (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q h
 apply old_mid L c
 rw [wMidFullCCC,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_left
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_right _ h

theorem old_core (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 wires (wCoreK L) ⊆ wires (ParkCarry8Develop.body L c) := by
 intro q h
 apply old_mid L c
 rw [wMidFullCCC,wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 apply Finset.mem_union_left
 rw [wires_append]
 apply Finset.mem_union_right
 rw [wires_append]
 exact Finset.mem_union_left _ h
#print axioms old_mid
#print axioms old_fwd
#print axioms old_inv
#print axioms old_core
end ECDSAAdd.Entrant.Carry9OldParts

end -- isolated Carry9 component

section
-- Carry9BodyRefined
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry9BodyRefined
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop Carry9BodySubset
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

                                                                                       
                                                                                                        
                          
                                                                            
                                                                                                   
                            
                              
                                                                                         
                                                                                                                              
                                                      
           
                                                                            
                                               
                   
                                                    
                                                    
                                    
                                                    
                                                    
                                                    
                                           
                                                    
                                                    
                                                    
                                             
                                                    
                                                    
                                                    
                                                    
                                             
                                                                                                           
                                                                               
                                                        
                                                                                                                    
                                                                                                                                 
                                                                           
            
                                                                                                                           
                                                                                                                               
                                                                                                                              
                                                                                                                              
             
             
                                              
                                                       
                                               
             
                                              
                                                       
                                               
                                                                                        
                                
                                                         
                   
                                                         
                   
                                                
                   
                                                                               
                                                       
                                                 
                                                                
                                                                                                      
                          
                      
                                
          
                                                                                    
                                              
                                      
                                                                                                                                     
                                                                                                                                        
                                                                                                                                          
                                                                                                   
                                                                                                                  
              
                                                                                                       
                                                                                                                  
                                                                  
                                                                                                                  
                                                                                                                                         
                                                                                                                      
                                                                                                                                            
                                                                                                                                                               
                                                                                                                                                     

                          
end ECDSAAdd.Entrant.Carry9BodyRefined

end -- isolated Carry9 component

end

section

-- Reuse the fourth cached carry with a cheaper low-bit host.

section
-- LowBitCarryLoan
open ECDSAAdd ECDSAAdd.Arithmetic
namespace LowBitCarryLoan
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def loan0 (g src u q : Wire) : Program := [.measureX q [] [.Z u,.CZ g src]]
def restore0 (g src u q : Wire) : Program := [.CCX g src q,.CX u q]
def value (s : BasisState) (g src u : Wire) : Bool := s u ^^ (s g && s src)

theorem loan0_run (g src u q : Wire) (nd:[g,src,u,q].Nodup) (s : State) (m : List Bool)
 (h:s.basis q=value s.basis g src u) :
 run (loan0 g src u q) m s=⟨s.phase,writeBit s.basis q false⟩ := by
 have ng:g≠q :=FourthCarryLoan.get_ne _ nd 0 3 (by simp) (by simp) (by decide)
 have ns:src≠q :=FourthCarryLoan.get_ne _ nd 1 3 (by simp) (by simp) (by decide)
 have nu:u≠q :=FourthCarryLoan.get_ne _ nd 2 3 (by simp) (by simp) (by decide)
 cases m with
 | nil => simp [loan0,run,measureAndCorrect,correct]
 | cons b ms =>
  cases b <;> cases hg:s.basis g <;> cases hs:s.basis src <;> cases hu:s.basis u <;>
   simp [loan0,run,measureAndCorrect,correct,h,value,writeBit,Function.update_apply,
    ng,ns,nu,hg,hs,hu]

theorem restore0_run (g src u q : Wire) (nd:[g,src,u,q].Nodup) (s : State) (m : List Bool) :
 run (restore0 g src u q) m s=⟨s.phase,writeBit s.basis q (s.basis q ^^ value s.basis g src u)⟩ := by
 have ng:g≠q :=FourthCarryLoan.get_ne _ nd 0 3 (by simp) (by simp) (by decide)
 have ns:src≠q :=FourthCarryLoan.get_ne _ nd 1 3 (by simp) (by simp) (by decide)
 have nu:u≠q :=FourthCarryLoan.get_ne _ nd 2 3 (by simp) (by simp) (by decide)
 change (⟨s.phase,_⟩:State)=⟨s.phase,_⟩
 apply congrArg (State.mk s.phase)
 funext w
 by_cases h:w=q
 · subst w
   cases hg:s.basis g <;> cases hs:s.basis src <;> cases hu:s.basis u <;> cases hq:s.basis q <;>
    simp [restore0,run,value,writeBit,Function.update_apply,ng,ns,nu,hg,hs,hu,hq]
 · simp [restore0,run,writeBit,Function.update_apply,h]

                                   
                                                                          
                                                                                
                                                                                           
                                                                                                   
#print axioms loan0_run
#print axioms restore0_run
                    
end LowBitCarryLoan

end -- isolated Carry10 component

section
-- LowBitCarryEnds
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def prepare4L (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) : Program :=
 prepare3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 ++
 (LowBitCarryLoan.loan0 g v0 u0 e0 ++ prime2 u3 r3 h2 e0)
def finish4L (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) : Program :=
 clear2 u3 r3 h2 e0 ++
 (LowBitCarryLoan.restore0 g v0 u0 e0 ++ finish3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2)

theorem geometry15_12 (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) :
 [g,v1,u0,u1,u2,r0,r1,r2,e0,cache,h1,h2].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h:=List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_nil]at h ⊢
 omega

theorem geometry15_4 (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) :
 [g,v0,u0,e0].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h:=List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_nil]at h ⊢
 omega

theorem prepare4L_run (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) (s:State) (m:List Bool)
 (hz:s.basis cache=false)
 (hl1:s.basis h1=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0 && s.basis e0)))
 (hl2:s.basis h2=loanValue2 s.basis g v1 u0 u1 u2 e0 h1)
 (hl0:s.basis e0=LowBitCarryLoan.value s.basis g v0 u0) :
 let k0:=s.basis u0 && !s.basis r0
 let k1:=carryBit (s.basis u1) (!s.basis r1) k0
 let k2:=carryBit (s.basis u2) (!s.basis r2) k1
 let k3:=carryBit (s.basis u3) (!s.basis r3) k2
 run (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) m s=
  ⟨s.phase,writeBit (writeBit (writeBit (writeBit s.basis cache k0) h1 k1) h2 k2) e0 k3⟩ := by
 have geom:=nd
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have nd12:=geometry15_12 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4:=geometry15_4 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 let k0:=s.basis u0 && !s.basis r0
 let k1:=carryBit (s.basis u1) (!s.basis r1) k0
 let k2:=carryBit (s.basis u2) (!s.basis r2) k1
 let k3:=carryBit (s.basis u3) (!s.basis r3) k2
 let S1:State:=⟨s.phase,writeBit (writeBit (writeBit s.basis cache k0) h1 k1) h2 k2⟩
 let S2:State:=⟨s.phase,writeBit S1.basis e0 false⟩
 have p:∀r,run (prepare3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2) r s=S1 := by
  intro r
  exact prepare3_run g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 nd12 s r hz hl1 hl2
 have q:∀r,run (LowBitCarryLoan.loan0 g v0 u0 e0) r S1=S2 := by
  intro r
  apply LowBitCarryLoan.loan0_run g v0 u0 e0 nd4 S1 r
  simpa [S1,LowBitCarryLoan.value,writeBit,Function.update_apply,
   show e0≠cache by tauto,show e0≠h1 by tauto,show e0≠h2 by tauto,
   show g≠cache by tauto,show g≠h1 by tauto,show g≠h2 by tauto,
   show v0≠cache by tauto,show v0≠h1 by tauto,show v0≠h2 by tauto,
   show u0≠cache by tauto,show u0≠h1 by tauto,show u0≠h2 by tauto] using hl0
 have z:∀r,run (prime2 u3 r3 h2 e0) r S2=
  ⟨s.phase,writeBit (writeBit (writeBit (writeBit s.basis cache k0) h1 k1) h2 k2) e0 k3⟩ := by
  intro r
  rw [prime2_run u3 r3 h2 e0 (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) S2 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases h:w=e0
  · subst w
    simp [S2,S1,k3,writeBit,Function.update_apply,
     show u3≠cache by tauto,show u3≠h1 by tauto,show u3≠h2 by tauto,show u3≠e0 by tauto,
     show r3≠cache by tauto,show r3≠h1 by tauto,show r3≠h2 by tauto,show r3≠e0 by tauto,
     show h2≠cache by tauto,show h2≠h1 by tauto,show h2≠e0 by tauto]
  · simp [S2,S1,writeBit,Function.update_apply,h]
 dsimp only
 rw [prepare4L,run_append,p,run_append,q,z]

theorem finish4L_run (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) (s:State) (m:List Bool)
 (hk0:s.basis cache=(s.basis u0 && !s.basis r0))
 (hk1:s.basis h1=carryBit (s.basis u1) (!s.basis r1) (s.basis cache))
 (hk2:s.basis h2=carryBit (s.basis u2) (!s.basis r2) (s.basis h1))
 (hk3:s.basis e0=carryBit (s.basis u3) (!s.basis r3) (s.basis h2)) :
 let b0:=writeBit s.basis e0 (LowBitCarryLoan.value s.basis g v0 u0)
 let t:=writeBit (writeBit (writeBit b0 h2 false) h1
  (b0 u1 ^^ b0 u0 ^^ (b0 u0 && b0 e0))) cache false
 let t2:=writeBit t h2 (loanValue2 t g v1 u0 u1 u2 e0 h1)
 run (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) m s=⟨s.phase,t2⟩ := by
 have geom:=nd
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have nd12:=geometry15_12 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4:=geometry15_4 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 let S0:State:=⟨s.phase,writeBit s.basis e0 false⟩
 let b0:=writeBit s.basis e0 (LowBitCarryLoan.value s.basis g v0 u0)
 let S1:State:=⟨s.phase,b0⟩
 let t:=writeBit (writeBit (writeBit b0 h2 false) h1
  (b0 u1 ^^ b0 u0 ^^ (b0 u0 && b0 e0))) cache false
 let t2:=writeBit t h2 (loanValue2 t g v1 u0 u1 u2 e0 h1)
 have p:∀r,run (clear2 u3 r3 h2 e0) r s=S0 := by
  intro r
  exact clear2_run u3 r3 h2 e0 (by tauto) (by tauto) (by tauto) s r hk3
 have q:∀r,run (LowBitCarryLoan.restore0 g v0 u0 e0) r S0=S1 := by
  intro r
  rw [LowBitCarryLoan.restore0_run g v0 u0 e0 nd4 S0 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases h:w=e0
  · subst w
    simp [S0,S1,b0,LowBitCarryLoan.value,writeBit,Function.update_apply,
     show u0≠e0 by tauto,show g≠e0 by tauto,show v0≠e0 by tauto]
  · simp [S0,S1,b0,writeBit,Function.update_apply,h]
 have z:∀r,run (finish3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2) r S1=⟨s.phase,t2⟩ := by
  intro r
  rw [finish3_run g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 nd12 S1 r]
  · simpa [S1,b0,writeBit,Function.update_apply,show cache≠e0 by tauto,
     show u0≠e0 by tauto,show r0≠e0 by tauto] using hk0
  · simpa [S1,b0,writeBit,Function.update_apply,show h1≠e0 by tauto,
     show u1≠e0 by tauto,show r1≠e0 by tauto,show cache≠e0 by tauto] using hk1
  · simpa [S1,b0,writeBit,Function.update_apply,show h2≠e0 by tauto,
     show u2≠e0 by tauto,show r2≠e0 by tauto,show h1≠e0 by tauto] using hk2
 dsimp only
 rw [finish4L,run_append,p,run_append,q,z]
#print axioms prepare4L_run
#print axioms finish4L_run
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryGeometry
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem geometry15 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (g : Wire) (hg : g ∉ L.wires) :
 [g,bit1 L.core.high,L.core.high.headD 0,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,
  cacheWire L,hostWire L,host2Wire L].Nodup := by
 have geo := mGeo L hw hn
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have uc := head4_count (mU L) (by rw [geo.u]; decide) q
 have rc := head4_count (mR L) (by rw [geo.r]; decide) q
 have ec := head3_count ((eReg L).take 129) (by simp [eReg_length L hw]) q
 have hhead : ((eReg L).take 129).headD 0 = (eReg L).headD 0 := head_take_pos _ _ (by decide)
 have hbit : bit1 ((eReg L).take 129) = hostWire L := bit1_take _ _ (by decide)
 have hbit2 : bit2 ((eReg L).take 129) = host2Wire L := bit2_take _ _ (by decide)
 rw [hhead,hbit,hbit2] at ec
 have ed := congrArg (List.count q) (cache_decomp L hw)
 have ud : (mU L).count q ≤ (hiReg L).count q := (List.drop_sublist _ _).count_le q
 have rd : (mR L).count q ≤ L.core.work.count q :=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).count_le q
 have hy : 3 ≤ L.core.high.length := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
 have hv := head3_count L.core.high hy q
 have vy : L.core.high.count q ≤ L.core.y.count q := by
  apply List.Sublist.count_le
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
 have vc : ([bit1 L.core.high,L.core.high.headD 0] : List Wire).count q ≤ L.core.y.count q := by
  simp only [List.count_cons,List.count_nil] at hv ⊢
  omega
 have ps := productSplit L q
 have es := eReg_count L q
 have lc := List.nodup_iff_count_le_one.mp (List.nodup_cons.mpr ⟨hg,hn⟩) q
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil] at lc uc rc ec ed vc ⊢
 omega

theorem e0_ne_key (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 (eReg L).headD 0≠eU L := by
 have shape:=(eShape L hw).1
 have len:(eRlow L).length=128:=by simp[eRlow,hw.core.product]
 have hm:(eReg L).headD 0∈eRlow L:=by
  rw [shape]
  cases hr:eRlow L with
  | nil => simp [hr] at len
  | cons a rest => simp
 have nd:=eReg_nodup L hn
 rw [shape]at nd
 exact (List.nodup_append.mp nd).2.2 _ hm _ (by simp)
#print axioms geometry15
#print axioms e0_ne_key
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryNumbers
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.SecondCarryLoan ECDSAAdd.Entrant.ThirdCarryLoanDevelop
namespace LowBitCarryNumbers
set_option maxHeartbeats 8000000

theorem loan0_from_mod2 (g : Bool) (S U E : Nat)
 (hE:E%2=((if g then S else 0)^2+U)%2) :
 digit E 0=(digit U 0 ^^ (g && digit S 0)) := by
 have hs:S%2=0 ∨ S%2=1:=by omega
 have hu:U%2=0 ∨ U%2=1:=by omega
 cases g <;> rcases hs with hs|hs <;> rcases hu with hu|hu <;>
  simp_all [digit,Nat.add_mod,Nat.pow_mod]
#print axioms loan0_from_mod2
end LowBitCarryNumbers

end -- isolated Carry10 component

section
-- LowBitCarryPrimitiveResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
namespace LowBitCarryLoan
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem physical (g src u q : Wire) (nd:[g,src,u,q].Nodup) :
 GatePhysical (loan0 g src u q) ∧ GatePhysical (restore0 g src u q) := by
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at nd
 simp [loan0,restore0,GatePhysical,PhysicalInstr,ProperGate]
 tauto

theorem support (g src u q : Wire) :
 wires (loan0 g src u q)⊆[g,src,u,q].toFinset ∧
 wires (restore0 g src u q)⊆[g,src,u,q].toFinset := by
 constructor <;> intro r h <;>
  simp [loan0,restore0,wires,Instr.wires,correctionWires]at h ⊢ <;> tauto
#print axioms physical
#print axioms support
end LowBitCarryLoan

end -- isolated Carry10 component

section
-- LowBitCarryEndsResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ECDSAAdd.RecordedQuantum
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem prepare4L_counts (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) :
 toffoliCount (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=4 ∧
 measurementCount (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=3 ∧
 Challenge.gateSlots (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=41 := by
 refine ⟨rfl,rfl,?_⟩
 simp[prepare4L,LowBitCarryLoan.loan0,prepare3,loan2,SecondCarryLoan.prepare,loan,prime,prime2,majority,
  Challenge.gateSlots,Challenge.instructionSlots]

theorem finish4L_counts (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) :
 toffoliCount (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=4 ∧
 measurementCount (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=4 ∧
 Challenge.gateSlots (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=34 := by
 refine ⟨rfl,rfl,?_⟩
 simp[finish4L,LowBitCarryLoan.restore0,finish3,restore2,SecondCarryLoan.finish,clear,clear2,restore,
  Challenge.gateSlots,Challenge.instructionSlots]

theorem ends4L_physical (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) :
 GatePhysical (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) ∧
 GatePhysical (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) := by
 have nd12:=geometry15_12 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4:=geometry15_4 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4': [u3,r3,h2,e0].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h:=List.nodup_iff_count_le_one.mp nd q
  simp only[List.count_cons,List.count_nil]at h ⊢
  omega
 have a:=LowBitCarryLoan.physical g v0 u0 e0 nd4
 have b:=ends3_physical g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 nd12
 have p:GatePhysical (prime2 u3 r3 h2 e0) ∧ GatePhysical (clear2 u3 r3 h2 e0) := by
  simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at nd4'
  simp[prime2,majority,clear2,GatePhysical,PhysicalInstr,ProperGate]
  tauto
 simp only[prepare4L,finish4L,gatePhysical_append]
 exact ⟨⟨b.1,a.1,p.1⟩,p.2,a.2,b.2⟩

theorem ends4L_support (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) :
 wires (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)⊆
 [g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].toFinset ∧
 wires (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)⊆
 [g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].toFinset := by
 have a:=LowBitCarryLoan.support g v0 u0 e0
 have b:=ends3_support g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2
 have p:wires (prime2 u3 r3 h2 e0)⊆[u3,r3,h2,e0].toFinset ∧
   wires (clear2 u3 r3 h2 e0)⊆[u3,r3,h2,e0].toFinset := by
  constructor <;> intro q h <;>
   simp[prime2,majority,clear2,ECDSAAdd.wires,Instr.wires,correctionWires]at h ⊢ <;> tauto
 constructor <;> intro q h
 · simp only[prepare4L,wires_append,Finset.mem_union]at h
   rcases h with h|h|h
   · have z:=b.1 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=a.1 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=p.1 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
 · simp only[finish4L,wires_append,Finset.mem_union]at h
   rcases h with h|h|h
   · have z:=p.2 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=a.2 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=b.2 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
#print axioms prepare4L_counts
#print axioms finish4L_counts
#print axioms ends4L_physical
#print axioms ends4L_support
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryFull
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def wMidFullCCC0 (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
 prepare4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) ++
 ((wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) ++ (wCoreK L ++ wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0))) ++
 finish4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L))

theorem wMidFullCCC0_step (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (c:Wire) (hcw:c∉L.wires) (base:BasisState) (hc:L.PairClean base) (O E b1:Nat)
 (hb1:regValue (hiReg L) base=b1) (hb1lt:b1<2^128) (hO:O<SquareReduction.p)
 (H l K:Nat) (hH:H<2^96) (hl:l<2^32) (hK:K≤1) (hE:E=2^32*H+l+2^128*K)
 (hLoan:(E/2%2==1)=((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
   ((b1/2^96%2==1)&&(E%2==1))))
 (hLoan2:digit E 2= (digit (b1/2^96) 2 ^^
   (base (bit1 L.core.high)&&base c) ^^ (base (bit1 L.core.high)&&digit E 0) ^^
   (base (bit1 L.core.high)&&digit (b1/2^96) 0) ^^
   (digit (b1/2^96) 1&&digit E 1) ^^ digit (b1/2^96) 1))
 (hLoan0 : digit E 0 = (digit (b1/2^96) 0 ^^ (base c && base (L.core.high.headD 0)))) :
 Triple (BState L base O E (4294968272*b1)) (wMidFullCCC0 L c)
 (BState L base (((b1/2^96+4294968273*(4294968272*b1/2^128-b1/2^96))+4294968272*2^32*K+
   2^128*((4294968272*b1)%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E (4294968272*b1)) := by
 intro s m h
 let u0:Wire:=(mU L).headD 0
 let u1:Wire:=bit1 (mU L)
 let u2:Wire:=bit2 (mU L)
 let u3:Wire:=bit3 (mU L)
 let r0:Wire:=(mR L).headD 0
 let r1:Wire:=bit1 (mR L)
 let r2:Wire:=bit2 (mR L)
 let r3:Wire:=bit3 (mR L)
 let e0:Wire:=(eReg L).headD 0
 let v:Wire:=bit1 L.core.high
 let v0:Wire:=L.core.high.headD 0
 let cache:Wire:=cacheWire L
 let host:Wire:=hostWire L
 let host2:Wire:=host2Wire L
 let u:=b1/2^96
 let d:=4294968272*b1/2^128-u
 let k0:Bool:=(u%2==1)&&(d%2==1)
 let k1:Bool:=carryLow2 u d
 let k2:Bool:=carryLow3 u d
 let k3:Bool:=carryLow4 u d
 have nd:[c,v,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,host,host2].Nodup:=geometry15 L hw hn c hcw
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have n0_11:c≠e0:=FourthCarryLoan.get_ne _ nd 0 11 (by simp) (by simp) (by decide)
 have n0_12:c≠cache:=FourthCarryLoan.get_ne _ nd 0 12 (by simp) (by simp) (by decide)
 have n0_13:c≠host:=FourthCarryLoan.get_ne _ nd 0 13 (by simp) (by simp) (by decide)
 have n0_14:c≠host2:=FourthCarryLoan.get_ne _ nd 0 14 (by simp) (by simp) (by decide)
 have n1_11:v≠e0:=FourthCarryLoan.get_ne _ nd 1 11 (by simp) (by simp) (by decide)
 have n1_12:v≠cache:=FourthCarryLoan.get_ne _ nd 1 12 (by simp) (by simp) (by decide)
 have n1_13:v≠host:=FourthCarryLoan.get_ne _ nd 1 13 (by simp) (by simp) (by decide)
 have n1_14:v≠host2:=FourthCarryLoan.get_ne _ nd 1 14 (by simp) (by simp) (by decide)
 have n2_11:v0≠e0:=FourthCarryLoan.get_ne _ nd 2 11 (by simp) (by simp) (by decide)
 have n2_12:v0≠cache:=FourthCarryLoan.get_ne _ nd 2 12 (by simp) (by simp) (by decide)
 have n2_13:v0≠host:=FourthCarryLoan.get_ne _ nd 2 13 (by simp) (by simp) (by decide)
 have n2_14:v0≠host2:=FourthCarryLoan.get_ne _ nd 2 14 (by simp) (by simp) (by decide)
 have n3_11:u0≠e0:=FourthCarryLoan.get_ne _ nd 3 11 (by simp) (by simp) (by decide)
 have n3_12:u0≠cache:=FourthCarryLoan.get_ne _ nd 3 12 (by simp) (by simp) (by decide)
 have n3_13:u0≠host:=FourthCarryLoan.get_ne _ nd 3 13 (by simp) (by simp) (by decide)
 have n3_14:u0≠host2:=FourthCarryLoan.get_ne _ nd 3 14 (by simp) (by simp) (by decide)
 have n4_11:u1≠e0:=FourthCarryLoan.get_ne _ nd 4 11 (by simp) (by simp) (by decide)
 have n4_12:u1≠cache:=FourthCarryLoan.get_ne _ nd 4 12 (by simp) (by simp) (by decide)
 have n4_13:u1≠host:=FourthCarryLoan.get_ne _ nd 4 13 (by simp) (by simp) (by decide)
 have n4_14:u1≠host2:=FourthCarryLoan.get_ne _ nd 4 14 (by simp) (by simp) (by decide)
 have n5_11:u2≠e0:=FourthCarryLoan.get_ne _ nd 5 11 (by simp) (by simp) (by decide)
 have n5_12:u2≠cache:=FourthCarryLoan.get_ne _ nd 5 12 (by simp) (by simp) (by decide)
 have n5_13:u2≠host:=FourthCarryLoan.get_ne _ nd 5 13 (by simp) (by simp) (by decide)
 have n5_14:u2≠host2:=FourthCarryLoan.get_ne _ nd 5 14 (by simp) (by simp) (by decide)
 have n6_11:u3≠e0:=FourthCarryLoan.get_ne _ nd 6 11 (by simp) (by simp) (by decide)
 have n6_12:u3≠cache:=FourthCarryLoan.get_ne _ nd 6 12 (by simp) (by simp) (by decide)
 have n6_13:u3≠host:=FourthCarryLoan.get_ne _ nd 6 13 (by simp) (by simp) (by decide)
 have n6_14:u3≠host2:=FourthCarryLoan.get_ne _ nd 6 14 (by simp) (by simp) (by decide)
 have n7_11:r0≠e0:=FourthCarryLoan.get_ne _ nd 7 11 (by simp) (by simp) (by decide)
 have n7_12:r0≠cache:=FourthCarryLoan.get_ne _ nd 7 12 (by simp) (by simp) (by decide)
 have n7_13:r0≠host:=FourthCarryLoan.get_ne _ nd 7 13 (by simp) (by simp) (by decide)
 have n7_14:r0≠host2:=FourthCarryLoan.get_ne _ nd 7 14 (by simp) (by simp) (by decide)
 have n8_11:r1≠e0:=FourthCarryLoan.get_ne _ nd 8 11 (by simp) (by simp) (by decide)
 have n8_12:r1≠cache:=FourthCarryLoan.get_ne _ nd 8 12 (by simp) (by simp) (by decide)
 have n8_13:r1≠host:=FourthCarryLoan.get_ne _ nd 8 13 (by simp) (by simp) (by decide)
 have n8_14:r1≠host2:=FourthCarryLoan.get_ne _ nd 8 14 (by simp) (by simp) (by decide)
 have n9_11:r2≠e0:=FourthCarryLoan.get_ne _ nd 9 11 (by simp) (by simp) (by decide)
 have n9_12:r2≠cache:=FourthCarryLoan.get_ne _ nd 9 12 (by simp) (by simp) (by decide)
 have n9_13:r2≠host:=FourthCarryLoan.get_ne _ nd 9 13 (by simp) (by simp) (by decide)
 have n9_14:r2≠host2:=FourthCarryLoan.get_ne _ nd 9 14 (by simp) (by simp) (by decide)
 have n10_11:r3≠e0:=FourthCarryLoan.get_ne _ nd 10 11 (by simp) (by simp) (by decide)
 have n10_12:r3≠cache:=FourthCarryLoan.get_ne _ nd 10 12 (by simp) (by simp) (by decide)
 have n10_13:r3≠host:=FourthCarryLoan.get_ne _ nd 10 13 (by simp) (by simp) (by decide)
 have n10_14:r3≠host2:=FourthCarryLoan.get_ne _ nd 10 14 (by simp) (by simp) (by decide)
 have n11_12:e0≠cache:=FourthCarryLoan.get_ne _ nd 11 12 (by simp) (by simp) (by decide)
 have n11_13:e0≠host:=FourthCarryLoan.get_ne _ nd 11 13 (by simp) (by simp) (by decide)
 have n11_14:e0≠host2:=FourthCarryLoan.get_ne _ nd 11 14 (by simp) (by simp) (by decide)
 have n12_11:cache≠e0:=FourthCarryLoan.get_ne _ nd 12 11 (by simp) (by simp) (by decide)
 have n12_13:cache≠host:=FourthCarryLoan.get_ne _ nd 12 13 (by simp) (by simp) (by decide)
 have n12_14:cache≠host2:=FourthCarryLoan.get_ne _ nd 12 14 (by simp) (by simp) (by decide)
 have n13_11:host≠e0:=FourthCarryLoan.get_ne _ nd 13 11 (by simp) (by simp) (by decide)
 have n13_12:host≠cache:=FourthCarryLoan.get_ne _ nd 13 12 (by simp) (by simp) (by decide)
 have n13_14:host≠host2:=FourthCarryLoan.get_ne _ nd 13 14 (by simp) (by simp) (by decide)
 have n14_11:host2≠e0:=FourthCarryLoan.get_ne _ nd 14 11 (by simp) (by simp) (by decide)
 have n14_12:host2≠cache:=FourthCarryLoan.get_ne _ nd 14 12 (by simp) (by simp) (by decide)
 have n14_13:host2≠host:=FourthCarryLoan.get_ne _ nd 14 13 (by simp) (by simp) (by decide)
 have ce:cache∈eReg L:=cache_mem L hw
 have he:host∈eReg L:=host_mem L hw
 have he2:host2∈eReg L:=host2_mem L hw
 have he0:e0∈eReg L:=head_mem _ (by simp [eReg_length L hw])
 have ca:=external_away L c hcw
 have vy:v∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
  (bit1_mem L.core.high (by simp[CuccaroStreamedSquareLayout.high,hw.core.y,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13])))
 have va:=source_away L hn v vy
 have vy0:v0∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
  (head_mem L.core.high (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])))
 have va0:=source_away L hn v0 vy0
 have sg:s.basis c=base c:=h.2.2.2 c ca.1 ca.2.1 ca.2.2
 have sv:s.basis v=base v:=h.2.2.2 v va.1 va.2.1 va.2.2
 have sv0 : s.basis v0 = base v0 := h.2.2.2 v0 va0.1 va0.2.1 va0.2.2
 have hz:s.basis cache=false:=e_cache_zero L hw s.basis E h.2.1 (by rw[hE];omega)
 have b0:=bstate_heads L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b1s:=bstate_heads2 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b2:=bstate_heads3 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b3:=bstate_heads4 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have es:s.basis e0=(E%2==1):=by
  dsimp[e0,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13];rw[head_parity (eReg L) s.basis (by simp[eReg_length L hw,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]),h.2.1]
 have hs:s.basis host=(E/2%2==1):=by
  dsimp[host,hostWire,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13];rw[bit1_parity (eReg L) s.basis (by simp[eReg_length L hw,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]),h.2.1]
 have hs2:s.basis host2=digit E 2:=by
  dsimp[host2,host2Wire,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13];rw[bit2_parity (eReg L) s.basis (by simp[eReg_length L hw,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]),h.2.1]
 have ready:s.basis host=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0)):=by
  rw[hs,b0.1,b1s.1,es];exact hLoan
 have ready2:s.basis host2=loanValue2 s.basis c v u0 u1 u2 e0 host:=by
  rw[hs2]
  unfold loanValue2
  rw[b2.1,b0.1,b1s.1,es,hs,sg,sv]
  simpa only[digit,pow_zero,pow_one,Nat.div_one,v]using hLoan2
 have ready0:s.basis e0=LowBitCarryLoan.value s.basis c v0 u0:=by
  rw[es]
  unfold LowBitCarryLoan.value
  rw[b0.1,sg,sv0]
  simpa only[digit,pow_zero,Nat.div_one,v0]using hLoan0
 have carry0:(s.basis u0&&!s.basis r0)=k0:=by
  rw[b0.1,b0.2];simpa only[Nat.one_mul]using carry_parity u d 1 (by decide)
 have carry1:carryBit (s.basis u1) (!s.basis r1) k0=k1:=by
  rw[b1s.1,b1s.2];simpa only[Nat.one_mul]using sub_second u d 1 (by decide)
 have carry2:carryBit (s.basis u2) (!s.basis r2) k1=k2:=by
  rw[b2.1,b2.2];simpa only[Nat.one_mul]using sub_third u d 1 (by decide)
 have carry3 : carryBit (s.basis u3) (!s.basis r3) k2 = k3 := by
  rw [b3.1,b3.2]; simpa only [Nat.one_mul] using sub_fourth u d 1 (by decide)
 let t:BasisState:=writeBit (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2) e0 k3
 let EP:Nat:=regValue (eReg L) t
 have prepared:∀mm,run (prepare4L c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2) mm s=⟨s.phase,t⟩:=by
  intro mm
  rw[prepare4L_run c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 nd s mm hz ready ready2 ready0,carry0,carry1,carry2,carry3]
 have hb0:=bstate_write_e L hn cache ce base s.basis O E _ h k0
 have hb2:=bstate_write_e L hn host he base (writeBit s.basis cache k0) O
  (regValue (eReg L) (writeBit s.basis cache k0)) _ hb0 k1
 have hb3:=bstate_write_e L hn host2 he2 base (writeBit (writeBit s.basis cache k0) host k1) O
  (regValue (eReg L) (writeBit (writeBit s.basis cache k0) host k1)) _ hb2 k2
 have hb4 := bstate_write_e L hn e0 he0 base
  (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2) O
  (regValue (eReg L) (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2)) _ hb3 k3
 have inp:BState L base O EP (4294968272*b1) t ∧ t cache=k0 ∧ t host=k1 ∧ t host2=k2 ∧ t e0=k3 ∧
  (if t (eU L) then 1 else 0)=K:=by
  refine ⟨hb4,?_,?_,?_,?_,?_⟩
  · simp[t,writeBit,Function.update_apply,show cache≠host from FourthCarryLoan.get_ne _ nd 12 13 (by simp) (by simp) (by decide),show cache≠host2 from FourthCarryLoan.get_ne _ nd 12 14 (by simp) (by simp) (by decide),n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · simp[t,writeBit,Function.update_apply,show host≠host2 from FourthCarryLoan.get_ne _ nd 13 14 (by simp) (by simp) (by decide),n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · simp[t,writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · simp[t,writeBit,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · have hk:=bstate_key L hw s.basis E H l K h.2.1 hH hl hK hE
    simpa[t,writeBit,Function.update_apply,show eU L≠cache from (cache_ne_k L hw hn).symm,
     show eU L≠host from (host_ne_key L hw hn).symm,show eU L≠host2 from (host2_ne_key L hw hn).symm,show eU L≠e0 from (e0_ne_key L hw hn).symm]using hk
 let mid:=wFwdCCCC L cache host host2 e0++(wCoreK L++wInvCCCC L cache host host2 e0)
 let rest:=m.drop (measurementCount (prepare4L c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2))
 let mmid:=rest.take (measurementCount mid)
 rw[wMidFullCCC0,run_append,prepared,run_append]
 have hm:=wMidCCCC_step L hw hn cache ce host he host2 he2 e0 he0 base hc O EP b1 hb1 hb1lt hO K hK
  (⟨s.phase,t⟩:State) mmid inp
 generalize hr:run mid mmid (⟨s.phase,t⟩:State)=r at hm ⊢
 have br0:=bstate_heads L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br1:=bstate_heads2 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br2:=bstate_heads3 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br3:=bstate_heads4 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have er:∀q∈eReg L,r.basis q=t q:=(regValue_eq_iff _ _ _).mp hm.2.1.2.1
 have rU0:r.basis u0=s.basis u0:=br0.1.trans b0.1.symm
 have rU1:r.basis u1=s.basis u1:=br1.1.trans b1s.1.symm
 have rU2:r.basis u2=s.basis u2:=br2.1.trans b2.1.symm
 have rR0:r.basis r0=s.basis r0:=br0.2.trans b0.2.symm
 have rR1:r.basis r1=s.basis r1:=br1.2.trans b1s.2.symm
 have rR2:r.basis r2=s.basis r2:=br2.2.trans b2.2.symm
 have rU3:r.basis u3=s.basis u3:=br3.1.trans b3.1.symm
 have rR3:r.basis r3=s.basis r3:=br3.2.trans b3.2.symm
 have rV0:r.basis v0=s.basis v0:=(hm.2.1.2.2.2 v0 va0.1 va0.2.1 va0.2.2).trans sv0.symm
 have rG:r.basis c=s.basis c:=(hm.2.1.2.2.2 c ca.1 ca.2.1 ca.2.2).trans sg.symm
 have rV:r.basis v=s.basis v:=(hm.2.1.2.2.2 v va.1 va.2.1 va.2.2).trans sv.symm
 have rk:r.basis cache=(r.basis u0&&!r.basis r0):=by
  rw[rU0,rR0,carry0];exact hm.2.2.1
 have rk1:r.basis host=carryBit (r.basis u1) (!r.basis r1) (r.basis cache):=by
  rw[rU1,rR1,hm.2.2.1,carry1];exact hm.2.2.2.1
 have rk2:r.basis host2=carryBit (r.basis u2) (!r.basis r2) (r.basis host):=by
  rw[rU2,rR2,hm.2.2.2.1,carry2];exact hm.2.2.2.2.1
 have rk3:r.basis e0=carryBit (r.basis u3) (!r.basis r3) (r.basis host2):=by
  rw[rU3,rR3,hm.2.2.2.2.1,carry3];exact hm.2.2.2.2.2.1
 have restored0:LowBitCarryLoan.value r.basis c v0 u0=s.basis e0:=by
  unfold LowBitCarryLoan.value
  rw[rG,rV0,rU0]
  exact ready0.symm
 rw[finish4L_run c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 nd r _ rk rk1 rk2 rk3]
 dsimp only
 rw[restored0]
 let b0':=writeBit r.basis e0 (s.basis e0)
 have restored1:(b0' u1 ^^ b0' u0 ^^ (b0' u0&&b0' e0))=s.basis host:=by
  simp only[b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13,ite_false,ite_true,rU0,rU1]
  exact ready.symm
 rw[restored1]
 let t0:=writeBit (writeBit (writeBit b0' host2 false) host (s.basis host)) cache false
 have restored2:loanValue2 t0 c v u0 u1 u2 e0 host=s.basis host2:=by
  simp only[loanValue2,t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13,ite_false,ite_true,rG,rV,rU0,rU1,rU2]
  exact ready2.symm
 refine ⟨hm.1,?_⟩
 have hf0:=bstate_write_e L hn e0 he0 base r.basis _ EP _ hm.2.1 (s.basis e0)
 have hf1:=bstate_write_e L hn host2 he2 base b0' _ (regValue (eReg L) b0') _ hf0 false
 have hf2:=bstate_write_e L hn host he base (writeBit b0' host2 false) _
  (regValue (eReg L) (writeBit b0' host2 false)) _ hf1 (s.basis host)
 have hf3:=bstate_write_e L hn cache ce base (writeBit (writeBit b0' host2 false) host (s.basis host)) _
  (regValue (eReg L) (writeBit (writeBit b0' host2 false) host (s.basis host))) _ hf2 false
 have hf4:=bstate_write_e L hn host2 he2 base t0 _ (regValue (eReg L) t0) _ hf3 (loanValue2 t0 c v u0 u1 u2 e0 host)
 have ev:regValue (eReg L) (writeBit t0 host2 (loanValue2 t0 c v u0 u1 u2 e0 host))=E:=by
  rw[restored2]
  apply Eq.trans _ h.2.1
  apply regValue_congr
  intro q hq
  by_cases q0:q=e0
  · subst q;simp[t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  by_cases q2:q=host2
  · subst q;simp[writeBit]
  by_cases q1:q=host
  · subst q;simp[t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  by_cases qc:q=cache
  · subst q;simp[t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13,hz]
  · simp only[t0,b0',writeBit,Function.update_apply,q0,q2,q1,qc,ite_false]
    rw[er q hq]
    simp[t,writeBit,Function.update_apply,q0,q2,q1,qc]
 simpa only[ev]using hf4
#print axioms wMidFullCCC0_step
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryOldE
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem e0_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 (eReg L).headD 0∈eReg L:=head_mem _ (by simp[eReg_length L hw])

theorem armsCCC0_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 wires (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆oldE L ∧
 wires (wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆oldE L:=by
 have hh:((eReg L).headD 0)∈oldE L:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (e0_mem L hw)))))
 have f:=(fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
 have i:=(invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
 constructor
 · intro q h;rcases Finset.mem_insert.mp (f h)with e|h
   · exact e ▸ hh
   · exact (armsCCC_oldE L hw).1 h
 · intro q h;rcases Finset.mem_insert.mp (i h)with e|h
   · exact e ▸ hh
   · exact (armsCCC_oldE L hw).2 h

theorem ends4L_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g v v2:Wire):
 wires (prepare4L g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L))⊆insert g (insert v (insert v2 (oldE L))) ∧
 wires (finish4L g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L))⊆insert g (insert v (insert v2 (oldE L))):=by
 have lens:=mLens L hw
 have uMem (q:Wire) (h:q∈mU L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inl (List.mem_of_mem_drop h)))
 have rMem (q:Wire) (h:q∈mR L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
 have eMem (q:Wire) (h:q∈eReg L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl h))))
 have hu0:=uMem _ (head_mem _ (by rw[lens.u];decide))
 have hu1:=uMem _ (bit1_mem _ (by rw[lens.u];decide))
 have hu2:=uMem _ (bit2_mem _ (by rw[lens.u];decide))
 have hu3:=uMem _ (bit3_mem _ (by rw[lens.u];decide))
 have hr0:=rMem _ (head_mem _ (by rw[lens.r];decide))
 have hr1:=rMem _ (bit1_mem _ (by rw[lens.r];decide))
 have hr2:=rMem _ (bit2_mem _ (by rw[lens.r];decide))
 have hr3:=rMem _ (bit3_mem _ (by rw[lens.r];decide))
 have he0:=eMem _ (head_mem _ (by simp[eReg_length L hw]))
 have hcache:=eMem _ (cache_mem L hw)
 have hh1:=eMem _ (host_mem L hw)
 have hh2:=eMem _ (host2_mem L hw)
 have carrier:([g,v,v2,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
    (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,
    cacheWire L,hostWire L,host2Wire L]:List Wire).toFinset⊆insert g (insert v (insert v2 (oldE L))):=by
  intro q h
  simp only[List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
   simp only[Finset.mem_insert] <;> tauto
 have cap:=ends4L_support g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
   ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
   (cacheWire L) (hostWire L) (host2Wire L)
 exact ⟨cap.1.trans carrier,cap.2.trans carrier⟩

theorem e0_not_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 ¬WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (((eReg L).headD 0)):=by
 have ce:=e0_mem L hw
 have cp:=List.count_pos_iff.mpr (eReg_product L _ ce)
 have lc:=layoutCount L hn (((eReg L).headD 0))
 intro hm
 rcases hm with hi|hu|hr|hs|hz|hc
 · have cinPos:0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
     L.core.modFlag,L.core.sumCarry].count (((eReg L).headD 0)):=List.count_pos_iff.mpr (by rw[hi];simp)
   omega
 · exact (eReg_away L hn _ ce).2.2 (List.mem_of_mem_drop hu)
 · have :=List.count_pos_iff.mpr (mR_work L _ hr);omega
 · have :=List.count_pos_iff.mpr (mS_pad L _ hs);omega
 · have :=List.count_pos_iff.mpr (mZ_pad L _ hz);omega
 · have :=List.count_pos_iff.mpr (mC_pad L _ hc);omega

#print axioms armsCCC0_oldE
#print axioms ends4L_oldE
#print axioms e0_not_mem
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryMiddleCounts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem midCCC0_patch (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 Patch ((eReg L).headD 0) 4
  (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0)++
   (wCoreK L++wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0)))
  (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)++
   (wCoreK L++wInvCCC L (cacheWire L) (hostWire L) (host2Wire L))):=
 (fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) (eU L)).app
  ((Patch.refl _ (wCoreK L)).app
   (invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) (eU L)))

theorem middle_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (wMidFullCCC0 L c)+2 = toffoliCount (wMidFullCCC L c) ∧
 measurementCount (wMidFullCCC0 L c) = measurementCount (wMidFullCCC L c)+2 ∧
 Challenge.gateSlots (wMidFullCCC0 L c)+1 = Challenge.gateSlots (wMidFullCCC L c) := by
 have h := midCCC0_patch L hw
 have ht := h.t; have hm := h.m; have hs := h.slots
 simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at ht hm hs
 have prepT (a b c d e f g h i j k l m n o : Wire) : toffoliCount (prepare4L a b c d e f g h i j k l m n o) = 4 := (prepare4L_counts a b c d e f g h i j k l m n o).1
 have prepM (a b c d e f g h i j k l m n o : Wire) : measurementCount (prepare4L a b c d e f g h i j k l m n o) = 3 := (prepare4L_counts a b c d e f g h i j k l m n o).2.1
 have prepS (a b c d e f g h i j k l m n o : Wire) : Challenge.gateSlots (prepare4L a b c d e f g h i j k l m n o) = 41 := (prepare4L_counts a b c d e f g h i j k l m n o).2.2
 have finT (a b c d e f g h i j k l m n o : Wire) : toffoliCount (finish4L a b c d e f g h i j k l m n o) = 4 := (finish4L_counts a b c d e f g h i j k l m n o).1
 have finM (a b c d e f g h i j k l m n o : Wire) : measurementCount (finish4L a b c d e f g h i j k l m n o) = 4 := (finish4L_counts a b c d e f g h i j k l m n o).2.1
 have finS (a b c d e f g h i j k l m n o : Wire) : Challenge.gateSlots (finish4L a b c d e f g h i j k l m n o) = 34 := (finish4L_counts a b c d e f g h i j k l m n o).2.2
 have oldPT (a b c d e f g h i j k l : Wire) : toffoliCount (prepare3 a b c d e f g h i j k l) = 3 := rfl
 have oldPM (a b c d e f g h i j k l : Wire) : measurementCount (prepare3 a b c d e f g h i j k l) = 2 := rfl
 have oldPS (a b c d e f g h i j k l : Wire) : Challenge.gateSlots (prepare3 a b c d e f g h i j k l) = 30 := by simp [prepare3,loan2,SecondCarryLoan.prepare,prime,loan,prime2,majority,Challenge.gateSlots,Challenge.instructionSlots]
 have oldFT (a b c d e f g h i j k l : Wire) : toffoliCount (finish3 a b c d e f g h i j k l) = 3 := rfl
 have oldFM (a b c d e f g h i j k l : Wire) : measurementCount (finish3 a b c d e f g h i j k l) = 3 := rfl
 have oldFS (a b c d e f g h i j k l : Wire) : Challenge.gateSlots (finish3 a b c d e f g h i j k l) = 26 := by simp [finish3,SecondCarryLoan.finish,clear2,clear,restore,restore2,Challenge.gateSlots,Challenge.instructionSlots]
 simp only [wMidFullCCC0,wMidFullCCC,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  prepT,prepM,prepS,finT,finM,finS,oldPT,oldPM,oldPS,oldFT,oldFM,oldFS]
 exact ⟨by omega,by omega,by omega⟩
#print axioms middle_counts
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryPhysical
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem middle_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hc : c ∉ L.wires) : GatePhysical (wMidFullCCC0 L c) := by
 have hp := ThirdCarryLoanDevelop.middle_physical L hw hn c hc
 simp only [wMidFullCCC,gatePhysical_append] at hp
 have geo := geometry15 L hw hn c hc
 have nc : ((eReg L).headD 0) ≠ cacheWire L := FourthCarryLoan.get_ne _ geo 11 12 (by simp) (by simp) (by decide)
 have n1 : ((eReg L).headD 0) ≠ hostWire L := FourthCarryLoan.get_ne _ geo 11 13 (by simp) (by simp) (by decide)
 have n2 : ((eReg L).headD 0) ≠ host2Wire L := FourthCarryLoan.get_ne _ geo 11 14 (by simp) (by simp) (by decide)
 have af : ((eReg L).headD 0) ∉ wires (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)) := by
  intro h
  rcases Finset.mem_insert.mp ((fwdCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support h) with he|h
  · exact n2 he
  rcases Finset.mem_insert.mp ((fwdCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h) with he|h
  · exact n1 he
  rcases Finset.mem_insert.mp ((fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h) with he|h
  · exact nc he
  rcases WinArith.tFwdK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact e0_not_mem L hw hn hm
  · exact e0_ne_key L hw hn he
 have ai : ((eReg L).headD 0) ∉ wires (wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)) := by
  intro h
  rcases Finset.mem_insert.mp ((invCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support h) with he|h
  · exact n2 he
  rcases Finset.mem_insert.mp ((invCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h) with he|h
  · exact n1 he
  rcases Finset.mem_insert.mp ((invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h) with he|h
  · exact nc he
  rcases WinArith.tInvK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact e0_not_mem L hw hn hm
  · exact e0_ne_key L hw hn he
 have pf := (fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).phys af hp.2.1.1
 have pi := (invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).phys ai hp.2.1.2.2
 have ends := ends4L_physical c (bit1 L.core.high) (L.core.high.headD 0)
  ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L))
  ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) geo
 simp only [wMidFullCCC0,gatePhysical_append]
 exact ⟨ends.1,⟨pf,hp.2.1.2.1,pi⟩,ends.2⟩
#print axioms middle_physical
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- ParkCarry10Core
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry10Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop LowBitCarryDevelop ParkCarry7Develop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem mid_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hc : c ∉ L.wires) : L.core.sumCarry ∉ wires (wMidFullCCC0 L c) := by
 have oe := ParkCarry7Develop.oldE_sumCarry_free L hw hn c hc
 have ng : L.core.sumCarry ≠ c := by
  intro h; apply hc
  simp [←h,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
 have nv : L.core.sumCarry ≠ bit1 L.core.high := by
  intro h
  apply ParkCarryDevelop.sumCarry_away L hn
  have vy := ParkCarry8Develop.sourceHigh_in_y L hw
  rw [←h] at vy
  simp [ParkCarryDevelop.restWires,vy]
 have nv0:L.core.sumCarry≠L.core.high.headD 0:=by
  intro h
  apply ParkCarryDevelop.sumCarry_away L hn
  have vy:L.core.high.headD 0∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
   (head_mem _ (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])))
  rw[←h]at vy
  simp[ParkCarryDevelop.restWires,vy]
 have ends := ends4L_oldE L hw c (bit1 L.core.high) (L.core.high.headD 0)
 have arms := armsCCC0_oldE L hw
 have co : L.core.sumCarry ∉ wires (wCoreK L) := by
  have off := (b_wloop_sumCarry_free L hw hn c hc).2.1
  simp only [wires_append,Finset.mem_union,not_or] at off
  exact off.2.1
 have erase {P : Program} (sub : wires P ⊆ insert c (insert (bit1 L.core.high) (insert (L.core.high.headD 0) (oldE L)))) :
   L.core.sumCarry ∉ wires P := by
  intro h
  rcases Finset.mem_insert.mp (sub h) with e|h
  · exact ng e
  rcases Finset.mem_insert.mp h with e|h
  · exact nv e
  rcases Finset.mem_insert.mp h with e|h
  · exact nv0 e
  · exact oe h
 intro h
 simp only [wMidFullCCC0,wires_append,Finset.mem_union] at h
 rcases h with h|((h|(h|h))|h)
 · exact erase ends.1 h
 · exact oe (arms.1 h)
 · exact co h
 · exact oe (arms.2 h)
 · exact erase ends.2 h

def fold (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 eAddLo L++(buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
  (wMidFullCCC0 L c++(unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
   (ParkCarryDevelop.program (eU L) L.core.sumCarry++eSubK L))))
def rebuild (L:CuccaroStreamedSquareWideLayout):Program:=eAddB L++(restore L++padM L 744)
def body (L:CuccaroStreamedSquareWideLayout)(c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(fold L c++(eFoldTq L c++rebuild L)))

theorem body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (hSource:M=if base c then regValue L.core.high base else 0) :
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
    intro h;apply sumCarry_away L hn;simp [restWires,h]
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
  have off:=b_wloop_sumCarry_free L hw hn c hcw
  have loop:=cached_wloop_bstate_step L hw hn base hc hsum O2 (2^32*H+l'+2^128*K) O3
    (wMidFullCCC0 L c) wmBase off.1 (mid_sumCarry_free L hw hn c hcw) off.2.2
  have kc:=park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (fold L c) (BState L baseK O3 E1 0) :=
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
  have rp := padM_step L hw hn base hc O4 b0 0 744
  have tr : Triple (BState L baseK O4 E1 0) (rebuild L) (BState L base O4 b0 0) :=
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
  exact all

#print axioms mid_sumCarry_free
#print axioms body_frame
end ECDSAAdd.Entrant.ParkCarry10Develop

end -- isolated Carry10 component

section
-- ParkCarry10Metrics
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry10Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop LowBitCarryDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem body_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 toffoliCount (body L c)=4762 ∧ measurementCount (body L c)=5924:=by
 have base:=ParkCarry8Develop.body_counts L hw c
 have mid:=LowBitCarryDevelop.middle_counts L hw c
 have p:=padM_counts L 744
 have q:=padM_counts L 746
 simp only[body,fold,rebuild,ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,
  toffoliCount_append,measurementCount_append]at base ⊢
 exact ⟨by omega,by omega⟩

theorem body_slots (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 Challenge.gateSlots (body L c)+3=Challenge.gateSlots (ParkCarry8Develop.body L c):=by
 have mid:=(LowBitCarryDevelop.middle_counts L hw c).2.2
 have p:=padM_slots L 744
 have q:=padM_slots L 746
 simp only[body,fold,rebuild,ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,
  Challenge.gateSlots_append]
 omega

theorem body_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (hn:(c::L.wires).Nodup):GatePhysical (body L c):=by
 have hp:=ParkCarry8Develop.body_physical L hw c hn
 have nd:=(List.nodup_cons.mp hn).2
 have mid:=LowBitCarryDevelop.middle_physical L hw nd c (List.nodup_cons.mp hn).1
 have pad:=padM_physical L 744
 simp only[ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,gatePhysical_append]at hp
 simp only[body,fold,rebuild,gatePhysical_append]
 tauto

#print axioms body_counts
#print axioms body_slots
#print axioms body_physical
end ECDSAAdd.Entrant.ParkCarry10Develop

end -- isolated Carry10 component

section
-- ParkCarry10Hosting
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry10Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def hostedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 body (hostLayout L rho) c

theorem hosted_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire)
 (h : rho L.core.sumCarry = L.core.sumCarry) : hostedBody L rho c = body L c := by
 rw [hostedBody,ParkCarryDevelop.host_eq L rho h]

theorem hosted_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedBody L rho c) = 4762 ∧ measurementCount (hostedBody L rho c) = 5924 :=
 body_counts (hostLayout L rho) (host_widths L hw rho) c

theorem hosted_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
 Challenge.gateSlots (hostedBody L rho c) = Challenge.gateSlots (body L c) := by
 have old := ParkCarry8Develop.hosted_slots L hw rho c
 have v := ParkCarry8Develop.bodyV_slots (hostLayout L rho) c (rho.symm (SecondCarryLoan.bit1 L.core.high))
 change Challenge.gateSlots (ParkCarry8Develop.bodyV (hostLayout L rho) c (rho.symm (SecondCarryLoan.bit1 L.core.high))) =
  Challenge.gateSlots (ParkCarry8Develop.body L c) at old
 have a := body_slots (hostLayout L rho) (host_widths L hw rho) c
 have b := body_slots L hw c
 change Challenge.gateSlots (body (hostLayout L rho) c) = Challenge.gateSlots (body L c)
 omega
#print axioms hosted_eq
#print axioms hosted_counts
#print axioms hosted_slots
end ECDSAAdd.Entrant.ParkCarry10Develop

end -- isolated Carry10 component

section
-- Carry10BodyRefined
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry10BodyRefined
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop LowBitCarryDevelop Carry9BodySubset
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem body_refined (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 wires (ParkCarry10Develop.body L c)⊆insert (L.core.high.headD 0) (wires (ParkCarry8Develop.body L c)) := by
 let v := L.core.high.headD 0
 have same {P : Program} (hp : wires P⊆wires (ParkCarry8Develop.body L c)) :
  wires P⊆insert v (wires (ParkCarry8Develop.body L c)) := fun _ h=>Finset.mem_insert_of_mem (hp h)
 have roles:=old_prepare L c
 have extras:=new_roles L hw c
 have carrier : [c,bit1 L.core.high,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset
  ⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  intro q h
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
  all_goals subst q
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.2.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
 have ends:=ends4L_support c (bit1 L.core.high) v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L)
 have endEmbed {P : Program} (hp : wires P⊆[c,bit1 L.core.high,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset) :
  wires P⊆insert v (wires (ParkCarry8Develop.body L c)) := hp.trans carrier
 have arms :
  wires (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆insert v (wires (ParkCarry8Develop.body L c)) ∧
  wires (wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  have f:=(fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
  have i:=(invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
  constructor
  · intro q h
    rcases Finset.mem_insert.mp (f h) with e|h
    · subst q;exact Finset.mem_insert_of_mem (roles (by simp))
    · exact same (Carry9OldParts.old_fwd L c) h
  · intro q h
    rcases Finset.mem_insert.mp (i h) with e|h
    · subst q;exact Finset.mem_insert_of_mem (roles (by simp))
    · exact same (Carry9OldParts.old_inv L c) h
 have mid : wires (wMidFullCCC0 L c)⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  rw [wMidFullCCC0,wires_append]
  refine Finset.union_subset_iff.mpr ⟨endEmbed ends.1,?_⟩
  rw [wires_append]
  refine Finset.union_subset_iff.mpr ⟨?_,endEmbed ends.2⟩
  rw [wires_append]
  refine Finset.union_subset_iff.mpr ⟨arms.1,?_⟩
  rw [wires_append]
  exact Finset.union_subset_iff.mpr ⟨same (Carry9OldParts.old_core L c),arms.2⟩
 have pad : wires (padM L 744)⊆wires (padM L 746) := by
  have hp : padM L 746=padM L 744++padM L 2 := by
   change List.replicate (744+2) (Instr.measureX (eKw L) [] [])=
    List.replicate 744 (Instr.measureX (eKw L) [] [])++List.replicate 2 (Instr.measureX (eKw L) [] [])
   rw [List.replicate_add]
  rw [hp,wires_append]
  exact Finset.subset_union_left
 intro q h
 simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,ParkCarry10Develop.rebuild,
  wires_append,Finset.mem_union,or_assoc] at h
 rcases h with h|h|h|h|h|h|h|h|h|h|h|h
 · exact same (P:=measuredFoldQTq L (negP L)) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=measuredFoldQTq L (rot128F L)) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddLo L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact mid h
 · exact same (P:=unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.program (eU L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eSubK L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eFoldTq L c) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddB L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.restore L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=padM L 746) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) (pad h)

#print axioms body_refined
end ECDSAAdd.Entrant.Carry10BodyRefined

end -- isolated Carry10 component

end

section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
namespace ParkAChain
open ECDSAAdd ZeroReadDevelop

/-- Opaque exact one-host output equalities, with each output passed to the next host. -/
inductive Steps : List Wire → Program → Program → Prop
 | nil (p : Program) : Steps [] p p
 | cons (q : Wire) (qs : List Wire) (p r t : Program)
     (head : (compileChunked? q p).map (fun c => c.out)=some r)
     (tail : Steps qs r t) : Steps (q::qs) p t

set_option linter.unnecessarySimpa false in
theorem outputs (qs : List Wire) (p t : Program) (h : Steps qs p t) :
 (compileManyChunked? qs p).map (fun c => c.out)=some t := by
 induction h with
 | nil p => rfl
 | cons q qs p r t head tail ih =>
   rw [compileManyChunked?]
   cases hc : compileChunked? q p with
   | none => simp [hc] at head
   | some first =>
     have e : first.out=r := by simpa [hc] using head
     subst r
     cases hr : compileManyChunked? qs first.out <;>
       simpa [hc,hr,Option.map,Option.bind] using ih

                                                                    
                                             
                             
                                         
                           
                

#print axioms outputs
                    
end ParkAChain

namespace ParkAChain
open ECDSAAdd ZeroReadDevelop
                                                          
                                                                             
                                                   
                 
                     
                                  
                      
                                            
                                    
                              
                  
                                                    
            
                                                         
                                
                                         

end ParkAChain

end

section

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant

/-! Proof-local constructors. The selected runtime definitions remain unchanged. -/
namespace ParkAInputFast

/-- Append the caller's suffix while constructing each recursive output only once. -/
def mappedAddTail : List MappedBit → List Wire → List Wire → Wire → Program → Program
  | b::b'::bits, y::y'::ys, c::cs, cin, tail =>
      mappedMajority b y cin c ++
        mappedAddTail (b'::bits) (y'::ys) cs c
          (mappedEraseCarry b y cin c ++ (mappedSum b y cin ++ tail))
  | [b], [y], _, cin, tail => mappedSum b y cin ++ tail
  | _, _, _, _, tail => tail

/-- Exact syntax equality, including every malformed-length fallback. -/
theorem mappedAddTail_eq (bits : List MappedBit) (ys carry : List Wire)
    (cin : Wire) (tail : Program) :
    mappedAddTail bits ys carry cin tail = mappedAdd bits ys carry cin ++ tail := by
  induction bits generalizing ys carry cin tail with
  | nil => cases ys <;> cases carry <;> rfl
  | cons b bits ih =>
      cases bits with
      | nil =>
          cases ys with
          | nil => rfl
          | cons y ys => cases ys <;> rfl
      | cons b' bits =>
          cases ys with
          | nil => rfl
          | cons y ys =>
              cases ys with
              | nil => rfl
              | cons y' ys =>
                  cases carry with
                  | nil => rfl
                  | cons c cs =>
                      change mappedMajority b y cin c ++
                        mappedAddTail (b'::bits) (y'::ys) cs c
                          (mappedEraseCarry b y cin c ++ (mappedSum b y cin ++ tail)) =
                        (((mappedMajority b y cin c ++ mappedAdd (b'::bits) (y'::ys) cs c) ++
                          mappedEraseCarry b y cin c) ++ mappedSum b y cin) ++ tail
                      rw [ih]
                      simp only [List.append_assoc]

def eraseLtTail : List Wire → List Wire → List Wire → Wire → Wire → Program → Program
  | a::a'::as, b::b'::bs, c::cs, cin, target, tail =>
      borrowMajority a b cin c ++
        eraseLtTail (a'::as) (b'::bs) cs c target (eraseBorrow a b cin c ++ tail)
  | [a], [b], _, cin, target, tail => eraseBorrow a b cin target ++ tail
  | _, _, _, _, _, tail => tail

theorem eraseLtTail_eq (xs ys carry : List Wire) (cin target : Wire) (tail : Program) :
    eraseLtTail xs ys carry cin target tail = eraseLtChain xs ys carry cin target ++ tail := by
  induction xs generalizing ys carry cin target tail with
  | nil => cases ys <;> cases carry <;> rfl
  | cons a xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => rfl
          | cons b ys => cases ys <;> rfl
      | cons a' xs =>
          cases ys with
          | nil => rfl
          | cons b ys =>
              cases ys with
              | nil => rfl
              | cons b' ys =>
                  cases carry with
                  | nil => rfl
                  | cons c cs =>
                      change borrowMajority a b cin c ++
                        eraseLtTail (a'::xs) (b'::ys) cs c target (eraseBorrow a b cin c ++ tail) =
                        ((borrowMajority a b cin c ++
                          eraseLtChain (a'::xs) (b'::ys) cs c target) ++ eraseBorrow a b cin c) ++ tail
                      rw [ih]
                      simp only [List.append_assoc]

/-- The original qprogTq syntax with only its three recursive constructors replaced. -/
def qprogFast (K : MeasuredCanonicalModLayout) (p : Nat) : Program :=
  notRegister K.out ++
    mappedAddTail (mappedRead K.src false ++ [({wire := none, flip := false} : MappedBit)])
      K.extended K.carry K.cin [] ++
    [.CX K.high K.flag, .X K.flag] ++
    mappedAddTail (mappedConstant (some K.flag) K.out.length p) K.out
      (K.carry.take (K.out.length - 1)) K.cin [] ++
    [.CX K.flag K.high] ++ [.X K.high, .X K.flag] ++
    eraseLtTail K.out K.src (K.carry.take (K.out.length - 1)) K.cin K.flag []

theorem qprogFast_eq (K : MeasuredCanonicalModLayout) (p : Nat) :
    qprogFast K p = qprogTq K p := by
  simp only [qprogFast, mappedAddTail_eq, eraseLtTail_eq, List.append_nil,
    qprogTq, MeasuredCanonicalModLayout.sum, mappedConstAdd]

def aMiddleFast (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK ++
    (qprogFast L.measuredCore SquareReduction.p ++
      maskedConstant g (accReg L) OwnDiagAll12Square.cFlipK)

theorem aMiddleFast_eq (L : CuccaroStreamedSquareWideLayout) (g : Wire) :
    aMiddleFast L g = InverseCarryDevelop.aMiddle L g := by
  rw [aMiddleFast, qprogFast_eq, InverseCarryDevelop.aMiddle]

theorem fast_input_bool : ParkAProgramBool.programEq ParkAData.p0
    (ParkAInputFast.aMiddleFast Baselines.layout.dialogStreamedSquareWide
      Baselines.layout.core.generic) = true := by
  decide +kernel

theorem original_input_eq : ParkAData.p0 =
    InverseCarryDevelop.aMiddle Baselines.layout.dialogStreamedSquareWide
      Baselines.layout.core.generic :=
  (ParkAProgramBool.programEq_sound _ _ fast_input_bool).trans
    (ParkAInputFast.aMiddleFast_eq _ _)

end ParkAInputFast

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ParkAStagedProof

theorem input_bool : ParkAProgramBool.programEq ParkAData.p0
 (aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic)=true := by
 exact (ParkAProgramBool.programEq_iff _ _).mpr ParkAInputFast.original_input_eq

theorem input_eq : ParkAData.p0 =
 aMiddle Baselines.layout.dialogStreamedSquareWide Baselines.layout.core.generic :=
 ParkAProgramBool.programEq_sound _ _ input_bool

                              
                                                                       

                                                                                                                                                                                                                            

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                              

                   
                                                                                
                                               

                                              
                                                           
                                               

                   
                                                                                 
                                               


end ParkAStagedProof

end

section
open ECDSAAdd ECDSAAdd.Entrant ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
namespace ECDSAAdd.Entrant.RepadBSteps
                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                       

                                                                                                                                               

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  

                                                                                                                                                         

                                                                                                                                                  


end ECDSAAdd.Entrant.RepadBSteps

                                      
                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                      

                                                                                                                                              

                                                                                                                                                       

                                                                                                                                               


                                

end
