import ECDSAAdd.Submission.Entrant.ParkAMany
import ECDSAAdd.Submission.Entrant.ParkAWorkLoan
import ECDSAAdd.Submission.Entrant.ParkAThird
import ECDSAAdd.Submission.Entrant.ParkCarry10
import ECDSAAdd.Submission.Entrant.ParkCarry9
import ECDSAAdd.Submission.Entrant.ParkCarry8
import ECDSAAdd.Submission.Entrant.MainPart04Base

-- The circuit and generic proofs live in the cached base module. This remainder
-- instantiates the resource bounds and completes the point-addition interface.

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
attribute [local irreducible] ECDSAAdd.Entrant.RawClearSquare.clear
  ECDSAAdd.Entrant.KnownAllRowsRaw.rawClearSafe
  ECDSAAdd.Entrant.LowZero18KG.make ECDSAAdd.Entrant.LowZero18KG.clear
  ECDSAAdd.Entrant.TrimMid.tsqM ECDSAAdd.Entrant.TrimSquare4.tsqcM4
  ECDSAAdd.Entrant.PlainKnownClear.program

section
section
section
section

namespace ECDSAAdd.Entrant.PlainKnownClear
open Arithmetic
 theorem program_slots_rel (xs dst pad carry : List Wire) (cin : Wire) :
    Challenge.gateSlots (program xs dst pad carry cin)≤Challenge.gateSlots (TrimSquare.tsqc2 xs dst pad carry cin) := by
  unfold program
  split_ifs with h
  · exact (slots xs dst pad carry cin h.1 h.2.1 h.2.2.1 h.2.2.2).trans
      (TrimSquare3.tsq3_slots_rel xs dst pad carry cin).2
  · rw [TrimSquare4.tsqcM4_slots]
    exact (TrimSquare3.tsqM_slots_rel xs dst pad carry cin).2
end ECDSAAdd.Entrant.PlainKnownClear

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst3
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (he : 300≤ext.length)

attribute [local irreducible] toffoliCount measurementCount

include hw in
theorem oregs_lens (h : 128≤src.length) (h2 : src.length≤129) :
    (oregs L ext src dst).h=64 ∧ (oregs L ext src dst).bank.length=src.length := by
  have sz := L.measured_bank_widths hw
  refine ⟨rfl,?_⟩
  simp only [oregs,List.length_take,sz.1]; omega

include hw h128 hsmax hlen he in
theorem kgH_counts (h : src.length=128) :
    toffoliCount (LowZero18KG.make (kgH L ext src dst))=6565 ∧ measurementCount (LowZero18KG.make (kgH L ext src dst))=6681 ∧
    toffoliCount (LowZero18KG.clear (kgH L ext src dst))=6040 ∧ measurementCount (LowZero18KG.clear (kgH L ext src dst))=6684 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have e : (oregs L ext src dst).S.length=65 := by omega
  have f : (oregs L ext src dst).T.length=130 := by omega
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have t5 : toffoliCount (kgH L ext src dst).Q5=ksq 65-2 ∧ measurementCount (kgH L ext src dst).Q5=ksq 65-2 ∧
      toffoliCount (kgH L ext src dst).Q5c=ksq 65-128 ∧ measurementCount (kgH L ext src dst).Q5c=ksq 65-1 := by
    have qm := TrimMid.tsqM_counts_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have q4 := TrimSquare4.tsqcM4_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have qn := PlainKnownClear.program_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have k : signedSquareRowsCount 65+130-3=ksq 65-1 := rfl
    rw [e,f] at q
    rw [e,TrimMid.par_65] at qm
    rw [e,TrimMid.par_65] at qn
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimMid.tsqM (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show toffoliCount (PlainKnownClear.program (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (PlainKnownClear.program (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsH L ext src dst).h=32 := rfl
  have pi : DiagSq.parR (iregs L ext src dst)=1 := by rw [DiagSq.parR_eq _ wi,il,ih]; decide
  have pj : DiagSq.parR (jregsH L ext src dst)=1 := by rw [DiagSq.parR_eq _ wj,jl,jh]; decide
  rw [pi] at i1; rw [pj] at j1
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30)-4-1+32 ∧
      toffoliCount (kgH L ext src dst).Q1c=(raw_kcost 64 32-30)-14-182 ∧ measurementCount (kgH L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smkT++(LowZero18Diagonal.clear (iregs L ext src dst)))=_
      have hk := ((iregs L ext src dst).smkT_counts wi).1
      rw [ip.1] at hk
      rw [toffoliCount_append,i2.1]
      norm_num [raw_kcost,raw_ksq,signedSquareRowsCount] at hk ⊢
      omega
    · show measurementCount ((iregs L ext src dst).smkT++(RawClearSquare.clear (iregs L ext src dst)))=_
      rw [measurementCount_append,((iregs L ext src dst).smkT_counts wi).2,ip.2.1]; have := i2.2; omega
  have t2 : toffoliCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30)-4-1 ∧
      toffoliCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-32-13-182 ∧ measurementCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30)-4 :=
    ⟨j1.1,j1.2,j2.1,by show measurementCount (RawClearSquare.clear (jregsH L ext src dst))=_; have := j2.2; omega⟩
  have rb : (kgH L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgH L ext src dst).R.h=64 := rfl
  have tk : ¬(kgH L ext src dst).R.trimOK := by
    show ¬(2*(kgH L ext src dst).R.h+1≤(kgH L ext src dst).R.bank.length); rw [rb,rh,h]; norm_num
  have mk := LowZero18KG.make_counts (kgH L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgH L ext src dst) w
  rw [if_neg tk,Nat.add_zero] at mk cl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

include hw h128 hsmax hlen he in
theorem kgS_counts (h : src.length=129) :
    toffoliCount (LowZero18KG.make (kgS L ext src dst))=6679 ∧ measurementCount (LowZero18KG.make (kgS L ext src dst))=6797 ∧
    toffoliCount (LowZero18KG.clear (kgS L ext src dst))=6149 ∧ measurementCount (LowZero18KG.clear (kgS L ext src dst))=6801 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have e : (oregs L ext src dst).hi.length=65 := by omega
  have f : (oregs L ext src dst).dhi.length=130 := by omega
  have q := TrimSquare3.tsq3_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have t2 : toffoliCount (kgS L ext src dst).Q2=ksq 65-2 ∧ measurementCount (kgS L ext src dst).Q2=ksq 65-2 ∧
      toffoliCount (kgS L ext src dst).Q2c=ksq 65-128 ∧ measurementCount (kgS L ext src dst).Q2c=ksq 65-1 := by
    have qm := TrimMid.tsqM_counts_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have q4 := TrimSquare4.tsqcM4_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have qn := PlainKnownClear.program_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
    have k : signedSquareRowsCount 65+130-3=ksq 65-1 := rfl
    rw [e,f] at q
    rw [e,TrimMid.par_65] at qm
    rw [e,TrimMid.par_65] at qn
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (TrimMid.tsqM (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show toffoliCount (PlainKnownClear.program (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
    · show measurementCount (PlainKnownClear.program (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin)=_; omega
  have i1 := LowZero18Diagonal.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := LowZero18Diagonal.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have ip0 := (iregs L ext src dst).scl1591_counts wi
  have j1 := LowZero18Diagonal.make_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have j2 := LowZero18Diagonal.clear_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsS L ext src dst).h=33 := rfl
  have pi : DiagSq.parR (iregs L ext src dst)=1 := by rw [DiagSq.parR_eq _ wi,il,ih]; decide
  have pj : DiagSq.parR (jregsS L ext src dst)=2 := by rw [DiagSq.parR_eq _ wj,jl,jh]; decide
  rw [pi] at i1; rw [pj] at j1
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip ip0
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-11-1 ∧ measurementCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30)-4-1+32 ∧
      toffoliCount (kgS L ext src dst).Q1c=(raw_kcost 64 32-30)-14-182 ∧ measurementCount (kgS L ext src dst).Q1c=32+((raw_kcost 64 32-30)-4) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [toffoliCount_append,ip0.1]; have := i1.1; omega
    · show measurementCount ((LowZero18Diagonal.make (iregs L ext src dst))++(iregs L ext src dst).scl1591)=_; rw [measurementCount_append,ip0.2]; have := i1.2; omega
    · show toffoliCount ((iregs L ext src dst).smkT++(LowZero18Diagonal.clear (iregs L ext src dst)))=_
      have hk := ((iregs L ext src dst).smkT_counts wi).1
      rw [ip.1] at hk
      rw [toffoliCount_append,i2.1]
      norm_num [raw_kcost,raw_ksq,signedSquareRowsCount] at hk ⊢
      omega
    · show measurementCount ((iregs L ext src dst).smkT++(RawClearSquare.clear (iregs L ext src dst)))=_
      rw [measurementCount_append,((iregs L ext src dst).smkT_counts wi).2,ip.2.1]; have := i2.2; omega
  have t5 : toffoliCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-11-2 ∧ measurementCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31)-4-2 ∧
      toffoliCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-33-13-188 ∧ measurementCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31)-4 :=
    ⟨j1.1,j1.2,j2.1,by show measurementCount (RawClearSquare.clear (jregsS L ext src dst))=_; have := j2.2; omega⟩
  have rb : (kgS L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgS L ext src dst).R.h=64 := rfl
  have tk : (kgS L ext src dst).R.trimOK := by
    show 2*(kgS L ext src dst).R.h+1≤(kgS L ext src dst).R.bank.length; rw [rb,rh,h]
  have mk := LowZero18KG.make_counts (kgS L ext src dst) w
  have cl := LowZero18KG.clear_counts (kgS L ext src dst) w
  rw [if_pos tk] at mk cl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  refine ⟨?_,?_,?_,?_⟩ <;> omega

end Inst3
end ECDSAAdd.Entrant.LowZero18LowK

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout KRegs

section Inst4
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

theorem kg_R : (kg L ext src dst).R=oregs L ext src dst := by
  unfold kg; split <;> rfl

theorem kg_I1 : (kg L ext src dst).I1=(iregs L ext src dst).invC := by
  unfold kg; split <;> rfl

theorem kg_X (q : Wire) (h : q∈(kg L ext src dst).X) : q∈ext ∨ q∈((ktmp L).drop 66).take 33 := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · rcases List.mem_append.mp h with h|h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take (h : q∈((ext.drop 198).take 34).take 33))))
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 66)))
    · exact absurd h (List.not_mem_nil)
  · rw [kg,if_neg c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · exact absurd h (List.not_mem_nil)
    · rcases List.mem_append.mp h with h|h
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 198).take 34)))
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 68)))

include hn hs hd hx hdx in
theorem kg_nodup : (kg L ext src dst).all.Nodup := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]; exact kgH_nodup L control hn ext src dst hs hd hx hdx
  · rw [kg,if_neg c]; exact kgS_nodup L control hn ext src dst hs hd hx hdx

include hw h128 hsmax hlen he in
theorem kg_spec (hall : (kg L ext src dst).all.Nodup) : (kg L ext src dst).Spec := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at hall ⊢; exact kgH_spec L hw ext src dst h128 hsmax hlen he c hall
  · rw [kg,if_neg c] at hall ⊢; exact kgS_spec L hw ext src dst h128 hsmax hlen he (by omega) hall

def lowkcost2 (n : Nat) : Nat := if n=128 then 6681 else 6797
def lowkcostTMake (n : Nat) : Nat := if n=128 then 6565 else 6679
def lowkcostTClear (n : Nat) : Nat := if n=128 then 6040 else 6149
def lowkcostMClear (n : Nat) : Nat := if n=128 then 6684 else 6801
def lowkcostTPair (n : Nat) : Nat := lowkcostTMake n+lowkcostTClear n

include hw h128 hsmax hlen he in
theorem kg_counts :
    toffoliCount (LowZero18KG.make (kg L ext src dst))=lowkcostTMake src.length ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))=lowkcost2 src.length ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))=lowkcostTClear src.length ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))=lowkcostMClear src.length := by
  by_cases c : src.length=128
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,lowkcostMClear,if_pos c]; exact kgH_counts L hw ext src dst h128 hsmax hlen he c
  · simp only [kg,lowkcost2,lowkcostTMake,lowkcostTClear,lowkcostMClear,if_neg c]; exact kgS_counts L hw ext src dst h128 hsmax hlen he (by omega)

include hw h128 hsmax hlen he in
theorem kg_support :
    ECDSAAdd.wires (LowZero18KG.make (kg L ext src dst))⊆(kg L ext src dst).all.toFinset ∧
    ECDSAAdd.wires (LowZero18KG.clear (kg L ext src dst))⊆(kg L ext src dst).all.toFinset := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (oregs L ext src dst).piece_support w
  have ip := (iregs L ext src dst).piece_support wi
  have is := LowZero18Diagonal.steps_support (iregs L ext src dst) wi
  have isc := (iregs L ext src dst).scl1591_support wi
  have tr {P : Program} {A B : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : A⊆B) : ECDSAAdd.wires P⊆B := h1.trans h2
  have ap {P Q : Program} {A : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : ECDSAAdd.wires Q⊆A) :
      ECDSAAdd.wires (P++Q)⊆A := by rw [wires_append]; exact Finset.union_subset h1 h2
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have js := LowZero18Diagonal.steps_support (jregsH L ext src dst) wj
    have iK := sub_of_count (kgH_iall L ext src dst)
    have jK := sub_of_count (kgH_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgH L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ((iregs L ext src dst).smkT_support wi ip.1) iK) (tr is.2 iK))
      (tr js.1 jK) (tr js.2 jK) (tr ((TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.2.2.1) rK) (tr ((PlainKnownClear.program_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).trans rp.2.2.2.2.2.2.2) rK)
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have js := LowZero18Diagonal.steps_support (jregsS L ext src dst) wj
    have iK := sub_of_count (kgS_iall L ext src dst)
    have jK := sub_of_count (kgS_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgS L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact LowZero18KG.steps_support _ w (ap (tr is.1 iK) (tr isc iK)) (ap (tr ((iregs L ext src dst).smkT_support wi ip.1) iK) (tr is.2 iK))
      (tr ((TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1.trans rp.2.2.2.2.1) rK) (tr ((PlainKnownClear.program_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).trans rp.2.2.2.2.2.1) rK) (tr js.1 jK) (tr js.2 jK)

include hw h128 hsmax hlen he in
theorem kg_physical (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (LowZero18KG.make (kg L ext src dst)) ∧ GatePhysical (LowZero18KG.clear (kg L ext src dst)) := by
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  by_cases h : src.length=128
  · rw [kg,if_pos h] at hall ⊢
    have wj := jregsH_W L hw ext src dst h hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgH_iall L ext src dst)
    have nj := knd hall (kgH_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsH L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ((iregs L ext src dst).smkT_physical wi ni ip.1) is.2) js.1 js.2 (TrimMid.tsqM_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).1 (PlainKnownClear.program_physical (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (TrimMid.tsqM_physical_of (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2).2)
  · rw [kg,if_neg h] at hall ⊢
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgS_iall L ext src dst)
    have nj := knd hall (kgS_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := LowZero18Diagonal.steps_physical (iregs L ext src dst) wi ni
    have isc := (iregs L ext src dst).scl1591_physical wi ni
    have js := LowZero18Diagonal.steps_physical (jregsS L ext src dst) wj nj
    exact LowZero18KG.steps_physical _ (oregs_W L hw ext src dst h128 hsmax hlen he) hall (ap is.1 isc) (ap ((iregs L ext src dst).smkT_physical wi ni ip.1) is.2) (TrimMid.tsqM_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).1 (PlainKnownClear.program_physical (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)) (TrimMid.tsqM_physical_of (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin rp.2.2.2.2.1 rp.2.2.2.2.2.1).2) js.1 js.2

include hw h128 hsmax hlen he in
theorem kg_slots :
    Challenge.gateSlots (LowZero18KG.make (kg L ext src dst))+Challenge.gateSlots (LowZero18KG.clear (kg L ext src dst))≤1200000 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have ol := oregs_lens L hw ext src dst h128 hsmax
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T
  have ad := (oregs L ext src dst).adder_slots w rfl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have it := LowZero18Diagonal.tiny_slots (iregs L ext src dst) wi (by rw [il,ih]) (by rw [ih]; omega)
  simp only [LowZero18Diagonal.clear] at it
  have oldit := (iregs L ext src dst).tiny_slots wi (by rw [ih]; omega) (by rw [il,ih]; omega) (by omega)
  have isb := (iregs L ext src dst).make_sub_slots wi
  have isc := (iregs L ext src dst).scl1591_slots
  have g2 := TrimMid.tsqM_gateSlots_le (oregs L ext src dst).hi (oregs L ext src dst).dhi
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g2' := PlainKnownClear.program_slots (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5 := TrimMid.tsqM_gateSlots_le (oregs L ext src dst).S (oregs L ext src dst).T
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5' := PlainKnownClear.program_slots (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have x2 : (oregs L ext src dst).hi.length*(12*((oregs L ext src dst).hi.length+1)+6*(oregs L ext src dst).dhi.length) ≤ 65*(12*66+6*130) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : (oregs L ext src dst).S.length*(12*((oregs L ext src dst).S.length+1)+6*(oregs L ext src dst).T.length) ≤ 66*(12*67+6*132) :=
    Nat.mul_le_mul (by omega) (by omega)
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
    have jh : (jregsH L ext src dst).h=32 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsH L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgH L ext src dst) w
    have sk := (iregs L ext src dst).smkT_slots
    simp only [kgH,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,RawClearSquare.clearC,KRegs.m5,KRegs.c5,Challenge.gateSlots_append] at st ad ⊢
    omega
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
    have jh : (jregsS L ext src dst).h=33 := rfl
    have jt := LowZero18Diagonal.tiny_slots (jregsS L ext src dst) wj (by rw [jl,jh]) (by omega)
    simp only [LowZero18Diagonal.clear] at jt
    have st := LowZero18KG.steps_slots2 (kgS L ext src dst) w
    have sk := (iregs L ext src dst).smkT_slots
    simp only [kgS,LowZero18Diagonal.makeC,LowZero18Diagonal.clearC,LowZero18Diagonal.clear,RawClearSquare.clearC,KRegs.m2,KRegs.c2,Challenge.gateSlots_append] at st ad ⊢
    omega

end Inst4
end ECDSAAdd.Entrant.LowZero18LowK


namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem kg_metadata (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (kg L ext src dst).R=(FrontierSumCleanup1591LowK.kg L ext src dst).R ∧
    (kg L ext src dst).X1=(FrontierSumCleanup1591LowK.kg L ext src dst).X1 ∧
    (kg L ext src dst).X=(FrontierSumCleanup1591LowK.kg L ext src dst).X ∧
    (kg L ext src dst).all=(FrontierSumCleanup1591LowK.kg L ext src dst).all := by
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true];exact ⟨rfl,rfl,rfl,rfl⟩
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false];exact ⟨rfl,rfl,rfl,rfl⟩

theorem kg_Q1c_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (kg L ext src dst).Q1c⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1c := by
  have a := LowZero18Diagonal.clearC_support_subset (iregs L ext src dst)
    (iregs_W L hw ext src dst h128 hsmax hlen he)
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_Q1_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (kg L ext src dst).Q1⊆wires (FrontierSumCleanup1591LowK.kg L ext src dst).Q1 := by
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have a := LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi
  by_cases h : src.length=128
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,kgH,FrontierSumCleanup1591LowK.kgH] using a
  · simpa only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,kgS,FrontierSumCleanup1591LowK.kgS] using a

theorem kg_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (LowZero18KG.make (kg L ext src dst))+32+3*(if src.length=128 then 0 else 1)=
      toffoliCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.make (kg L ext src dst))+12+2*(if src.length=128 then 0 else 1)=
      measurementCount (FrontierSumCleanup1591KG.make (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    toffoliCount (LowZero18KG.clear (kg L ext src dst))+525+7*(if src.length=128 then 0 else 1)=
      toffoliCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) ∧
    measurementCount (LowZero18KG.clear (kg L ext src dst))+9+1*(if src.length=128 then 0 else 1)=
      measurementCount (FrontierSumCleanup1591KG.clear (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have a := kg_counts L hw ext src dst h128 h129 hd he
  have b := FrontierSumCleanup1591LowK.kg_counts L hw ext src dst h128 h129 hd he
  by_cases h : src.length=128
  all_goals simp only [lowkcostTMake,lowkcostTClear,lowkcostMClear,lowkcost2,FrontierSumCleanup1591LowK.lowkcostTMake,
    FrontierSumCleanup1591LowK.lowkcostTClear,FrontierSumCleanup1591LowK.lowkcost2,h,ite_true,ite_false] at a b ⊢
  all_goals exact ⟨by omega,by omega,by omega,by omega⟩

end ECDSAAdd.Entrant.LowZero18LowK

end


namespace ECDSAAdd.Entrant.CodexBorrowedUnion

/-- The borrowed controls of E already occur in the retained C segment. -/
theorem eight {α : Type} [DecidableEq α]
    {a b c d e f g h A B D E F G : Finset α}
    (ha : a ⊆ A) (hb : b ⊆ B) (hd : d ⊆ D)
    (he : e ⊆ E ∪ c) (hf : f ⊆ F) (hg : g ⊆ G) :
    a ∪ b ∪ c ∪ d ∪ e ∪ f ∪ g ∪ h ⊆
      A ∪ B ∪ c ∪ D ∪ E ∪ F ∪ G ∪ h := by
  intro q hq
  simp only [Finset.mem_union] at hq ⊢
  rcases hq with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (ha h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hb h)))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hd h)))))
  · rcases Finset.mem_union.mp (he h) with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inr (hf h)))
  · exact Or.inl (Or.inr (hg h))
  · exact Or.inr h

theorem seven {α : Type} [DecidableEq α]
    {b c d e f g h B D E F G : Finset α}
    (hb : b ⊆ B) (hd : d ⊆ D)
    (he : e ⊆ E ∪ c) (hf : f ⊆ F) (hg : g ⊆ G) :
    b ∪ c ∪ d ∪ e ∪ f ∪ g ∪ h ⊆
      B ∪ c ∪ D ∪ E ∪ F ∪ G ∪ h := by
  simpa only [Finset.union_self] using
    eight (a := b) (A := B) (h := h) hb hb hd he hf hg

end ECDSAAdd.Entrant.CodexBorrowedUnion

namespace ECDSAAdd.Entrant.LowZero18LowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

theorem loan_make_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.makeC_support_subset (iregs L ext src dst) wi)
  have ro : FrontierSumCleanup1591LowK.oregs L ext src dst = oregs L ext src dst := rfl
  have ri : FrontierSumCleanup1591LowK.iregs L ext src dst = iregs L ext src dst := rfl
  have a6 := (oregs L ext src dst).m6h_wires_smk w
  have a7 := (oregs L ext src dst).m7k_wires w
  have a8 := (oregs L ext src dst).m8z_wires w
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_support_subset (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    have rj : FrontierSumCleanup1591LowK.jregsH L ext src dst = jregsH L ext src dst := rfl
    have q5 := (TrimMid.tsqM_wires_le (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append,ro,ri,rj]
    exact CodexBorrowedUnion.eight ip jp q5 a6 a7 a8
  · have jp := LowZero18Diagonal.make_support_subset (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    have rj : FrontierSumCleanup1591LowK.jregsS L ext src dst = jregsS L ext src dst := rfl
    have q2 := (TrimMid.tsqM_wires_le (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin).1
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append,ro,ri,rj]
    exact CodexBorrowedUnion.eight ip q2 jp a6 a7 a8

theorem loan_clear_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    wires (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))⊆
      wires (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have ipc := OneFlagReplay.rename_subset (SquareCarryLoan719.earlyPerm L) _ _
    (LowZero18Diagonal.clearC_support_subset (iregs L ext src dst)
      (iregs_W L hw ext src dst h128 h129 hd he))
  have jhc := fun h => LowZero18Diagonal.clear_support_subset (jregsH L ext src dst) (jregsH_W L hw ext src dst h hd he)
  have jsc := fun h => LowZero18Diagonal.clear_support_subset (jregsS L ext src dst) (jregsS_W L hw ext src dst h hd he)
  by_cases h : src.length=128
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.c5,wires_append]
    repeat' first | exact LowZero18KG.smkT_c8z (oregs L ext src dst) w | apply Finset.union_subset_union
    all_goals first | exact ipc | exact jhc h | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact PlainKnownClear.program_wires_le _ _ _ _ _ | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7t_wires | exact (oregs L ext src dst).c6h_wires w | exact Finset.Subset.refl _
  · simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.clear,
      SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.c2,wires_append]
    repeat' first | exact LowZero18KG.smkT_c8z (oregs L ext src dst) w | apply Finset.union_subset_union
    all_goals first | exact ipc | exact jsc (by omega) | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact PlainKnownClear.program_wires_le _ _ _ _ _ | exact (oregs L ext src dst).c8z_wires w |
      exact (oregs L ext src dst).c7t_wires | exact (oregs L ext src dst).c6h_wires w | exact Finset.Subset.refl _

theorem loan_make_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.make (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have wi := iregs_W L hw ext src dst h128 h129 hd he
  have ip := LowZero18Diagonal.makeC_slots_old (iregs L ext src dst) wi
  have a := (oregs L ext src dst).m7t_slots
  have a7 := (oregs L ext src dst).m7k_slots w
  have b := (oregs L ext src dst).m8z_slots w
  have c6 := ((oregs L ext src dst).m6h_slots w).trans ((oregs L ext src dst).m6k_slots w)
  have q5 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  by_cases h : src.length=128
  · have jp := LowZero18Diagonal.make_slots_le (jregsH L ext src dst)
      (jregsH_W L hw ext src dst h hd he)
    have rj : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a a7 b c6 jp q5 ⊢
    omega
  · have jp := LowZero18Diagonal.make_slots_le (jregsS L ext src dst)
      (jregsS_W L hw ext src dst (by omega) hd he)
    have rj : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
    simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_false,LowZero18KG.make,
      SquareCarryLoan719BF.make,FrontierSumCleanup1591KG.make,SquareCarryLoan719.patchKG,
      kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    simp only [ro,ri,rj] at ip a a7 b c6 jp q2 ⊢
    omega

theorem loan_clear_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (h128 : 128≤src.length) (h129 : src.length≤129)
    (hd : dst.length=2*src.length) (he : 300≤ext.length) :
    Challenge.gateSlots (LowZero18KG.clear (SquareCarryLoan719.patchKG L (kg L ext src dst)))≤
      Challenge.gateSlots (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  have w := oregs_W L hw ext src dst h128 h129 hd he
  have a := (oregs L ext src dst).c8z_slots w
  have b := (oregs L ext src dst).c7t_slots
  have c6 := (oregs L ext src dst).c6h_slots w
  have q5 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2 := TrimSquare3.tsqM_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q5' := PlainKnownClear.program_slots_rel (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have q2' := PlainKnownClear.program_slots_rel (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have i1 := LowZero18Diagonal.clearC_slots_old (iregs L ext src dst)
  have sko := (oregs L ext src dst).smkT_slots
  have jh := LowZero18Diagonal.clear_slots_old (jregsH L ext src dst)
  have js := LowZero18Diagonal.clear_slots_old (jregsS L ext src dst)
  have ro : oregs L ext src dst=FrontierSumCleanup1591LowK.oregs L ext src dst := rfl
  have ri : iregs L ext src dst=FrontierSumCleanup1591LowK.iregs L ext src dst := rfl
  have rh : jregsH L ext src dst=FrontierSumCleanup1591LowK.jregsH L ext src dst := rfl
  have rs : jregsS L ext src dst=FrontierSumCleanup1591LowK.jregsS L ext src dst := rfl
  by_cases h : src.length=128
  all_goals simp only [kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,LowZero18KG.clear,
    SquareCarryLoan719BF.clear,FrontierSumCleanup1591KG.clear,SquareCarryLoan719.patchKG,
    kgH,kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
    LowZero18Diagonal.clearC,LowZero18Diagonal.clear,KRegs.c5,KRegs.c2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
  all_goals simp only [LowZero18Diagonal.clearC,LowZero18Diagonal.clear,ro,ri,rh,rs] at a b c6 q5 q2 q5' q2' i1 jh js sko ⊢
  all_goals omega

end ECDSAAdd.Entrant.LowZero18LowK
end -- original module boundary


-- Synthetic: close inherited anonymous MainC section at this file boundary.
end


set_option Elab.async false
-- Synthetic: reopen the inherited anonymous MainC section; no local context commands.
section

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProgram =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18LowK

/-! The checked675/BF719 square with only the18 carry-free low-bit changes. -/
section CachedSquareCopyHelpers
namespace ECDSAAdd.Entrant.CachedSquareCopy
open Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def copy (control cache : Wire) : List Wire → List Wire → Program
 | _::src, b::dst => [.CX cache b] ++ copyRegister (some control) src dst
 | src, dst => copyRegister (some control) src dst

theorem run_eq (control cache : Wire) (src dst : List Wire) (s : State) (m : List Bool)
    (h : s.basis cache = (s.basis control && s.basis (src.headD 0))) :
    run (copy control cache src dst) m s = run (copyRegister (some control) src dst) m s := by
 cases src with
 | nil => rfl
 | cons a src =>
  cases dst with
  | nil => rfl
  | cons b dst =>
   have first (r : List Bool) : run [.CX cache b] r s = run [.CCX control a b] r s := by
    change (⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis cache)⟩ : State) =
      ⟨s.phase,writeBit s.basis b (s.basis b ^^ (s.basis control && s.basis a))⟩
    simpa only [List.headD_cons] using congrArg
      (fun v => (⟨s.phase,writeBit s.basis b (s.basis b ^^ v)⟩ : State)) h
   simp only [copy,copyRegister,copyGate,run_append]
   rw [first]
   rfl

theorem head_bit (r : List Wire) (s : State) (hr : 0<r.length) :
    s.basis (r.headD 0) = (regValue r s.basis % 2 == 1) := by
 have h:=RawClearCarryProbe.register_bit r 0 s.basis hr
 cases r with
 | nil => simp at hr
 | cons a rs => simpa using h

theorem square_head (src dst : List Wire) (control : Wire) (s : State)
    (hs : 0<src.length) (hd : 0<dst.length)
    (hv : regValue dst s.basis=(if s.basis control then regValue src s.basis else 0)^2) :
    s.basis (dst.headD 0) = (s.basis control && s.basis (src.headD 0)) := by
 rw [head_bit dst s hd,head_bit src s hs,hv]
 have squareMod (n : Nat) : (n^2)%2=n%2 := by
  have hn : n%2=0 ∨ n%2=1 := by omega
  rcases hn with hn|hn <;> simp [pow_two,Nat.mul_mod,hn]
 cases s.basis control <;> simp [squareMod]

theorem counts (control cache a b : Wire) (src dst : List Wire) :
    toffoliCount (copy control cache (a::src) (b::dst))+1 =
      toffoliCount (copyRegister (some control) (a::src) (b::dst)) ∧
    measurementCount (copy control cache (a::src) (b::dst)) =
      measurementCount (copyRegister (some control) (a::src) (b::dst)) := by
 simp [copy,copyRegister,copyGate,toffoliCount,measurementCount,Nat.add_comm]

theorem measurements (control cache : Wire) (src dst : List Wire) :
    measurementCount (copy control cache src dst) =
      measurementCount (copyRegister (some control) src dst) := by
 cases src <;> cases dst <;> rfl

theorem counts_nonempty (control cache : Wire) (src dst : List Wire)
    (hs : 0<src.length) (hd : 0<dst.length) :
    toffoliCount (copy control cache src dst)+1 =
      toffoliCount (copyRegister (some control) src dst) := by
 cases src with
 | nil => simp at hs
 | cons a src =>
  cases dst with
  | nil => simp at hd
  | cons b dst => exact (counts control cache a b src dst).1

theorem head_mem (r : List Wire) (hr : 0<r.length) : r.headD 0∈r := by
 cases r with
 | nil => simp at hr
 | cons a rs => exact List.mem_cons_self

theorem wires_subset (control cache : Wire) (src dst : List Wire) :
    wires (copy control cache src dst) ⊆
      wires (copyRegister (some control) src dst) ∪ {cache} := by
 cases src <;> cases dst
 all_goals
  simp only [copy,copyRegister,copyGate,wires_append,wires,Instr.wires,Finset.union_empty]
  intro q h
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h ⊢
  tauto

theorem slots (control cache : Wire) (src dst : List Wire) :
    Challenge.gateSlots (copy control cache src dst) ≤
      Challenge.gateSlots (copyRegister (some control) src dst) := by
 cases src <;> cases dst
 all_goals simp [copy,copyRegister,copyGate,Challenge.gateSlots,Challenge.instructionSlots]

theorem physical (control cache : Wire) (src dst : List Wire)
    (hc : cache≠dst.headD 0) (old : GatePhysical (copyRegister (some control) src dst)) :
    GatePhysical (copy control cache src dst) := by
 cases src with
 | nil => exact old
 | cons a src =>
  cases dst with
  | nil => exact old
  | cons b dst =>
   simp only [copy,copyRegister,copyGate,gatePhysical_append] at old ⊢
   refine ⟨?_,old.2⟩
   simpa [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate] using hc

end ECDSAAdd.Entrant.CachedSquareCopy
end CachedSquareCopyHelpers

namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

abbrev target := SquareCarryLoan719.target
abbrev earlyHost := SquareCarryLoan719.earlyHost
abbrev earlyPerm := SquareCarryLoan719.earlyPerm
abbrev foldPerm := SquareCarryLoan719.foldPerm
abbrev patchKG := SquareCarryLoan719.patchKG
abbrev K : Nat := ControlLoan1589BFFold.K

def cacheWire (L : CuccaroStreamedSquareWideLayout) (dst : List Wire) : Wire :=
  earlyPerm L (dst.headD 0)

theorem cacheWire_fixed (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (dst : List Wire)
    (hd : ∀q,dst.count q≤L.core.product.count q) (hp : 0<dst.length) :
    cacheWire L dst=dst.headD 0 := by
 have mem : dst.headD 0∈dst := by
  cases dst with
  | nil => simp at hp
  | cons d ds => exact List.mem_cons_self
 have prod : dst.headD 0∈L.core.product :=
  List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr mem) (hd _))
 have targetM : target L∈LowZero18LowK.ktmp L := by
  change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
  exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
 have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
  change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
  exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
 have targetPad : target L∈L.foldPad := List.mem_of_mem_drop targetM
 have hostPad : earlyHost L∈L.foldPad := List.mem_of_mem_drop hostM
 have ta := (L.pairAuxAway hn (target L) (by simp only [List.mem_append,List.mem_cons]; tauto)).1
 have ha := (L.pairAuxAway hn (earlyHost L) (by simp only [List.mem_append,List.mem_cons]; tauto)).1
 change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
 rw [SquareCarryLoan719.earlyPerm_eq L hw]
 exact Equiv.swap_apply_of_ne_of_ne (fun e => ta (by simpa only [e] using prod))
   (fun e => ha (by simpa only [e] using prod))

theorem cached_copy_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (control : Wire) (src dst : List Wire)
    (hd : ∀q,dst.count q≤L.core.product.count q) (hp : 0<dst.length)
    (hb : 0<(L.inputBank.take src.length).length)
    (nd : (dst++L.inputBank.take src.length).Nodup)
    (old : GatePhysical (copyRegister (some control) src (L.inputBank.take src.length))) :
    GatePhysical (CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length)) := by
 apply CachedSquareCopy.physical _ _ _ _ _ old
 rw [cacheWire_fixed L hw hn dst hd hp]
 intro eq
 have dmem := CachedSquareCopy.head_mem dst hp
 have bmem := CachedSquareCopy.head_mem (L.inputBank.take src.length) hb
 have dis := (List.nodup_append'.mp nd).2.2
 exact List.disjoint_left.mp dis dmem (by rw [eq]; exact bmem)


section CachedCopyFootprint
attribute [local irreducible] wires
theorem cached_rename_append (f : Wire → Wire) (P Q : Program) :
    renameProgram f (P++Q) = renameProgram f P++renameProgram f Q := by
 simp only [renameProgram,List.map_append]

theorem cache_wire_in_old_make (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)
    (hd : 0<dst.length) :
    cacheWire L dst ∈ wires (SquareCarryLoan719BF.make L
      (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
 let I := FrontierSumCleanup1591LowK.iregs L ext src dst
 have dm : dst.headD 0∈I.dlo := by
  change dst.headD 0∈(dst.take 128).take 64
  cases dst with
  | nil => simp at hd
  | cons d ds => exact List.mem_cons_self
 have dn : dst.headD 0∈wires (notRegister I.dlo) := by
  rw [notRegister_wires]
  exact List.mem_toFinset.mpr dm
 have diag : dst.headD 0∈wires (DiagSq.make I) := by
  simp only [DiagSq.make,DiagSq.headBlock,mappedDiagSub,mappedSub,wires_append,
    Finset.mem_union]
  tauto
 have sub : wires (renameProgram (earlyPerm L) (DiagSq.make I)) ⊆
     wires (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
  by_cases h : src.length=128
  all_goals
   simp only [SquareCarryLoan719BF.make,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,
    FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
    SquareCarryLoan719.patchKG,FrontierSumCleanup1591KG.make,
    FrontierSumCleanup1591Diagonal.makeC,cached_rename_append,wires_append]
   intro q hq
   simp only [Finset.mem_union] at *
   tauto
 apply sub
 rw [renameProgram_support]
 exact Finset.mem_image.mpr ⟨dst.headD 0,diag,rfl⟩


theorem cached_context_support (A M M0 E B A' C C0 : Program)
    (hm : wires M⊆wires M0) (hc : wires C⊆wires C0)
    (hp : wires A'⊆wires A∪wires M0) :
    wires (A++M++E++B++A'++C++E)⊆wires (A++M0++E++B++A++C0++E) := by
  simp only [wires_append]
  intro q hq
  have mm:=@hm q
  have cc:=@hc q
  have pp:=@hp q
  simp only [Finset.mem_union] at hq mm cc pp ⊢
  tauto


end CachedCopyFootprint


def make (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.make (patchKG L R)

def clear (L : CuccaroStreamedSquareWideLayout) (R : KG) : Program :=
  LowZero18KG.clear (patchKG L R)

def clearPrefix (R : KG) : Program :=
  R.R.smkT++R.R.c8z++R.R.c7t++R.R.c6h++R.Q5c++R.R.scl1591++R.Q2c

def withLowK2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program) : Program :=
  let R := LowZero18LowK.kg L ext src dst
  copyRegister (some control) src (L.inputBank.take src.length)++make L R++
    eraseMask control src (L.inputBank.take src.length)++
    renameProgram (foldPerm L ext) body++
    CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length)++clear L R++
    eraseMask control src (L.inputBank.take src.length)

def branchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagAll12Square.gPrep L++
    withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)++
    OwnDiagAll12Square.gClear L

set_option maxHeartbeats 4000000 in
theorem withLowK2_bodyCK (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) :
    toffoliCount (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))+31=
      toffoliCount (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    measurementCount (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))=
      measurementCount (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    wires (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))⊆
      wires (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) ∧
    Challenge.gateSlots (withLowK2 L ext control src dst (CodexCKAccTail.bodyCTail L control))≤
      Challenge.gateSlots (withLowK2 L ext control src dst (OwnDiagAll12Square.bodyC L control)) := by
  have r := CodexCKAccTail.bodyCTail_rel L hw control
  refine ⟨?_,?_,?_,?_⟩
  · simp only [withLowK2,toffoliCount_append,(renameProgram_counts _ _).1]; omega
  · simp only [withLowK2,measurementCount_append,(renameProgram_counts _ _).2]; omega
  · simp only [withLowK2,wires_append,renameProgram_support]
    repeat' apply Finset.union_subset_union
    all_goals first | exact Finset.image_subset_image r.2.2.1 | exact Finset.Subset.refl _
  · simp only [withLowK2,Challenge.gateSlots_append,Baselines.rename_gateSlots]; omega

def branchBF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.high (L.core.product.take 256) (ParkCarry7Develop.hostedBody L (foldPerm L ext) control)

def branchAF (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  withLowK2 L ext control L.core.low (L.core.product.take 256) (InverseCarryDevelop.hostedADual L (foldPerm L ext) control)

def reflection (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) : Program :=
  renameProgram (foldPerm L ext) L.reflectOutput

def raw (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control++reflection L ext

def fastCandidate (L : ControlledPointLayout) : Program :=
  raw L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def place (L : ControlledPointLayout) (P : Program) : Program :=
  let p0 := renameProgram (Square5Placement.blockPerm L 202) P
  let p1 := renameProgram (OwnPlusSquare.swap L) p0
  let p2 := renameProgram (OwnGuardSquare.swap L) p1
  let p3 := renameProgram (OwnQ4Square.swap L) p2
  let p4 := renameProgram (OwnQ5Square.swap L) p3
  let p5 := renameProgram (OwnDiagAll12PlacedQ6.swap L) p4
  let p6 := renameProgram (OwnDiagAll12PlacedQ7.swap L) p5
  let p7 := renameProgram (PrefixFrontierSquare1591.swap L) p6
  let p8 := renameProgram (Prefix1590Square.swap L) p7
  renameProgram (ControlLoan1589Square.swap L) p8

def program (L : ControlledPointLayout) : Program := place L (fastCandidate L)

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary


section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem sumCarry_off_foldPad (L : CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
    L.core.sumCarry∉L.foldPad := by
  intro h
  apply sumCarry_away L hn
  simpa only [foldPad,List.mem_append,restWires,List.mem_cons,List.not_mem_nil,or_false,or_assoc] using
    (show L.core.sumCarry∈restWires L from by
      simp only [foldPad,List.mem_append] at h
      simp only [restWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      tauto)

theorem fold_fixes_sumCarry (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (ext : List Wire) (hlen:300≤ext.length)
    (away:∀q∈ext,q∉L.wires) :
    SquareCarryLoan719.foldPerm L ext L.core.sumCarry=L.core.sumCarry := by
  have ht:SquareCarryLoan719.target L∈L.foldPad := by
    apply List.mem_of_mem_drop
    exact DiagSq.getD_in (LowZero18LowK.ktmp L) 67 (by rw [LowZero18LowK.ktmp_length L hw];omega)
  have hn1:L.core.sumCarry≠SquareCarryLoan719.target L := by
    intro h;exact sumCarry_off_foldPad L hn (h ▸ ht)
  have hn2:L.core.sumCarry≠ext.getD 0 0 := by
    intro h
    have hx:=away (ext.getD 0 0) (DiagSq.getD_in ext 0 (by omega))
    apply hx
    rw [←h]
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
  rw [SquareCarryLoan719.foldPerm_eq L hw]
  exact Equiv.swap_apply_of_ne_of_ne hn1 hn2

end ECDSAAdd.Entrant.ParkCarryDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic LowZero18Square

theorem withLowK2_body_extra (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body body0 : Program) (dT dM : Nat) (extra : Wire)
    (hT:toffoliCount body+dT=toffoliCount body0)
    (hM:measurementCount body+dM=measurementCount body0) (h:ExtraLe extra body body0) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst body)+dT=toffoliCount (LowZero18Square.withLowK2 L ext control src dst body0) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst body)+dM=measurementCount (LowZero18Square.withLowK2 L ext control src dst body0) ∧
    wires (LowZero18Square.withLowK2 L ext control src dst body)⊆insert ((foldPerm L ext) extra) (wires (LowZero18Square.withLowK2 L ext control src dst body0)) ∧
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body)≤Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body0) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [LowZero18Square.withLowK2,toffoliCount_append,(renameProgram_counts _ _).1]
    omega
  · simp only [LowZero18Square.withLowK2,measurementCount_append,(renameProgram_counts _ _).2]
    omega
  · intro q hq
    by_cases he:q=(foldPerm L ext) extra
    · exact Finset.mem_insert.mpr (Or.inl he)
    apply Finset.mem_insert_of_mem
    simp only [LowZero18Square.withLowK2,wires_append,renameProgram_support,Finset.mem_union,or_assoc] at hq ⊢
    rcases hq with hq|hq|hq|hq|hq|hq|hq
    · exact Or.inl hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr (Or.inl hq))
    · obtain ⟨a,ha,eq⟩:=Finset.mem_image.mp hq
      rcases Finset.mem_insert.mp (h.1 ha) with ha|ha
      · apply False.elim
        apply he
        exact eq.symm.trans (congrArg (foldPerm L ext) ha)
      · have image: q∈(wires body0).image (foldPerm L ext) := Finset.mem_image.mpr ⟨a,ha,eq⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl image)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq)))))
  · have slots:=h.2
    simp only [LowZero18Square.withLowK2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    omega

end ECDSAAdd.Entrant.ParkCarryDevelop
end

section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic

theorem ExtraLe.rename (rho : Equiv.Perm Wire) {q : Wire} {P Q : Program} (h:ExtraLe q P Q) :
    ExtraLe (rho q) (renameProgram rho P) (renameProgram rho Q) := by
  refine ⟨?_,?_⟩
  · rw [renameProgram_support,renameProgram_support]
    intro w hw
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hw
    rcases Finset.mem_insert.mp (h.1 ha) with ha|ha
    · exact Finset.mem_insert.mpr (Or.inl (congrArg rho ha))
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  · simpa only [Baselines.rename_gateSlots] using h.2

theorem hosted_window_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) :
    toffoliCount (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))+1052=
      toffoliCount (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c)) ∧
    measurementCount (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))+4=
      measurementCount (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c)) ∧
    wires (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))⊆
      insert L.core.sumCarry (wires (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c))) ∧
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))≤
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c)) := by
  have h:=hosted_rel L hw (LowZero18Square.foldPerm L ext) c
  simpa only [Equiv.apply_symm_apply] using
    withLowK2_body_extra L ext c src dst _ _ 1052 4 _ h.1 h.2.1 h.2.2

end ECDSAAdd.Entrant.ParkCarryDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem sumCarry_gPrep (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) :
    L.core.sumCarry∈wires (OwnDiagAll12Square.gPrep L) := by
  have h:=OwnDiagAll12Square.sum_lengths L hw
  rw [OwnDiagAll12Square.gPrep,addInPlace_wires _ _ _ _ (by omega) (by omega)]
  simp [CuccaroStreamedSquareLayout.sum]

end ECDSAAdd.Entrant.ParkCarryDevelop
end

section
set_option autoImplicit false
namespace ECDSAAdd.Entrant.ParkCarryDevelop
open Arithmetic

theorem absorb_support (q : Wire) (P P0 B B0 : Program)
    (hp:wires P⊆wires P0) (hb:wires B⊆insert q (wires B0)) (hq:q∈wires P0) :
    wires (P++B)⊆wires (P0++B0) := by
  rw [wires_append,wires_append]
  apply Finset.union_subset
  · exact fun _ h=>Finset.mem_union_left _ (hp h)
  · intro x hx
    rcases Finset.mem_insert.mp (hb hx) with h|h
    · exact Finset.mem_union_left _ (h ▸ hq)
    · exact Finset.mem_union_right _ h

end ECDSAAdd.Entrant.ParkCarryDevelop
end


section
set_option autoImplicit false
set_option maxHeartbeats 6000000
-- Superseded comparison declarations omitted.
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic

theorem aBodyCached_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (c : Wire) : wires (aBodyCached L c)⊆(c::L.wires).toFinset := by
  intro q hq
  have h:=Finset.mem_insert.mp ((aBodyCached_rel L hw c).2.2.1 hq)
  rcases h with h|h
  · subst q;simp [Arithmetic.CuccaroStreamedSquareWideLayout.wires,Arithmetic.CuccaroStreamedSquareLayout.wires]
  · exact ControlLoan1589BFFold.aBody_support L hw hn c h

theorem hostedA_window_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) :
    toffoliCount (LowZero18Square.withLowK2 L ext c src dst (hostedA L (LowZero18Square.foldPerm L ext) c))+129=
      toffoliCount (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.aBody L c)) ∧
    measurementCount (LowZero18Square.withLowK2 L ext c src dst (hostedA L (LowZero18Square.foldPerm L ext) c))+3=
      measurementCount (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.aBody L c)) ∧
    wires (LowZero18Square.withLowK2 L ext c src dst (hostedA L (LowZero18Square.foldPerm L ext) c))⊆
      insert L.core.sumCarry (wires (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.aBody L c))) ∧
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (hostedA L (LowZero18Square.foldPerm L ext) c))≤
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.aBody L c)) := by
  have h:=hostedA_rel L hw (LowZero18Square.foldPerm L ext) c
  simpa only [Equiv.apply_symm_apply] using
    ParkCarryDevelop.withLowK2_body_extra L ext c src dst _ _ 129 3 _ h.1 h.2.1 h.2.2

end ECDSAAdd.Entrant.InverseCarryDevelop
end


section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic LowZero18Square

theorem withLowK2_body_extra_two (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body body0 : Program) (dT dM : Nat) (extra extraR : Wire)
    (hT:toffoliCount body+dT=toffoliCount body0)
    (hM:measurementCount body+dM=measurementCount body0) (h:ExtraLeTwo extra extraR body body0) :
    toffoliCount (LowZero18Square.withLowK2 L ext control src dst body)+dT=toffoliCount (LowZero18Square.withLowK2 L ext control src dst body0) ∧
    measurementCount (LowZero18Square.withLowK2 L ext control src dst body)+dM=measurementCount (LowZero18Square.withLowK2 L ext control src dst body0) ∧
    wires (LowZero18Square.withLowK2 L ext control src dst body)⊆insert ((foldPerm L ext) extra) (insert ((foldPerm L ext) extraR) (wires (LowZero18Square.withLowK2 L ext control src dst body0))) ∧
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body)≤Challenge.gateSlots (LowZero18Square.withLowK2 L ext control src dst body0) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [LowZero18Square.withLowK2,toffoliCount_append,(renameProgram_counts _ _).1]
    omega
  · simp only [LowZero18Square.withLowK2,measurementCount_append,(renameProgram_counts _ _).2]
    omega
  · intro q hq
    by_cases he:q=(foldPerm L ext) extra
    · exact Finset.mem_insert.mpr (Or.inl he)
    by_cases heR:q=(foldPerm L ext) extraR
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl heR))
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    simp only [LowZero18Square.withLowK2,wires_append,renameProgram_support,Finset.mem_union,or_assoc] at hq ⊢
    rcases hq with hq|hq|hq|hq|hq|hq|hq
    · exact Or.inl hq
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr (Or.inl hq))
    · obtain ⟨a,ha,eq⟩:=Finset.mem_image.mp hq
      rcases Finset.mem_insert.mp (h.1 ha) with ha|ha
      · apply False.elim
        apply he
        exact eq.symm.trans (congrArg (foldPerm L ext) ha)
      · rcases Finset.mem_insert.mp ha with ha|ha
        · apply False.elim
          apply heR
          exact eq.symm.trans (congrArg (foldPerm L ext) ha)
        · have image: q∈(wires body0).image (foldPerm L ext) := Finset.mem_image.mpr ⟨a,ha,eq⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl image)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq)))))
  · have slots:=h.2
    simp only [LowZero18Square.withLowK2,Challenge.gateSlots_append,Baselines.rename_gateSlots]
    omega

end ECDSAAdd.Entrant.InverseCarryDevelop
end

section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.ParkCarry7Develop
open Arithmetic

theorem hosted_window_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) :
    toffoliCount (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))+1058=
      toffoliCount (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c)) ∧
    measurementCount (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))+4=
      measurementCount (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c)) ∧
    wires (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))⊆
      insert L.core.sumCarry (wires (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c))) ∧
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))≤
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (ControlLoan1589BFFold.bBody L c)) := by
  have h:=hosted_rel L hw (LowZero18Square.foldPerm L ext) c
  simpa only [Equiv.apply_symm_apply] using
    ParkCarryDevelop.withLowK2_body_extra L ext c src dst _ _ 1058 4 _ h.1 h.2.1 h.2.2
end ECDSAAdd.Entrant.ParkCarry7Develop
namespace ECDSAAdd.Entrant.InverseCarryDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

theorem hostedADual_window_rel (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) :
    toffoliCount (LowZero18Square.withLowK2 L ext c src dst (hostedADual L (LowZero18Square.foldPerm L ext) c))+130=
      toffoliCount (LowZero18Square.withLowK2 L ext c src dst (aBody L c)) ∧
    measurementCount (LowZero18Square.withLowK2 L ext c src dst (hostedADual L (LowZero18Square.foldPerm L ext) c))+3=
      measurementCount (LowZero18Square.withLowK2 L ext c src dst (aBody L c)) ∧
    wires (LowZero18Square.withLowK2 L ext c src dst (hostedADual L (LowZero18Square.foldPerm L ext) c))⊆
      insert L.core.sumCarry (insert ((LowZero18Square.foldPerm L ext) (eV L)) (wires (LowZero18Square.withLowK2 L ext c src dst (aBody L c)))) ∧
    Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (hostedADual L (LowZero18Square.foldPerm L ext) c))≤
      Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (aBody L c)) := by
  have h:=hostedADual_rel L hw (LowZero18Square.foldPerm L ext) c
  simpa only [Equiv.apply_symm_apply] using
    withLowK2_body_extra_two L ext c src dst _ _ 130 3 _ _ h.1 h.2.1 h.2.2

theorem old_b_window_eV_mem (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (ext : List Wire)
    (c : Wire) (_he:300≤ext.length) :
    (LowZero18Square.foldPerm L ext) (eV L)∈wires (SquareCarryLoan719BF.branchBF L ext c) := by
  have image:(LowZero18Square.foldPerm L ext) (eV L)∈(wires (bBody L c)).image (LowZero18Square.foldPerm L ext) :=
    Finset.mem_image.mpr ⟨eV L,old_bbody_eV_mem L hw c,rfl⟩
  simp only [SquareCarryLoan719BF.branchBF,SquareCarryLoan719BF.withLowK2,
    wires_append,renameProgram_support,Finset.mem_union,or_assoc]
  exact Or.inr (Or.inr (Or.inr (Or.inl image)))

theorem absorb_support_two (q r : Wire) (P P0 B B0 : Program)
    (hp:wires P⊆wires P0) (hb:wires B⊆insert q (insert r (wires B0)))
    (hq:q∈wires P0) (hr:r∈wires P0) : wires (P++B)⊆wires (P0++B0) := by
  rw [wires_append,wires_append]
  apply Finset.union_subset
  · exact fun _ h=>Finset.mem_union_left _ (hp h)
  · intro w hw
    rcases Finset.mem_insert.mp (hb hw) with h|h
    · exact Finset.mem_union_left _ (h ▸ hq)
    · rcases Finset.mem_insert.mp h with h|h
      · exact Finset.mem_union_left _ (h ▸ hr)
      · exact Finset.mem_union_right _ h

end ECDSAAdd.Entrant.InverseCarryDevelop
end

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareSupport =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProgram

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18SquareSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout LowZero18Square
attribute [local irreducible] wires

theorem kg_X1_eq (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) :
    (LowZero18LowK.kg L ext src dst).X1=(OwnDiagLowK.kg L ext src dst).X1 :=
  (LowZero18LowK.kg_metadata L ext src dst).2.1.trans
    (SquareCarryLoan719BFSupport.kg_X1_eq L ext src dst)

section Normal
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hw in
theorem target_mem_X1 : target L∈(LowZero18LowK.kg L ext src dst).X1 := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).2.1]
  exact SquareCarryLoan719BFSupport.target_mem_X1 L hw ext src dst

include hw h128 in
theorem earlyHost_mem_outer : earlyHost L∈(LowZero18LowK.kg L ext src dst).R.S := by
  rw [(LowZero18LowK.kg_metadata L ext src dst).1]
  exact SquareCarryLoan719BFSupport.earlyHost_mem_outer L hw ext src dst h128

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem earlyHost_Q1_free :
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1 ∧
    earlyHost L∉wires (LowZero18LowK.kg L ext src dst).Q1c := by
  have old := SquareCarryLoan719BFSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  exact ⟨fun used=>old.1 (LowZero18LowK.kg_Q1_subset L hw ext src dst h128 hsmax hlen he used),
    fun used=>old.2 (LowZero18LowK.kg_Q1c_subset L hw ext src dst h128 hsmax hlen he used)⟩

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem target_clearPrefix_free :
    target L∉wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst)) := by
  have old := SquareCarryLoan719BFSupport.target_clearPrefix_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))⊆
      wires (SquareCarryLoan719BF.clearPrefix (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
    by_cases h : src.length=128
    all_goals simp only [LowZero18Square.clearPrefix,SquareCarryLoan719BF.clearPrefix,
      LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,ite_false,
      LowZero18LowK.kgH,LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgH,FrontierSumCleanup1591LowK.kgS,
      KRegs.c5,KRegs.c2,wires_append]
    all_goals repeat' first | exact LowZero18KG.smkT_c8z (LowZero18LowK.oregs L ext src dst) w | apply Finset.union_subset_union
    all_goals first | exact (TrimMid.tsqM_wires_le _ _ _ _ _).2 | exact PlainKnownClear.program_wires_le _ _ _ _ _ | exact LowZero18Diagonal.clear_support_subset _ (LowZero18LowK.jregsH_W L hw ext src dst h hlen he) | exact LowZero18Diagonal.clear_support_subset _ (LowZero18LowK.jregsS_W L hw ext src dst (by omega) hlen he) |
      exact (LowZero18LowK.oregs L ext src dst).c8z_wires w |
      exact (LowZero18LowK.oregs L ext src dst).c7t_wires | exact (LowZero18LowK.oregs L ext src dst).c6h_wires w |
      exact Finset.Subset.refl _
  exact fun used=>old (sub used)

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem make_tail_free :
    target L∉wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6h++(LowZero18LowK.kg L ext src dst).R.m7k++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591) := by
  have old := SquareCarryLoan719BFSupport.make_tail_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sub : wires ((LowZero18LowK.kg L ext src dst).Q2++
      (LowZero18LowK.kg L ext src dst).R.smk++(LowZero18LowK.kg L ext src dst).Q5++
      (LowZero18LowK.kg L ext src dst).R.m6h++(LowZero18LowK.kg L ext src dst).R.m7k++
      (LowZero18LowK.kg L ext src dst).R.m8z++(LowZero18LowK.kg L ext src dst).R.scl1591)⊆
    wires ((FrontierSumCleanup1591LowK.kg L ext src dst).Q2++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.smk++(FrontierSumCleanup1591LowK.kg L ext src dst).Q5++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m6++(FrontierSumCleanup1591LowK.kg L ext src dst).R.m7++
      (FrontierSumCleanup1591LowK.kg L ext src dst).R.m8++(FrontierSumCleanup1591LowK.kg L ext src dst).R.scl1591) := by
    have ro : FrontierSumCleanup1591LowK.oregs L ext src dst = LowZero18LowK.oregs L ext src dst := rfl
    have a6 := (LowZero18LowK.oregs L ext src dst).m6h_wires_smk w
    have a7 := (LowZero18LowK.oregs L ext src dst).m7k_wires w
    have a8 := (LowZero18LowK.oregs L ext src dst).m8z_wires w
    by_cases h : src.length=128
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsH L ext src dst)
        (LowZero18LowK.jregsH_W L hw ext src dst h hlen he)
      have rj : FrontierSumCleanup1591LowK.jregsH L ext src dst = LowZero18LowK.jregsH L ext src dst := rfl
      have q5 := (TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).S (LowZero18LowK.oregs L ext src dst).T (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).1
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_true,
        LowZero18LowK.kgH,FrontierSumCleanup1591LowK.kgH,KRegs.m5,wires_append,ro,rj]
      exact CodexBorrowedUnion.seven jp q5 a6 a7 a8
    · have jp := LowZero18Diagonal.make_support_subset (LowZero18LowK.jregsS L ext src dst)
        (LowZero18LowK.jregsS_W L hw ext src dst (by omega) hlen he)
      have rj : FrontierSumCleanup1591LowK.jregsS L ext src dst = LowZero18LowK.jregsS L ext src dst := rfl
      have q2 := (TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).hi (LowZero18LowK.oregs L ext src dst).dhi (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).1
      simp only [LowZero18LowK.kg,FrontierSumCleanup1591LowK.kg,h,ite_false,
        LowZero18LowK.kgS,FrontierSumCleanup1591LowK.kgS,KRegs.m2,wires_append,ro,rj]
      exact CodexBorrowedUnion.seven q2 jp a6 a7 a8
  exact fun used=>old (sub used)

end Normal
end ECDSAAdd.Entrant.LowZero18SquareSupport
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareSupport

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] run wires

abbrev fold_run_eq := SquareCarryLoan719.fold_run_eq

theorem patchKG_make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (K : KG)
    (sp : K.Spec) (targetX1 : target L∈K.X1) (hostS : earlyHost L∈K.R.S)
    (hostFree : earlyHost L∉wires K.Q1)
    (innerZero : ∀v t,K.I1 v t → t (target L)=false) (s : State) (m : List Bool)
    (hd0 : regValue K.R.dst s.basis=0) (hS0 : regValue K.R.S s.basis=0)
    (hX0 : regValue K.X s.basis=0) (hz0 : regValue K.R.z s.basis=0)
    (hp0 : regValue K.R.pad s.basis=0) (hc0 : regValue K.R.carry s.basis=0)
    (hi0 : s.basis K.R.cin=false) :
    run (LowZero18Square.make L K) m s=run (LowZero18KG.make K) m s := by
  have dlo0 : regValue K.R.dlo s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hd0 q (List.mem_of_mem_take hq))
  have x10 : regValue K.X1 s.basis=0 := (regValue_zero _ _).mpr (fun q hq =>
    (regValue_zero _ _).mp hX0 q (by simp only [KG.X,List.mem_append];tauto))
  have headEq (records : List Bool) := SquareCarryLoan719.q1_run_eq L hw K sp targetX1 hostFree innerZero
    s records dlo0 x10 hp0 hc0 hz0 hi0 ((regValue_zero _ _).mp hS0 _ hostS)
  let tail := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591
  have oldShape : LowZero18KG.make K=K.Q1++tail := by simp only [LowZero18KG.make,tail,List.append_assoc]
  have newShape : LowZero18Square.make L K=renameProgram (earlyPerm L) K.Q1++tail := by
    simp only [LowZero18Square.make,SquareCarryLoan719.patchKG,LowZero18KG.make,tail,List.append_assoc]
  simp only [newShape,oldShape,run_append,(renameProgram_counts _ _).2]
  rw [headEq]

theorem make_run_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (sp : (LowZero18LowK.kg L ext src dst).Spec) (s : State) (m : List Bool)
    (hd0 : regValue (LowZero18LowK.kg L ext src dst).R.dst s.basis=0)
    (hS0 : regValue (LowZero18LowK.kg L ext src dst).R.S s.basis=0)
    (hX0 : regValue (LowZero18LowK.kg L ext src dst).X s.basis=0)
    (hz0 : regValue (LowZero18LowK.kg L ext src dst).R.z s.basis=0)
    (hp0 : regValue (LowZero18LowK.kg L ext src dst).R.pad s.basis=0)
    (hc0 : regValue (LowZero18LowK.kg L ext src dst).R.carry s.basis=0)
    (hi0 : s.basis (LowZero18LowK.kg L ext src dst).R.cin=false) :
    run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) m s=
      run (LowZero18KG.make (LowZero18LowK.kg L ext src dst)) m s := by
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  apply patchKG_make_run_eq L hw (LowZero18LowK.kg L ext src dst) sp
    (LowZero18SquareSupport.target_mem_X1 L hw ext src dst)
    (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128) free.1
    ?_ s m hd0 hS0 hX0 hz0 hp0 hc0 hi0
  intro v t inv
  rw [LowZero18LowK.kg_I1] at inv
  exact (regValue_zero _ _).mp inv.1 _
    (SquareCarryLoan719Support.target_mem_inner L hw ext src dst)

theorem clear_run_eq_of_boundaries (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (K : KG) (s : State) (m : List Bool)
    (prefixFree : target L∉wires (clearPrefix K))
    (hostFree : earlyHost L∉wires K.Q1c)
    (targetIn : s.basis (target L)=false)
    (targetOut : (run (LowZero18KG.clear K) m s).basis (target L)=false)
    (hostOut : (run (LowZero18KG.clear K) m s).basis (earlyHost L)=false) :
    run (LowZero18Square.clear L K) m s=run (LowZero18KG.clear K) m s := by
  let middle := run (clearPrefix K) (m.take (measurementCount (clearPrefix K))) s
  let records := m.drop (measurementCount (clearPrefix K))
  have oldShape : LowZero18KG.clear K=clearPrefix K++K.Q1c := by
    simp only [LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have newShape : LowZero18Square.clear L K=clearPrefix K++renameProgram (earlyPerm L) K.Q1c := by
    simp only [LowZero18Square.clear,SquareCarryLoan719.patchKG,LowZero18KG.clear,LowZero18Square.clearPrefix,List.append_assoc]
  have oldRun : run (LowZero18KG.clear K) m s=run K.Q1c records middle := by rw [oldShape,run_append]
  have targetMid : middle.basis (target L)=false :=
    (run_preserves_outside _ _ s _ prefixFree).trans targetIn
  rw [oldRun] at targetOut hostOut
  have hostMid : middle.basis (earlyHost L)=false :=
    (run_preserves_outside _ records middle _ hostFree).symm.trans hostOut
  have lastEq := NewFieldFrameOB5.rebind_swap_run (target L) (earlyHost L) K.Q1c
    middle records targetMid hostMid targetOut hostOut
  rw [←SquareCarryLoan719.earlyPerm_eq L hw] at lastEq
  rw [newShape,oldShape,run_append,run_append]
  exact lastEq

theorem cross_host_zero (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)
    (h128 : 128≤src.length) (he : 300≤ext.length) (s : BasisState) (a b : Nat)
    (value : regValue (LowZero18LowK.oregs L ext src dst).T s=2*a*b) :
    s (ext.getD 0 0)=false :=
  SquareCarryLoan719.cross_host_zero L ext src dst h128 he s a b value

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareProof =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareHandoff

/-! The checked BF719 state proof with only the LowZero producer/cleanup constructors changed. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

private theorem k2_xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem withLowK2_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (LowZero18Square.withLowK2 L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.withLowK2 L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have cacheFix : earlyPerm L (dst.headD 0)=dst.headD 0 := by
    have mem : dst.headD 0∈dst := by
      rcases dst with _|⟨d,ds⟩
      · have hz : src.length=0 := by simpa using hlen.symm
        omega
      · exact List.mem_cons_self
    have targetM : target L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (fun e => tmpD _ targetM (by simpa only [e] using mem))
      (fun e => tmpD _ hostM (by simpa only [e] using mem))
  let P := if s.basis control then regValue src s.basis else 0
  obtain ⟨a6,r7,e7⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) records s
  obtain ⟨a5,r6,e6⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++
    CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length)) (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body)
    (CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length)) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++eraseMask control src (L.inputBank.take src.length)) (renameProgram (foldPerm L ext) body) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))) (eraseMask control src (L.inputBank.take src.length)) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)) (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) a2 s
  rw [show LowZero18Square.withLowK2 L ext control src dst body=copyRegister (some control) src (L.inputBank.take src.length)++(LowZero18Square.make L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length)++renameProgram (foldPerm L ext) body++CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length)++(LowZero18Square.clear L (LowZero18LowK.kg L ext src dst))++
    eraseMask control src (L.inputBank.take src.length) from rfl,e7,e6,e5,e4,e3,e2]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- erase
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask u1 r3 (by
    rw [bank1,ctl1,src1])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r3 u1=u2 at ep1 ef1 ev1 ⊢
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev1 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · exact (ef1 q hb).trans ((u1z q hq hx).trans (u0s q hb))
  have u2ext : ∀q∈ext,u2.basis q=u1.basis q := fun q h => ef1 q (extB q h)
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact ef1 q (fun h => bD q h hq)
  have cb := callback u2' r4 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r4 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r4 u2'=v' at cb loc
  generalize hv : run body r4 u2=v at loc
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r4 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r4 u2 q hb,run_preserves_outside body r4 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply k2_xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r4 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r4 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
  -- second copy
  have vDst : regValue dst v.basis=P^2 := by
    calc
      regValue dst v.basis = regValue dst u2.basis :=
        regValue_congr _ _ _ (fun q hq => vFrame q (dOut q hq))
      _ = regValue dst u1.basis :=
        regValue_congr _ _ _ (fun q hq => ef1 q (fun hb => bD q hb hq))
      _ = P^2 := dst1
  have vControl : v.basis control=s.basis control :=
    (vFrame _ ctlO).trans (u2s _ ctlD ctlE)
  have vSource : regValue src v.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq =>
      (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq)))
  have cached : v.basis (dst.headD 0)=(v.basis control && v.basis (src.headD 0)) :=
    CachedSquareCopy.square_head src dst control v (by omega) (by omega)
      (by simpa only [P,vControl,vSource] using vDst)
  rw [cacheWire,cacheFix,CachedSquareCopy.run_eq control (dst.headD 0) src (L.inputBank.take src.length) v r5 cached]
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB v r5
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r5 v=w0 at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := by
    rw [cv2,show regValue (L.inputBank.take src.length) v.basis=0 from (regValue_congr _ _ _ vB).trans banks.1,Nat.zero_xor]
    change (if v.basis control then regValue src v.basis else 0)=P
    rw [show v.basis control=s.basis control from (vFrame _ ctlO).trans (u2s _ ctlD ctlE),regValue_congr _ _ _ vSrc]
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    rw [cf2 q hb,vFrame q ho]
    by_cases hx : q∈ext
    · exact u2ext q hx
    · exact ef1 q hb
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r6
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r6
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r6 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2 q (srcB q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2 _ ctlB).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r7 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r7 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (cp2.trans (vPhase.trans (ep1.trans (mk.1.trans cp1))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2 q (fun h => bOut q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX,cf2 q hb,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx



theorem reflection_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (ext : List Wire)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (O : Nat) (hO : O<SquareReduction.p)
    (s : State) (m : List Bool) (ho : regValue L.core.out s.basis=O)
    (hc : L.PairClean s.basis) (hz : regValue ext s.basis=0) :
    (run (reflection L ext) m s).phase=s.phase ∧
    regValue L.core.out (run (reflection L ext) m s).basis=SquareReduction.p-1-O ∧
    ∀q,q∉L.core.out → (run (reflection L ext) m s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have old := L.reflectOutput_correct hw nd O hO s m ho hc
  have len := OwnDiagLowK.ktmp_length L hw
  have member : target L∈OwnDiagLowK.ktmp L := DiagSq.getD_in _ 67 (by omega)
  have pad : target L∈L.foldPad := List.mem_of_mem_drop member
  have away : target L∉L.core.out :=
    (L.pairAuxAway nd _ (by simp only [List.mem_append];tauto)).2
  have tin : s.basis (target L)=false := (regValue_zero _ _).mp hc.pad _ pad
  have tout : (run L.reflectOutput m s).basis (target L)=false := (old.2.2 _ away).trans tin
  have host : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by have h:=he.len;omega)
  have hin : s.basis (ext.getD 0 0)=false := (regValue_zero _ _).mp hz _ host
  have free : ext.getD 0 0∉wires L.reflectOutput := fun used=>
    he.away _ host (List.mem_toFinset.mp (ControlLoan1589BFFold.reflect_support L control used))
  have eq := SquareCarryLoan719.fold_run_eq L hw ext L.reflectOutput s m tin tout hin free
  simpa only [reflection,eq] using old

def middleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  LowZero18Square.withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)

theorem middleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (middleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (middleCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (middleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (OwnDiagAll12Square.bodyCKTq L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (OwnDiagAll12Square.bodyCK_supportTq L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (OwnDiagAll12Square.bodyCKTq L control) hbody
    s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := OwnDiagAll12Square.accMiddleCFK_bodyTq L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem branchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (LowZero18Square.branchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (LowZero18Square.branchCK L ext control) records s).basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (LowZero18Square.branchCK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := middleCK L ext control
  let mp := measurementCount (OwnDiagAll12Square.gPrep L)
  let rest := records.drop mp
  let u := run (OwnDiagAll12Square.gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (OwnDiagAll12Square.gClear L) (rest.drop (measurementCount middle)) v
  have prep := OwnDiagAll12Square.gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (OwnDiagAll12Square.sum_in L control q bad)))).trans hz
  have used := middleCK_correct L hw ext control hn (A+B) O hO u
    (rest.take (measurementCount middle)) prep.2.1 outU productU cleanU he hzU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have workRestore : regValue L.core.work restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hc.work
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [hq])).2
    simp [restoreBase,away]
  have cleared := OwnDiagAll12Square.gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      OwnDiagAll12Square.resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [LowZero18Square.branchCK,middleCK,middle,u,v,out,rest,mp,run_append] using final


theorem branchBF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchBF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchBF L ext control) records s).basis=
      ControlLoan1589BFFold.resBF ((if s.basis control then B else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchBF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  simp only [branchBF,ParkCarry7Develop.hosted_eq L (foldPerm L ext) control
    (ParkCarryDevelop.fold_fixes_sumCarry L hw nd ext he.len (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h)))]
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (ParkCarry7Develop.body L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (ParkCarry7Develop.body_support L hw nd control hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.high (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len
    (ParkCarry7Develop.body L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have sumProd:L.core.sumCarry∉L.core.product.take 256 := by
    intro h
    apply ParkCarryDevelop.sumCarry_away L nd
    simp [ParkCarryDevelop.restWires,List.mem_of_mem_take h]
  have hsumT:t.basis L.core.sumCarry=false := (same _ sumProd).trans hsum
  have frame := ParkCarry7Develop.body_frame L hw nd control hcw t.basis M mb full clean hsumT O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ControlLoan1589BFFold.bO4_eq M O (t.basis control) mb hg hO,ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩

theorem branchAF_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum:s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (branchAF L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (branchAF L ext control) records s).basis=
      ControlLoan1589BFFold.resAF ((if s.basis control then A else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchAF L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  simp only [branchAF,InverseCarryDevelop.hostedADual_eq L (foldPerm L ext) control
    (ParkCarryDevelop.fold_fixes_sumCarry L hw nd ext he.len
      (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h)))]
  have aSupport:=InverseCarryDevelop.aBodyDual_support L hw nd control
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (InverseCarryDevelop.aBodyDual L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (aSupport hw'))
  apply LowZero18Square.withLowK2_correct L hw control hn L.core.low (L.core.product.take 256) srcCount dstCount
    (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) ext he.nodup he.away he.len
    (InverseCarryDevelop.aBodyDual L control) hbody s records hc dstZero hz
  intro t m dstValue same
  rw [ha] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have sumProd:L.core.sumCarry∉L.core.product.take 256 := by
    intro h;apply ParkCarryDevelop.sumCarry_away L nd
    simp [ParkCarryDevelop.restWires,List.mem_of_mem_take h]
  have hsumT:t.basis L.core.sumCarry=false := (same _ sumProd).trans hsum
  have frame := InverseCarryDevelop.aBodyDual_frame L hw nd control hcw t.basis M mb full clean hsumT O hO hg t m ⟨outO,fun _ _ => rfl⟩
  rw [ctrlT] at frame
  exact ⟨frame.1,frame.2.1,frame.2.2⟩


theorem raw_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (raw L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (raw L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (raw L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (LowZero18Square.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := LowZero18Square.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc)
      ((hf.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc)
      ((hf.2 _ (ParkCarryDevelop.sumCarry_off_regs L nd).1).trans hs0) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepR : Triple (SquareFrame L.core.out s.basis OA) (reflection L ext)
      (SquareFrame L.core.out s.basis (SquareReduction.p-1-OA)) := by
    intro t m hf
    have h := reflection_correct L hw control hn ext he OA (ofCast_lt _ _) t m hf.1
      (L.squareFrame_clean nd s.basis t.basis OA hf hc) (extZ _ _ hf)
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := ((stepC.seq stepB).seq stepA).seq stepR
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  exact ⟨phase,value.trans exactResult,frame⟩


theorem raw_state_eq (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (m mOld : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis) (he : ECDSAAdd.Entrant.ExtOK L control ext)
    (hz : regValue ext s.basis=0) :
    run (raw L ext control) m s=run (ControlLoan1589BFFold.program L ext control) mOld s := by
  have fresh := raw_correct L hw ext control hn Y O hO s m hy ho hp0 hs0 hc he hz
  have prior := ControlLoan1589BFFold.correct L hw ext control hn Y O hO s mOld hy ho hp0 hs0 hc he hz
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · funext q
    by_cases inside : q∈L.core.out
    · exact (regValue_eq_iff _ _ _).mp (fresh.2.1.trans prior.2.1.symm) q inside
    · exact (fresh.2.2 q inside).trans (prior.2.2 q inside).symm

open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCandidate_state_eq (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (hX : X<p) (s : State) (m mOld : List Bool)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    run (fastCandidate L) m s=run (ControlLoan1589BFSquare.fastCandidate L) mOld s := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_state_eq K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m mOld hy hx prod0 sum0 clean
    (ECDSAAdd.Entrant.kext_ok L hw hn) hz
  simpa only [fastCandidate,ControlLoan1589BFSquare.fastCandidate] using kernel

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (fastCandidate L) := by
  intro X Y G origin s m v
  have old := ControlLoan1589BFSquare.candidate_correct L hw hn X Y G origin s m v
  have eq := fastCandidate_state_eq L hw hn X.val Y.val X.isLt s m m v.x v.y v.clean
  simpa only [eq] using old

private theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (old : ControlLoan1589BFSquare.SquareCorrectK L K P) :
    ControlLoan1589BFSquare.SquareCorrectK L K (renameProgram e P) := by
  intro X Y G origin s m v
  have result := old X Y G origin s m v
  have eq := Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean result.2.clean
  simpa only [eq] using result

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ControlLoan1589BFSquare.SquareCorrectK L K (program L) := by
  have a0 := relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have a1 := relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw) _ a0
  have a2 := relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw) _ a1
  have a3 := relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw) _ a2
  have a4 := relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw) _ a3
  have a5 := relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw) (OwnDiagAll12PlacedQ6.outside L hw) _ a4
  have a6 := relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw) (OwnDiagAll12PlacedQ7.outside L hw) _ a5
  have a7 := relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw) (PrefixFrontierSquare1591.outside L hw) _ a6
  have a8 := relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw) (Prefix1590Square.outside L hw) _ a7
  have a9 := relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw) (ControlLoan1589Square.outside L hw) _ a8
  exact a9

theorem step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (K:Fp) else 0)) Y G origin) :=
  correct L hw hn X Y G origin

private theorem values_unique {L : ControlledPointLayout} {X Y : Fp} {G : Bool}
    {origin a b : BasisState} (ha : PointDialogValues L X Y G origin a)
    (hb : PointDialogValues L X Y G origin b) : a=b := by
  funext q
  by_cases hx : q∈L.point.x
  · exact (regValue_eq_iff _ _ _).mp (ha.x.trans hb.x.symm) q hx
  · by_cases hy : q∈L.point.y
    · exact (regValue_eq_iff _ _ _).mp (ha.y.trans hb.y.symm) q hy
    · have away : q∉L.point.x++L.point.y := by
        simpa only [List.mem_append,not_or] using And.intro hx hy
      exact (ha.rest q away).trans (hb.rest q away).symm

theorem state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m mOld : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    run (program L) m s=run (ControlLoan1589BFSquare.program L) mOld s := by
  have fresh := correct L hw hn X Y G origin s m v
  have prior := ControlLoan1589BFSquare.correct L hw hn X Y G origin s mOld v
  apply State.extensionality
  · exact fresh.1.trans prior.1.symm
  · exact values_unique fresh.2 prior.2

theorem cleanup (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    regValue L.dialogPool (run (program L) m s).basis=0 :=
  (correct L hw hn X Y G origin s m v).2.clean

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.LowZero18SquareResources =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareProof

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.LowZero18Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] wires toffoliCount measurementCount Challenge.gateSlots

private theorem source_counts (L : CuccaroStreamedSquareWideLayout) :
    (∀q,L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q) ∧
    (∀q,(L.core.product.take 256).count q≤L.core.product.count q) := by
  have hh (q : Wire) : L.core.high.count q≤L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans ((List.drop_sublist 128 L.core.y).count_le q)
  refine ⟨?_,?_,?_,fun q=>(List.take_sublist 256 L.core.product).count_le q⟩
  · intro q
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢;omega
  · intro q;have h := hh q;simp only [List.count_append];omega
  · intro q;have h := hh q;simp only [CuccaroStreamedSquareLayout.sum,List.count_append];omega

theorem patchKG_counts (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    toffoliCount (LowZero18Square.make L R)=toffoliCount (LowZero18KG.make R) ∧
    measurementCount (LowZero18Square.make L R)=measurementCount (LowZero18KG.make R) ∧
    toffoliCount (LowZero18Square.clear L R)=toffoliCount (LowZero18KG.clear R) ∧
    measurementCount (LowZero18Square.clear L R)=measurementCount (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,toffoliCount_append,measurementCount_append,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem patchKG_slots (L : CuccaroStreamedSquareWideLayout) (R : KG) :
    Challenge.gateSlots (LowZero18Square.make L R)=Challenge.gateSlots (LowZero18KG.make R) ∧
    Challenge.gateSlots (LowZero18Square.clear L R)=Challenge.gateSlots (LowZero18KG.clear R) := by
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,Challenge.gateSlots_append,
    Baselines.rename_gateSlots,and_self]

theorem withLowK2_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (withLowK2 L ext control src dst body)+558+10*(if src.length=128 then 0 else 1)=
      toffoliCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) ∧
    measurementCount (withLowK2 L ext control src dst body)+21+3*(if src.length=128 then 0 else 1)=
      measurementCount (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have bankLen : (L.inputBank.take src.length).length=src.length := by
    simp [(L.measured_bank_widths hw).1,h129]
  have copyT := CachedSquareCopy.counts_nonempty control (cacheWire L dst) src
    (L.inputBank.take src.length) (by omega) (by rw [bankLen]; omega)
  have copyM := CachedSquareCopy.measurements control (cacheWire L dst) src (L.inputBank.take src.length)
  have d := LowZero18LowK.kg_counts_diff L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,toffoliCount_append,measurementCount_append,
    (patchKG_counts L _).1,(patchKG_counts L _).2.1,(patchKG_counts L _).2.2.1,(patchKG_counts L _).2.2.2,
    (SquareCarryLoan719BF.patchKG_counts L _).1,(SquareCarryLoan719BF.patchKG_counts L _).2.1,
    (SquareCarryLoan719BF.patchKG_counts L _).2.2.1,(SquareCarryLoan719BF.patchKG_counts L _).2.2.2,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

section CachedCopySubsetOpaque
attribute [local irreducible] LowZero18LowK.kg FrontierSumCleanup1591LowK.kg make clear SquareCarryLoan719BF.make SquareCarryLoan719BF.clear copyRegister eraseMask renameProgram CachedSquareCopy.copy
theorem withLowK2_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    wires (withLowK2 L ext control src dst body)⊆
      wires (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have m := LowZero18LowK.loan_make_support_subset L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_support_subset L hw ext src dst h128 h129 hd he
  have cp := CachedSquareCopy.wires_subset control (cacheWire L dst) src (L.inputBank.take src.length)
  have used := cache_wire_in_old_make L ext src dst (by omega)
  have hp : wires (CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length))⊆
      wires (copyRegister (some control) src (L.inputBank.take src.length))∪
        wires (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst)) := by
    apply cp.trans
    apply Finset.union_subset_union (Finset.Subset.refl _)
    intro q hq
    have eq : q=cacheWire L dst := Finset.mem_singleton.mp hq
    simpa only [eq] using used
  simpa only [withLowK2,SquareCarryLoan719BF.withLowK2] using
    cached_context_support
      (copyRegister (some control) src (L.inputBank.take src.length))
      (make L (LowZero18LowK.kg L ext src dst))
      (SquareCarryLoan719BF.make L (FrontierSumCleanup1591LowK.kg L ext src dst))
      (eraseMask control src (L.inputBank.take src.length))
      (renameProgram (foldPerm L ext) body)
      (CachedSquareCopy.copy control (cacheWire L dst) src (L.inputBank.take src.length))
      (clear L (LowZero18LowK.kg L ext src dst))
      (SquareCarryLoan719BF.clear L (FrontierSumCleanup1591LowK.kg L ext src dst)) (by simpa only [make] using m) (by simpa only [clear] using c) hp


end CachedCopySubsetOpaque

theorem withLowK2_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (SquareCarryLoan719BF.withLowK2 L ext control src dst body) := by
  have cp := CachedSquareCopy.slots control (cacheWire L dst) src (L.inputBank.take src.length)
  have m := LowZero18LowK.loan_make_slots_le L hw ext src dst h128 h129 hd he
  have c := LowZero18LowK.loan_clear_slots_le L hw ext src dst h128 h129 hd he
  simp only [withLowK2,SquareCarryLoan719BF.withLowK2,make,clear,patchKG,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

/-- Replacing the body of `withLowK2` by a statically refining body with known count savings. -/
theorem withLowK2_body_rel (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body body0 : Program) (dT dM : Nat)
    (hT : toffoliCount body+dT=toffoliCount body0) (hM : measurementCount body+dM=measurementCount body0)
    (hle : QRel.Le body body0) :
    toffoliCount (withLowK2 L ext control src dst body)+dT=toffoliCount (withLowK2 L ext control src dst body0) ∧
    measurementCount (withLowK2 L ext control src dst body)+dM=
      measurementCount (withLowK2 L ext control src dst body0) ∧
    wires (withLowK2 L ext control src dst body)⊆wires (withLowK2 L ext control src dst body0) ∧
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤
      Challenge.gateSlots (withLowK2 L ext control src dst body0) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [withLowK2,toffoliCount_append,(renameProgram_counts _ _).1]; omega
  · simp only [withLowK2,measurementCount_append,(renameProgram_counts _ _).2]; omega
  · simp only [withLowK2,wires_append,renameProgram_support]
    repeat' apply Finset.union_subset_union
    all_goals first | exact Finset.image_subset_image hle.1 | exact Finset.Subset.refl _
  · have := hle.2
    simp only [withLowK2,Challenge.gateSlots_append,Baselines.rename_gateSlots]; omega

theorem raw_counts_diff (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    toffoliCount (raw L ext control)+3032=toffoliCount (SquareCarryLoan719BF.raw L ext control) ∧
    measurementCount (raw L ext control)+75=measurementCount (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_counts_diff L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_counts_diff L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_counts_diff L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := ParkCarry7Develop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256)
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedADual_window_rel L hw ext control L.core.low (L.core.product.take 256)
  rw [if_neg (show ¬L.core.sum.length=128 by omega)] at c
  rw [if_pos high] at b
  rw [if_pos low] at a
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,
    toffoliCount_append,measurementCount_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2]
  constructor <;> omega

theorem raw_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    wires (raw L ext control)⊆wires (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_support_subset L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_support_subset L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_support_subset L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := ParkCarry7Develop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256)
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedADual_window_rel L hw ext control L.core.low (L.core.product.take 256)
  have k3 := q3.trans k3
  have b := b3.trans (Finset.insert_subset_insert L.core.sumCarry b)
  have a := a3.trans (Finset.insert_subset_insert L.core.sumCarry (Finset.insert_subset_insert ((foldPerm L ext) (ControlLoan1589BFFold.eV L)) a))
  have ck:wires (LowZero18Square.branchCK L ext control)⊆wires (SquareCarryLoan719BF.branchCK L ext control) := by
    simp only [LowZero18Square.branchCK,SquareCarryLoan719BF.branchCK,wires_append]
    repeat' apply Finset.union_subset_union
    all_goals first | exact k3.trans c | exact Finset.Subset.refl _
  have qmem:L.core.sumCarry∈wires (SquareCarryLoan719BF.branchCK L ext control) := by
    simp only [SquareCarryLoan719BF.branchCK,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (ParkCarryDevelop.sumCarry_gPrep L hw))
  have cb:=ParkCarryDevelop.absorb_support L.core.sumCarry _ _ _ _ ck b qmem
  have qab:L.core.sumCarry∈wires (SquareCarryLoan719BF.branchCK L ext control++SquareCarryLoan719BF.branchBF L ext control) := by
    rw [wires_append];exact Finset.mem_union_left _ qmem
  have rab:(foldPerm L ext) (ControlLoan1589BFFold.eV L)∈wires
      (SquareCarryLoan719BF.branchCK L ext control++SquareCarryLoan719BF.branchBF L ext control) := by
    rw [wires_append]
    exact Finset.mem_union_right _ (InverseCarryDevelop.old_b_window_eV_mem L hw ext control he)
  have cba:=InverseCarryDevelop.absorb_support_two L.core.sumCarry ((foldPerm L ext) (ControlLoan1589BFFold.eV L)) _ _ _ _ cb a qab rab
  simp only [wires_append] at cba
  simp only [raw,SquareCarryLoan719BF.raw,wires_append]
  exact Finset.union_subset_union cba (Finset.Subset.refl _)

theorem raw_slots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (raw L ext control)≤Challenge.gateSlots (SquareCarryLoan719BF.raw L ext control) := by
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have c := withLowK2_slots_le L hw ext control L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have b := withLowK2_slots_le L hw ext control L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (by omega) (by omega) (by omega) he
  have a := withLowK2_slots_le L hw ext control L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (by omega) (by omega) (by omega) he
  obtain ⟨q1,q2,q3,q4⟩ := withLowK2_body_rel L ext control L.core.sum L.core.product _ _ 129 2
    (QRel.bodyCK_rel L hw control).1 (QRel.bodyCK_rel L hw control).2.1 (QRel.bodyCK_rel L hw control).2.2
  obtain ⟨b1,b2,b3,b4⟩ := ParkCarry7Develop.hosted_window_rel L hw ext control L.core.high (L.core.product.take 256)
  obtain ⟨a1,a2,a3,a4⟩ := InverseCarryDevelop.hostedADual_window_rel L hw ext control L.core.low (L.core.product.take 256)
  simp only [raw,SquareCarryLoan719BF.raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,SquareCarryLoan719BF.branchCK,SquareCarryLoan719BF.branchBF,
    SquareCarryLoan719BF.branchAF,reflection,SquareCarryLoan719BF.reflection,Challenge.gateSlots_append,
    Baselines.rename_gateSlots]
  omega

private theorem tRename (f : Wire→Wire) (P : Program) :
    toffoliCount (renameProgram f P)=toffoliCount P := (renameProgram_counts f P).1
private theorem mRename (f : Wire→Wire) (P : Program) :
    measurementCount (renameProgram f P)=measurementCount P := (renameProgram_counts f P).2

theorem counts_diff (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+3032=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+75=measurementCount (SquareCarryLoan719BF.program L) := by
  have h := raw_counts_diff L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,tRename,mRename] using h

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=49227 ∧ measurementCount (program L)=53000 := by
  have a := counts_diff L hw
  have b := SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  have h := raw_slots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])
  simpa only [program,SquareCarryLoan719BF.program,place,SquareCarryLoan719BF.place,
    fastCandidate,SquareCarryLoan719BF.fastCandidate,Baselines.rename_gateSlots] using h

theorem slots (L : ControlledPointLayout) (hw : L.Widths) : Challenge.gateSlots (program L)≤8000000 :=
  (slots_le L hw).trans (SquareCarryLoan719BF.slots L hw)

private theorem place_support_mono (L : ControlledPointLayout) (P Q : Program) (sub : wires P⊆wires Q) :
    wires (place L P)⊆wires (SquareCarryLoan719BF.place L Q) := by
  unfold place SquareCarryLoan719BF.place
  repeat' apply OneFlagReplay.rename_subset
  exact sub

theorem support_subset (L : ControlledPointLayout) (hw : L.Widths) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  apply place_support_mono
  exact raw_support_subset L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L hw).trans (SquareCarryLoan719BF.support L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire k∉wires (program L) :=
  fun used=>SquareCarryLoan719BF.square_free L hw hn k hk (support_subset L hw used)

theorem retired_free719 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 719∉wires (program L) := square_free L hw hn 719 (by simp)
theorem retired_free768 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 768∉wires (program L) := square_free L hw hn 768 (by simp)
theorem retired_free718 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 718∉wires (program L) := square_free L hw hn 718 (by simp)

private theorem patchKG_physical (L : CuccaroStreamedSquareWideLayout) (R : KG)
    (hm : GatePhysical (LowZero18KG.make R))
    (hc : GatePhysical (LowZero18KG.clear R)) :
    GatePhysical (LowZero18Square.make L R) ∧ GatePhysical (LowZero18Square.clear L R) := by
  simp only [LowZero18KG.make,gatePhysical_append] at hm
  simp only [LowZero18KG.clear,gatePhysical_append] at hc
  have first : GatePhysical (renameProgram (earlyPerm L) R.Q1) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  have last : GatePhysical (renameProgram (earlyPerm L) R.Q1c) :=
    gatePhysical_rename (earlyPerm L) (earlyPerm L).injective _ (by tauto)
  simp only [LowZero18Square.make,LowZero18Square.clear,SquareCarryLoan719.patchKG,
    LowZero18KG.make,LowZero18KG.clear,gatePhysical_append]
  tauto

private theorem withLowK2_physical_of_old (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (src dst : List Wire) (body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hlen : dst.length=2*src.length)
    (old : GatePhysical (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst body)) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  simp only [FrontierSumCleanup1591LowK.withLowK2,gatePhysical_append] at old
  have nd := LowZero18LowK.kg_nodup L control hn ext src dst hs hd he.nodup he.away
  have ph := LowZero18LowK.kg_physical L hw ext src dst h128 h129 hlen he.len nd
  have kernels := patchKG_physical L (LowZero18LowK.kg L ext src dst) ph.1 ph.2
  have bodyNew : GatePhysical (renameProgram (foldPerm L ext) body) :=
    gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ (by tauto)
  have big := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext he.nodup he.away
  have db : (dst++L.inputBank.take src.length).Nodup := knd big (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have bankLen : (L.inputBank.take src.length).length=src.length := by
    simp [(L.measured_bank_widths hw).1,h129]
  have cachedPhysical := cached_copy_physical L hw (List.nodup_cons.mp hn).2 control src dst hd
    (by omega) (by rw [bankLen]; omega) db (by tauto)
  simp only [withLowK2,gatePhysical_append]
  tauto

private theorem withLowK2_physical_of_old2 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (src dst : List Wire) (body0 body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hlen : dst.length=2*src.length)
    (old : GatePhysical (FrontierSumCleanup1591LowK.withLowK2 L ext control src dst body0))
    (hb : GatePhysical body) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  simp only [FrontierSumCleanup1591LowK.withLowK2,gatePhysical_append] at old
  have nd := LowZero18LowK.kg_nodup L control hn ext src dst hs hd he.nodup he.away
  have ph := LowZero18LowK.kg_physical L hw ext src dst h128 h129 hlen he.len nd
  have kernels := patchKG_physical L (LowZero18LowK.kg L ext src dst) ph.1 ph.2
  have bodyNew : GatePhysical (renameProgram (foldPerm L ext) body) :=
    gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ hb
  have big := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext he.nodup he.away
  have db : (dst++L.inputBank.take src.length).Nodup := knd big (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have bankLen : (L.inputBank.take src.length).length=src.length := by
    simp [(L.measured_bank_widths hw).1,h129]
  have cachedPhysical := cached_copy_physical L hw (List.nodup_cons.mp hn).2 control src dst hd
    (by omega) (by rw [bankLen]; omega) db (by tauto)
  simp only [withLowK2,gatePhysical_append]
  tauto

private theorem raw_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) : GatePhysical (raw L ext control) := by
  have old := ControlLoan1589BFFold.physical L hw ext control hn he
  simp only [ControlLoan1589BFFold.program,FrontierSumCleanup1591Raw.accBranchCK,
    FrontierSumCleanup1591Raw.accMiddleCK,ControlLoan1589BFFold.branchBF,
    ControlLoan1589BFFold.branchAF,gatePhysical_append] at old
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have sc := source_counts L
  have c := withLowK2_physical_of_old L hw ext control hn he L.core.sum L.core.product
    (OwnDiagAll12Square.bodyC L control) sc.2.2.1 (fun _=>le_rfl)
    (by omega) (by omega) (by rw [hw.core.product,sum]) old.1.1.1.1.2
  obtain ⟨k1,k2,k3,k4⟩ := LowZero18Square.withLowK2_bodyCK L hw ext control L.core.sum L.core.product
  have c : GatePhysical (withLowK2 L ext control L.core.sum L.core.product (OwnDiagAll12Square.bodyCKTq L control)) := by
    have pb := OwnDiagAll12Square.bodyCK_physicalTq L hw (List.nodup_cons.mp hn).2 control (List.nodup_cons.mp hn).1
    have pr := gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ pb
    simp only [withLowK2,gatePhysical_append] at c ⊢
    tauto
  have b := withLowK2_physical_of_old2 L hw ext control hn he L.core.high (L.core.product.take 256)
    (ControlLoan1589BFFold.bBody L control) (ParkCarry7Develop.hostedBody L (foldPerm L ext) control) sc.2.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.1.2 (by
      rw [ParkCarry7Develop.hosted_eq L (foldPerm L ext) control
        (ParkCarryDevelop.fold_fixes_sumCarry L hw (List.nodup_cons.mp hn).2 ext he.len
          (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h)))]
      exact ParkCarry7Develop.body_physical L hw control hn)
  have a := withLowK2_physical_of_old2 L hw ext control hn he L.core.low (L.core.product.take 256)
    (ControlLoan1589BFFold.aBody L control) (InverseCarryDevelop.hostedADual L (foldPerm L ext) control) sc.1 sc.2.2.2
    (by omega) (by omega) (by omega) old.1.2 (by
      rw [InverseCarryDevelop.hostedADual_eq L (foldPerm L ext) control
        (ParkCarryDevelop.fold_fixes_sumCarry L hw (List.nodup_cons.mp hn).2 ext he.len
          (fun q hq h=>he.away q hq (List.mem_cons_of_mem control h)))]
      exact InverseCarryDevelop.aBodyDual_physical L hw control hn)
  have r := gatePhysical_rename (foldPerm L ext) (foldPerm L ext).injective _ old.2
  simp only [raw,LowZero18Square.branchCK,LowZero18Square.branchBF,
    LowZero18Square.branchAF,reflection,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨old.1.1.1.1.1,c⟩,old.1.1.1.2⟩,b⟩,a⟩,r⟩

private theorem control_nd (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup := by
  have nd := L.streamedSquare_control_nodup hw hn
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp nd q
  simp only [List.count_cons] at h ⊢
  omega

private theorem place_physical (L : ControlledPointLayout) (P : Program) (hp : GatePhysical P) :
    GatePhysical (place L P) := by
  unfold place
  apply gatePhysical_rename (ControlLoan1589Square.swap L) (ControlLoan1589Square.swap L).injective
  apply gatePhysical_rename (Prefix1590Square.swap L) (Prefix1590Square.swap L).injective
  apply gatePhysical_rename (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.swap L).injective
  apply gatePhysical_rename (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.swap L).injective
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202) (Square5Placement.blockPerm L 202).injective _ hp

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (program L) :=
  place_physical L _ (raw_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
    (OwnDiagAll12Square.kext L) L.core.generic (control_nd L hw hn) (ECDSAAdd.Entrant.kext_ok L hw hn))

end ECDSAAdd.Entrant.LowZero18Square
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Rolling1588LowZeroFinal =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588BFFinal
-- consolidated import: import ECDSAAdd.Submission.Entrant.LowZero18SquareResources

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.Rolling1588LowZeroFinal
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog CompressedAllocation CompressedFieldSupport DirectSkywalk
  BalancedField History5 EntryFuse EntryFuseFinite FrontierEntry1591Callers
  ControlLoan1589BFFinal
attribute [local irreducible] run wires toffoliCount measurementCount gateSlots

def gen (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  Offset.gen L (division Rolling1588.entryKernel L) (LowZero18Square.program L)
    (exit Rolling1588.exitKernel L) cx cy

private def Metrics (P Q : Program) : Prop :=
  toffoliCount P+3032=toffoliCount Q ∧ measurementCount P+75=measurementCount Q ∧
    gateSlots P≤gateSlots Q

private theorem gen_metrics_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : Metrics S Old) : Metrics G G0 := by
  subst G G0
  simp only [Metrics,Offset.gen,Offset.mid,Offset.generic,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at hs ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_metrics (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    Metrics (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) := by
  have counts:=LowZero18Square.counts_diff L hw
  exact gen_metrics_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    ⟨counts.1,counts.2,LowZero18Square.slots_le L hw⟩

theorem gen_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    toffoliCount (gen L cx cy)+3032=toffoliCount (Rolling1588BFFinal.gen L cx cy) ∧
    measurementCount (gen L cx cy)+75=measurementCount (Rolling1588BFFinal.gen L cx cy) :=
  ⟨(gen_metrics L hw cx cy).1,(gen_metrics L hw cx cy).2.1⟩

private theorem wrapper_metrics (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : Metrics P Q) :
    Metrics (Edges.wrapper L C cy P) (Edges.wrapper L C cy Q) := by
  simp only [Metrics,Edges.wrapper,Edges.finiteProgram,toffoliCount_append,
    measurementCount_append,gateSlots_append,renameProgram_counts,rename_gateSlots] at h ⊢
  exact ⟨by omega,by omega,by omega⟩

private theorem gen_subset_of_shapes (L : ControlledPointLayout) (D : Fp→Program)
    (S Old P G G0 : Program) (cx cy : Fp)
    (hG : G=Offset.gen L D S P cx cy) (hG0 : G0=Offset.gen L D Old P cx cy)
    (hs : wires S⊆wires Old) : wires G⊆wires G0 := by
  subst G G0
  simp only [Offset.gen,Offset.mid,Offset.generic,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact hs | exact Finset.Subset.refl _

theorem gen_support_subset (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    wires (gen L cx cy)⊆wires (Rolling1588BFFinal.gen L cx cy) :=
  gen_subset_of_shapes L (division Rolling1588.entryKernel L)
    (LowZero18Square.program L) (SquareCarryLoan719BF.program L) (exit Rolling1588.exitKernel L)
    (gen L cx cy) (Rolling1588BFFinal.gen L cx cy) cx cy
    (by unfold gen; rfl) (by unfold Rolling1588BFFinal.gen; rfl)
    (LowZero18Square.support_subset L hw)

private theorem wrapper_subset (L : ControlledPointLayout) (C : Point) (cy : Fp)
    (P Q : Program) (h : wires P⊆wires Q) :
    wires (Edges.wrapper L C cy P)⊆wires (Edges.wrapper L C cy Q) := by
  simp only [Edges.wrapper,Edges.finiteProgram,wires_append,renameProgram_support]
  repeat' first | apply Finset.union_subset_union | apply Finset.image_subset_image
  all_goals first | exact h | exact Finset.Subset.refl _

private theorem qubits_mono (P Q : Program) (h : wires P⊆wires Q) : qubits P≤qubits Q := by
  change (ioWires∪wires P).card≤(ioWires∪wires Q).card
  exact Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _) h)

theorem gen_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) : GenericOK L hc (gen L cx cy) := by
  have config:=MappedCompressed.LaneA.laneLogical_config
  have above : History5.HistoryAbove base := by intro j hj;simp [base]
  exact Offset.genFFused_ok L hw hn _ _ _
    (FrontierEntry1591Callers.exit_correct Rolling1588.exitKernel
      Rolling1588.exitKernel_support Rolling1588.exit_correct L hw hn)
    (FrontierEntry1591Callers.division_step Rolling1588.entryKernel
      Rolling1588.entryKernel_support Rolling1588.entry_correct
      L hw hn config.1 above config.2.1 config.2.2)
    (LowZero18Square.step L hw hn) hc

theorem gen_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : wires (gen L cx cy)⊆(OB5Support.genericSites L).toFinset :=
  (gen_support_subset L hw cx cy).trans (Rolling1588BFFinal.gen_sites L hw hn cx cy)

theorem gen_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) : GatePhysical (gen L cx cy) :=
  Offset.gen_physical L hw hn _ _ _
    (division_physical Rolling1588.entryKernel Rolling1588.entryKernel_support
      Rolling1588.entryKernel_physical L hw hn)
    (LowZero18Square.physical L hw hn)
    (placed_physical Rolling1588.exitKernel Rolling1588.exitKernel_support
      Rolling1588.exitKernel_physical L hw hn) cx cy

theorem wrapper_qubits (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (gen layout cx cy))≤1588 :=
  (qubits_mono _ _ (wrapper_subset layout C cy _ _
    (gen_support_subset layout layout_widths cx cy))).trans
    (Rolling1588BFFinal.wrapper_qubits C cx cy)

theorem wrapper_toffoli (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    toffoliCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤2149200 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).1
  have old:=Rolling1588BFFinal.wrapper_toffoli cx cy hc
  omega

theorem wrapper_measurements (cx cy : Fp) (hc : curve.toAffine.Nonsingular cx cy) :
    measurementCount (Edges.wrapper layout (.some hc) cy (gen layout cx cy))≤1499945 := by
  have diff:=(wrapper_metrics layout (.some hc) cy _ _ (gen_metrics layout layout_widths cx cy)).2.1
  have old:=Rolling1588BFFinal.wrapper_measurements cx cy hc
  omega

theorem wrapper_slots (C : Point) (cx cy : Fp) :
    gateSlots (Edges.wrapper layout C cy (gen layout cx cy))≤50139199+Rolling1588.slotGrowth :=
  (wrapper_metrics layout C cy _ _ (gen_metrics layout layout_widths cx cy)).2.2.trans
    (Rolling1588BFFinal.wrapper_slots C cx cy)

def program (C : Point) : Program :=
  match C with
  | .zero => []
  | @WeierstrassCurve.Affine.Point.some _ _ _ cx cy _ =>
      Edges.wrapper layout C cy (gen layout cx cy)

def entry : Challenge.Entry := fun C => normalizeProgram (program C)
def bounds : Challenge.Bounds := ⟨2149200,1499945,1588,50139199+Rolling1588.slotGrowth⟩

theorem program_correct (C : Point) (b : Bool) (R : Point) :
    Triple (encodes b R) (program C) (encodes b (if b then R+C else R)) := by
  cases C with
  | zero =>
    intro s m hs
    simpa only [program,run,←WeierstrassCurve.Affine.Point.zero_def,add_zero,ite_self]
      using And.intro (Eq.refl s.phase) hs
  | @some cx cy hc =>
    have sites:=gen_sites layout layout_widths layout_nodup cx cy
    exact fixed_correct _ b R _
      (Edges.full_spec layout layout_widths layout_nodup R hc b _
        (gen_ok layout layout_widths layout_nodup hc) sites)
      ((Edges.wrapper_support layout layout_widths layout_nodup _ cy _ sites).trans
        (WrapperOB5.support_used layout layout_widths))

theorem program_toffoli (C : Point) : toffoliCount (program C)≤2149200 := by
  cases C with
  | zero => simp [program,toffoliCount]
  | @some cx cy hc => exact wrapper_toffoli cx cy hc

theorem program_measurements (C : Point) : measurementCount (program C)≤1499945 := by
  cases C with
  | zero => simp [program,measurementCount]
  | @some cx cy hc => exact wrapper_measurements cx cy hc

theorem program_qubits (C : Point) : qubits (program C)≤1588 := by
  cases C with
  | zero => change qubits []≤1588;rw [qubits_empty];decide
  | @some cx cy hc => exact wrapper_qubits (.some hc) cx cy

theorem program_physical (C : Point) : GatePhysical (program C) := by
  cases C with
  | zero => simp [program,GatePhysical]
  | @some cx cy hc =>
    exact Edges.wrapper_physical layout layout_widths layout_nodup _ cy _
      (gen_physical layout layout_widths layout_nodup cx cy)

theorem program_gateSlots (C : Point) : gateSlots (program C)≤50139199+Rolling1588.slotGrowth := by
  cases C with
  | zero => simp [program,gateSlots]
  | @some cx cy hc => exact wrapper_slots (.some hc) cx cy

theorem certificate : Challenge.Certificate entry bounds where
  correct C b R := (normalize_triple _ _ _).mpr (program_correct C b R)
  physical C := normalize_physical _ (program_physical C)
  toffoli_le C := (normalize_toffoli _).trans (program_toffoli C)
  measurements_le C := by
    change measurementCount (normalizeProgram (program C))≤1499945
    rw [normalize_measurements];exact program_measurements C
  qubits_le C := by
    change qubits (normalizeProgram (program C))≤1588
    rw [normalize_qubits];exact program_qubits C
  gateSlots_le C := by
    change gateSlots (normalizeProgram (program C))≤50139199+Rolling1588.slotGrowth
    rw [normalize_slots];exact program_gateSlots C

end ECDSAAdd.Entrant.Rolling1588LowZeroFinal
end -- original module boundary

-- Selected checked E1 branch follows; the audited LowZero18 branch is omitted.

-- ===== ECDSAAdd.Submission.Entrant.ReflectionE1Square =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.SquareCarryLoan719BFProof

/-! Remove only the BF square's final reflection. All719 loans stay intact. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.ReflectionE1Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
  SquareCarryLoan719BF
attribute [local irreducible] run wires

def core (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  branchCK L ext control++branchBF L ext control++branchAF L ext control

def fastCore (L : ControlledPointLayout) : Program :=
  core L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L) L.core.generic

def program (L : ControlledPointLayout) : Program := place L (fastCore L)

def reflectedTail (L : ControlledPointLayout) : Program :=
  place L (reflection L.dialogStreamedSquareWide (OwnDiagAll12Square.kext L))

theorem raw_split (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) :
    raw L ext control=core L ext control++reflection L ext := rfl

theorem place_append (L : ControlledPointLayout) (P Q : Program) :
    place L (P++Q)=place L P++place L Q := by
  simp only [place,renameProgram,List.map_append]

theorem program_split (L : ControlledPointLayout) :
    SquareCarryLoan719BF.program L=program L++reflectedTail L := by
  simp only [SquareCarryLoan719BF.program,SquareCarryLoan719BF.fastCandidate,
    raw_split,place_append,program,fastCore,reflectedTail]

theorem raw_core_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (core L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (core L ext control) records s).basis=
      SquareReduction.p-1-
        (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
          (if s.basis control then K else 0))%SquareReduction.p) ∧
    ∀q,q∉L.core.out → (run (core L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := OwnDiagAll12Square.resCF enabled PC O
  let OB := ControlLoan1589BFFold.resBF PB OC enabled
  let OA := ControlLoan1589BFFold.resAF PA OB enabled
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumAway (q : Wire) (hq : q∈L.core.sum) : q∉L.core.out :=
    List.disjoint_left.mp (L.measured_sum_disjoint nd).2 hq
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have low (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.low t=A := regValue_congr _ _ _ (fun q hq => hf.2 q (lowAway q hq))
  have high (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.high t=B := regValue_congr _ _ _ (fun q hq => hf.2 q (highAway q hq))
  have sum (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.sum t=B :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (sumAway q hq))).trans sumB
  have prod (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue L.core.product t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have extZ (X : Nat) (t : BasisState) (hf : SquareFrame L.core.out s.basis X t) :
      regValue ext t=0 :=
    (regValue_congr _ _ _ (fun q hq => hf.2 q (ECDSAAdd.Entrant.ext_out L control ext he q hq))).trans hz
  have stepC : Triple (SquareFrame L.core.out s.basis O) (SquareCarryLoan719BF.branchCK L ext control)
      (SquareFrame L.core.out s.basis OC) := by
    intro t m hf
    have h := SquareCarryLoan719BF.branchCK_correct L hw ext control hn A B O hO t m
      (low _ _ hf) (sum _ _ hf) sumBound hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis O hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepB : Triple (SquareFrame L.core.out s.basis OC) (branchBF L ext control)
      (SquareFrame L.core.out s.basis OB) := by
    intro t m hf
    have h := branchBF_correct L hw ext control hn B OC (ofCast_lt _ _) t m (high _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OC hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have stepA : Triple (SquareFrame L.core.out s.basis OB) (branchAF L ext control)
      (SquareFrame L.core.out s.basis OA) := by
    intro t m hf
    have h := branchAF_correct L hw ext control hn A OB (ofCast_lt _ _) t m (low _ _ hf) hf.1 (prod _ _ hf)
      (L.squareFrame_clean nd s.basis t.basis OB hf hc) he (extZ _ _ hf)
    rw [hf.2 control ctrlAway] at h
    exact ⟨h.1,h.2.1,fun q hq => (h.2.2 q hq).trans (hf.2 q hq)⟩
  have all := (stepC.seq stepB).seq stepA
  obtain ⟨phase,value,frame⟩ := all s records ⟨ho,fun _ _ => rfl⟩
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have exactResult := ControlLoan1589BFFold.complete_exact enabled A B O
  rw [split] at exactResult
  unfold subModValue at exactResult
  have oaLt : OA<SquareReduction.p := ofCast_lt _ _
  have reflected : OA=SquareReduction.p-1-
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) := by
    change SquareReduction.p-1-OA=
      (((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then K else 0))%SquareReduction.p) at exactResult
    omega
  exact ⟨phase,value.trans reflected,frame⟩


open Secp256k1 MappedCompressed CompressedPointDialog

theorem fastCore_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(((X+p-(if B then Y*Y else 0)%p)%p+(if B then ControlLoan1589BFFold.K else 0))%p) ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := raw_core_correct K hwK (OwnDiagAll12Square.kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCore,hb,hp,pow_two] using kernel


theorem fastCore_boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (fastCore L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCore L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (fastCore L) m s).basis q=s.basis q := by
  have fresh:=fastCore_correct L hw hn X.val Y.val G X.isLt s m v.generic v.x v.y v.clean
  have prior:=ControlLoan1589BFSquare.fastCandidate_correct L hw hn X.val Y.val G X.isLt s []
    v.generic v.x v.y v.clean
  have canonical:=SquareCarryLoan719BF.candidate_correct L hw hn X Y G origin s [] v
  have eq:=SquareCarryLoan719BF.fastCandidate_state_eq L hw hn X.val Y.val X.isLt s [] []
    v.x v.y v.clean
  rw [eq] at canonical
  have value:=prior.2.1.symm.trans canonical.2.x
  rw [value] at fresh
  exact fresh

private theorem place_relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool) (hf : ∀q,q∉L.dialogPool → e q=q)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (renameProgram e P) m s=run P m s :=
  Square5Placement.pool_relabel_state_eq L e hp hf P s m before after

/-- Transport the complete State before taking any projection. -/
theorem place_run_eq (L : ControlledPointLayout) (hw : L.Widths)
    (P : Program) (s : State) (m : List Bool)
    (before : regValue L.dialogPool s.basis=0) (after : regValue L.dialogPool (run P m s).basis=0) :
    run (place L P) m s=run P m s := by
  have a0:=place_relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) P s m before after
  have a1:=place_relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw) (OwnPlusSquare.outside L hw)
    _ s m before (by rw [a0];exact after)
  have a2:=place_relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw) (OwnGuardSquare.outside L hw)
    _ s m before (by rw [a1,a0];exact after)
  have a3:=place_relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw) (OwnQ4Square.outside L hw)
    _ s m before (by rw [a2,a1,a0];exact after)
  have a4:=place_relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw) (OwnQ5Square.outside L hw)
    _ s m before (by rw [a3,a2,a1,a0];exact after)
  have a5:=place_relabel L (OwnDiagAll12PlacedQ6.swap L) (OwnDiagAll12PlacedQ6.pool L hw)
    (OwnDiagAll12PlacedQ6.outside L hw) _ s m before (by rw [a4,a3,a2,a1,a0];exact after)
  have a6:=place_relabel L (OwnDiagAll12PlacedQ7.swap L) (OwnDiagAll12PlacedQ7.pool L hw)
    (OwnDiagAll12PlacedQ7.outside L hw) _ s m before (by rw [a5,a4,a3,a2,a1,a0];exact after)
  have a7:=place_relabel L (PrefixFrontierSquare1591.swap L) (PrefixFrontierSquare1591.pool L hw)
    (PrefixFrontierSquare1591.outside L hw) _ s m before (by rw [a6,a5,a4,a3,a2,a1,a0];exact after)
  have a8:=place_relabel L (Prefix1590Square.swap L) (Prefix1590Square.pool L hw)
    (Prefix1590Square.outside L hw) _ s m before (by rw [a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  have a9:=place_relabel L (ControlLoan1589Square.swap L) (ControlLoan1589Square.pool L hw)
    (ControlLoan1589Square.outside L hw) _ s m before (by rw [a8,a7,a6,a5,a4,a3,a2,a1,a0];exact after)
  simpa only [place,a8,a7,a6,a5,a4,a3,a2,a1,a0] using a9


private theorem pool_away_x (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have dis:=(List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2
  intro hx
  have resident : q∈CompressedPointSquare.residents L := by
    simp only [CompressedPointSquare.residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis resident hq

theorem boundary (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) (s : State) (m : List Bool)
    (v : PointDialogValues L X Y G origin s.basis) :
    (run (program L) m s).phase=s.phase ∧
    regValue L.point.x (run (program L) m s).basis=
      p-1-(X-(if G then Y*Y else 0)+(if G then (SquareCarryLoan719BF.K:Fp) else 0)).val ∧
    ∀q,q∉L.point.x → (run (program L) m s).basis q=s.basis q := by
  have result:=fastCore_boundary L hw hn X Y G origin s m v
  obtain ⟨out,heq⟩ : ∃out : State,run (fastCore L) m s=out := ⟨_,rfl⟩
  rw [heq] at result
  have clean : regValue L.dialogPool out.basis=0 := by
    rw [regValue_congr _ _ s.basis (fun q hq=>result.2.2 q (pool_away_x L hn q hq)),v.clean]
  have eq:=place_run_eq L hw (fastCore L) s m v.clean (by rw [heq];exact clean)
  change run (program L) m s=run (fastCore L) m s at eq
  rw [eq,heq]
  exact result

theorem support_subset (L : ControlledPointLayout) :
    wires (program L)⊆wires (SquareCarryLoan719BF.program L) := by
  rw [program_split,wires_append]
  exact Finset.subset_union_left

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  (support_subset L).trans (SquareCarryLoan719BF.support L hw hn)

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  have old:=SquareCarryLoan719BF.physical L hw hn
  rw [program_split,gatePhysical_append] at old
  exact old.1

theorem free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i : Nat) (hi : i∈[1800,766,765,767,770,1285,1286,769,768,718,719]) :
    L.core.poolWire i∉wires (program L) := by
  by_cases h : i=719
  · subst i;exact fun used=>SquareCarryLoan719BF.retired_free719 L hw hn (support_subset L used)
  · exact fun used=>SquareCarryLoan719BF.square_free L hw hn i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto) (support_subset L used)

theorem place_counts (L : ControlledPointLayout) (P : Program) :
    toffoliCount (place L P)=toffoliCount P ∧ measurementCount (place L P)=measurementCount P := by
  simp only [place,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,and_self]

theorem reflectedTail_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (reflectedTail L)=255 ∧ measurementCount (reflectedTail L)=255 := by
  have r:=(L.dialogStreamedSquareWide.measured_small_operation_counts
    (L.dialogStreamedSquareWide_widths hw)).2.2
  simpa only [reflectedTail,(place_counts _ _).1,(place_counts _ _).2,reflection,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2] using r

theorem counts_delta (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)+255=toffoliCount (SquareCarryLoan719BF.program L) ∧
    measurementCount (program L)+255=measurementCount (SquareCarryLoan719BF.program L) := by
  rw [program_split,toffoliCount_append,measurementCount_append,
    (reflectedTail_counts L hw).1,(reflectedTail_counts L hw).2]
  exact ⟨rfl,rfl⟩

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=52004 ∧ measurementCount (program L)=52820 := by
  have d:=counts_delta L hw
  have c:=SquareCarryLoan719BF.counts L hw
  constructor <;> omega

theorem slots_le (L : ControlledPointLayout) :
    Challenge.gateSlots (program L)≤Challenge.gateSlots (SquareCarryLoan719BF.program L) := by
  rw [program_split,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.ReflectionE1Square
end -- original module boundary



-- Synthetic: close inherited anonymous MainC section at this file boundary.
end
end


set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option exponentiation.threshold 1024
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Entrant.ParkCopy.CrossBits
open Arithmetic

theorem cross_bound (v:Nat) (hv:v<2^64) : 2*(v%2^32)*(v/2^32)<2^65 := by
 have ha:v%2^32<2^32 := Nat.mod_lt _ (by positivity)
 have hb:v/2^32<2^32 := by norm_num at hv ⊢;omega
 have hh:=Nat.mul_lt_mul_of_lt_of_lt ha hb
 norm_num at hh ⊢
 nlinarith

theorem top_zero (r:List Wire) (hr:r.length=66) (v:Nat) (hv:v<2^64)
 (s:BasisState) (h:regValue r s=2*(v%2^32)*(v/2^32)) : s (r.getD 65 0)=false := by
 have hb:=regValue_bit r 65 0 s (by rw [hr];decide)
 rw [h,Nat.div_eq_of_lt (cross_bound v hv)] at hb
 simpa only [Nat.zero_mod,Bool.toNat_eq_zero] using hb


theorem outer_bound (a b:Nat) (ha:a<2^64) (hb:b<2^64) : 2*a*b<2^129 := by
 have h:=Nat.mul_lt_mul_of_lt_of_lt ha hb
 norm_num at h ⊢
 nlinarith

theorem outer_zero (r:List Wire) (hr:r.length=130) (a b:Nat) (ha:a<2^64) (hb:b<2^64)
 (s:BasisState) (h:regValue r s=2*a*b) : s (r.getD 129 0)=false := by
 have bit:=regValue_bit r 129 0 s (by rw [hr];decide)
 rw [h,Nat.div_eq_of_lt (outer_bound a b ha hb)] at bit
 simpa only [Nat.zero_mod,Bool.toNat_eq_zero] using bit

end ECDSAAdd.Entrant.ParkCopy.CrossBits

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Bank-bit parking for the 128-bit square leaves.

Four sites lie outside the producer registers: ext[131], ext[231], ext[298],
and ext[299]. Five further sites are zero at the producer boundary: ext[197]
and ext[297] are the top bits of 66-bit inner cross terms, ext[129] is the top
bit of the 130-bit outer cross term, and ext[132] and ext[232] are the low bits
of the even inner cross terms. These nine sites hold the bank suffix through
the body. Restoring the suffix with CX gates saves nine controlled recopies.
The inner and outer cross invariants are restored before producer cleanup. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ParkCopy.CrossBits
open Arithmetic

theorem low_zero (r:List Wire) (hr:0<r.length) (a b:Nat) (s:BasisState)
 (h:regValue r s=2*a*b) : s (r.getD 0 0)=false := by
 have bit:=regValue_bit r 0 0 s hr
 rw [h] at bit
 simpa only [pow_zero,Nat.div_one,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,
   Bool.toNat_eq_zero] using bit

end ECDSAAdd.Entrant.ParkCopy.CrossBits
namespace ECDSAAdd.Entrant.ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

def freeHostIdx : List Nat := [131,231,298,299]

def freeHosts (ext : List Wire) : List Wire := freeHostIdx.map (fun i => ext.getD i 0)

/-- Measurements of zero wires without corrections: they keep the record alignment. -/
def dummies (hs : List Wire) : Program := hs.map (fun h => Instr.measureX h [] [])

/-- Move a register into a zero register (and back): two CX passes. -/
def move (a b : List Wire) : Program := copyRegister none a b ++ copyRegister none b a

theorem freeHosts_length (ext : List Wire) : (freeHosts ext).length=4 := rfl

/-- Index characterisation of membership in a slice of a duplicate-free list. -/
theorem getD_mem_slice (l : List Wire) (hl : l.Nodup) (i a b : Nat) (hi : i<l.length) :
    l.getD i 0∈(l.drop a).take b ↔ a ≤ i ∧ i<a+b := by
  rw [List.getD_eq_getElem _ _ hi]
  constructor
  · intro h
    obtain ⟨j,hj,e⟩ := List.getElem_of_mem h
    simp only [List.getElem_take,List.getElem_drop] at e
    have := (List.Nodup.getElem_inj_iff hl).mp e
    simp only [List.length_take,List.length_drop] at hj
    omega
  · rintro ⟨h1,h2⟩
    have hj : i-a<((l.drop a).take b).length := by
      simp only [List.length_take,List.length_drop]; omega
    have e : ((l.drop a).take b)[i-a]'hj=l[i] := by
      simp only [List.getElem_take,List.getElem_drop]
      congr 1; omega
    rw [←e]; exact List.getElem_mem _

theorem getD_mem_take (l : List Wire) (hl : l.Nodup) (i b : Nat) (hi : i<l.length) :
    l.getD i 0∈l.take b ↔ i<b := by
  have h := getD_mem_slice l hl i 0 b hi
  simpa using h

theorem headD_take (l : List Wire) (k : Nat) (hk : 0<k) : (l.take k).headD 0=l.headD 0 := by
  cases l with
  | nil => simp
  | cons a l =>
    cases k with
    | zero => omega
    | succ k => simp

theorem getD_mem (l : List Wire) (i : Nat) (hi : i<l.length) : l.getD i 0∈l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

section Hosts
variable (ext : List Wire) (hx : ext.Nodup) (he : 300≤ext.length)

include he in
theorem freeHosts_sub : ∀h∈freeHosts ext,h∈ext := by
  intro h hh
  simp only [freeHosts,freeHostIdx,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl|rfl <;> exact getD_mem _ _ (by omega)

include hx he in
theorem freeHosts_nodup : (freeHosts ext).Nodup := by
  have inj (i j : Nat) (hi : i<ext.length) (hj : j<ext.length) (e : ext.getD i 0=ext.getD j 0) : i=j := by
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at e
    exact (List.Nodup.getElem_inj_iff hx).mp e
  simp only [freeHosts,freeHostIdx,List.map_cons,List.map_nil,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,List.nodup_nil,and_true]
  refine ⟨?_,?_,?_,?_⟩ <;> (try refine ⟨?_,?_⟩) <;> (try refine ⟨?_,?_⟩) <;> (try refine ⟨?_,?_⟩)
  all_goals first
    | (intro e; rcases e with e|e|e|e <;> (have := inj _ _ (by omega) (by omega) e; omega))
    | (intro e; rcases e with e|e|e <;> (have := inj _ _ (by omega) (by omega) e; omega))
    | (intro e; rcases e with e|e <;> (have := inj _ _ (by omega) (by omega) e; omega))
    | (intro e; have := inj _ _ (by omega) (by omega) e; omega)
    | trivial

/-- Each host index avoids all four `ext` slices used by the 128-bit leaf KG and `ext[0]`. -/
theorem idx_free (i : Nat) (hi : i∈freeHostIdx) :
    ¬ i < 131 ∧ ¬(132 ≤ i ∧ i<132+66) ∧ ¬(198 ≤ i ∧ i<198+33) ∧ ¬(232 ≤ i ∧ i<232+66) ∧ i≠0 ∧ i<300 := by
  simp only [freeHostIdx,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> omega

include hx he in
theorem host_not_T (h : Wire) (hh : h∈freeHosts ext) : h∉(ext.take 132).take 130 := by
  simp only [freeHosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  have f := idx_free i hi
  rw [List.take_take,show min 130 132=130 by omega,getD_mem_take ext hx i 130 (by have := f.2.2.2.2.2; omega)]
  have := f.1; omega

include hx he in
theorem host_not_iT (h : Wire) (hh : h∈freeHosts ext) : h∉(ext.drop 132).take 66 := by
  simp only [freeHosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [getD_mem_slice ext hx i 132 66 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.1

include hx he in
theorem host_not_jS (h : Wire) (hh : h∈freeHosts ext) : h∉((ext.drop 198).take 34).take 33 := by
  simp only [freeHosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [List.take_take,show min 33 34=33 by omega,
    getD_mem_slice ext hx i 198 33 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.2.1

include hx he in
theorem host_not_jT (h : Wire) (hh : h∈freeHosts ext) : h∉(ext.drop 232).take 66 := by
  simp only [freeHosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [getD_mem_slice ext hx i 232 66 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.2.2.1

include hx he in
theorem freeHost_ne_zero (h : Wire) (hh : h∈freeHosts ext) : h≠ext.getD 0 0 := by
  simp only [freeHosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  intro e
  have f := idx_free i hi
  rw [List.getD_eq_getElem _ _ (by have := f.2.2.2.2.2; omega),List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  exact f.2.2.2.2.1 this

end Hosts

section KGH
variable (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)

/-- For the 128-bit leaf, an `ext` wire outside the three inner slices is not a KG `X` wire. -/
theorem host_not_X (hx : ext.Nodup) (he : 300≤ext.length) (h128 : src.length=128)
    (hE : ∀q∈(LowZero18LowK.ktmp L),q∉ext) (h : Wire) (hh : h∈freeHosts ext) :
    h∉(LowZero18LowK.kg L ext src dst).X := by
  intro hX
  rw [LowZero18LowK.kg,if_pos h128] at hX
  simp only [KG.X,LowZero18LowK.kgH] at hX
  have hext := freeHosts_sub ext he h hh
  rcases List.mem_append.mp hX with hX|hX
  · rcases List.mem_append.mp hX with hX|hX
    · rcases List.mem_append.mp hX with hX|hX
      · exact hE h (List.mem_of_mem_drop (List.mem_of_mem_take (hX : h∈((LowZero18LowK.ktmp L).drop 66).take 33))) hext
      · exact host_not_iT ext hx he h hh hX
    · rcases List.mem_append.mp hX with hX|hX
      · exact host_not_jS ext hx he h hh hX
      · exact host_not_jT ext hx he h hh hX
  · exact List.not_mem_nil hX

theorem host_not_oT (hx : ext.Nodup) (he : 300≤ext.length) (h128 : src.length=128)
    (h : Wire) (hh : h∈freeHosts ext) : h∉(LowZero18LowK.oregs L ext src dst).T := by
  simp only [LowZero18LowK.oregs,h128]
  exact host_not_T ext hx he h hh

end KGH


def hostIdx : List Nat := [131,231,298,299,197,297,129,132,232]
def hosts (ext:List Wire) : List Wire := hostIdx.map (fun i=>ext.getD i 0)
theorem hosts_length (ext:List Wire) : (hosts ext).length=9 := rfl

theorem host_index (i:Nat) (hi:i∈hostIdx) : i<300 ∧ i≠0 := by
 simp only [hostIdx,List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem hosts_sub (ext:List Wire) (he:300≤ext.length) : ∀h∈hosts ext,h∈ext := by
 intro h hh
 obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hh
 exact getD_mem ext i (by have hh:=host_index i hi;omega)

theorem hosts_nodup (ext:List Wire) (hx:ext.Nodup) (he:300≤ext.length) : (hosts ext).Nodup := by
 unfold hosts
 apply List.Nodup.map_on
 · intro i hi j hj h
   have ilt:i<ext.length:=by have hh:=host_index i hi;omega
   have jlt:j<ext.length:=by have hh:=host_index j hj;omega
   rw [List.getD_eq_getElem _ _ ilt,List.getD_eq_getElem _ _ jlt] at h
   exact (List.Nodup.getElem_inj_iff hx).mp h
 · decide

theorem host_ne_zero (ext:List Wire) (hx:ext.Nodup) (he:300≤ext.length)
 (h:Wire) (hh:h∈hosts ext) : h≠ext.getD 0 0 := by
 obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hh
 intro e
 have hn:=host_index i hi
 rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
 exact hn.2 ((List.Nodup.getElem_inj_iff hx).mp e)

theorem hosts_split (ext:List Wire) (h:Wire) (hh:h∈hosts ext) :
 h∈freeHosts ext ∨ h=ext.getD 197 0 ∨ h=ext.getD 297 0 ∨ h=ext.getD 129 0 ∨ h=ext.getD 132 0 ∨ h=ext.getD 232 0 := by
 simpa only [hosts,hostIdx,freeHosts,freeHostIdx,List.map_cons,List.map_nil,
 List.mem_cons,List.not_mem_nil,or_false,or_assoc] using hh

/-! Program-shape lemmas. -/

theorem eraseMask_split (c : Wire) : ∀ (k : Nat) (src dst : List Wire), src.length=dst.length →
    eraseMask c src dst=eraseMask c (src.take k) (dst.take k)++eraseMask c (src.drop k) (dst.drop k)
  | 0, src, dst, _ => by simp [eraseMask]
  | k+1, [], dst, h => by
    have : dst=[] := List.eq_nil_of_length_eq_zero h.symm
    subst this; rfl
  | k+1, a::src, [], h => by simp at h
  | k+1, a::src, b::dst, h => by
    simp only [List.take_succ_cons,List.drop_succ_cons,eraseMask,List.cons_append]
    rw [eraseMask_split c k src dst (by simpa using h)]

theorem copyRegister_split (c : Option Wire) : ∀ (k : Nat) (src dst : List Wire), src.length=dst.length →
    copyRegister c src dst=copyRegister c (src.take k) (dst.take k)++copyRegister c (src.drop k) (dst.drop k)
  | 0, src, dst, _ => by simp [copyRegister]
  | k+1, [], dst, h => by
    have : dst=[] := List.eq_nil_of_length_eq_zero h.symm
    subst this; rfl
  | k+1, a::src, [], h => by simp at h
  | k+1, a::src, b::dst, h => by
    simp only [List.take_succ_cons,List.drop_succ_cons,copyRegister,List.cons_append,List.singleton_append]
    rw [copyRegister_split c k src dst (by simpa using h)]
    simp only [List.nil_append,List.append_assoc]

theorem dummies_run (hs : List Wire) (t : State) (m : List Bool)
    (h0 : ∀q∈hs,t.basis q=false) : run (dummies hs) m t=t := by
  induction hs generalizing t m with
  | nil => rfl
  | cons a hs ih =>
    have ha : t.basis a=false := h0 a (by simp)
    have step : measureAndCorrect a [] [] (m.headD false) t=t := by
      apply State.extensionality
      · cases m.headD false <;> simp [measureAndCorrect,correct,ha]
      · funext q
        by_cases e : q=a
        · subst e; cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,ha]
        · cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,e]
    change run (dummies hs) m.tail (measureAndCorrect a [] [] (m.headD false) t)=t
    rw [step]
    exact ih t m.tail (fun q hq => h0 q (by simp [hq]))

theorem dummies_counts (hs : List Wire) :
    toffoliCount (dummies hs)=0 ∧ measurementCount (dummies hs)=hs.length := by
  induction hs with
  | nil => exact ⟨rfl,rfl⟩
  | cons a hs ih =>
    constructor
    · change toffoliCount (Instr.measureX a [] [] :: dummies hs)=0
      simpa [toffoliCount] using ih.1
    · have h := ih.2
      change measurementCount (Instr.measureX a [] [] :: dummies hs)=hs.length+1
      simp [measurementCount]
      omega

end ECDSAAdd.Entrant.ParkCopy

/-! Part B: the parked 128-bit leaf and its correctness (appended after part A). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

section Pieces
variable (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
  (body : Program)

def pA : Program := copyRegister (some control) src (L.inputBank.take src.length)
def pM : Program := LowZero18Square.make L (LowZero18LowK.kg L ext src dst)
def pE1 : Program := eraseMask control (src.take 119) ((L.inputBank.take src.length).take 119)
def pD : Program := dummies (hosts ext)
def pMI : Program := move ((L.inputBank.take src.length).drop 119) (hosts ext)
def pB : Program := renameProgram (LowZero18Square.foldPerm L ext) body
def pC1 : Program := CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) (src.take 119) ((L.inputBank.take src.length).take 119)
def pMO : Program := move (hosts ext) ((L.inputBank.take src.length).drop 119)
def pCL : Program := LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)
def pE : Program := eraseMask control src (L.inputBank.take src.length)

/-- The 128-bit leaf with its last nine bank bits parked on zero extension wires. -/
def withLowK2P : Program :=
  pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++
    pC1 L control src dst++pMO L ext src++pCL L ext src dst++pE L control src

end Pieces

private theorem xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem move_correct (a b : List Wire) (hl : a.length=b.length) (hnd : (a++b).Nodup)
    (t : State) (m : List Bool) (hb : regValue b t.basis=0) :
    (run (move a b) m t).phase=t.phase ∧
    (∀w,w∉a → w∉b → (run (move a b) m t).basis w=t.basis w) ∧
    regValue b (run (move a b) m t).basis=regValue a t.basis ∧
    regValue a (run (move a b) m t).basis=0 := by
  have hnd' : (b++a).Nodup := (List.perm_append_comm.nodup_iff).mp hnd
  unfold move
  rw [run_append]
  obtain ⟨p1,f1,v1⟩ := copyRegister_correct none a b hl hnd (by simp) t (m.take (measurementCount (copyRegister none a b)))
  generalize run (copyRegister none a b) (m.take (measurementCount (copyRegister none a b))) t=t1 at p1 f1 v1
  obtain ⟨p2,f2,v2⟩ := copyRegister_correct none b a hl.symm hnd' (by simp) t1 (m.drop (measurementCount (copyRegister none a b)))
  generalize run (copyRegister none b a) (m.drop (measurementCount (copyRegister none a b))) t1=t2 at p2 f2 v2
  have aDisj : ∀w∈a,w∉b := fun w hw hwb => by
    have := List.nodup_append.mp hnd
    exact this.2.2 w hw w hwb rfl
  have v1' : regValue b t1.basis=regValue a t.basis := by
    rw [v1,hb,Nat.zero_xor]; rfl
  have a1 : regValue a t1.basis=regValue a t.basis :=
    regValue_congr _ _ _ (fun w hw => f1 w (aDisj w hw))
  refine ⟨p2.trans p1,fun w ha hb' => (f2 w ha).trans (f1 w hb'),?_,?_⟩
  · rw [←v1']
    exact regValue_congr _ _ _ (fun w hw => f2 w (fun ha => aDisj w ha hw))
  · rw [v2]
    change regValue a t1.basis ^^^ regValue b t1.basis=0
    rw [a1,v1',Nat.xor_self]

end ECDSAAdd.Entrant.ParkCopy


namespace ECDSAAdd.Entrant.ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

open LowZero18Square in
theorem withLowK2P_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (h128' : src.length=128)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (withLowK2P L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2P L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2P L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have cacheFix : earlyPerm L (dst.headD 0)=dst.headD 0 := by
    have mem : dst.headD 0∈dst := by
      rcases dst with _|⟨d,ds⟩
      · have hz : src.length=0 := by simpa using hlen.symm
        omega
      · exact List.mem_cons_self
    have targetM : target L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (fun e => tmpD _ targetM (by simpa only [e] using mem))
      (fun e => tmpD _ hostM (by simpa only [e] using mem))
  let P := if s.basis control then regValue src s.basis else 0
  -- parking data
  have Blen : (L.inputBank.take src.length).length=128 := by rw [inputLen,h128']
  have hHx : ∀h∈hosts ext,h∈ext := hosts_sub ext he
  have hHnd : (hosts ext).Nodup := hosts_nodup ext hx he
  have hHT : ∀h∈freeHosts ext,h∉(LowZero18LowK.oregs L ext src dst).T := fun h hh => host_not_oT L ext src dst hx he h128' h hh
  have hHX : ∀h∈freeHosts ext,h∉(LowZero18LowK.kg L ext src dst).X := fun h hh => host_not_X L ext src dst hx he h128' tmpE h hh
  have hH0 : ∀h∈hosts ext,h≠ext.getD 0 0 := host_ne_zero ext hx he
  have hHB : ∀h∈hosts ext,h∉(L.inputBank.take src.length) := fun h hh => extB h (hHx h hh)
  have hHD : ∀h∈hosts ext,h∉dst := fun h hh => extD h (hHx h hh)
  have hHo : ∀h∈hosts ext,h∉L.core.out := fun h hh => extOut h (hHx h hh)
  have hHs : ∀q∈src,q∉hosts ext := fun q hq hh => extSrc q (hHx q hh) hq
  have ctlH : control∉hosts ext := fun h => ctlE (hHx _ h)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have b15 : ∀q∈(L.inputBank.take src.length).take 119,q∉(L.inputBank.take src.length).drop 119 := by
    intro q h1 h5
    have nd : ((L.inputBank.take src.length).take 119++(L.inputBank.take src.length).drop 119).Nodup := by
      rw [List.take_append_drop]; exact bNd
    exact (List.nodup_append.mp nd).2.2 q h1 q h5 rfl
  have b51 : ∀q∈(L.inputBank.take src.length).drop 119,q∉(L.inputBank.take src.length).take 119 :=
    fun q h5 h1 => b15 q h1 h5
  have ndMI : ((L.inputBank.take src.length).drop 119++hosts ext).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => hHB b hb (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (hosts ext++(L.inputBank.take src.length).drop 119).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  have lenMI : ((L.inputBank.take src.length).drop 119).length=(hosts ext).length := by
    rw [List.length_drop,Blen,hosts_length]
  obtain ⟨a9,r10,e10⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src++pCL L ext src dst) (pE L control src) records s
  obtain ⟨a8,r9,e9⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src) (pCL L ext src dst) a9 s
  obtain ⟨a7,r8,e8⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst) (pMO L ext src) a8 s
  obtain ⟨a6,r7,e7⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body) (pC1 L control src dst) a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src) (pB L ext body) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext) (pMI L ext src) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src) (pD ext) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (pA L control src++pM L ext src dst) (pE1 L control src) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (pA L control src) (pM L ext src dst) a2 s
  rw [show withLowK2P L ext control src dst body=pA L control src++pM L ext src dst++pE1 L control src++pD ext++
    pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src++pCL L ext src dst++pE L control src from rfl,
    e10,e9,e8,e7,e6,e5,e4,e3,e2]
  simp only [pA,pM,pE1,pD,pMI,pB,pC1,pMO,pCL,pE]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- hosts stay zero through the copy and the producer
  have loLen : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).1]
    rfl
  have hiLen : (LowZero18LowK.oregs L ext src dst).hi.length=64 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).2.1]
    change (L.inputBank.take src.length).length-64=64
    rw [Blen]
  have loBound : regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis<2^64 := by
    simpa only [loLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
  have hiBound : regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^64 := by
    simpa only [hiLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
  have inv1:=mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at inv1
  have inv2:=mk.2.2.2.2.2.1
  simp only [LowZero18LowK.kg,if_pos h128',LowZero18LowK.kgH] at inv2
  have itLen : (LowZero18LowK.iregs L ext src dst).T.length=66 := by
    simp only [LowZero18LowK.iregs,List.length_take,List.length_drop]
    omega
  have jtLen : (LowZero18LowK.jregsH L ext src dst).T.length=66 := by
    simp only [LowZero18LowK.jregsH,List.length_take,List.length_drop]
    omega
  have iz:=CrossBits.top_zero (LowZero18LowK.iregs L ext src dst).T itLen
    (regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis) loBound u1.basis inv1.2
  have jz:=CrossBits.top_zero (LowZero18LowK.jregsH L ext src dst).T jtLen
    (regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis) hiBound u1.basis inv2.2
  have slice_get (a n i:Nat) (hi:i<n) (ha:a+i<ext.length) :
      ((ext.drop a).take n).getD i 0=ext.getD (a+i) 0 := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take,List.length_drop];omega),
      List.getD_eq_getElem _ _ ha]
    simp only [List.getElem_take,List.getElem_drop]
  simp only [LowZero18LowK.iregs] at iz
  simp only [LowZero18LowK.jregsH] at jz
  rw [slice_get 132 66 65 (by omega) (by omega)] at iz
  rw [slice_get 232 66 65 (by omega) (by omega)] at jz
  have otLen : (LowZero18LowK.oregs L ext src dst).T.length=130 := by
    simp only [LowZero18LowK.oregs,h128',List.length_take]
    omega
  have oz:=CrossBits.outer_zero (LowZero18LowK.oregs L ext src dst).T otLen
    (regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)
    (regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis) loBound hiBound u1.basis mk.2.2.2.1
  have otget : (LowZero18LowK.oregs L ext src dst).T.getD 129 0=ext.getD 129 0 := by
    simp only [LowZero18LowK.oregs,h128']
    rw [List.take_take]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take];omega),
      List.getD_eq_getElem _ _ (by omega)]
    simp only [List.getElem_take]
  rw [otget] at oz
  have iz0:=CrossBits.low_zero (LowZero18LowK.iregs L ext src dst).T (by rw [itLen];decide)
    ((regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)%2^32)
    ((regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)/2^32) u1.basis inv1.2
  have jz0:=CrossBits.low_zero (LowZero18LowK.jregsH L ext src dst).T (by rw [jtLen];decide)
    ((regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis)%2^32)
    ((regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis)/2^32) u1.basis inv2.2
  simp only [LowZero18LowK.iregs] at iz0
  simp only [LowZero18LowK.jregsH] at jz0
  rw [slice_get 132 66 0 (by omega) (by omega)] at iz0
  rw [slice_get 232 66 0 (by omega) (by omega)] at jz0
  have hU1 : ∀h∈hosts ext,u1.basis h=false := by
    intro h hh
    rcases hosts_split ext h hh with hf|rfl|rfl|rfl|rfl|rfl
    · exact (u1s h (hHD h hh) (hHT h hf) (hHX h hf)).trans
        ((u0s h (hHB h hh)).trans (ext0 h (hHx h hh)))
    · exact iz
    · exact jz
    · exact oz
    · exact iz0
    · exact jz0
  have srcw1 : ∀q∈src,u1.basis q=s.basis q := fun q hq =>
    (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq))
  have mask1 : regValue ((L.inputBank.take src.length).take 119) u1.basis=
      if u1.basis control then regValue (src.take 119) u1.basis else 0 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ 119 (by rw [inputLen]; omega) u1.basis,bank1,
      CuccaroStreamedSquareWideLayout.regValue_take_mod src 119 (by omega) u1.basis,ctl1,src1]
    simp only [P]
    split_ifs <;> simp
  -- erase only the first 119 bank bits
  have ndMask1 : (control::(src.take 119++(L.inputBank.take src.length).take 119)).Nodup :=
    ndMask.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _)))
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control (src.take 119) ((L.inputBank.take src.length).take 119)
    (by simp only [List.length_take,inputLen]) ndMask1 u1 r3 mask1
  generalize run (eraseMask control (src.take 119) ((L.inputBank.take src.length).take 119)) r3 u1=u2a at ep1 ef1 ev1 ⊢
  -- record-preserving dummies on the (zero) hosts
  have hU2a : ∀h∈hosts ext,u2a.basis h=false := fun h hh =>
    (ef1 h (fun hb => hHB h hh (List.mem_of_mem_take hb))).trans (hU1 h hh)
  rw [dummies_run (hosts ext) u2a r4 hU2a]
  -- park the last four bank bits on the hosts
  obtain ⟨mp1,mf1,mv1,mz1⟩ := move_correct ((L.inputBank.take src.length).drop 119) (hosts ext) lenMI ndMI u2a r5
    ((regValue_zero _ _).mpr hU2a)
  generalize run (move ((L.inputBank.take src.length).drop 119) (hosts ext)) r5 u2a=u2 at mp1 mf1 mv1 mz1 ⊢
  have x5 : regValue (hosts ext) u2.basis=regValue ((L.inputBank.take src.length).drop 119) u1.basis := by
    rw [mv1]; exact regValue_congr _ _ _ (fun q hq => ef1 q (b51 q hq))
  have u2B : ∀q∈(L.inputBank.take src.length),u2.basis q=false := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 119 ∨ q∈(L.inputBank.take src.length).drop 119 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · rw [mf1 q (b15 q h1) (fun hh => hHB q hh hq)]; exact (regValue_zero _ _).mp ev1 q h1
    · exact (regValue_zero _ _).mp mz1 q h5
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx'
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact (u2B q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [mf1 q (fun h => hb (List.mem_of_mem_drop h)) (fun h => hx' (hHx q h)),
        ef1 q (fun h => hb (List.mem_of_mem_take h))]
      exact (u1z q hq hx').trans (u0s q hb)
  have u2ext : ∀q∈ext,q∉hosts ext → u2.basis q=u1.basis q := fun q h hH =>
    (mf1 q (fun h5 => extB q h (List.mem_of_mem_drop h5)) hH).trans (ef1 q (fun h1 => extB q h (List.mem_of_mem_take h1)))
  have u2u1 : ∀q,q∉(L.inputBank.take src.length) → q∉hosts ext → u2.basis q=u1.basis q := fun q hb hH =>
    (mf1 q (fun h => hb (List.mem_of_mem_drop h)) hH).trans (ef1 q (fun h => hb (List.mem_of_mem_take h)))
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact u2u1 q (fun h => bD q h hq) (fun h => hHD q h hq)
  have cb := callback u2' r6 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r6 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r6 u2'=v' at cb loc
  generalize hv : run body r6 u2=v at loc
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r6 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r6 u2 q hb,run_preserves_outside body r6 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r6 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember (fun hm => hH0 _ hm rfl)).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r6 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
  -- second copy
  have vDst : regValue dst v.basis=P^2 := by
    calc
      regValue dst v.basis = regValue dst u2.basis :=
        regValue_congr _ _ _ (fun q hq => vFrame q (dOut q hq))
      _ = regValue dst u1.basis :=
        regValue_congr _ _ _ (fun q hq => u2u1 q (fun hb => bD q hb hq) (fun h => hHD q h hq))
      _ = P^2 := dst1
  have vControl : v.basis control=s.basis control :=
    (vFrame _ ctlO).trans (u2s _ ctlD ctlE)
  have vSource : regValue src v.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq =>
      (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq)))
  have cached : v.basis (dst.headD 0)=(v.basis control && v.basis (src.headD 0)) :=
    CachedSquareCopy.square_head src dst control v (by omega) (by omega)
      (by simpa only [P,vControl,vSource] using vDst)
  rw [cacheWire,cacheFix,CachedSquareCopy.run_eq control (dst.headD 0) (src.take 119) ((L.inputBank.take src.length).take 119) v r7
    (by rw [headD_take src 119 (by omega)]; exact cached)]
  have inputLen1 : (src.take 119).length=((L.inputBank.take src.length).take 119).length := by
    simp only [List.length_take,inputLen]
  have ndCopy1 : (src.take 119++(L.inputBank.take src.length).take 119).Nodup :=
    ndCopy.sublist (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _))
  have hcB1 : ∀c∈some control,c∉(L.inputBank.take src.length).take 119 := fun c hc' h =>
    hcB c hc' (List.mem_of_mem_take h)
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) (src.take 119) ((L.inputBank.take src.length).take 119)
    inputLen1 ndCopy1 hcB1 v r7
  generalize run (copyRegister (some control) (src.take 119) ((L.inputBank.take src.length).take 119)) r7 v=w0' at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have w0'B5 : regValue ((L.inputBank.take src.length).drop 119) w0'.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (cf2 q (b51 q hq)).trans ((vB q (List.mem_of_mem_drop hq)).trans
      ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_drop hq))))
  -- unpark: hosts back into the bank, hosts cleared
  obtain ⟨mp2,mf2,mv2,mz2⟩ := move_correct (hosts ext) ((L.inputBank.take src.length).drop 119) lenMI.symm ndMO w0' r8 w0'B5
  generalize run (move (hosts ext) ((L.inputBank.take src.length).drop 119)) r8 w0'=w0 at mp2 mf2 mv2 mz2 ⊢
  have cf2n : ∀q,q∉(L.inputBank.take src.length) → q∉hosts ext → w0.basis q=v.basis q := fun q hb hH =>
    (mf2 q hH (fun h => hb (List.mem_of_mem_drop h))).trans (cf2 q (fun h => hb (List.mem_of_mem_take h)))
  have w0B5 : regValue ((L.inputBank.take src.length).drop 119) w0.basis=
      regValue ((L.inputBank.take src.length).drop 119) u1.basis := by
    rw [mv2,←x5]
    apply regValue_congr; intro q hq
    rw [cf2 q (fun h => hHB q hq (List.mem_of_mem_take h)),vIn q (hHx q hq)]
  have vCtl1 : v.basis control=u1.basis control := (vFrame _ ctlO).trans ((u2s _ ctlD ctlE).trans ctl1.symm)
  have w0B1 : regValue ((L.inputBank.take src.length).take 119) w0.basis=
      regValue ((L.inputBank.take src.length).take 119) u1.basis := by
    have v0 : regValue ((L.inputBank.take src.length).take 119) v.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (vB q (List.mem_of_mem_take hq)).trans
        ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_take hq)))
    have vs1 : regValue (src.take 119) v.basis=regValue (src.take 119) u1.basis :=
      regValue_congr _ _ _ (fun q hq => (vSrc q (List.mem_of_mem_take hq)).trans (srcw1 q (List.mem_of_mem_take hq)).symm)
    rw [show regValue ((L.inputBank.take src.length).take 119) w0.basis=
        regValue ((L.inputBank.take src.length).take 119) w0'.basis from
      regValue_congr _ _ _ (fun q hq => mf2 q (fun h => hHB q h (List.mem_of_mem_take hq)) (b15 q hq)),
      cv2,mask1,v0,Nat.zero_xor]
    change (if v.basis control then regValue (src.take 119) v.basis else 0)=_
    rw [vCtl1,vs1]
  have wB : ∀q∈(L.inputBank.take src.length),w0.basis q=u1.basis q := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 119 ∨ q∈(L.inputBank.take src.length).drop 119 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · exact (regValue_eq_iff _ _ _).mp w0B1 q h1
    · exact (regValue_eq_iff _ _ _).mp w0B5 q h5
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := (regValue_congr _ _ _ wB).trans bank1
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    by_cases hH : q∈hosts ext
    · rw [(regValue_zero _ _).mp mz2 q hH,hU1 q hH]
    · rw [cf2n q hb hH,vFrame q ho]
      by_cases hx' : q∈ext
      · exact u2ext q hx' hH
      · exact u2u1 q hb hH
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r9
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r9
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r9 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2n q (srcB q hq) (hHs q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2n _ ctlB ctlH).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r10 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r10 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (mp2.trans (cp2.trans (vPhase.trans (mp1.trans (ep1.trans (mk.1.trans cp1))))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2n q (fun h => bOut q h hq) (fun h => hHo q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX]
      by_cases hH : q∈hosts ext
      · rw [(regValue_zero _ _).mp mz2 q hH]; exact (ext0 q (hHx q hH)).symm
      rw [cf2n q hb hH,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx hH,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx

end ECDSAAdd.Entrant.ParkCopy

#print axioms ECDSAAdd.Entrant.ParkCopy.withLowK2P_correct

set_option exponentiation.threshold 1024
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option exponentiation.threshold 1024
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.CKDonors
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem bit_zero (r:List Wire) (i:Nat) (hi:i<r.length) (s:BasisState)
 (h:regValue r s<2^i) : s (r.getD i 0)=false := by
 have b:=regValue_bit r i 0 s hi
 rw [Nat.div_eq_of_lt h] at b
 simpa only [Nat.zero_mod,Bool.toNat_eq_zero] using b

theorem even_zero (r:List Wire) (hr:0<r.length) (a b:Nat) (s:BasisState)
 (h:regValue r s=2*a*b) : s (r.getD 0 0)=false := by
 have bit:=regValue_bit r 0 0 s hr
 rw [h] at bit
 simpa only [pow_zero,Nat.div_one,Nat.mul_mod,Nat.mod_self,Nat.zero_mul,Nat.zero_mod,
   Bool.toNat_eq_zero] using bit

theorem cross_bound (v k:Nat) (hv:v<2^(2*k)) :
 2*(v%2^k)*(v/2^k)<2^(2*k+1) := by
 have ha:v%2^k<2^k:=Nat.mod_lt _ (by positivity)
 have hb:v/2^k<2^k := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  simpa only [pow_add,two_mul] using hv
 have h:=Nat.mul_lt_mul_of_lt_of_lt ha hb
 rw [pow_add,pow_one]
 rw [show 2^(2*k)=2^k*2^k by rw [two_mul,pow_add]]
 nlinarith

theorem donors_zero (L:CuccaroStreamedSquareWideLayout) (ext src dst:List Wire)
 (hs:src.length=129) (he:300≤ext.length) (a b:Nat) (ha:a<2^64) (hb:b<2^65)
 (s:BasisState)
 (ot:regValue (LowZero18LowK.oregs L ext src dst).T s=2*a*b)
 (i1:(LowZero18LowK.iregs L ext src dst).invC a s)
 (i5:(LowZero18LowK.jregsS L ext src dst).invF (a+b) s) :
 ∀q∈([131,132,197,232,299]:List Nat),s (ext.getD q 0)=false := by
 have ab:a+b<2^66:=by norm_num at ha hb ⊢;omega
 have out:2*a*b<2^131:=by
  have h:=Nat.mul_lt_mul_of_lt_of_lt ha hb
  norm_num at h ⊢;nlinarith
 have it:regValue (LowZero18LowK.iregs L ext src dst).T s<2^65:=by
  rw [i1.2];exact cross_bound a 32 (by simpa using ha)
 have jt:regValue (LowZero18LowK.jregsS L ext src dst).T s<2^67:=by
  rw [i5.2];exact cross_bound (a+b) 33 (by simpa using ab)
 have iz:=bit_zero _ 65 (by simp [LowZero18LowK.iregs,List.length_take,List.length_drop];omega) s it
 have jz:=bit_zero _ 67 (by simp [LowZero18LowK.jregsS,List.length_take,List.length_drop];omega) s jt
 have oz:=bit_zero _ 131 (by simp [LowZero18LowK.oregs,hs,List.length_take];omega) s (ot ▸ out)
 have iz0:=even_zero _ (by simp [LowZero18LowK.iregs,List.length_take,List.length_drop];omega) _ _ s i1.2
 have jz0:=even_zero _ (by simp [LowZero18LowK.jregsS,List.length_take,List.length_drop];omega) _ _ s i5.2
 have get (n k i:Nat) (hi:i<k) (hni:n+i<ext.length) :
  ((ext.drop n).take k).getD i 0=ext.getD (n+i) 0:=by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_take,List.length_drop];omega),List.getD_eq_getElem _ _ hni]
  simp only [List.getElem_take,List.getElem_drop]
 simp only [LowZero18LowK.iregs] at iz iz0
 simp only [LowZero18LowK.jregsS] at jz jz0
 rw [get 132 66 65 (by omega) (by omega)] at iz
 rw [get 132 66 0 (by omega) (by omega)] at iz0
 rw [get 232 68 67 (by omega) (by omega)] at jz
 rw [get 232 68 0 (by omega) (by omega)] at jz0
 have og:(LowZero18LowK.oregs L ext src dst).T.getD 131 0=ext.getD 131 0:=by
  simp only [LowZero18LowK.oregs,hs,List.take_take]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_take];omega),List.getD_eq_getElem _ _ (by omega)]
  simp only [List.getElem_take]
 rw [og] at oz
 intro q hq
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl|rfl|rfl
 · exact oz
 · exact iz0
 · exact iz
 · exact jz0
 · exact jz
#print axioms donors_zero
end ECDSAAdd.Entrant.CKDonors
namespace ECDSAAdd.Entrant.CKParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

/-- Measurements of zero wires without corrections: they keep the record alignment. -/
def dummies (hs : List Wire) : Program := hs.map (fun h => Instr.measureX h [] [])

/-- Move a register into a zero register (and back): two CX passes. -/
def move (a b : List Wire) : Program := copyRegister none a b ++ copyRegister none b a

/-- Index characterisation of membership in a slice of a duplicate-free list. -/
theorem getD_mem_slice (l : List Wire) (hl : l.Nodup) (i a b : Nat) (hi : i<l.length) :
    l.getD i 0∈(l.drop a).take b ↔ a ≤ i ∧ i<a+b := by
  rw [List.getD_eq_getElem _ _ hi]
  constructor
  · intro h
    obtain ⟨j,hj,e⟩ := List.getElem_of_mem h
    simp only [List.getElem_take,List.getElem_drop] at e
    have := (List.Nodup.getElem_inj_iff hl).mp e
    simp only [List.length_take,List.length_drop] at hj
    omega
  · rintro ⟨h1,h2⟩
    have hj : i-a<((l.drop a).take b).length := by
      simp only [List.length_take,List.length_drop]; omega
    have e : ((l.drop a).take b)[i-a]'hj=l[i] := by
      simp only [List.getElem_take,List.getElem_drop]
      congr 1; omega
    rw [←e]; exact List.getElem_mem _

theorem getD_mem_take (l : List Wire) (hl : l.Nodup) (i b : Nat) (hi : i<l.length) :
    l.getD i 0∈l.take b ↔ i<b := by
  have h := getD_mem_slice l hl i 0 b hi
  simpa using h

theorem headD_take (l : List Wire) (k : Nat) (hk : 0<k) : (l.take k).headD 0=l.headD 0 := by
  cases l with
  | nil => simp
  | cons a l =>
    cases k with
    | zero => omega
    | succ k => simp

theorem getD_mem (l : List Wire) (i : Nat) (hi : i<l.length) : l.getD i 0∈l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

def hostIdx : List Nat := [131,132,197,232,299]
def hosts (ext:List Wire) : List Wire := hostIdx.map (fun i=>ext.getD i 0)
theorem hosts_length (ext:List Wire) : (hosts ext).length=5 := rfl

theorem host_index (i:Nat) (hi:i∈hostIdx) : i<300 ∧ i≠0 := by
 simp only [hostIdx,List.mem_cons,List.not_mem_nil,or_false] at hi
 rcases hi with rfl|rfl|rfl|rfl|rfl <;> omega

theorem hosts_sub (ext:List Wire) (he:300≤ext.length) : ∀h∈hosts ext,h∈ext := by
 intro h hh
 obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hh
 exact getD_mem ext i (by have hh:=host_index i hi;omega)

theorem hosts_nodup (ext:List Wire) (hx:ext.Nodup) (he:300≤ext.length) : (hosts ext).Nodup := by
 unfold hosts
 apply List.Nodup.map_on
 · intro i hi j hj h
   have ilt:i<ext.length:=by have hh:=host_index i hi;omega
   have jlt:j<ext.length:=by have hh:=host_index j hj;omega
   rw [List.getD_eq_getElem _ _ ilt,List.getD_eq_getElem _ _ jlt] at h
   exact (List.Nodup.getElem_inj_iff hx).mp h
 · decide

theorem host_ne_zero (ext:List Wire) (hx:ext.Nodup) (he:300≤ext.length)
 (h:Wire) (hh:h∈hosts ext) : h≠ext.getD 0 0 := by
 obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hh
 intro e
 have hn:=host_index i hi
 rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)] at e
 exact hn.2 ((List.Nodup.getElem_inj_iff hx).mp e)

/-! Program-shape lemmas. -/

theorem eraseMask_split (c : Wire) : ∀ (k : Nat) (src dst : List Wire), src.length=dst.length →
    eraseMask c src dst=eraseMask c (src.take k) (dst.take k)++eraseMask c (src.drop k) (dst.drop k)
  | 0, src, dst, _ => by simp [eraseMask]
  | k+1, [], dst, h => by
    have : dst=[] := List.eq_nil_of_length_eq_zero h.symm
    subst this; rfl
  | k+1, a::src, [], h => by simp at h
  | k+1, a::src, b::dst, h => by
    simp only [List.take_succ_cons,List.drop_succ_cons,eraseMask,List.cons_append]
    rw [eraseMask_split c k src dst (by simpa using h)]

theorem copyRegister_split (c : Option Wire) : ∀ (k : Nat) (src dst : List Wire), src.length=dst.length →
    copyRegister c src dst=copyRegister c (src.take k) (dst.take k)++copyRegister c (src.drop k) (dst.drop k)
  | 0, src, dst, _ => by simp [copyRegister]
  | k+1, [], dst, h => by
    have : dst=[] := List.eq_nil_of_length_eq_zero h.symm
    subst this; rfl
  | k+1, a::src, [], h => by simp at h
  | k+1, a::src, b::dst, h => by
    simp only [List.take_succ_cons,List.drop_succ_cons,copyRegister,List.cons_append,List.singleton_append]
    rw [copyRegister_split c k src dst (by simpa using h)]
    simp only [List.nil_append,List.append_assoc]

theorem dummies_run (hs : List Wire) (t : State) (m : List Bool)
    (h0 : ∀q∈hs,t.basis q=false) : run (dummies hs) m t=t := by
  induction hs generalizing t m with
  | nil => rfl
  | cons a hs ih =>
    have ha : t.basis a=false := h0 a (by simp)
    have step : measureAndCorrect a [] [] (m.headD false) t=t := by
      apply State.extensionality
      · cases m.headD false <;> simp [measureAndCorrect,correct,ha]
      · funext q
        by_cases e : q=a
        · subst e; cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,ha]
        · cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,e]
    change run (dummies hs) m.tail (measureAndCorrect a [] [] (m.headD false) t)=t
    rw [step]
    exact ih t m.tail (fun q hq => h0 q (by simp [hq]))

theorem dummies_counts (hs : List Wire) :
    toffoliCount (dummies hs)=0 ∧ measurementCount (dummies hs)=hs.length := by
  induction hs with
  | nil => exact ⟨rfl,rfl⟩
  | cons a hs ih =>
    constructor
    · change toffoliCount (Instr.measureX a [] [] :: dummies hs)=0
      simpa [toffoliCount] using ih.1
    · have h := ih.2
      change measurementCount (Instr.measureX a [] [] :: dummies hs)=hs.length+1
      simp [measurementCount]
      omega

end ECDSAAdd.Entrant.CKParkCopy

/-! Part B: the parked 128-bit leaf and its correctness (appended after part A). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.CKParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

section Pieces
variable (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
  (body : Program)

def pA : Program := copyRegister (some control) src (L.inputBank.take src.length)
def pM : Program := LowZero18Square.make L (LowZero18LowK.kg L ext src dst)
def pE1 : Program := eraseMask control (src.take 124) ((L.inputBank.take src.length).take 124)
def pD : Program := dummies (hosts ext)
def pMI : Program := move ((L.inputBank.take src.length).drop 124) (hosts ext)
def pB : Program := renameProgram (LowZero18Square.foldPerm L ext) body
def pC1 : Program := CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) (src.take 124) ((L.inputBank.take src.length).take 124)
def pMO : Program := move (hosts ext) ((L.inputBank.take src.length).drop 124)
def pCL : Program := LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)
def pE : Program := eraseMask control src (L.inputBank.take src.length)

/-- The 129-bit leaf with its last five bank bits parked on zero extension wires. -/
def withLowK2P : Program :=
  pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++
    pC1 L control src dst++pMO L ext src++pCL L ext src dst++pE L control src

end Pieces

private theorem xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem move_correct (a b : List Wire) (hl : a.length=b.length) (hnd : (a++b).Nodup)
    (t : State) (m : List Bool) (hb : regValue b t.basis=0) :
    (run (move a b) m t).phase=t.phase ∧
    (∀w,w∉a → w∉b → (run (move a b) m t).basis w=t.basis w) ∧
    regValue b (run (move a b) m t).basis=regValue a t.basis ∧
    regValue a (run (move a b) m t).basis=0 := by
  have hnd' : (b++a).Nodup := (List.perm_append_comm.nodup_iff).mp hnd
  unfold move
  rw [run_append]
  obtain ⟨p1,f1,v1⟩ := copyRegister_correct none a b hl hnd (by simp) t (m.take (measurementCount (copyRegister none a b)))
  generalize run (copyRegister none a b) (m.take (measurementCount (copyRegister none a b))) t=t1 at p1 f1 v1
  obtain ⟨p2,f2,v2⟩ := copyRegister_correct none b a hl.symm hnd' (by simp) t1 (m.drop (measurementCount (copyRegister none a b)))
  generalize run (copyRegister none b a) (m.drop (measurementCount (copyRegister none a b))) t1=t2 at p2 f2 v2
  have aDisj : ∀w∈a,w∉b := fun w hw hwb => by
    have := List.nodup_append.mp hnd
    exact this.2.2 w hw w hwb rfl
  have v1' : regValue b t1.basis=regValue a t.basis := by
    rw [v1,hb,Nat.zero_xor]; rfl
  have a1 : regValue a t1.basis=regValue a t.basis :=
    regValue_congr _ _ _ (fun w hw => f1 w (aDisj w hw))
  refine ⟨p2.trans p1,fun w ha hb' => (f2 w ha).trans (f1 w hb'),?_,?_⟩
  · rw [←v1']
    exact regValue_congr _ _ _ (fun w hw => f2 w (fun ha => aDisj w ha hw))
  · rw [v2]
    change regValue a t1.basis ^^^ regValue b t1.basis=0
    rw [a1,v1',Nat.xor_self]

end ECDSAAdd.Entrant.CKParkCopy


namespace ECDSAAdd.Entrant.CKParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

open LowZero18Square in
theorem withLowK2P_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (h129 : src.length=129)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (withLowK2P L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2P L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2P L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have cacheFix : earlyPerm L (dst.headD 0)=dst.headD 0 := by
    have mem : dst.headD 0∈dst := by
      rcases dst with _|⟨d,ds⟩
      · have hz : src.length=0 := by simpa using hlen.symm
        omega
      · exact List.mem_cons_self
    have targetM : target L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (fun e => tmpD _ targetM (by simpa only [e] using mem))
      (fun e => tmpD _ hostM (by simpa only [e] using mem))
  let P := if s.basis control then regValue src s.basis else 0
  -- parking data
  have Blen : (L.inputBank.take src.length).length=129 := by rw [inputLen,h129]
  have hHx : ∀h∈hosts ext,h∈ext := hosts_sub ext he
  have hHnd : (hosts ext).Nodup := hosts_nodup ext hx he

  have hH0 : ∀h∈hosts ext,h≠ext.getD 0 0 := host_ne_zero ext hx he
  have hHB : ∀h∈hosts ext,h∉(L.inputBank.take src.length) := fun h hh => extB h (hHx h hh)
  have hHD : ∀h∈hosts ext,h∉dst := fun h hh => extD h (hHx h hh)
  have hHo : ∀h∈hosts ext,h∉L.core.out := fun h hh => extOut h (hHx h hh)
  have hHs : ∀q∈src,q∉hosts ext := fun q hq hh => extSrc q (hHx q hh) hq
  have ctlH : control∉hosts ext := fun h => ctlE (hHx _ h)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have b15 : ∀q∈(L.inputBank.take src.length).take 124,q∉(L.inputBank.take src.length).drop 124 := by
    intro q h1 h5
    have nd : ((L.inputBank.take src.length).take 124++(L.inputBank.take src.length).drop 124).Nodup := by
      rw [List.take_append_drop]; exact bNd
    exact (List.nodup_append.mp nd).2.2 q h1 q h5 rfl
  have b51 : ∀q∈(L.inputBank.take src.length).drop 124,q∉(L.inputBank.take src.length).take 124 :=
    fun q h5 h1 => b15 q h1 h5
  have ndMI : ((L.inputBank.take src.length).drop 124++hosts ext).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => hHB b hb (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (hosts ext++(L.inputBank.take src.length).drop 124).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  have lenMI : ((L.inputBank.take src.length).drop 124).length=(hosts ext).length := by
    rw [List.length_drop,Blen,hosts_length]
  obtain ⟨a9,r10,e10⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src++pCL L ext src dst) (pE L control src) records s
  obtain ⟨a8,r9,e9⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src) (pCL L ext src dst) a9 s
  obtain ⟨a7,r8,e8⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst) (pMO L ext src) a8 s
  obtain ⟨a6,r7,e7⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body) (pC1 L control src dst) a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src) (pB L ext body) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext) (pMI L ext src) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src) (pD ext) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (pA L control src++pM L ext src dst) (pE1 L control src) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (pA L control src) (pM L ext src dst) a2 s
  rw [show withLowK2P L ext control src dst body=pA L control src++pM L ext src dst++pE1 L control src++pD ext++
    pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src++pCL L ext src dst++pE L control src from rfl,
    e10,e9,e8,e7,e6,e5,e4,e3,e2]
  simp only [pA,pM,pE1,pD,pMI,pB,pC1,pMO,pCL,pE]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- hosts stay zero through the copy and the producer
  have loLen : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).1]
    rfl
  have hiLen : (LowZero18LowK.oregs L ext src dst).hi.length=65 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).2.1]
    change (L.inputBank.take src.length).length-64=65
    rw [Blen]
  have loBound : regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis<2^64 := by
    simpa only [loLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
  have hiBound : regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^65 := by
    simpa only [hiLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
  have inv1:=mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at inv1
  have inv5:=mk.2.2.2.2.2.2.1
  simp only [LowZero18LowK.kg,if_neg (show src.length≠128 by omega),LowZero18LowK.kgS] at inv5
  have zeros:=CKDonors.donors_zero L ext src dst h129 he
    (regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)
    (regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis)
    loBound hiBound u1.basis mk.2.2.2.1 inv1 inv5
  have hU1 : ∀h∈hosts ext,u1.basis h=false := by
    intro h hh
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hh
    exact zeros i hi
  have srcw1 : ∀q∈src,u1.basis q=s.basis q := fun q hq =>
    (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq))
  have mask1 : regValue ((L.inputBank.take src.length).take 124) u1.basis=
      if u1.basis control then regValue (src.take 124) u1.basis else 0 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ 124 (by rw [inputLen]; omega) u1.basis,bank1,
      CuccaroStreamedSquareWideLayout.regValue_take_mod src 124 (by omega) u1.basis,ctl1,src1]
    simp only [P]
    split_ifs <;> simp
  -- erase only the first 124 bank bits
  have ndMask1 : (control::(src.take 124++(L.inputBank.take src.length).take 124)).Nodup :=
    ndMask.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _)))
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control (src.take 124) ((L.inputBank.take src.length).take 124)
    (by simp only [List.length_take,inputLen]) ndMask1 u1 r3 mask1
  generalize run (eraseMask control (src.take 124) ((L.inputBank.take src.length).take 124)) r3 u1=u2a at ep1 ef1 ev1 ⊢
  -- record-preserving dummies on the (zero) hosts
  have hU2a : ∀h∈hosts ext,u2a.basis h=false := fun h hh =>
    (ef1 h (fun hb => hHB h hh (List.mem_of_mem_take hb))).trans (hU1 h hh)
  rw [dummies_run (hosts ext) u2a r4 hU2a]
  -- park the last four bank bits on the hosts
  obtain ⟨mp1,mf1,mv1,mz1⟩ := move_correct ((L.inputBank.take src.length).drop 124) (hosts ext) lenMI ndMI u2a r5
    ((regValue_zero _ _).mpr hU2a)
  generalize run (move ((L.inputBank.take src.length).drop 124) (hosts ext)) r5 u2a=u2 at mp1 mf1 mv1 mz1 ⊢
  have x5 : regValue (hosts ext) u2.basis=regValue ((L.inputBank.take src.length).drop 124) u1.basis := by
    rw [mv1]; exact regValue_congr _ _ _ (fun q hq => ef1 q (b51 q hq))
  have u2B : ∀q∈(L.inputBank.take src.length),u2.basis q=false := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 124 ∨ q∈(L.inputBank.take src.length).drop 124 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · rw [mf1 q (b15 q h1) (fun hh => hHB q hh hq)]; exact (regValue_zero _ _).mp ev1 q h1
    · exact (regValue_zero _ _).mp mz1 q h5
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx'
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact (u2B q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [mf1 q (fun h => hb (List.mem_of_mem_drop h)) (fun h => hx' (hHx q h)),
        ef1 q (fun h => hb (List.mem_of_mem_take h))]
      exact (u1z q hq hx').trans (u0s q hb)
  have u2ext : ∀q∈ext,q∉hosts ext → u2.basis q=u1.basis q := fun q h hH =>
    (mf1 q (fun h5 => extB q h (List.mem_of_mem_drop h5)) hH).trans (ef1 q (fun h1 => extB q h (List.mem_of_mem_take h1)))
  have u2u1 : ∀q,q∉(L.inputBank.take src.length) → q∉hosts ext → u2.basis q=u1.basis q := fun q hb hH =>
    (mf1 q (fun h => hb (List.mem_of_mem_drop h)) hH).trans (ef1 q (fun h => hb (List.mem_of_mem_take h)))
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact u2u1 q (fun h => bD q h hq) (fun h => hHD q h hq)
  have cb := callback u2' r6 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r6 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r6 u2'=v' at cb loc
  generalize hv : run body r6 u2=v at loc
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r6 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r6 u2 q hb,run_preserves_outside body r6 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r6 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember (fun hm => hH0 _ hm rfl)).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r6 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
  -- second copy
  have vDst : regValue dst v.basis=P^2 := by
    calc
      regValue dst v.basis = regValue dst u2.basis :=
        regValue_congr _ _ _ (fun q hq => vFrame q (dOut q hq))
      _ = regValue dst u1.basis :=
        regValue_congr _ _ _ (fun q hq => u2u1 q (fun hb => bD q hb hq) (fun h => hHD q h hq))
      _ = P^2 := dst1
  have vControl : v.basis control=s.basis control :=
    (vFrame _ ctlO).trans (u2s _ ctlD ctlE)
  have vSource : regValue src v.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq =>
      (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq)))
  have cached : v.basis (dst.headD 0)=(v.basis control && v.basis (src.headD 0)) :=
    CachedSquareCopy.square_head src dst control v (by omega) (by omega)
      (by simpa only [P,vControl,vSource] using vDst)
  rw [cacheWire,cacheFix,CachedSquareCopy.run_eq control (dst.headD 0) (src.take 124) ((L.inputBank.take src.length).take 124) v r7
    (by rw [headD_take src 124 (by omega)]; exact cached)]
  have inputLen1 : (src.take 124).length=((L.inputBank.take src.length).take 124).length := by
    simp only [List.length_take,inputLen]
  have ndCopy1 : (src.take 124++(L.inputBank.take src.length).take 124).Nodup :=
    ndCopy.sublist (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _))
  have hcB1 : ∀c∈some control,c∉(L.inputBank.take src.length).take 124 := fun c hc' h =>
    hcB c hc' (List.mem_of_mem_take h)
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) (src.take 124) ((L.inputBank.take src.length).take 124)
    inputLen1 ndCopy1 hcB1 v r7
  generalize run (copyRegister (some control) (src.take 124) ((L.inputBank.take src.length).take 124)) r7 v=w0' at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have w0'B5 : regValue ((L.inputBank.take src.length).drop 124) w0'.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (cf2 q (b51 q hq)).trans ((vB q (List.mem_of_mem_drop hq)).trans
      ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_drop hq))))
  -- unpark: hosts back into the bank, hosts cleared
  obtain ⟨mp2,mf2,mv2,mz2⟩ := move_correct (hosts ext) ((L.inputBank.take src.length).drop 124) lenMI.symm ndMO w0' r8 w0'B5
  generalize run (move (hosts ext) ((L.inputBank.take src.length).drop 124)) r8 w0'=w0 at mp2 mf2 mv2 mz2 ⊢
  have cf2n : ∀q,q∉(L.inputBank.take src.length) → q∉hosts ext → w0.basis q=v.basis q := fun q hb hH =>
    (mf2 q hH (fun h => hb (List.mem_of_mem_drop h))).trans (cf2 q (fun h => hb (List.mem_of_mem_take h)))
  have w0B5 : regValue ((L.inputBank.take src.length).drop 124) w0.basis=
      regValue ((L.inputBank.take src.length).drop 124) u1.basis := by
    rw [mv2,←x5]
    apply regValue_congr; intro q hq
    rw [cf2 q (fun h => hHB q hq (List.mem_of_mem_take h)),vIn q (hHx q hq)]
  have vCtl1 : v.basis control=u1.basis control := (vFrame _ ctlO).trans ((u2s _ ctlD ctlE).trans ctl1.symm)
  have w0B1 : regValue ((L.inputBank.take src.length).take 124) w0.basis=
      regValue ((L.inputBank.take src.length).take 124) u1.basis := by
    have v0 : regValue ((L.inputBank.take src.length).take 124) v.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (vB q (List.mem_of_mem_take hq)).trans
        ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_take hq)))
    have vs1 : regValue (src.take 124) v.basis=regValue (src.take 124) u1.basis :=
      regValue_congr _ _ _ (fun q hq => (vSrc q (List.mem_of_mem_take hq)).trans (srcw1 q (List.mem_of_mem_take hq)).symm)
    rw [show regValue ((L.inputBank.take src.length).take 124) w0.basis=
        regValue ((L.inputBank.take src.length).take 124) w0'.basis from
      regValue_congr _ _ _ (fun q hq => mf2 q (fun h => hHB q h (List.mem_of_mem_take hq)) (b15 q hq)),
      cv2,mask1,v0,Nat.zero_xor]
    change (if v.basis control then regValue (src.take 124) v.basis else 0)=_
    rw [vCtl1,vs1]
  have wB : ∀q∈(L.inputBank.take src.length),w0.basis q=u1.basis q := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 124 ∨ q∈(L.inputBank.take src.length).drop 124 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · exact (regValue_eq_iff _ _ _).mp w0B1 q h1
    · exact (regValue_eq_iff _ _ _).mp w0B5 q h5
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := (regValue_congr _ _ _ wB).trans bank1
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    by_cases hH : q∈hosts ext
    · rw [(regValue_zero _ _).mp mz2 q hH,hU1 q hH]
    · rw [cf2n q hb hH,vFrame q ho]
      by_cases hx' : q∈ext
      · exact u2ext q hx' hH
      · exact u2u1 q hb hH
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r9
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r9
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r9 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2n q (srcB q hq) (hHs q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2n _ ctlB ctlH).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r10 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r10 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (mp2.trans (cp2.trans (vPhase.trans (mp1.trans (ep1.trans (mk.1.trans cp1))))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2n q (fun h => bOut q h hq) (fun h => hHo q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX]
      by_cases hH : q∈hosts ext
      · rw [(regValue_zero _ _).mp mz2 q hH]; exact (ext0 q (hHx q hH)).symm
      rw [cf2n q hb hH,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx hH,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx

end ECDSAAdd.Entrant.CKParkCopy

#print axioms ECDSAAdd.Entrant.CKParkCopy.withLowK2P_correct


namespace ParityBorrow

theorem parity_sum (v : Nat) (a b c : Bool)
    (ha : a.toNat=v%2) (hb : b.toNat=(v/2^32)%2)
    (hc : c.toNat=(v%2^32+v/2^32)%2) : c=(a ^^ b) := by
  have emod : (v%2^32)%2=v%2 := by omega
  rw [Nat.add_mod,emod,←ha,←hb] at hc
  clear ha hb emod v
  cases a <;> cases b <;> cases c <;> simp_all

theorem borrow_clear (a b : Bool) :
    ((a ^^ b) ^^ a)=b ∧ (b ^^ ((a ^^ b) ^^ a))=false := by
  cases a <;> cases b <;> decide

theorem restore (a b : Bool) :
    (false ^^ ((a ^^ b) ^^ a))=b ∧ (((a ^^ b) ^^ a) ^^ a)=(a ^^ b) := by
  cases a <;> cases b <;> decide

theorem bit1_add (x y : Nat) :
    (x+y)/2%2=((x/2)%2+(y/2)%2+(x%2)*(y%2))%2 := by
  have hx : x%2=0 ∨ x%2=1 := by omega
  have hy : y%2=0 ∨ y%2=1 := by omega
  rcases hx with hx|hx <;> rcases hy with hy|hy
  all_goals (simp only [hx,hy,Nat.zero_mul,Nat.mul_zero,Nat.one_mul]; omega)

theorem parity_sum_bit1 (x y : Nat) (a b carry c : Bool)
    (ha : a.toNat=(x/2)%2) (hb : b.toNat=(y/2)%2)
    (ht : carry.toNat=(x%2)*(y%2)) (hc : c.toNat=(x+y)/2%2) :
    c=((a ^^ b) ^^ carry) := by
  rw [bit1_add,←ha,←hb,←ht] at hc
  clear ha hb ht x y
  cases a <;> cases b <;> cases carry <;> cases c <;> simp_all

theorem bit1_truncated (v : Nat) : ((v%2^32)/2)%2=(v/2)%2 := by omega

theorem product_low_carry (x y : Nat) : (2*x*y/2)%2=(x%2)*(y%2) := by
  have e : 2*x*y=x*y*2 := by ring
  rw [e,Nat.mul_div_left _ (by decide),Nat.mul_mod]
  have hx : x%2=0 ∨ x%2=1 := by omega
  have hy : y%2=0 ∨ y%2=1 := by omega
  rcases hx with hx|hx <;> rcases hy with hy|hy <;> simp [hx,hy]

#print axioms parity_sum
#print axioms borrow_clear
#print axioms parity_sum_bit1
#print axioms product_low_carry
end ParityBorrow

namespace RegisterParityBorrow
open ECDSAAdd ECDSAAdd.Arithmetic

theorem retained_sum_bits (bank S T : List Wire) (hb : 34≤bank.length)
    (hS : 2≤S.length) (hT : 2≤T.length) (s : BasisState) (v : Nat)
    (bv : regValue bank s=v) (sv : regValue S s=v%2^32+v/2^32)
    (tv : regValue T s=2*(v%2^32)*(v/2^32)) :
    s (S.getD 0 0)=(s (bank.getD 0 0) ^^ s (bank.getD 32 0)) ∧
    s (S.getD 1 0)=((s (bank.getD 1 0) ^^ s (bank.getD 33 0)) ^^ s (T.getD 1 0)) := by
  have a0:=regValue_bit bank 0 0 s (by omega)
  have b0:=regValue_bit bank 32 0 s (by omega)
  have c0:=regValue_bit S 0 0 s (by omega)
  simp only [bv,pow_zero,Nat.div_one] at a0
  rw [bv] at b0
  simp only [sv,pow_zero,Nat.div_one] at c0
  have zero:=ParityBorrow.parity_sum v _ _ _ a0 b0 c0
  have a1:=regValue_bit bank 1 0 s (by omega)
  have b1:=regValue_bit bank 33 0 s (by omega)
  have c1:=regValue_bit S 1 0 s (by omega)
  have t1:=regValue_bit T 1 0 s (by omega)
  simp only [bv,pow_one] at a1
  rw [bv] at b1
  simp only [sv,pow_one] at c1
  simp only [tv,pow_one] at t1
  have aq : (s (bank.getD 1 0)).toNat=((v%2^32)/2)%2 :=
    a1.trans (ParityBorrow.bit1_truncated v).symm
  have bq : (s (bank.getD 33 0)).toNat=((v/2^32)/2)%2 := by
    rw [b1]
    have eq : v/2^33=(v/2^32)/2 := by omega
    rw [eq]
  have tq : (s (T.getD 1 0)).toNat=((v%2^32)%2)*((v/2^32)%2) :=
    t1.trans (ParityBorrow.product_low_carry _ _)
  exact ⟨zero,ParityBorrow.parity_sum_bit1 _ _ _ _ _ _ aq bq tq c1⟩

#print axioms retained_sum_bits
end RegisterParityBorrow

namespace LinearBankLoan
open ECDSAAdd

def loan0 (a b h : Wire) : Program := [.CX a h,.CX h b]
def restore0 (a b h : Wire) : Program := [.CX h b,.CX a h]
def loan1 (a b h t : Wire) : Program := [.CX a h,.CX t h,.CX h b]
def restore1 (a b h t : Wire) : Program := [.CX h b,.CX t h,.CX a h]

theorem loan0_run (a b h : Wire) (bh : b≠h) (s : State) (m : List Bool)
    (rel : s.basis h=(s.basis a ^^ s.basis b)) :
    run (loan0 a b h) m s=⟨s.phase,writeBit (writeBit s.basis h (s.basis b)) b false⟩ := by
  have hv : (s.basis h ^^ s.basis a)=s.basis b := by
    rw [rel]
    cases s.basis a <;> cases s.basis b <;> rfl
  simp [loan0,run,writeBit,bh,hv]

theorem restore0_run (a b h : Wire) (ab : a≠b) (hb : h≠b)
    (s : State) (m : List Bool) (bz : s.basis b=false) :
    run (restore0 a b h) m s=
      ⟨s.phase,writeBit (writeBit s.basis b (s.basis h)) h (s.basis h ^^ s.basis a)⟩ := by
  simp [restore0,run,writeBit,ab,hb,bz]

theorem loan1_run (a b h t : Wire) (bh : b≠h) (th : t≠h)
    (s : State) (m : List Bool)
    (rel : s.basis h=((s.basis a ^^ s.basis b) ^^ s.basis t)) :
    run (loan1 a b h t) m s=⟨s.phase,writeBit (writeBit s.basis h (s.basis b)) b false⟩ := by
  have hv : ((s.basis h ^^ s.basis a) ^^ s.basis t)=s.basis b := by
    rw [rel]
    cases s.basis a <;> cases s.basis b <;> cases s.basis t <;> rfl
  simp [loan1,run,writeBit,bh,th,hv]

theorem restore1_run (a b h t : Wire) (ab : a≠b) (ah : a≠h) (hb : h≠b) (tb : t≠b)
    (s : State) (m : List Bool) (bz : s.basis b=false) :
    run (restore1 a b h t) m s=
      ⟨s.phase,writeBit (writeBit s.basis b (s.basis h)) h ((s.basis h ^^ s.basis t) ^^ s.basis a)⟩ := by
  simp [restore1,run,writeBit,ab,ah,hb,tb,bz]

theorem loan0_counts (a b h : Wire) :
    toffoliCount (loan0 a b h)=0 ∧ measurementCount (loan0 a b h)=0 := by exact ⟨rfl,rfl⟩

theorem loan1_counts (a b h t : Wire) :
    toffoliCount (loan1 a b h t)=0 ∧ measurementCount (loan1 a b h t)=0 := by exact ⟨rfl,rfl⟩

theorem slots0 (a b h : Wire) :
    Challenge.gateSlots (loan0 a b h)=2 ∧ Challenge.gateSlots (restore0 a b h)=2 := by
  exact ⟨rfl,rfl⟩

theorem slots1 (a b h t : Wire) :
    Challenge.gateSlots (loan1 a b h t)=3 ∧ Challenge.gateSlots (restore1 a b h t)=3 := by
  exact ⟨rfl,rfl⟩

theorem physical0 (a b h : Wire) (ah : a≠h) (hb : h≠b) :
    Arithmetic.GatePhysical (loan0 a b h) ∧ Arithmetic.GatePhysical (restore0 a b h) := by
  simp [loan0,restore0,Arithmetic.GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ah,hb]

theorem physical1 (a b h t : Wire) (ah : a≠h) (th : t≠h) (hb : h≠b) :
    Arithmetic.GatePhysical (loan1 a b h t) ∧ Arithmetic.GatePhysical (restore1 a b h t) := by
  simp [loan1,restore1,Arithmetic.GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ah,th,hb]

theorem support0 (a b h : Wire) :
    wires (loan0 a b h)⊆{a,b,h} ∧ wires (restore0 a b h)⊆{a,b,h} := by
  constructor <;> intro q hq <;> simp [loan0,restore0,wires,Instr.wires] at hq ⊢ <;> tauto

theorem support1 (a b h t : Wire) :
    wires (loan1 a b h t)⊆{a,b,h,t} ∧ wires (restore1 a b h t)⊆{a,b,h,t} := by
  constructor <;> intro q hq <;> simp [loan1,restore1,wires,Instr.wires] at hq ⊢ <;> tauto

#print axioms loan0_run
#print axioms loan1_run
#print axioms restore1_run
end LinearBankLoan

namespace CombinedBankLoan
open ECDSAAdd

def loan (a0 a1 b0 b1 h0 h1 t : Wire) : Program :=
  LinearBankLoan.loan0 a0 b0 h0++LinearBankLoan.loan1 a1 b1 h1 t

def restore (a0 a1 b0 b1 h0 h1 t : Wire) : Program :=
  LinearBankLoan.restore1 a1 b1 h1 t++LinearBankLoan.restore0 a0 b0 h0

theorem get_ne (r : List Wire) (hn : r.Nodup) (i j : Nat)
    (hi : i<r.length) (hj : j<r.length) (hij : i≠j) : r.getD i 0≠r.getD j 0 := by
  intro h
  rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at h
  exact hij ((List.Nodup.getElem_inj_iff hn).mp h)

theorem loan_run (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis b0))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis b1) ^^ s.basis t)) :
    run (loan a0 a1 b0 b1 h0 h1 t) m s=
      ⟨s.phase,writeBit (writeBit (writeBit (writeBit s.basis h0 (s.basis b0)) b0 false)
        h1 (s.basis b1)) b1 false⟩ := by
  have ne (i j : Nat) (hi : i<7) (hj : j<7) (hij : i≠j) :
      [a0,a1,b0,b1,h0,h1,t].getD i 0≠[a0,a1,b0,b1,h0,h1,t].getD j 0 :=
    get_ne _ hn i j hi hj hij
  let u : State:=⟨s.phase,writeBit (writeBit s.basis h0 (s.basis b0)) b0 false⟩
  have keep (q : Wire) (qb : q≠b0) (qh : q≠h0) : u.basis q=s.basis q := by
    simp [u,writeBit,qb,qh]
  have kh1:=keep h1 (ne 5 2 (by decide) (by decide) (by decide)) (ne 5 4 (by decide) (by decide) (by decide))
  have ka1:=keep a1 (ne 1 2 (by decide) (by decide) (by decide)) (ne 1 4 (by decide) (by decide) (by decide))
  have kb1:=keep b1 (ne 3 2 (by decide) (by decide) (by decide)) (ne 3 4 (by decide) (by decide) (by decide))
  have kt:=keep t (ne 6 2 (by decide) (by decide) (by decide)) (ne 6 4 (by decide) (by decide) (by decide))
  have r1u : u.basis h1=((u.basis a1 ^^ u.basis b1) ^^ u.basis t) := by
    simpa only [kh1,ka1,kb1,kt] using r1
  have e0:=LinearBankLoan.loan0_run a0 b0 h0 (ne 2 4 (by decide) (by decide) (by decide)) s [] r0
  have e1:=LinearBankLoan.loan1_run a1 b1 h1 t
    (ne 3 5 (by decide) (by decide) (by decide)) (ne 6 5 (by decide) (by decide) (by decide)) u m r1u
  rw [loan,run_append,(LinearBankLoan.loan0_counts a0 b0 h0).2,List.take_zero,List.drop_zero,e0]
  simpa only [kb1] using e1

theorem restore_run (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup)
    (s : State) (m : List Bool) (z0 : s.basis b0=false) (z1 : s.basis b1=false) :
    run (restore a0 a1 b0 b1 h0 h1 t) m s=
      ⟨s.phase,writeBit (writeBit
        (writeBit (writeBit s.basis b1 (s.basis h1)) h1 ((s.basis h1 ^^ s.basis t) ^^ s.basis a1))
        b0 (s.basis h0)) h0 (s.basis h0 ^^ s.basis a0)⟩ := by
  have ne (i j : Nat) (hi : i<7) (hj : j<7) (hij : i≠j) :
      [a0,a1,b0,b1,h0,h1,t].getD i 0≠[a0,a1,b0,b1,h0,h1,t].getD j 0 :=
    get_ne _ hn i j hi hj hij
  let u : State:=⟨s.phase,writeBit (writeBit s.basis b1 (s.basis h1)) h1
    ((s.basis h1 ^^ s.basis t) ^^ s.basis a1)⟩
  have keep (q : Wire) (qb : q≠b1) (qh : q≠h1) : u.basis q=s.basis q := by
    simp [u,writeBit,qb,qh]
  have kh0:=keep h0 (ne 4 3 (by decide) (by decide) (by decide)) (ne 4 5 (by decide) (by decide) (by decide))
  have ka0:=keep a0 (ne 0 3 (by decide) (by decide) (by decide)) (ne 0 5 (by decide) (by decide) (by decide))
  have kb0:=keep b0 (ne 2 3 (by decide) (by decide) (by decide)) (ne 2 5 (by decide) (by decide) (by decide))
  have e1:=LinearBankLoan.restore1_run a1 b1 h1 t
    (ne 1 3 (by decide) (by decide) (by decide)) (ne 1 5 (by decide) (by decide) (by decide))
    (ne 5 3 (by decide) (by decide) (by decide)) (ne 6 3 (by decide) (by decide) (by decide)) s [] z1
  have e0:=LinearBankLoan.restore0_run a0 b0 h0
    (ne 0 2 (by decide) (by decide) (by decide)) (ne 4 2 (by decide) (by decide) (by decide)) u m (kb0.trans z0)
  have mc : measurementCount (LinearBankLoan.restore1 a1 b1 h1 t)=0 := rfl
  rw [restore,run_append,mc,List.take_zero,List.drop_zero,e1]
  simpa only [kh0,ka0] using e0

#print axioms loan_run
#print axioms restore_run
end CombinedBankLoan
namespace ECDSAAdd.Entrant.ParityLoan
open Arithmetic

theorem inner_sum_bits (R : KRegs) (hh : R.h=32) (hb : 34 ≤ R.bank.length)
    (hs : 2 ≤ R.S.length) (ht : 2 ≤ R.T.length) (p : BasisState) (v : Nat)
    (bv : regValue R.bank p=v) (inv : R.invF v p) :
    p (R.S.getD 0 0)=(p (R.bank.getD 0 0) ^^ p (R.bank.getD 32 0)) ∧
    p (R.S.getD 1 0)=((p (R.bank.getD 1 0) ^^ p (R.bank.getD 33 0)) ^^ p (R.T.getD 1 0)) := by
  have sv : regValue R.S p=v%2^32+v/2^32 := by simpa only [hh] using inv.1
  have tv : regValue R.T p=2*(v%2^32)*(v/2^32) := by simpa only [hh] using inv.2
  exact RegisterParityBorrow.retained_sum_bits R.bank R.S R.T hb hs ht p v bv sv tv

theorem restore_recovers (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup)
    (p w : State) (m : List Bool) (z0 : w.basis b0=false) (z1 : w.basis b1=false)
    (saved0 : w.basis h0=p.basis b0) (saved1 : w.basis h1=p.basis b1)
    (a0val : w.basis a0=p.basis a0) (a1val : w.basis a1=p.basis a1) (tval : w.basis t=p.basis t)
    (r0 : p.basis h0=(p.basis a0 ^^ p.basis b0))
    (r1 : p.basis h1=((p.basis a1 ^^ p.basis b1) ^^ p.basis t)) :
    run (CombinedBankLoan.restore a0 a1 b0 b1 h0 h1 t) m w=
      ⟨w.phase,writeBit (writeBit (writeBit (writeBit w.basis b1 (p.basis b1)) h1 (p.basis h1))
        b0 (p.basis b0)) h0 (p.basis h0)⟩ := by
  have v0 : (p.basis b0 ^^ p.basis a0)=p.basis h0 := by
    rw [r0]
    cases p.basis a0 <;> cases p.basis b0 <;> rfl
  have v1 : ((p.basis b1 ^^ p.basis t) ^^ p.basis a1)=p.basis h1 := by
    rw [r1]
    cases p.basis a1 <;> cases p.basis b1 <;> cases p.basis t <;> rfl
  have h:=CombinedBankLoan.restore_run a0 a1 b0 b1 h0 h1 t hn w m z0 z1
  simpa only [saved0,saved1,a0val,a1val,tval,v0,v1] using h

theorem restore_frame (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup)
    (out : List Wire) (p w : State) (m : List Bool) (z0 : w.basis b0=false) (z1 : w.basis b1=false)
    (saved0 : w.basis h0=p.basis b0) (saved1 : w.basis h1=p.basis b1)
    (a0val : w.basis a0=p.basis a0) (a1val : w.basis a1=p.basis a1) (tval : w.basis t=p.basis t)
    (r0 : p.basis h0=(p.basis a0 ^^ p.basis b0))
    (r1 : p.basis h1=((p.basis a1 ^^ p.basis b1) ^^ p.basis t))
    (agree : ∀q,q ∉ out → q≠b0 → q≠b1 → q≠h0 → q≠h1 → w.basis q=p.basis q)
    (away : ∀q ∈ out,q≠b0 ∧ q≠b1 ∧ q≠h0 ∧ q≠h1) :
    (run (CombinedBankLoan.restore a0 a1 b0 b1 h0 h1 t) m w).phase=w.phase ∧
    (∀q,q ∉ out → (run (CombinedBankLoan.restore a0 a1 b0 b1 h0 h1 t) m w).basis q=p.basis q) ∧
    (∀q ∈ out,(run (CombinedBankLoan.restore a0 a1 b0 b1 h0 h1 t) m w).basis q=w.basis q) := by
  rw [restore_recovers a0 a1 b0 b1 h0 h1 t hn p w m z0 z1 saved0 saved1 a0val a1val tval r0 r1]
  refine ⟨rfl,?_,?_⟩
  · intro q hq
    by_cases qh0 : q=h0
    · subst q
      simp [writeBit]
    by_cases qb0 : q=b0
    · subst q
      simp [writeBit,qh0]
    by_cases qh1 : q=h1
    · subst q
      simp [writeBit,qh0,qb0]
    by_cases qb1 : q=b1
    · subst q
      simp [writeBit,qh0,qb0,qh1]
    simpa [writeBit,qh0,qb0,qh1,qb1] using agree q hq qb0 qb1 qh0 qh1
  · intro q hq
    obtain ⟨qb0,qb1,qh0,qh1⟩:=away q hq
    simp [writeBit,qb0,qb1,qh0,qh1]

#print axioms inner_sum_bits
#print axioms restore_recovers
#print axioms restore_frame
end ECDSAAdd.Entrant.ParityLoan
namespace BankMask2
open ECDSAAdd ECDSAAdd.Arithmetic

def mask (r : List Wire) : List Wire := r.take 96++(r.drop 98).take 21

theorem mask_sublist (r : List Wire) : (mask r).Sublist r := by
  have h:=List.Sublist.append (List.Sublist.refl (r.take 96))
    ((List.take_sublist 21 ((r.drop 96).drop 2)).trans (List.drop_sublist 2 (r.drop 96)))
  simpa only [mask,List.drop_drop,List.take_append_drop] using h

theorem mask_length (r : List Wire) (hr : 119 ≤ r.length) : (mask r).length=117 := by
  simp only [mask,List.length_append,List.length_take,List.length_drop]
  omega

theorem mask_head (r : List Wire) : (mask r).headD 0=r.headD 0 := by
  cases r <;> rfl

theorem pair_nodup (a b : List Wire) (h : (a++b).Nodup) :
    (mask a++mask b).Nodup := h.sublist (List.Sublist.append (mask_sublist a) (mask_sublist b))

theorem getD_mem_slice (l : List Wire) (hl : l.Nodup) (i a b : Nat) (hi : i < l.length) :
    l.getD i 0 ∈ (l.drop a).take b  ↔  a ≤ i ∧ i < a+b := by
  rw [List.getD_eq_getElem _ _ hi]
  constructor
  · intro h
    obtain ⟨j,hj,e⟩:=List.getElem_of_mem h
    simp only [List.getElem_take,List.getElem_drop] at e
    have := (List.Nodup.getElem_inj_iff hl).mp e
    simp only [List.length_take,List.length_drop] at hj
    omega
  · rintro ⟨h1,h2⟩
    have hj : i-a < ((l.drop a).take b).length := by
      simp only [List.length_take,List.length_drop]
      omega
    have e : ((l.drop a).take b)[i-a]'hj=l[i] := by
      simp only [List.getElem_take,List.getElem_drop]
      congr 1
      omega
    rw [←e]
    exact List.getElem_mem _

theorem mask_mem (r : List Wire) (hn : r.Nodup) (i : Nat) (hi : i < r.length) :
    r.getD i 0 ∈ mask r  ↔  i < 96 ∨ (98 ≤ i ∧ i < 119) := by
  have ht:=getD_mem_slice r hn i 0 96 hi
  simp only [List.drop_zero,Nat.zero_le,true_and] at ht
  have hd:=getD_mem_slice r hn i 98 21 hi
  simp only [mask,List.mem_append,ht,hd]

theorem drop_mem (r : List Wire) (hn : r.Nodup) (i a : Nat) (hi : i < r.length) :
    r.getD i 0 ∈ r.drop a  ↔  a ≤ i := by
  have h:=getD_mem_slice r hn i a r.length hi
  have e : (r.drop a).take r.length=r.drop a :=
    List.take_of_length_le (by simp only [List.length_drop];omega)
  rw [e] at h
  constructor
  · intro hh
    exact (h.mp hh).1
  · intro hh
    exact h.mpr ⟨hh,by omega⟩

theorem partition (r : List Wire) (hn : r.Nodup) : ∀q ∈ r,
    q ∈ mask r ∨ q=r.getD 96 0 ∨ q=r.getD 97 0 ∨ q ∈ r.drop 119 := by
  intro q hq
  obtain ⟨i,hi,e⟩:=List.getElem_of_mem hq
  have eq : r.getD i 0=q := (List.getD_eq_getElem _ _ hi).trans e
  rw [←eq]
  by_cases hm : i < 96 ∨ (98 ≤ i ∧ i < 119)
  · exact Or.inl ((mask_mem r hn i hi).mpr hm)
  · have hc : i=96 ∨ i=97 ∨ 119 ≤ i := by omega
    rcases hc with rfl|rfl|hc
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr ((drop_mem r hn i 119 hi).mpr hc)))

theorem excludes (r : List Wire) (hn : r.Nodup) (hr : 119 ≤ r.length) :
    r.getD 96 0∉mask r ∧ r.getD 97 0∉mask r := by
  constructor
  · intro h
    have hh:=(mask_mem r hn 96 (by omega)).mp h
    omega
  · intro h
    have hh:=(mask_mem r hn 97 (by omega)).mp h
    omega

def clearMasked (c : Wire) (src bank : List Wire) : Program :=
  eraseMask c (src.take 96) (bank.take 96)++
    [Instr.measureX (bank.getD 96 0) [] [],Instr.measureX (bank.getD 97 0) [] []]++
    eraseMask c ((src.drop 98).take 21) ((bank.drop 98).take 21)

theorem erase_slots (c : Wire) : ∀(src dst : List Wire),src.length=dst.length →
    Challenge.gateSlots (eraseMask c src dst)=2*src.length
  | [], [], _ => rfl
  | [], _::_, h => by simp at h
  | _::_, [], h => by simp at h
  | a::src,b::dst,h => by
    have ih:=erase_slots c src dst (by simpa using h)
    change 2+Challenge.gateSlots (eraseMask c src dst)=2*(src.length+1)
    rw [ih]
    omega

theorem clear_counts (c : Wire) (src bank : List Wire) (hs : 119 ≤ src.length) (hb : 119 ≤ bank.length) :
    toffoliCount (clearMasked c src bank)=0 ∧
    measurementCount (clearMasked c src bank)=119 ∧
    Challenge.gateSlots (clearMasked c src bank)=236 := by
  have s0 : (src.take 96).length=96 := by simp only [List.length_take];omega
  have b0 : (bank.take 96).length=96 := by simp only [List.length_take];omega
  have s1 : ((src.drop 98).take 21).length=21 := by simp only [List.length_take,List.length_drop];omega
  have b1 : ((bank.drop 98).take 21).length=21 := by simp only [List.length_take,List.length_drop];omega
  have e0:=eraseMask_counts c (src.take 96) (bank.take 96) (by rw [s0,b0])
  have e1:=eraseMask_counts c ((src.drop 98).take 21) ((bank.drop 98).take 21) (by rw [s1,b1])
  have z0:=erase_slots c (src.take 96) (bank.take 96) (by rw [s0,b0])
  have z1:=erase_slots c ((src.drop 98).take 21) ((bank.drop 98).take 21) (by rw [s1,b1])
  simp only [clearMasked,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
    e0.1,e1.1,e0.2,e1.2,z0,z1,s0,s1,b0,b1]
  exact ⟨rfl,rfl,rfl⟩

#print axioms partition
#print axioms clear_counts
end BankMask2

namespace BankMask2
open ECDSAAdd ECDSAAdd.Arithmetic

theorem dummy_run (b : Wire) (s : State) (m : List Bool) (hb : s.basis b=false) :
    run [Instr.measureX b [] []] m s=s := by
  have upd : writeBit s.basis b false=s.basis := by
    funext q
    by_cases hq : q=b
    · subst q
      simp [writeBit,hb]
    · simp [writeBit,hq]
  simp [run,measureAndCorrect,correct,hb,upd]

theorem dummy_pair_run (b0 b1 : Wire) (s : State) (m : List Bool)
    (h0 : s.basis b0=false) (h1 : s.basis b1=false) :
    run [Instr.measureX b0 [] [],Instr.measureX b1 [] []] m s=s := by
  have z0:=dummy_run b0 s m h0
  change measureAndCorrect b0 [] [] (m.headD false) s=s at z0
  change run [Instr.measureX b1 [] []] m.tail (measureAndCorrect b0 [] [] (m.headD false) s)=s
  rw [z0]
  exact dummy_run b1 s m.tail h1

theorem run_cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

theorem head_middle_disjoint (r : List Wire) (hn : r.Nodup) :
    List.Disjoint (r.take 96) ((r.drop 98).take 21) := by
  apply List.disjoint_left.mpr
  intro q hp hm
  have nd : (r.take 98++r.drop 98).Nodup := by
    simpa only [List.take_append_drop] using hn
  have e : r.take 96=(r.take 98).take 96 := by
    rw [List.take_take]
    norm_num
  rw [e] at hp
  exact List.disjoint_left.mp (List.nodup_append'.mp nd).2.2
    (List.mem_of_mem_take hp) (List.mem_of_mem_take hm)

theorem middle_sub_prefix (r : List Wire) : ∀q ∈ (r.drop 98).take 21,q ∈ r.take 119 := by
  intro q h
  have e : (r.drop 98).take 21=(r.take 119).drop 98 := by rw [List.drop_take]
  rw [e] at h
  exact List.mem_of_mem_drop h

theorem head_sub_prefix (r : List Wire) : ∀q ∈ r.take 96,q ∈ r.take 119 := by
  intro q h
  have e : r.take 96=(r.take 119).take 96 := by
    rw [List.take_take]
    norm_num
  rw [e] at h
  exact List.mem_of_mem_take h

theorem prefix_cover (r : List Wire) (hn : r.Nodup) : ∀q ∈ r.take 119,
    q ∈ r.take 96 ∨ q=r.getD 96 0 ∨ q=r.getD 97 0 ∨ q ∈ (r.drop 98).take 21 := by
  intro q hq
  have p:=partition r hn q (List.mem_of_mem_take hq)
  rcases p with p|p|p|p
  · rcases List.mem_append.mp p with p|p
    · exact Or.inl p
    · exact Or.inr (Or.inr (Or.inr p))
  · exact Or.inr (Or.inl p)
  · exact Or.inr (Or.inr (Or.inl p))
  · have nd : (r.take 119++r.drop 119).Nodup := by
      simpa only [List.take_append_drop] using hn
    exact False.elim (List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 hq p)

theorem clear_correct (c : Wire) (src bank : List Wire)
    (hs : 119 ≤ src.length) (hb : 119 ≤ bank.length) (hn : (c::(src++bank)).Nodup)
    (s : State) (m : List Bool)
    (h0 : regValue (bank.take 96) s.basis=if s.basis c then regValue (src.take 96) s.basis else 0)
    (h1 : regValue ((bank.drop 98).take 21) s.basis=
      if s.basis c then regValue ((src.drop 98).take 21) s.basis else 0)
    (z0 : s.basis (bank.getD 96 0)=false) (z1 : s.basis (bank.getD 97 0)=false) :
    (run (clearMasked c src bank) m s).phase=s.phase ∧
    (∀q,q ∉ bank.take 119 → (run (clearMasked c src bank) m s).basis q=s.basis q) ∧
    regValue (bank.take 119) (run (clearMasked c src bank) m s).basis=0 := by
  have bn : bank.Nodup := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.1
  have sb : List.Disjoint src bank := (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
  have cb : c ∉ bank := fun h=> (List.nodup_cons.mp hn).1 (List.mem_append_right _ h)
  have s0 : (src.take 96).length=96 := by simp only [List.length_take];omega
  have b0 : (bank.take 96).length=96 := by simp only [List.length_take];omega
  have s1 : ((src.drop 98).take 21).length=21 := by simp only [List.length_take,List.length_drop];omega
  have b1 : ((bank.drop 98).take 21).length=21 := by simp only [List.length_take,List.length_drop];omega
  have nd0 : (c::(src.take 96++bank.take 96)).Nodup :=
    hn.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _)))
  have nd1 : (c::((src.drop 98).take 21++(bank.drop 98).take 21)).Nodup :=
    hn.sublist (List.Sublist.cons₂ _ (List.Sublist.append
      ((List.take_sublist _ _).trans (List.drop_sublist _ _))
      ((List.take_sublist _ _).trans (List.drop_sublist _ _))))
  let u:=run (eraseMask c (src.take 96) (bank.take 96)) m s
  have e0:=eraseMask_correct c (src.take 96) (bank.take 96) (by rw [s0,b0]) nd0 s m h0
  have f0 : ∀q,q ∉ bank.take 96 → u.basis q=s.basis q := e0.2.1
  have h96 : bank.getD 96 0 ∉ bank.take 96 := by
    intro hh
    have h:=(getD_mem_slice bank bn 96 0 96 (by omega)).mp (by simpa using hh)
    omega
  have h97 : bank.getD 97 0 ∉ bank.take 96 := by
    intro hh
    have h:=(getD_mem_slice bank bn 97 0 96 (by omega)).mp (by simpa using hh)
    omega
  have z0u : u.basis (bank.getD 96 0)=false := (f0 _ h96).trans z0
  have z1u : u.basis (bank.getD 97 0)=false := (f0 _ h97).trans z1
  have midHead : ∀q ∈ (bank.drop 98).take 21,q ∉ bank.take 96 :=
    fun q hm hp=>List.disjoint_left.mp (head_middle_disjoint bank bn) hp hm
  have srcHead : ∀q ∈ (src.drop 98).take 21,q ∉ bank.take 96 := by
    intro q hq hq'
    exact List.disjoint_left.mp sb (List.mem_of_mem_drop (List.mem_of_mem_take hq)) (List.mem_of_mem_take hq')
  have midU : regValue ((bank.drop 98).take 21) u.basis=regValue ((bank.drop 98).take 21) s.basis :=
    regValue_congr _ _ _ (fun q hq=>f0 q (midHead q hq))
  have srcU : regValue ((src.drop 98).take 21) u.basis=regValue ((src.drop 98).take 21) s.basis :=
    regValue_congr _ _ _ (fun q hq=>f0 q (srcHead q hq))
  have ctlU : u.basis c=s.basis c := f0 _ (fun h=>cb (List.mem_of_mem_take h))
  have h1u : regValue ((bank.drop 98).take 21) u.basis=
      if u.basis c then regValue ((src.drop 98).take 21) u.basis else 0 := by
    rw [midU,srcU,ctlU]
    exact h1
  let v:=run (eraseMask c ((src.drop 98).take 21) ((bank.drop 98).take 21)) (m.drop 98) u
  have e1:=eraseMask_correct c ((src.drop 98).take 21) ((bank.drop 98).take 21)
    (by rw [s1,b1]) nd1 u (m.drop 98) h1u
  have f1 : ∀q,q ∉ (bank.drop 98).take 21 → v.basis q=u.basis q := e1.2.1
  have cm0 : measurementCount (eraseMask c (src.take 96) (bank.take 96))=96 := by
    rw [(eraseMask_counts c _ _ (by rw [s0,b0])).2,b0]
  have cmD : measurementCount [Instr.measureX (bank.getD 96 0) [] [],Instr.measureX (bank.getD 97 0) [] []]=2 := rfl
  have shape : run (clearMasked c src bank) m s=v := by
    simp only [clearMasked,run_cat,measurementCount_append,cm0,cmD]
    rw [dummy_pair_run _ _ u (m.drop 96) z0u z1u]
  rw [shape]
  refine ⟨e1.1.trans e0.1,?_,?_⟩
  · intro q hq
    exact (f1 q (fun h=>hq (middle_sub_prefix bank q h))).trans
      (f0 q (fun h=>hq (head_sub_prefix bank q h)))
  · apply (regValue_zero _ _).mpr
    intro q hq
    rcases prefix_cover bank bn q hq with hp|rfl|rfl|hm
    · exact (f1 q (fun h=>List.disjoint_left.mp (head_middle_disjoint bank bn) hp h)).trans
        ((regValue_zero _ _).mp e0.2.2 q hp)
    · have outside : bank.getD 96 0 ∉ (bank.drop 98).take 21 := by
        intro h
        have h':=(getD_mem_slice bank bn 96 98 21 (by omega)).mp h
        omega
      exact (f1 _ outside).trans z0u
    · have outside : bank.getD 97 0 ∉ (bank.drop 98).take 21 := by
        intro h
        have h':=(getD_mem_slice bank bn 97 98 21 (by omega)).mp h
        omega
      exact (f1 _ outside).trans z1u
    · exact (regValue_zero _ _).mp e1.2.2 q hm

#print axioms clear_correct
end BankMask2

namespace BankMask2
open ECDSAAdd ECDSAAdd.Arithmetic
open ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout

theorem masked_take (c : Wire) (src bank : List Wire) (n : Nat)
    (hs : n ≤ src.length) (hb : n ≤ bank.length) (s : State)
    (hv : regValue bank s.basis=if s.basis c then regValue src s.basis else 0) :
    regValue (bank.take n) s.basis=if s.basis c then regValue (src.take n) s.basis else 0 := by
  rw [regValue_take_mod bank n hb,regValue_take_mod src n hs,hv]
  cases s.basis c <;> simp

theorem masked_drop (c : Wire) (src bank : List Wire) (n : Nat)
    (hs : n ≤ src.length) (hb : n ≤ bank.length) (s : State)
    (hv : regValue bank s.basis=if s.basis c then regValue src s.basis else 0) :
    regValue (bank.drop n) s.basis=if s.basis c then regValue (src.drop n) s.basis else 0 := by
  rw [regValue_drop_div bank n hb,regValue_drop_div src n hs,hv]
  cases s.basis c <;> simp

theorem masked_chunks (c : Wire) (src bank : List Wire) (hs : 119 ≤ src.length)
    (hb : 119 ≤ bank.length) (s : State)
    (hv : regValue bank s.basis=if s.basis c then regValue src s.basis else 0) :
    (regValue (bank.take 96) s.basis=if s.basis c then regValue (src.take 96) s.basis else 0) ∧
    (regValue ((bank.drop 98).take 21) s.basis=
      if s.basis c then regValue ((src.drop 98).take 21) s.basis else 0) := by
  refine ⟨masked_take c src bank 96 (by omega) (by omega) s hv,?_⟩
  have hd:=masked_drop c src bank 98 (by omega) (by omega) s hv
  exact masked_take c (src.drop 98) (bank.drop 98) 21
    (by simp only [List.length_drop];omega) (by simp only [List.length_drop];omega) s hd

theorem masked_mask (c : Wire) (src bank : List Wire) (hs : 119 ≤ src.length)
    (hb : 119 ≤ bank.length) (s : State)
    (hv : regValue bank s.basis=if s.basis c then regValue src s.basis else 0) :
    regValue (mask bank) s.basis=if s.basis c then regValue (mask src) s.basis else 0 := by
  have h:=masked_chunks c src bank hs hb s hv
  have sl : (src.take 96).length=96 := by simp only [List.length_take];omega
  have bl : (bank.take 96).length=96 := by simp only [List.length_take];omega
  simp only [mask,regValue_append,h.1,h.2,sl,bl]
  cases s.basis c <;> simp

theorem recopy_correct (c : Wire) (src bank : List Wire) (hs : 119 ≤ src.length)
    (hb : 119 ≤ bank.length) (hn : (src++bank).Nodup) (hc : c ∉ bank)
    (p v : State) (m : List Bool)
    (old : regValue bank p.basis=if p.basis c then regValue src p.basis else 0)
    (vz : regValue (mask bank) v.basis=0)
    (ctl : v.basis c=p.basis c) (source : regValue (mask src) v.basis=regValue (mask src) p.basis) :
    (run (copyRegister (some c) (mask src) (mask bank)) m v).phase=v.phase ∧
    (∀q,q ∉ mask bank → (run (copyRegister (some c) (mask src) (mask bank)) m v).basis q=v.basis q) ∧
    (∀q ∈ mask bank,(run (copyRegister (some c) (mask src) (mask bank)) m v).basis q=p.basis q) := by
  have sl:=mask_length src hs
  have bl:=mask_length bank hb
  have hc' : c ∉ mask bank := fun h=>hc ((mask_sublist bank).subset h)
  have controls : ∀q ∈ (some c : Option Wire),q ∉ mask bank := by simpa using hc'
  have h:=copyRegister_correct (some c) (mask src) (mask bank) (by rw [sl,bl])
    (pair_nodup src bank hn) controls v m
  have oldMask:=masked_mask c src bank hs hb p old
  have value : regValue (mask bank) (run (copyRegister (some c) (mask src) (mask bank)) m v).basis=
      regValue (mask bank) p.basis := by
    rw [h.2.2,vz,Nat.zero_xor]
    change (if v.basis c then regValue (mask src) v.basis else 0)=regValue (mask bank) p.basis
    rw [ctl,source]
    exact oldMask.symm
  exact ⟨h.1,h.2.1,(regValue_eq_iff _ _ _).mp value⟩

#print axioms masked_mask
#print axioms recopy_correct
end BankMask2
namespace ECDSAAdd.Entrant.ParityLoan
open Arithmetic

theorem loan_frame (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis b0))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis b1) ^^ s.basis t)) :
    (run (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t) m s).phase=s.phase ∧
    (∀q,q≠b0 → q≠b1 → q≠h0 → q≠h1 →
      (run (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t) m s).basis q=s.basis q) := by
  rw [CombinedBankLoan.loan_run a0 a1 b0 b1 h0 h1 t hn s m r0 r1]
  refine ⟨rfl,?_⟩
  intro q qb0 qb1 qh0 qh1
  simp [writeBit,qb0,qb1,qh0,qh1]

theorem loan_masked (a0 a1 h0 h1 t c : Wire) (src bank : List Wire)
    (hs : 119≤src.length) (hb : 119≤bank.length)
    (hn : [a0,a1,bank.getD 96 0,bank.getD 97 0,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis (bank.getD 96 0)))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis (bank.getD 97 0)) ^^ s.basis t))
    (old : regValue bank s.basis=if s.basis c then regValue src s.basis else 0)
    (away : ∀q∈c::(BankMask2.mask src++BankMask2.mask bank),
      q≠bank.getD 96 0 ∧ q≠bank.getD 97 0 ∧ q≠h0 ∧ q≠h1) :
    let u:=run (CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t) m s
    (regValue (bank.take 96) u.basis=if u.basis c then regValue (src.take 96) u.basis else 0) ∧
    (regValue ((bank.drop 98).take 21) u.basis=
      if u.basis c then regValue ((src.drop 98).take 21) u.basis else 0) := by
  dsimp only
  let u:=run (CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t) m s
  have frame:=loan_frame a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s m r0 r1
  have keep (q : Wire) (hq : q∈c::(BankMask2.mask src++BankMask2.mask bank)) : u.basis q=s.basis q := by
    obtain ⟨qb0,qb1,qh0,qh1⟩:=away q hq
    exact frame.2 q qb0 qb1 qh0 qh1
  have ctl : u.basis c=s.basis c := keep c (by simp)
  have sv : ∀q∈BankMask2.mask src,u.basis q=s.basis q := by
    intro q hq;exact keep q (by simp [hq])
  have bv : ∀q∈BankMask2.mask bank,u.basis q=s.basis q := by
    intro q hq;exact keep q (by simp [hq])
  have chunks:=BankMask2.masked_chunks c src bank hs hb s old
  have s0:=regValue_congr (src.take 96) u.basis s.basis (by
    intro q hq;exact sv q (by simp [BankMask2.mask,hq]))
  have s1:=regValue_congr ((src.drop 98).take 21) u.basis s.basis (by
    intro q hq;exact sv q (by simp [BankMask2.mask,hq]))
  have b0:=regValue_congr (bank.take 96) u.basis s.basis (by
    intro q hq;exact bv q (by simp [BankMask2.mask,hq]))
  have b1:=regValue_congr ((bank.drop 98).take 21) u.basis s.basis (by
    intro q hq;exact bv q (by simp [BankMask2.mask,hq]))
  change (regValue (bank.take 96) u.basis=_) ∧ (regValue ((bank.drop 98).take 21) u.basis=_)
  rw [ctl,s0,s1,b0,b1]
  exact chunks

#print axioms loan_frame
#print axioms loan_masked
end ECDSAAdd.Entrant.ParityLoan
namespace ECDSAAdd.Entrant.ParityLoan
open Arithmetic

theorem loan_zero (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis b0))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis b1) ^^ s.basis t)) :
    (run (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t) m s).basis b0=false ∧
    (run (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t) m s).basis b1=false := by
  have ne (i j : Nat) (hi : i<7) (hj : j<7) (hij : i≠j) :
      [a0,a1,b0,b1,h0,h1,t].getD i 0≠[a0,a1,b0,b1,h0,h1,t].getD j 0 :=
    CombinedBankLoan.get_ne _ hn i j hi hj hij
  have b0h1 : b0≠h1:=ne 2 5 (by decide) (by decide) (by decide)
  have b0b1 : b0≠b1:=ne 2 3 (by decide) (by decide) (by decide)
  rw [CombinedBankLoan.loan_run a0 a1 b0 b1 h0 h1 t hn s m r0 r1]
  simp [writeBit,b0h1,b0b1]

theorem loan_clear (a0 a1 h0 h1 t c : Wire) (src bank : List Wire)
    (hs : 119≤src.length) (hb : 119≤bank.length) (hcb : (c::(src++bank)).Nodup)
    (hn : [a0,a1,bank.getD 96 0,bank.getD 97 0,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis (bank.getD 96 0)))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis (bank.getD 97 0)) ^^ s.basis t))
    (old : regValue bank s.basis=if s.basis c then regValue src s.basis else 0)
    (away : ∀q∈c::(BankMask2.mask src++BankMask2.mask bank),
      q≠bank.getD 96 0 ∧ q≠bank.getD 97 0 ∧ q≠h0 ∧ q≠h1) :
    let loan:=CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t
    (run (loan++BankMask2.clearMasked c src bank) m s).phase=s.phase ∧
    regValue (bank.take 119) (run (loan++BankMask2.clearMasked c src bank) m s).basis=0 := by
  dsimp only
  let loan:=CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t
  let u:=run loan [] s
  have cm : measurementCount loan=0 := rfl
  have chunks:=loan_masked a0 a1 h0 h1 t c src bank hs hb hn s [] r0 r1 old away
  have z:=loan_zero a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s [] r0 r1
  have cl:=BankMask2.clear_correct c src bank hs hb hcb u m chunks.1 chunks.2 z.1 z.2
  have fr:=loan_frame a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s [] r0 r1
  change (run (loan++_) m s).phase=s.phase ∧ _
  rw [run_append,cm,List.take_zero,List.drop_zero]
  exact ⟨cl.1.trans fr.1,cl.2.2⟩

#print axioms loan_clear
end ECDSAAdd.Entrant.ParityLoan

namespace ParityCachedResearch
open ECDSAAdd ECDSAAdd.Arithmetic
def copy (control cache : Wire) : List Wire → List Wire → Program
 | _::src, b::dst => [.CX cache b] ++ copyRegister (some control) src dst
 | src, dst => copyRegister (some control) src dst

theorem run_eq (control cache : Wire) (src dst : List Wire) (s : State) (m : List Bool)
    (h : s.basis cache = (s.basis control && s.basis (src.headD 0))) :
    run (copy control cache src dst) m s = run (copyRegister (some control) src dst) m s := by
 cases src with
 | nil => rfl
 | cons a src =>
  cases dst with
  | nil => rfl
  | cons b dst =>
   have first (r : List Bool) : run [.CX cache b] r s = run [.CCX control a b] r s := by
    change (⟨s.phase,writeBit s.basis b (s.basis b ^^ s.basis cache)⟩ : State) =
      ⟨s.phase,writeBit s.basis b (s.basis b ^^ (s.basis control && s.basis a))⟩
    simpa only [List.headD_cons] using congrArg
      (fun v => (⟨s.phase,writeBit s.basis b (s.basis b ^^ v)⟩ : State)) h
   simp only [copy,copyRegister,copyGate,run_append]
   rw [first]
   rfl


end ParityCachedResearch

namespace ECDSAAdd.Entrant.ParityLoan
open Arithmetic

theorem cached_recopy (c cache : Wire) (src bank : List Wire) (hs : 119 ≤ src.length)
    (hb : 119 ≤ bank.length) (hn : (src++bank).Nodup) (hc : c ∉ bank)
    (p v : State) (m : List Bool)
    (old : regValue bank p.basis=if p.basis c then regValue src p.basis else 0)
    (vz : regValue (BankMask2.mask bank) v.basis=0)
    (ctl : v.basis c=p.basis c)
    (source : regValue (BankMask2.mask src) v.basis=regValue (BankMask2.mask src) p.basis)
    (cached : v.basis cache=(v.basis c && v.basis (src.headD 0))) :
    (run (ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) m v).phase=v.phase ∧
    (∀q,q ∉ BankMask2.mask bank →
      (run (ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) m v).basis q=v.basis q) ∧
    (∀q ∈ BankMask2.mask bank,
      (run (ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) m v).basis q=p.basis q) := by
  have ch : v.basis cache=(v.basis c && v.basis ((BankMask2.mask src).headD 0)) := by
    simpa only [BankMask2.mask_head] using cached
  rw [ParityCachedResearch.run_eq c cache (BankMask2.mask src) (BankMask2.mask bank) v m ch]
  exact BankMask2.recopy_correct c src bank hs hb hn hc p v m old vz ctl source

#print axioms cached_recopy
end ECDSAAdd.Entrant.ParityLoan
namespace ECDSAAdd.Entrant.ParityLoan
open Arithmetic

theorem loan_saved (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis b0))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis b1) ^^ s.basis t)) :
    (run (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t) m s).basis h0=s.basis b0 ∧
    (run (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t) m s).basis h1=s.basis b1 := by
  have ne (i j : Nat) (hi : i<7) (hj : j<7) (hij : i≠j) :
      [a0,a1,b0,b1,h0,h1,t].getD i 0≠[a0,a1,b0,b1,h0,h1,t].getD j 0 :=
    CombinedBankLoan.get_ne _ hn i j hi hj hij
  have h0b1 : h0≠b1:=ne 4 3 (by decide) (by decide) (by decide)
  have h0h1 : h0≠h1:=ne 4 5 (by decide) (by decide) (by decide)
  have h0b0 : h0≠b0:=ne 4 2 (by decide) (by decide) (by decide)
  have h1b1 : h1≠b1:=ne 5 3 (by decide) (by decide) (by decide)
  rw [CombinedBankLoan.loan_run a0 a1 b0 b1 h0 h1 t hn s m r0 r1]
  simp [writeBit,h0b1,h0h1,h0b0,h1b1]

theorem loan_clear_saved (a0 a1 h0 h1 t c : Wire) (src bank : List Wire)
    (hs : 119≤src.length) (hb : 119≤bank.length) (hcb : (c::(src++bank)).Nodup)
    (hn : [a0,a1,bank.getD 96 0,bank.getD 97 0,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis (bank.getD 96 0)))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis (bank.getD 97 0)) ^^ s.basis t))
    (old : regValue bank s.basis=if s.basis c then regValue src s.basis else 0)
    (away : ∀q∈c::(BankMask2.mask src++BankMask2.mask bank),
      q≠bank.getD 96 0 ∧ q≠bank.getD 97 0 ∧ q≠h0 ∧ q≠h1)
    (hp0 : h0 ∉ bank.take 119) (hp1 : h1 ∉ bank.take 119) :
    let loan:=CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t
    let u:=run (loan++BankMask2.clearMasked c src bank) m s
    u.phase=s.phase ∧ regValue (bank.take 119) u.basis=0 ∧
      u.basis h0=s.basis (bank.getD 96 0) ∧ u.basis h1=s.basis (bank.getD 97 0) := by
  dsimp only
  let loan:=CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t
  let v:=run loan [] s
  have cm : measurementCount loan=0 := rfl
  have chunks:=loan_masked a0 a1 h0 h1 t c src bank hs hb hn s [] r0 r1 old away
  have z:=loan_zero a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s [] r0 r1
  have cl:=BankMask2.clear_correct c src bank hs hb hcb v m chunks.1 chunks.2 z.1 z.2
  have saved:=loan_saved a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s [] r0 r1
  have fr:=loan_frame a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s [] r0 r1
  change (run (loan++_) m s).phase=s.phase ∧ _
  rw [run_append,cm,List.take_zero,List.drop_zero]
  exact ⟨cl.1.trans fr.1,cl.2.2,(cl.2.1 h0 hp0).trans saved.1,(cl.2.1 h1 hp1).trans saved.2⟩

#print axioms loan_clear_saved
end ECDSAAdd.Entrant.ParityLoan
namespace ParityProtocolResources
open ECDSAAdd ECDSAAdd.Arithmetic

theorem copy_slots (c cache : Wire) : ∀(src dst : List Wire),src.length=dst.length →
    Challenge.gateSlots (ParityCachedResearch.copy c cache src dst)=src.length
  | [],[],_ => rfl
  | [],_::_,h => by simp at h
  | _::_,[],h => by simp at h
  | _::src,_::dst,h => by
    have lengths : src.length=dst.length := by simpa using h
    have cp : ∀(a b : List Wire),a.length=b.length →
        Challenge.gateSlots (copyRegister (some c) a b)=a.length := by
      intro a
      induction a with
      | nil => intro b hb;cases b <;> simp_all [copyRegister,Challenge.gateSlots]
      | cons x a ih =>
        intro b hb
        cases b with
        | nil => simp at hb
        | cons y b =>
          have eql : a.length=b.length := by simpa using hb
          simp only [copyRegister,copyGate,Challenge.gateSlots,Challenge.instructionSlots,List.map_cons,List.sum_cons]
          have e:=ih b eql
          change 1+Challenge.gateSlots (copyRegister (some c) a b)=a.length+1
          omega
    have e:=cp src dst lengths
    change 1+Challenge.gateSlots (copyRegister (some c) src dst)=src.length+1
    omega

theorem copy_counts (c cache : Wire) (src dst : List Wire) (hlen : src.length=dst.length)
    (nonempty : 0<src.length) :
    toffoliCount (ParityCachedResearch.copy c cache src dst)+1=src.length ∧
    measurementCount (ParityCachedResearch.copy c cache src dst)=0 := by
  cases src with
  | nil => simp at nonempty
  | cons a src =>
    cases dst with
    | nil => simp at hlen
    | cons b dst =>
      have lengths : src.length=dst.length := by simpa using hlen
      have old:=copyRegister_counts (some c) src dst lengths
      simp [ParityCachedResearch.copy,toffoliCount,measurementCount,old.1,old.2]

#print axioms copy_counts
#print axioms copy_slots
end ParityProtocolResources
namespace ParityProtocolResources
open ECDSAAdd ECDSAAdd.Arithmetic

def fragment (a0 a1 b0 b1 h0 h1 t c cache : Wire) (src bank : List Wire) : Program :=
  CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t++BankMask2.clearMasked c src bank++
    ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank)++
    CombinedBankLoan.restore a0 a1 b0 b1 h0 h1 t

theorem fragment_counts (a0 a1 b0 b1 h0 h1 t c cache : Wire) (src bank : List Wire)
    (hs : 119≤src.length) (hb : 119≤bank.length) :
    toffoliCount (fragment a0 a1 b0 b1 h0 h1 t c cache src bank)=116 ∧
    measurementCount (fragment a0 a1 b0 b1 h0 h1 t c cache src bank)=119 ∧
    Challenge.gateSlots (fragment a0 a1 b0 b1 h0 h1 t c cache src bank)=363 := by
  have sl:=BankMask2.mask_length src hs
  have bl:=BankMask2.mask_length bank hb
  have cp:=copy_counts c cache (BankMask2.mask src) (BankMask2.mask bank) (by rw [sl,bl]) (by omega)
  have cs:=copy_slots c cache (BankMask2.mask src) (BankMask2.mask bank) (by rw [sl,bl])
  have cc:=BankMask2.clear_counts c src bank hs hb
  have ct : toffoliCount (ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank))=116 := by omega
  have cslot : Challenge.gateSlots (ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank))=117 := cs.trans sl
  simp only [fragment,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,ct,cp.2,cc.1,cc.2.1,cc.2.2,cslot]
  exact ⟨rfl,rfl,rfl⟩

theorem original_counts (c cache : Wire) (src bank : List Wire)
    (hs : 119≤src.length) (hb : 119≤bank.length) :
    let old:=eraseMask c (src.take 119) (bank.take 119)++
      ParityCachedResearch.copy c cache (src.take 119) (bank.take 119)
    toffoliCount old=118 ∧ measurementCount old=119 ∧ Challenge.gateSlots old=357 := by
  dsimp only
  have sl : (src.take 119).length=119 := by simp only [List.length_take];omega
  have bl : (bank.take 119).length=119 := by simp only [List.length_take];omega
  have cp:=copy_counts c cache (src.take 119) (bank.take 119) (by rw [sl,bl]) (by omega)
  have cs:=copy_slots c cache (src.take 119) (bank.take 119) (by rw [sl,bl])
  have cc:=eraseMask_counts c (src.take 119) (bank.take 119) (by rw [sl,bl])
  have es:=BankMask2.erase_slots c (src.take 119) (bank.take 119) (by rw [sl,bl])
  simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  omega

#print axioms fragment_counts
#print axioms original_counts
end ParityProtocolResources
namespace ParityProtocolResources
open ECDSAAdd ECDSAAdd.Arithmetic

theorem loans_physical (a0 a1 b0 b1 h0 h1 t : Wire) (hn : [a0,a1,b0,b1,h0,h1,t].Nodup) :
    GatePhysical (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t) ∧
    GatePhysical (CombinedBankLoan.restore a0 a1 b0 b1 h0 h1 t) := by
  have ne (i j : Nat) (hi : i<7) (hj : j<7) (hij : i≠j) :
      [a0,a1,b0,b1,h0,h1,t].getD i 0≠[a0,a1,b0,b1,h0,h1,t].getD j 0 :=
    CombinedBankLoan.get_ne _ hn i j hi hj hij
  have p0:=LinearBankLoan.physical0 a0 b0 h0
    (ne 0 4 (by decide) (by decide) (by decide)) (ne 4 2 (by decide) (by decide) (by decide))
  have p1:=LinearBankLoan.physical1 a1 b1 h1 t
    (ne 1 5 (by decide) (by decide) (by decide)) (ne 6 5 (by decide) (by decide) (by decide))
    (ne 5 3 (by decide) (by decide) (by decide))
  simpa only [CombinedBankLoan.loan,CombinedBankLoan.restore,gatePhysical_append] using And.intro (And.intro p0.1 p1.1) (And.intro p1.2 p0.2)

theorem clear_physical (c : Wire) (src bank : List Wire) : GatePhysical (BankMask2.clearMasked c src bank) := by
  rw [BankMask2.clearMasked,gatePhysical_append,gatePhysical_append]
  exact ⟨⟨eraseMask_physical _ _ _,by intro i hi;simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;rcases hi with rfl|rfl <;> trivial⟩,eraseMask_physical _ _ _⟩

theorem cached_physical (c cache : Wire) (src bank : List Wire)
    (hn : (src++bank).Nodup) (hc : c ∉ bank) (hd : cache≠bank.headD 0) :
    GatePhysical (ParityCachedResearch.copy c cache src bank) := by
  have cp:=copyRegister_physical (some c) src bank hn (by simpa using hc)
  cases src with
  | nil => exact cp
  | cons a src =>
    cases bank with
    | nil => exact cp
    | cons b bank =>
      simp only [ParityCachedResearch.copy,copyRegister,copyGate,gatePhysical_append] at cp ⊢
      refine ⟨?_,cp.2⟩
      intro i hi
      have hi' : i=Instr.CX cache b := by simpa using hi
      subst i
      simpa [GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate] using hd

theorem fragment_physical (a0 a1 b0 b1 h0 h1 t c cache : Wire) (src bank : List Wire)
    (hn : [a0,a1,b0,b1,h0,h1,t].Nodup) (hsb : (src++bank).Nodup)
    (hc : c ∉ bank) (hd : cache≠(BankMask2.mask bank).headD 0) :
    GatePhysical (fragment a0 a1 b0 b1 h0 h1 t c cache src bank) := by
  have lp:=loans_physical a0 a1 b0 b1 h0 h1 t hn
  have mp:=cached_physical c cache (BankMask2.mask src) (BankMask2.mask bank)
    (BankMask2.pair_nodup src bank hsb) (fun h=>hc ((BankMask2.mask_sublist bank).subset h)) hd
  simp only [fragment,gatePhysical_append]
  exact ⟨⟨⟨lp.1,clear_physical c src bank⟩,mp⟩,lp.2⟩

#print axioms fragment_physical
end ParityProtocolResources
namespace ParityProtocolResources
open ECDSAAdd ECDSAAdd.Arithmetic

theorem clear_support (c : Wire) (src bank : List Wire) (hb : 98≤bank.length) :
    wires (BankMask2.clearMasked c src bank)⊆(c::(src++bank)).toFinset := by
  have sub (a b : List Wire) (ha : ∀q∈a,q∈src) (hb : ∀q∈b,q∈bank) :
      wires (eraseMask c a b)⊆(c::(src++bank)).toFinset := by
    intro q hq
    have h:=eraseMask_wires_subset c a b hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    rcases h with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl (ha q h))
    · exact Or.inr (Or.inr (hb q h))
  have e0:=sub (src.take 96) (bank.take 96)
    (fun _ h=>List.mem_of_mem_take h) (fun _ h=>List.mem_of_mem_take h)
  have e1:=sub ((src.drop 98).take 21) ((bank.drop 98).take 21)
    (fun _ h=>List.mem_of_mem_drop (List.mem_of_mem_take h))
    (fun _ h=>List.mem_of_mem_drop (List.mem_of_mem_take h))
  have m0 : bank.getD 96 0∈bank := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have m1 : bank.getD 97 0∈bank := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  intro q hq
  simp only [BankMask2.clearMasked,wires_append,Finset.mem_union] at hq
  rcases hq with (h|h)|h
  · exact e0 h
  · simp [wires,Instr.wires,correctionWires] at h
    rcases h with rfl|rfl
    · simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
      exact Or.inr (Or.inr m0)
    · simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
      exact Or.inr (Or.inr m1)
  · exact e1 h

#print axioms clear_support
end ParityProtocolResources
namespace ECDSAAdd.Entrant.ParityLoan
open Arithmetic

theorem restored_bank_frame (bank out : List Wire) (h0 h1 t : Wire)
    (hb : 119≤bank.length) (bn : bank.Nodup)
    (hn : [bank.getD 64 0,bank.getD 65 0,bank.getD 96 0,bank.getD 97 0,h0,h1,t].Nodup)
    (p w : State) (m : List Bool)
    (z0 : w.basis (bank.getD 96 0)=false) (z1 : w.basis (bank.getD 97 0)=false)
    (saved0 : w.basis h0=p.basis (bank.getD 96 0))
    (saved1 : w.basis h1=p.basis (bank.getD 97 0)) (tval : w.basis t=p.basis t)
    (r0 : p.basis h0=(p.basis (bank.getD 64 0) ^^ p.basis (bank.getD 96 0)))
    (r1 : p.basis h1=((p.basis (bank.getD 65 0) ^^ p.basis (bank.getD 97 0)) ^^ p.basis t))
    (masked : ∀q∈BankMask2.mask bank,w.basis q=p.basis q)
    (suffix : ∀q∈bank.drop 119,w.basis q=p.basis q)
    (outside : ∀q,q ∉ out → q ∉ bank → q≠h0 → q≠h1 → w.basis q=p.basis q)
    (away : ∀q∈out,q ∉ bank ∧ q≠h0 ∧ q≠h1) :
    let restored:=run (CombinedBankLoan.restore (bank.getD 64 0) (bank.getD 65 0)
      (bank.getD 96 0) (bank.getD 97 0) h0 h1 t) m w
    restored.phase=w.phase ∧ (∀q,q ∉ out → restored.basis q=p.basis q) ∧
      (∀q∈out,restored.basis q=w.basis q) := by
  have ma0 : bank.getD 64 0∈BankMask2.mask bank :=
    (BankMask2.mask_mem bank bn 64 (by omega)).mpr (Or.inl (by decide))
  have ma1 : bank.getD 65 0∈BankMask2.mask bank :=
    (BankMask2.mask_mem bank bn 65 (by omega)).mpr (Or.inl (by decide))
  have b0mem : bank.getD 96 0∈bank := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have b1mem : bank.getD 97 0∈bank := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  apply restore_frame (bank.getD 64 0) (bank.getD 65 0) (bank.getD 96 0) (bank.getD 97 0)
    h0 h1 t hn out p w m z0 z1 saved0 saved1 (masked _ ma0) (masked _ ma1) tval r0 r1
  · intro q hq qb0 qb1 qh0 qh1
    by_cases hbank : q∈bank
    · rcases BankMask2.partition bank bn q hbank with h|h|h|h
      · exact masked q h
      · exact False.elim (qb0 h)
      · exact False.elim (qb1 h)
      · exact suffix q h
    · exact outside q hq hbank qh0 qh1
  · intro q hq
    obtain ⟨qb,qh0,qh1⟩:=away q hq
    exact ⟨fun h=>qb (h ▸ b0mem),fun h=>qb (h ▸ b1mem),qh0,qh1⟩

#print axioms restored_bank_frame
end ECDSAAdd.Entrant.ParityLoan
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def bank (L : CuccaroStreamedSquareWideLayout) (src : List Wire) := L.inputBank.take src.length

def loan (L : CuccaroStreamedSquareWideLayout) (ext src : List Wire) : Program :=
  CombinedBankLoan.loan ((bank L src).getD 64 0) ((bank L src).getD 65 0)
    ((bank L src).getD 96 0) ((bank L src).getD 97 0) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)

def restore (L : CuccaroStreamedSquareWideLayout) (ext src : List Wire) : Program :=
  CombinedBankLoan.restore ((bank L src).getD 64 0) ((bank L src).getD 65 0)
    ((bank L src).getD 96 0) ((bank L src).getD 97 0) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)

def clearMasked (L : CuccaroStreamedSquareWideLayout) (control : Wire) (src : List Wire) : Program :=
  BankMask2.clearMasked control src (bank L src)

def recopy (L : CuccaroStreamedSquareWideLayout) (control : Wire) (src dst : List Wire) : Program :=
  CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) (BankMask2.mask src) (BankMask2.mask (bank L src))

def program (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program) : Program :=
  ParkCopy.pA L control src++ParkCopy.pM L ext src dst++loan L ext src++clearMasked L control src++
    ParkCopy.pD ext++ParkCopy.pMI L ext src++ParkCopy.pB L ext body++recopy L control src dst++
    ParkCopy.pMO L ext src++restore L ext src++ParkCopy.pCL L ext src dst++ParkCopy.pE L control src

theorem counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program) (h128 : src.length=128) :
    toffoliCount (program L ext control src dst body)+2=toffoliCount (ParkCopy.withLowK2P L ext control src dst body) ∧
    measurementCount (program L ext control src dst body)=measurementCount (ParkCopy.withLowK2P L ext control src dst body) ∧
    Challenge.gateSlots (program L ext control src dst body)=Challenge.gateSlots (ParkCopy.withLowK2P L ext control src dst body)+6 := by
  have bl : (bank L src).length=128 := by
    simp only [bank,List.length_take,(L.measured_bank_widths hw).1,h128]
    rfl
  have hn:=ParityProtocolResources.fragment_counts ((bank L src).getD 64 0) ((bank L src).getD 65 0)
    ((bank L src).getD 96 0) ((bank L src).getD 97 0) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)
    control (LowZero18Square.cacheWire L dst) src (bank L src) (by omega) (by omega)
  have ho:=ParityProtocolResources.original_counts control (LowZero18Square.cacheWire L dst) src (bank L src) (by omega) (by omega)
  have copy_eq (a b : List Wire) :
      ParityCachedResearch.copy control (LowZero18Square.cacheWire L dst) a b=
        CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) a b := by
    cases a <;> cases b <;> rfl
  simp only [ParityProtocolResources.fragment,copy_eq,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at hn ho
  simp only [program,ParkCopy.withLowK2P,ParkCopy.pE1,ParkCopy.pC1,loan,restore,clearMasked,recopy,bank,
    toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at hn ho ⊢
  omega

#print axioms counts
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem slice_get (r : List Wire) (a n i : Nat) (hi : i<n) (hr : a+i<r.length) :
    ((r.drop a).take n).getD i 0=r.getD (a+i) 0 := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_take,List.length_drop];omega),
    List.getD_eq_getElem _ _ hr]
  simp only [List.getElem_take,List.getElem_drop]

theorem drop_get (r : List Wire) (a i : Nat) (hr : a+i<r.length) :
    (r.drop a).getD i 0=r.getD (a+i) 0 := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_drop];omega),List.getD_eq_getElem _ _ hr]
  simp only [List.getElem_drop]

theorem actual_sum_bits (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (he : 300≤ext.length) (h128 : src.length=128)
    (p : BasisState) (v : Nat)
    (bv : regValue (LowZero18LowK.jregsH L ext src dst).bank p=v)
    (inv : (LowZero18LowK.jregsH L ext src dst).invF v p) :
    p (ext.getD 198 0)=(p ((bank L src).getD 64 0) ^^ p ((bank L src).getD 96 0)) ∧
    p (ext.getD 199 0)=((p ((bank L src).getD 65 0) ^^ p ((bank L src).getD 97 0)) ^^ p (ext.getD 233 0)) := by
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  let R:=LowZero18LowK.jregsH L ext src dst
  have rb : R.bank=(bank L src).drop 64 := rfl
  have rs : R.S=(ext.drop 198).take 33 := by simp [R,LowZero18LowK.jregsH,List.take_take]
  have rt : R.T=(ext.drop 232).take 66 := rfl
  have bits:=ParityLoan.inner_sum_bits R rfl (by rw [rb,List.length_drop,bl];decide)
    (by rw [rs];simp only [List.length_take,List.length_drop];omega)
    (by rw [rt];simp only [List.length_take,List.length_drop];omega) p v bv inv
  have b0 : R.bank.getD 0 0=(bank L src).getD 64 0 := by rw [rb,drop_get _ 64 0 (by omega)]
  have b1 : R.bank.getD 1 0=(bank L src).getD 65 0 := by rw [rb,drop_get _ 64 1 (by omega)]
  have b32 : R.bank.getD 32 0=(bank L src).getD 96 0 := by rw [rb,drop_get _ 64 32 (by omega)]
  have b33 : R.bank.getD 33 0=(bank L src).getD 97 0 := by rw [rb,drop_get _ 64 33 (by omega)]
  have s0 : R.S.getD 0 0=ext.getD 198 0 := by rw [rs,slice_get _ 198 33 0 (by decide) (by omega)]
  have s1 : R.S.getD 1 0=ext.getD 199 0 := by rw [rs,slice_get _ 198 33 1 (by decide) (by omega)]
  have t1 : R.T.getD 1 0=ext.getD 233 0 := by rw [rt,slice_get _ 232 66 1 (by decide) (by omega)]
  simpa only [b0,b1,b32,b33,s0,s1,t1] using bits

#print axioms actual_sum_bits
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic

theorem index_nodup (r : List Wire) (hn : r.Nodup) (idx : List Nat) (hi : idx.Nodup)
    (hb : ∀i∈idx,i<r.length) : (idx.map (fun i=>r.getD i 0)).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj e
    rw [List.getD_eq_getElem _ _ (hb i hi),List.getD_eq_getElem _ _ (hb j hj)] at e
    exact (List.Nodup.getElem_inj_iff hn).mp e
  · exact hi

theorem loan_nodup (bank ext : List Wire) (hb : bank.length=128) (he : 300≤ext.length)
    (hn : (bank++ext).Nodup) :
    [bank.getD 64 0,bank.getD 65 0,bank.getD 96 0,bank.getD 97 0,
      ext.getD 198 0,ext.getD 199 0,ext.getD 233 0].Nodup := by
  have bn:= (List.nodup_append'.mp hn).1
  have en:= (List.nodup_append'.mp hn).2.1
  have dj:= (List.nodup_append'.mp hn).2.2
  have nb : [bank.getD 64 0,bank.getD 65 0,bank.getD 96 0,bank.getD 97 0].Nodup := by
    apply index_nodup bank bn [64,65,96,97] (by decide)
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> omega
  have ne : [ext.getD 198 0,ext.getD 199 0,ext.getD 233 0].Nodup := by
    apply index_nodup ext en [198,199,233] (by decide)
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl <;> omega
  have disjoint : ∀q∈[bank.getD 64 0,bank.getD 65 0,bank.getD 96 0,bank.getD 97 0],
      q ∉ [ext.getD 198 0,ext.getD 199 0,ext.getD 233 0] := by
    intro q hq hq'
    have qb : q∈bank := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> exact ParkCopy.getD_mem _ _ (by omega)
    have qe : q∈ext := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq'
      rcases hq' with rfl|rfl|rfl <;> exact ParkCopy.getD_mem _ _ (by omega)
    exact dj qb qe
  exact List.nodup_append'.mpr ⟨nb,ne,disjoint⟩

#print axioms loan_nodup
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem pre_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (control : Wire) (he : 300≤ext.length) (h128 : src.length=128)
    (p : State) (m : List Bool) (v : Nat)
    (bv : regValue (LowZero18LowK.jregsH L ext src dst).bank p.basis=v)
    (inv : (LowZero18LowK.jregsH L ext src dst).invF v p.basis)
    (old : regValue (bank L src) p.basis=if p.basis control then regValue src p.basis else 0)
    (hn : (control::(src++bank L src++ext)).Nodup) :
    let u:=run (loan L ext src++clearMasked L control src) m p
    u.phase=p.phase ∧ regValue ((bank L src).take 119) u.basis=0 ∧
      u.basis (ext.getD 198 0)=p.basis ((bank L src).getD 96 0) ∧
      u.basis (ext.getD 199 0)=p.basis ((bank L src).getD 97 0) := by
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have hctl:= (List.nodup_cons.mp hn).1
  have hrest:= (List.nodup_cons.mp hn).2
  have hnSB:= (List.nodup_append'.mp hrest).1
  have hnE:= (List.nodup_append'.mp hrest).2.1
  have djE:= (List.nodup_append'.mp hrest).2.2
  have hnS:= (List.nodup_append'.mp hnSB).1
  have hnB:= (List.nodup_append'.mp hnSB).2.1
  have djB:= (List.nodup_append'.mp hnSB).2.2
  have bankExt : (bank L src++ext).Nodup :=
    List.nodup_append'.mpr ⟨hnB,hnE,fun {_} hq hq'=>djE (List.mem_append_right src hq) hq'⟩
  have ln:=loan_nodup (bank L src) ext bl he bankExt
  have bits:=actual_sum_bits L hw ext src dst he h128 p.basis v bv inv
  have x0 : ext.getD 198 0∈ext := ParkCopy.getD_mem _ _ (by omega)
  have x1 : ext.getD 199 0∈ext := ParkCopy.getD_mem _ _ (by omega)
  have b0 : (bank L src).getD 96 0∈bank L src := ParkCopy.getD_mem _ _ (by omega)
  have b1 : (bank L src).getD 97 0∈bank L src := ParkCopy.getD_mem _ _ (by omega)
  have exclusions:=BankMask2.excludes (bank L src) hnB (by omega)
  have away : ∀q∈control::(BankMask2.mask src++BankMask2.mask (bank L src)),
      q≠(bank L src).getD 96 0 ∧ q≠(bank L src).getD 97 0 ∧ q≠ext.getD 198 0 ∧ q≠ext.getD 199 0 := by
    intro q hq
    simp only [List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hq|hq
    · refine ⟨?_,?_,?_,?_⟩ <;> intro e <;> apply hctl
      · exact e.symm ▸ List.mem_append_left ext (List.mem_append_right src b0)
      · exact e.symm ▸ List.mem_append_left ext (List.mem_append_right src b1)
      · exact e.symm ▸ List.mem_append_right (src++bank L src) x0
      · exact e.symm ▸ List.mem_append_right (src++bank L src) x1
    · have qs: q∈src:=(BankMask2.mask_sublist src).subset hq
      refine ⟨?_,?_,?_,?_⟩ <;> intro e
      · exact djB qs (e.symm ▸ b0)
      · exact djB qs (e.symm ▸ b1)
      · exact djE (List.mem_append_left _ qs) (e.symm ▸ x0)
      · exact djE (List.mem_append_left _ qs) (e.symm ▸ x1)
    · have qb: q∈bank L src:=(BankMask2.mask_sublist (bank L src)).subset hq
      refine ⟨?_,?_,?_,?_⟩ <;> intro e
      · exact exclusions.1 (e ▸ hq)
      · exact exclusions.2 (e ▸ hq)
      · exact djE (List.mem_append_right src qb) (e.symm ▸ x0)
      · exact djE (List.mem_append_right src qb) (e.symm ▸ x1)
  have oldN : (control::(src++bank L src)).Nodup := List.nodup_cons.mpr
    ⟨fun h=>hctl (List.mem_append_left ext h),hnSB⟩
  have hp0 : ext.getD 198 0 ∉ (bank L src).take 119 := fun h=>
    djE (List.mem_append_right src (List.mem_of_mem_take h)) x0
  have hp1 : ext.getD 199 0 ∉ (bank L src).take 119 := fun h=>
    djE (List.mem_append_right src (List.mem_of_mem_take h)) x1
  exact ParityLoan.loan_clear_saved ((bank L src).getD 64 0) ((bank L src).getD 65 0)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) control src (bank L src)
    (by omega) (by omega) oldN ln p m bits.1 bits.2 old away hp0 hp1

#print axioms pre_correct
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityLoan
open Arithmetic

theorem loan_clear_frame (a0 a1 h0 h1 t c : Wire) (src bank : List Wire)
    (hs : 119≤src.length) (hb : 119≤bank.length) (hcb : (c::(src++bank)).Nodup)
    (hn : [a0,a1,bank.getD 96 0,bank.getD 97 0,h0,h1,t].Nodup)
    (s : State) (m : List Bool)
    (r0 : s.basis h0=(s.basis a0 ^^ s.basis (bank.getD 96 0)))
    (r1 : s.basis h1=((s.basis a1 ^^ s.basis (bank.getD 97 0)) ^^ s.basis t))
    (old : regValue bank s.basis=if s.basis c then regValue src s.basis else 0)
    (away : ∀q∈c::(BankMask2.mask src++BankMask2.mask bank),
      q≠bank.getD 96 0 ∧ q≠bank.getD 97 0 ∧ q≠h0 ∧ q≠h1) :
    ∀q,q ∉ bank.take 119 → q≠h0 → q≠h1 →
      (run (CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t++
        BankMask2.clearMasked c src bank) m s).basis q=s.basis q := by
  let loan:=CombinedBankLoan.loan a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t
  let u:=run loan [] s
  have cm : measurementCount loan=0 := rfl
  have chunks:=loan_masked a0 a1 h0 h1 t c src bank hs hb hn s [] r0 r1 old away
  have z:=loan_zero a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s [] r0 r1
  have cl:=BankMask2.clear_correct c src bank hs hb hcb u m chunks.1 chunks.2 z.1 z.2
  have fr:=loan_frame a0 a1 (bank.getD 96 0) (bank.getD 97 0) h0 h1 t hn s [] r0 r1
  have bn:= (List.nodup_append'.mp (List.nodup_cons.mp hcb).2).2.1
  have b0mem : bank.getD 96 0∈bank.take 119 := by
    simpa only [List.drop_zero] using (BankMask2.getD_mem_slice bank bn 96 0 119 (by omega)).mpr (by omega)
  have b1mem : bank.getD 97 0∈bank.take 119 := by
    simpa only [List.drop_zero] using (BankMask2.getD_mem_slice bank bn 97 0 119 (by omega)).mpr (by omega)
  intro q hq qh0 qh1
  have qb0 : q≠bank.getD 96 0 := fun e=>hq (e.symm ▸ b0mem)
  have qb1 : q≠bank.getD 97 0 := fun e=>hq (e.symm ▸ b1mem)
  change (run (loan++_) m s).basis q=s.basis q
  rw [run_append,cm,List.take_zero,List.drop_zero]
  exact (cl.2.1 q hq).trans (fr.2 q qb0 qb1 qh0 qh1)

#print axioms loan_clear_frame
end ECDSAAdd.Entrant.ParityLoan
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem pre_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (control : Wire) (he : 300≤ext.length) (h128 : src.length=128)
    (p : State) (m : List Bool) (v : Nat)
    (bv : regValue (LowZero18LowK.jregsH L ext src dst).bank p.basis=v)
    (inv : (LowZero18LowK.jregsH L ext src dst).invF v p.basis)
    (old : regValue (bank L src) p.basis=if p.basis control then regValue src p.basis else 0)
    (hn : (control::(src++bank L src++ext)).Nodup) :
    ∀q,q ∉ (bank L src).take 119 → q≠ext.getD 198 0 → q≠ext.getD 199 0 →
      (run (loan L ext src++clearMasked L control src) m p).basis q=p.basis q := by
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have hctl:= (List.nodup_cons.mp hn).1
  have hrest:= (List.nodup_cons.mp hn).2
  have hnSB:= (List.nodup_append'.mp hrest).1
  have hnE:= (List.nodup_append'.mp hrest).2.1
  have djE:= (List.nodup_append'.mp hrest).2.2
  have hnS:= (List.nodup_append'.mp hnSB).1
  have hnB:= (List.nodup_append'.mp hnSB).2.1
  have djB:= (List.nodup_append'.mp hnSB).2.2
  have bankExt : (bank L src++ext).Nodup :=
    List.nodup_append'.mpr ⟨hnB,hnE,fun {_} hq hq'=>djE (List.mem_append_right src hq) hq'⟩
  have ln:=loan_nodup (bank L src) ext bl he bankExt
  have bits:=actual_sum_bits L hw ext src dst he h128 p.basis v bv inv
  have x0 : ext.getD 198 0∈ext := ParkCopy.getD_mem _ _ (by omega)
  have x1 : ext.getD 199 0∈ext := ParkCopy.getD_mem _ _ (by omega)
  have b0 : (bank L src).getD 96 0∈bank L src := ParkCopy.getD_mem _ _ (by omega)
  have b1 : (bank L src).getD 97 0∈bank L src := ParkCopy.getD_mem _ _ (by omega)
  have exclusions:=BankMask2.excludes (bank L src) hnB (by omega)
  have away : ∀q∈control::(BankMask2.mask src++BankMask2.mask (bank L src)),
      q≠(bank L src).getD 96 0 ∧ q≠(bank L src).getD 97 0 ∧ q≠ext.getD 198 0 ∧ q≠ext.getD 199 0 := by
    intro q hq
    simp only [List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hq|hq
    · refine ⟨?_,?_,?_,?_⟩ <;> intro e <;> apply hctl
      · exact e.symm ▸ List.mem_append_left ext (List.mem_append_right src b0)
      · exact e.symm ▸ List.mem_append_left ext (List.mem_append_right src b1)
      · exact e.symm ▸ List.mem_append_right (src++bank L src) x0
      · exact e.symm ▸ List.mem_append_right (src++bank L src) x1
    · have qs: q∈src:=(BankMask2.mask_sublist src).subset hq
      refine ⟨?_,?_,?_,?_⟩ <;> intro e
      · exact djB qs (e.symm ▸ b0)
      · exact djB qs (e.symm ▸ b1)
      · exact djE (List.mem_append_left _ qs) (e.symm ▸ x0)
      · exact djE (List.mem_append_left _ qs) (e.symm ▸ x1)
    · have qb: q∈bank L src:=(BankMask2.mask_sublist (bank L src)).subset hq
      refine ⟨?_,?_,?_,?_⟩ <;> intro e
      · exact exclusions.1 (e ▸ hq)
      · exact exclusions.2 (e ▸ hq)
      · exact djE (List.mem_append_right src qb) (e.symm ▸ x0)
      · exact djE (List.mem_append_right src qb) (e.symm ▸ x1)
  have oldN : (control::(src++bank L src)).Nodup := List.nodup_cons.mpr
    ⟨fun h=>hctl (List.mem_append_left ext h),hnSB⟩
  have hp0 : ext.getD 198 0 ∉ (bank L src).take 119 := fun h=>
    djE (List.mem_append_right src (List.mem_of_mem_take h)) x0
  have hp1 : ext.getD 199 0 ∉ (bank L src).take 119 := fun h=>
    djE (List.mem_append_right src (List.mem_of_mem_take h)) x1
  exact ParityLoan.loan_clear_frame ((bank L src).getD 64 0) ((bank L src).getD 65 0)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) control src (bank L src)
    (by omega) (by omega) oldN ln p m bits.1 bits.2 old away

#print axioms pre_frame
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic

theorem hosts_away (ext : List Wire) (hx : ext.Nodup) (he : 300≤ext.length)
    (h : Wire) (hh : h∈ParkCopy.hosts ext) :
    h≠ext.getD 198 0 ∧ h≠ext.getD 199 0 ∧ h≠ext.getD 233 0 := by
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hh
  have ilt : i<ext.length := by have b:=ParkCopy.host_index i hi;omega
  have ex : i≠198 ∧ i≠199 ∧ i≠233 := by
    simp only [ParkCopy.hostIdx,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact ⟨CombinedBankLoan.get_ne ext hx i 198 ilt (by omega) ex.1,
    CombinedBankLoan.get_ne ext hx i 199 ilt (by omega) ex.2.1,
    CombinedBankLoan.get_ne ext hx i 233 ilt (by omega) ex.2.2⟩

#print axioms hosts_away
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem pre_move_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (control : Wire) (he : 300≤ext.length) (h128 : src.length=128)
    (p : State) (m n : List Bool) (v : Nat)
    (bv : regValue (LowZero18LowK.jregsH L ext src dst).bank p.basis=v)
    (inv : (LowZero18LowK.jregsH L ext src dst).invF v p.basis)
    (old : regValue (bank L src) p.basis=if p.basis control then regValue src p.basis else 0)
    (hn : (control::(src++bank L src++ext)).Nodup)
    (hz : regValue (ParkCopy.hosts ext) p.basis=0) :
    let u:=run (loan L ext src++clearMasked L control src) m p
    let w:=run (ParkCopy.move ((bank L src).drop 119) (ParkCopy.hosts ext)) n u
    w.phase=p.phase ∧ regValue (bank L src) w.basis=0 ∧
      regValue (ParkCopy.hosts ext) w.basis=regValue ((bank L src).drop 119) p.basis ∧
      w.basis (ext.getD 198 0)=p.basis ((bank L src).getD 96 0) ∧
      w.basis (ext.getD 199 0)=p.basis ((bank L src).getD 97 0) ∧
      (∀q,q ∉ bank L src → q ∉ ParkCopy.hosts ext → q≠ext.getD 198 0 → q≠ext.getD 199 0 → w.basis q=p.basis q) := by
  let u:=run (loan L ext src++clearMasked L control src) m p
  let w:=run (ParkCopy.move ((bank L src).drop 119) (ParkCopy.hosts ext)) n u
  have pre:=pre_correct L hw ext src dst control he h128 p m v bv inv old hn
  have frame:=pre_frame L hw ext src dst control he h128 p m v bv inv old hn
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have hrest:= (List.nodup_cons.mp hn).2
  have hsb:= (List.nodup_append'.mp hrest).1
  have en:= (List.nodup_append'.mp hrest).2.1
  have dj:= (List.nodup_append'.mp hrest).2.2
  have bn:= (List.nodup_append'.mp hsb).2.1
  have bankExt {q : Wire} (qb : q∈bank L src) (qe : q∈ext) : False :=
    dj (List.mem_append_right src qb) qe
  have sub:=ParkCopy.hosts_sub ext he
  have bsplit : ((bank L src).take 119++(bank L src).drop 119).Nodup := by simpa only [List.take_append_drop] using bn
  have bdj:= (List.nodup_append'.mp bsplit).2.2
  have awayE {q : Wire} (qe : q∈ext) : q ∉ bank L src := fun qb=>bankExt qb qe
  have x0 : ext.getD 198 0∈ext := ParkCopy.getD_mem _ _ (by omega)
  have x1 : ext.getD 199 0∈ext := ParkCopy.getD_mem _ _ (by omega)
  have keepH : ∀q∈ParkCopy.hosts ext,u.basis q=p.basis q := by
    intro q hq
    have neq:=hosts_away ext en he q hq
    exact frame q (fun h=>awayE (sub q hq) (List.mem_of_mem_take h)) neq.1 neq.2.1
  have uz : regValue (ParkCopy.hosts ext) u.basis=0 :=
    (regValue_congr _ _ _ keepH).trans hz
  have suffixKeep : regValue ((bank L src).drop 119) u.basis=regValue ((bank L src).drop 119) p.basis := by
    apply regValue_congr
    intro q hq
    have qb : q∈bank L src:=List.mem_of_mem_drop hq
    exact frame q (fun h=>bdj h hq)
      (fun e=>bankExt qb (e.symm ▸ x0)) (fun e=>bankExt qb (e.symm ▸ x1))
  have lengths : ((bank L src).drop 119).length=(ParkCopy.hosts ext).length := by
    rw [List.length_drop,bl,ParkCopy.hosts_length]
  have nd : ((bank L src).drop 119++ParkCopy.hosts ext).Nodup :=
    List.nodup_append'.mpr ⟨(List.nodup_append'.mp bsplit).2.1,ParkCopy.hosts_nodup ext en he,
      fun {_} hq hq'=>bankExt (List.mem_of_mem_drop hq) (sub _ hq')⟩
  have moved:=ParkCopy.move_correct _ _ lengths nd u n uz
  have bz : regValue (bank L src) w.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    have split : q∈(bank L src).take 119++(bank L src).drop 119 := by simpa only [List.take_append_drop] using hq
    rcases List.mem_append.mp split with hp|hs
    · exact (moved.2.1 q (fun h=>bdj hp h) (fun h=>bankExt hq (sub q h))).trans
        ((regValue_zero _ _).mp pre.2.1 q hp)
    · exact (regValue_zero _ _).mp moved.2.2.2 q hs
  have keepLoan (q : Wire) (qx : q∈ext) (qh : q ∉ ParkCopy.hosts ext) : w.basis q=u.basis q :=
    moved.2.1 q (fun h=>awayE qx (List.mem_of_mem_drop h)) qh
  have sh0 : ext.getD 198 0 ∉ ParkCopy.hosts ext := fun h=> (hosts_away ext en he _ h).1 rfl
  have sh1 : ext.getD 199 0 ∉ ParkCopy.hosts ext := fun h=> (hosts_away ext en he _ h).2.1 rfl
  refine ⟨moved.1.trans pre.1,bz,moved.2.2.1.trans suffixKeep,
    (keepLoan _ x0 sh0).trans pre.2.2.1,(keepLoan _ x1 sh1).trans pre.2.2.2,?_⟩
  intro q qb qh qh0 qh1
  exact (moved.2.1 q (fun h=>qb (List.mem_of_mem_drop h)) qh).trans
    (frame q (fun h=>qb (List.mem_of_mem_take h)) qh0 qh1)

#print axioms pre_move_correct
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic

theorem body_on_shadow (ext dst out : List Wire) (body : Program)
    (hbody : ∀q∈ext,q ∉ ECDSAAdd.wires body)
    (ed : ∀q∈ext,q ∉ dst) (eo : ∀q∈ext,q ∉ out)
    (s u : State) (m : List Bool) (P V : Nat)
    (ud : regValue dst u.basis=P^2)
    (uf : ∀q,q ∉ dst → q ∉ ext → u.basis q=s.basis q)
    (callback : ∀t : State,∀n : List Bool,regValue dst t.basis=P^2 →
      (∀q,q ∉ dst → t.basis q=s.basis q) →
      (run body n t).phase=t.phase ∧ regValue out (run body n t).basis=V ∧
        ∀q,q ∉ out → (run body n t).basis q=t.basis q) :
    (run body m u).phase=u.phase ∧ regValue out (run body m u).basis=V ∧
      ∀q,q ∉ out → (run body m u).basis q=u.basis q := by
  let shadow : State:=⟨u.phase,fun q=>if q∈ext then s.basis q else u.basis q⟩
  have sd : regValue dst shadow.basis=P^2 := by
    rw [←ud]
    apply regValue_congr
    intro q hq
    have qx : q ∉ ext:=fun h=>ed q h hq
    simp [shadow,qx]
  have sf : ∀q,q ∉ dst → shadow.basis q=s.basis q := by
    intro q qd
    by_cases qx : q∈ext
    · simp [shadow,qx]
    · simpa [shadow,qx] using uf q qd qx
  have cb:=callback shadow m sd sf
  have loc:=run_local_increment body u shadow m (by
    intro q hq
    have qx : q ∉ ext:=fun h=>hbody q h hq
    simp [shadow,qx])
  have inside (q : Wire) (qx : q∈ext) : (run body m u).basis q=u.basis q :=
    run_preserves_outside body m u q (hbody q qx)
  have outside (q : Wire) (qx : q ∉ ext) : (run body m u).basis q=(run body m shadow).basis q := by
    by_cases qb : q∈ECDSAAdd.wires body
    · exact loc.2 q qb
    · rw [run_preserves_outside body m u q qb,run_preserves_outside body m shadow q qb]
      simp [shadow,qx]
  have phase : (run body m u).phase=u.phase := by
    have hx : ((run body m u).phase ^^ u.phase)=false := by
      rw [loc.1,cb.1]
      cases u.phase <;> rfl
    clear cb loc
    cases hp : (run body m u).phase <;> cases hu : u.phase <;> simp_all
  refine ⟨phase,?_,?_⟩
  · rw [←cb.2.1]
    apply regValue_congr
    intro q hq
    exact outside q (fun h=>eo q h hq)
  · intro q qo
    by_cases qx : q∈ext
    · exact inside q qx
    · rw [outside q qx,cb.2.2 q qo]
      simp [shadow,qx]

#print axioms body_on_shadow
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic

theorem post_recycle (src bank hs out : List Wire) (c cache h0 h1 t : Wire)
    (hlen : src.length=128) (blen : bank.length=128) (hsl : hs.length=9)
    (nd : (src++bank++hs).Nodup)
    (ln : [bank.getD 64 0,bank.getD 65 0,bank.getD 96 0,bank.getD 97 0,h0,h1,t].Nodup)
    (hcb : c ∉ bank) (h0b : h0 ∉ bank) (h1b : h1 ∉ bank) (tb : t ∉ bank)
    (h0h : h0 ∉ hs) (h1h : h1 ∉ hs) (th : t ∉ hs)
    (outaway : ∀q∈out,q ∉ bank ∧ q ∉ hs ∧ q≠h0 ∧ q≠h1)
    (p v : State) (m n r : List Bool)
    (old : regValue bank p.basis=if p.basis c then regValue src p.basis else 0)
    (vz : regValue bank v.basis=0) (pz : regValue hs p.basis=0)
    (ctl : v.basis c=p.basis c)
    (source : regValue (BankMask2.mask src) v.basis=regValue (BankMask2.mask src) p.basis)
    (cached : v.basis cache=(v.basis c && v.basis (src.headD 0)))
    (saved : regValue hs v.basis=regValue (bank.drop 119) p.basis)
    (saved0 : v.basis h0=p.basis (bank.getD 96 0)) (saved1 : v.basis h1=p.basis (bank.getD 97 0))
    (tval : v.basis t=p.basis t)
    (r0 : p.basis h0=(p.basis (bank.getD 64 0) ^^ p.basis (bank.getD 96 0)))
    (r1 : p.basis h1=((p.basis (bank.getD 65 0) ^^ p.basis (bank.getD 97 0)) ^^ p.basis t))
    (outside : ∀q,q ∉ out → q ∉ bank → q ∉ hs → q≠h0 → q≠h1 → v.basis q=p.basis q) :
    let a:=run (ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) m v
    let b:=run (ParkCopy.move hs (bank.drop 119)) n a
    let w:=run (CombinedBankLoan.restore (bank.getD 64 0) (bank.getD 65 0)
      (bank.getD 96 0) (bank.getD 97 0) h0 h1 t) r b
    w.phase=v.phase ∧ (∀q,q ∉ out → w.basis q=p.basis q) ∧ (∀q∈out,w.basis q=v.basis q) := by
  let a:=run (ParityCachedResearch.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) m v
  let b:=run (ParkCopy.move hs (bank.drop 119)) n a
  have sb:= (List.nodup_append'.mp nd).1
  have hnH:= (List.nodup_append'.mp nd).2.1
  have djH:= (List.nodup_append'.mp nd).2.2
  have bn:= (List.nodup_append'.mp sb).2.1
  have bh {q : Wire} (qb : q∈bank) (qh : q∈hs) : False:=djH (List.mem_append_right src qb) qh
  have maskSub:= (BankMask2.mask_sublist bank).subset
  have fullZero:= (regValue_zero _ _).mp vz
  have maskZero : regValue (BankMask2.mask bank) v.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq=>fullZero q (maskSub hq))
  have cp:=ParityLoan.cached_recopy c cache src bank (by omega) (by omega) sb hcb p v m old maskZero ctl source cached
  have bsplit : (bank.take 119++bank.drop 119).Nodup := by simpa only [List.take_append_drop] using bn
  have djSplit:= (List.nodup_append'.mp bsplit).2.2
  have maskPrefix : ∀q∈BankMask2.mask bank,q∈bank.take 119 := by
    intro q hq
    simp only [BankMask2.mask,List.mem_append] at hq
    exact hq.elim (BankMask2.head_sub_prefix bank q) (BankMask2.middle_sub_prefix bank q)
  have suffixZero : regValue (bank.drop 119) a.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact (cp.2.1 q (fun h=>djSplit (maskPrefix q h) hq)).trans (fullZero q (List.mem_of_mem_drop hq))
  have ndMove : (hs++bank.drop 119).Nodup :=
    List.nodup_append'.mpr ⟨hnH,(List.nodup_append'.mp bsplit).2.1,
      fun {_} hq hq'=>bh (List.mem_of_mem_drop hq') hq⟩
  have mv:=ParkCopy.move_correct hs (bank.drop 119) (by rw [List.length_drop,blen,hsl]) ndMove a n suffixZero
  have bmask : ∀q∈BankMask2.mask bank,b.basis q=p.basis q := by
    intro q hq
    exact (mv.2.1 q (fun h=>bh (maskSub hq) h) (fun h=>djSplit (maskPrefix q hq) h)).trans (cp.2.2 q hq)
  have bsuffix : ∀q∈bank.drop 119,b.basis q=p.basis q := by
    have eqv : regValue (bank.drop 119) b.basis=regValue (bank.drop 119) p.basis := by
      rw [mv.2.2.1,←saved]
      exact regValue_congr hs a.basis v.basis (fun q hq=>cp.2.1 q (fun h=>bh (maskSub h) hq))
    exact (regValue_eq_iff _ _ _).mp eqv
  have keep (q : Wire) (qb : q ∉ bank) (qh : q ∉ hs) : b.basis q=v.basis q :=
    (mv.2.1 q qh (fun h=>qb (List.mem_of_mem_drop h))).trans (cp.2.1 q (fun h=>qb (maskSub h)))
  have exclusions:=BankMask2.excludes bank bn (by omega)
  have bnzero (i : Nat) (hi : i<119) (hnm : bank.getD i 0 ∉ BankMask2.mask bank) : b.basis (bank.getD i 0)=false := by
    have hiB : i<bank.length := by omega
    have inp : bank.getD i 0∈bank.take 119 := by
      simpa only [List.drop_zero] using (BankMask2.getD_mem_slice bank bn i 0 119 hiB).mpr (by omega)
    have inb : bank.getD i 0∈bank := List.mem_of_mem_take inp
    exact (mv.2.1 _ (fun h=>bh inb h) (fun h=>djSplit inp h)).trans ((cp.2.1 _ hnm).trans (fullZero _ inb))
  have bf : ∀q,q ∉ out → q ∉ bank → q≠h0 → q≠h1 → b.basis q=p.basis q := by
    intro q qo qb qh0 qh1
    by_cases qh : q∈hs
    · exact ((regValue_zero _ _).mp mv.2.2.2 q qh).trans ((regValue_zero _ _).mp pz q qh).symm
    · exact (keep q qb qh).trans (outside q qo qb qh qh0 qh1)
  have restore:=ParityLoan.restored_bank_frame bank out h0 h1 t (by omega) bn ln p b r
    (bnzero 96 (by decide) exclusions.1) (bnzero 97 (by decide) exclusions.2)
    ((keep _ h0b h0h).trans saved0) ((keep _ h1b h1h).trans saved1) ((keep _ tb th).trans tval)
    r0 r1 bmask bsuffix bf (fun q hq=>⟨(outaway q hq).1,(outaway q hq).2.2⟩)
  refine ⟨restore.1.trans (mv.1.trans cp.1),restore.2.1,?_⟩
  intro q hq
  have qa:=outaway q hq
  exact (restore.2.2 q hq).trans (keep q qa.1 qa.2.1)

#print axioms post_recycle
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem middle_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (control : Wire) (he : 300≤ext.length) (h128 : src.length=128) (hd : 0<dst.length)
    (hn : (control::(src++bank L src++ext)).Nodup)
    (extDst : ∀q∈ext,q ∉ dst) (extOut : ∀q∈ext,q ∉ L.core.out)
    (bankDst : ∀q∈bank L src,q ∉ dst) (bankOut : ∀q∈bank L src,q ∉ L.core.out)
    (srcOut : ∀q∈src,q ∉ L.core.out) (ctlOut : control ∉ L.core.out)
    (dstOut : ∀q∈dst,q ∉ L.core.out)
    (p s : State) (m0 m1 m2 m3 m4 m5 : List Bool) (v V : Nat)
    (bv : regValue (LowZero18LowK.jregsH L ext src dst).bank p.basis=v)
    (inv : (LowZero18LowK.jregsH L ext src dst).invF v p.basis)
    (masked : regValue (bank L src) p.basis=if p.basis control then regValue src p.basis else 0)
    (prod : regValue dst p.basis=(if p.basis control then regValue src p.basis else 0)^2)
    (hostzero : regValue (ParkCopy.hosts ext) p.basis=0) (bankzero : regValue (bank L src) s.basis=0)
    (pframe : ∀q,q ∉ bank L src → q ∉ dst → q ∉ ext → p.basis q=s.basis q)
    (body : Program) (hbody : ∀q∈ext,q ∉ ECDSAAdd.wires body)
    (callback : ∀t : State,∀n : List Bool,
      regValue dst t.basis=(if p.basis control then regValue src p.basis else 0)^2 →
      (∀q,q ∉ dst → t.basis q=s.basis q) →
      (run body n t).phase=t.phase ∧ regValue L.core.out (run body n t).basis=V ∧
        ∀q,q ∉ L.core.out → (run body n t).basis q=t.basis q) :
    let a:=run (loan L ext src++clearMasked L control src) m0 p
    let b:=run (ParkCopy.move ((bank L src).drop 119) (ParkCopy.hosts ext)) m1 a
    let c:=run body m2 b
    let d:=run (ParityCachedResearch.copy control (dst.headD 0) (BankMask2.mask src) (BankMask2.mask (bank L src))) m3 c
    let e:=run (ParkCopy.move (ParkCopy.hosts ext) ((bank L src).drop 119)) m4 d
    let f:=run (CombinedBankLoan.restore ((bank L src).getD 64 0) ((bank L src).getD 65 0)
      ((bank L src).getD 96 0) ((bank L src).getD 97 0) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)) m5 e
    f.phase=p.phase ∧ regValue L.core.out f.basis=V ∧ ∀q,q ∉ L.core.out → f.basis q=p.basis q := by
  let a:=run (loan L ext src++clearMasked L control src) m0 p
  let b:=run (ParkCopy.move ((bank L src).drop 119) (ParkCopy.hosts ext)) m1 a
  let c:=run body m2 b
  let d:=run (ParityCachedResearch.copy control (dst.headD 0) (BankMask2.mask src) (BankMask2.mask (bank L src))) m3 c
  let e:=run (ParkCopy.move (ParkCopy.hosts ext) ((bank L src).drop 119)) m4 d
  let f:=run (CombinedBankLoan.restore ((bank L src).getD 64 0) ((bank L src).getD 65 0)
      ((bank L src).getD 96 0) ((bank L src).getD 97 0) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)) m5 e
  have pre:=pre_move_correct L hw ext src dst control he h128 p m0 m1 v bv inv masked hn hostzero
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have nc:=(List.nodup_cons.mp hn).1
  have nr:=(List.nodup_cons.mp hn).2
  have nsb:=(List.nodup_append'.mp nr).1
  have nx:=(List.nodup_append'.mp nr).2.1
  have dx:=(List.nodup_append'.mp nr).2.2
  have dsb:=(List.nodup_append'.mp nsb).2.2
  have nb:=(List.nodup_append'.mp nsb).2.1
  have memX (i : Nat) (hi : i<300) : ext.getD i 0∈ext:=ParkCopy.getD_mem _ _ (by omega)
  have bX {q : Wire} (qb : q∈bank L src) (qx : q∈ext) : False:=dx (List.mem_append_right src qb) qx
  have sX {q : Wire} (qs : q∈src) (qx : q∈ext) : False:=dx (List.mem_append_left _ qs) qx
  have hostsX:=ParkCopy.hosts_sub ext he
  have keepB (q : Wire) (qb : q ∉ bank L src) (qx : q ∉ ext) : b.basis q=p.basis q :=
    pre.2.2.2.2.2 q qb (fun h=>qx (hostsX q h)) (fun h=>qx (h.symm ▸ memX 198 (by decide)))
      (fun h=>qx (h.symm ▸ memX 199 (by decide)))
  have bd : regValue dst b.basis=(if p.basis control then regValue src p.basis else 0)^2 := by
    rw [←prod]
    apply regValue_congr
    intro q hq
    exact keepB q (fun h=>bankDst q h hq) (fun h=>extDst q h hq)
  have bf : ∀q,q ∉ dst → q ∉ ext → b.basis q=s.basis q := by
    intro q qd qx
    by_cases qb : q∈bank L src
    · exact ((regValue_zero _ _).mp pre.2.1 q qb).trans ((regValue_zero _ _).mp bankzero q qb).symm
    · exact (keepB q qb qx).trans (pframe q qb qd qx)
  have bodyResult:=body_on_shadow ext dst L.core.out body hbody extDst extOut s b m2
    (if p.basis control then regValue src p.basis else 0) V bd bf callback
  have keep (q : Wire) (qo : q ∉ L.core.out) (qb : q ∉ bank L src)
      (qh : q ∉ ParkCopy.hosts ext) (q0 : q≠ext.getD 198 0) (q1 : q≠ext.getD 199 0) : c.basis q=p.basis q :=
    (bodyResult.2.2 q qo).trans (pre.2.2.2.2.2 q qb qh q0 q1)
  have sourceKeep : ∀q∈src,c.basis q=p.basis q := by
    intro q hq
    exact keep q (srcOut q hq) (fun h=>dsb hq h) (fun h=>sX hq (hostsX q h))
      (fun h=>sX hq (h.symm ▸ memX 198 (by decide))) (fun h=>sX hq (h.symm ▸ memX 199 (by decide)))
  have ctlKeep : c.basis control=p.basis control := by
    have offB : control ∉ bank L src:=fun h=>nc (List.mem_append_left ext (List.mem_append_right src h))
    have offX : control ∉ ext:=fun h=>nc (List.mem_append_right (src++bank L src) h)
    exact keep control ctlOut offB (fun h=>offX (hostsX _ h))
      (fun h=>offX (h.symm ▸ memX 198 (by decide))) (fun h=>offX (h.symm ▸ memX 199 (by decide)))
  have cd : regValue dst c.basis=(if c.basis control then regValue src c.basis else 0)^2 := by
    rw [regValue_congr dst c.basis b.basis (fun q hq=>bodyResult.2.2 q (dstOut q hq)),bd,ctlKeep,
      regValue_congr src c.basis p.basis sourceKeep]
  have cache:=CachedSquareCopy.square_head src dst control c (by omega) hd cd
  have ndPost : (src++bank L src++ParkCopy.hosts ext).Nodup :=
    List.nodup_append'.mpr ⟨nsb,ParkCopy.hosts_nodup ext nx he,fun {_} hq hh=>dx hq (hostsX _ hh)⟩
  have nbe : (bank L src++ext).Nodup :=
    List.nodup_append'.mpr ⟨nb,nx,fun {_} hb hx=>bX hb hx⟩
  have loanNd:=loan_nodup (bank L src) ext bl he nbe
  have xoffB (i : Nat) (hi : i<300) : ext.getD i 0 ∉ bank L src:=fun h=>bX h (memX i hi)
  have xoffH (i : Nat) (hi : i=198 ∨ i=199 ∨ i=233) : ext.getD i 0 ∉ ParkCopy.hosts ext := by
    intro h
    have a:=hosts_away ext nx he _ h
    rcases hi with rfl|rfl|rfl
    · exact a.1 rfl
    · exact a.2.1 rfl
    · exact a.2.2 rfl
  have tkeep : c.basis (ext.getD 233 0)=p.basis (ext.getD 233 0) :=
    keep _ (extOut _ (memX 233 (by decide))) (xoffB 233 (by decide)) (xoffH 233 (Or.inr (Or.inr rfl)))
      (CombinedBankLoan.get_ne ext nx 233 198 (by omega) (by omega) (by decide))
      (CombinedBankLoan.get_ne ext nx 233 199 (by omega) (by omega) (by decide))
  have cvzero : regValue (bank L src) c.basis=0 :=
    (regValue_congr _ _ _ (fun q hq=>bodyResult.2.2 q (bankOut q hq))).trans pre.2.1
  have saved : regValue (ParkCopy.hosts ext) c.basis=regValue ((bank L src).drop 119) p.basis :=
    (regValue_congr _ _ _ (fun q hq=>bodyResult.2.2 q (extOut q (hostsX q hq)))).trans pre.2.2.1
  have bits:=actual_sum_bits L hw ext src dst he h128 p.basis v bv inv
  have post:=post_recycle src (bank L src) (ParkCopy.hosts ext) L.core.out control (dst.headD 0)
    (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) h128 bl (ParkCopy.hosts_length ext) ndPost loanNd
    (fun h=>nc (List.mem_append_left ext (List.mem_append_right src h)))
    (xoffB 198 (by decide)) (xoffB 199 (by decide)) (xoffB 233 (by decide))
    (xoffH 198 (Or.inl rfl)) (xoffH 199 (Or.inr (Or.inl rfl))) (xoffH 233 (Or.inr (Or.inr rfl)))
    (by intro q hq;exact ⟨fun h=>bankOut q h hq,fun h=>extOut q (hostsX q h) hq,
      fun h=>extOut _ (memX 198 (by decide)) (h ▸ hq),fun h=>extOut _ (memX 199 (by decide)) (h ▸ hq)⟩)
    p c m3 m4 m5 masked cvzero hostzero ctlKeep
    (regValue_congr _ _ _ (fun q hq=>sourceKeep q ((BankMask2.mask_sublist src).subset hq))) cache saved
    ((bodyResult.2.2 _ (extOut _ (memX 198 (by decide)))).trans pre.2.2.2.1)
    ((bodyResult.2.2 _ (extOut _ (memX 199 (by decide)))).trans pre.2.2.2.2.1)
    tkeep bits.1 bits.2 keep
  refine ⟨post.1.trans (bodyResult.1.trans pre.1),?_,post.2.1⟩
  exact (regValue_congr _ _ _ post.2.2).trans bodyResult.2.1

#print axioms middle_correct
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def pre (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src : List Wire) : Program :=
  loan L ext src++clearMasked L control src

def post (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire) : Program :=
  recopy L control src dst++ParkCopy.pMO L ext src++restore L ext src

theorem program_shape (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire) (body : Program) :
    program L ext control src dst body=
      ParkCopy.pA L control src++ParkCopy.pM L ext src dst++pre L ext control src++ParkCopy.pD ext++
      ParkCopy.pMI L ext src++ParkCopy.pB L ext body++post L ext control src dst++
      ParkCopy.pCL L ext src dst++ParkCopy.pE L control src := by
  simp only [program,pre,post,List.append_assoc]

theorem post_run (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (control : Wire) (h128 : src.length=128) (s : State) (r : List Bool) :
    run (post L ext control src dst) r s=
      run (restore L ext src) r (run (ParkCopy.pMO L ext src) [] (run (recopy L control src dst) [] s)) := by
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have sl:=BankMask2.mask_length src (by omega)
  have ml:=BankMask2.mask_length (bank L src) (by omega)
  have cp:=copyRegister_counts (some control) (BankMask2.mask src) (BankMask2.mask (bank L src)) (by rw [sl,ml])
  have cm : measurementCount (recopy L control src dst)=0 := by
    rw [recopy,CachedSquareCopy.measurements]
    exact cp.2
  have len : (ParkCopy.hosts ext).length=((bank L src).drop 119).length := by rw [ParkCopy.hosts_length,List.length_drop,bl]
  have c1:=copyRegister_counts none (ParkCopy.hosts ext) ((bank L src).drop 119) len
  have c2:=copyRegister_counts none ((bank L src).drop 119) (ParkCopy.hosts ext) len.symm
  have mm : measurementCount (ParkCopy.pMO L ext src)=0 := by
    change measurementCount (ParkCopy.move (ParkCopy.hosts ext) ((bank L src).drop 119))=0
    rw [ParkCopy.move,measurementCount_append,c1.2,c2.2]
  simp only [post,run_append,measurementCount_append,cm,mm,Nat.zero_add,List.take_zero,List.drop_zero]

#print axioms post_run
end ECDSAAdd.Entrant.ParityParkCopy

namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout ParkCopy
attribute [local irreducible] run wires
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
open LowZero18Square in
theorem correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (h128' : src.length=128)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (program L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (program L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (program L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have cacheFix : earlyPerm L (dst.headD 0)=dst.headD 0 := by
    have mem : dst.headD 0∈dst := by
      rcases dst with _|⟨d,ds⟩
      · have hz : src.length=0 := by simpa using hlen.symm
        omega
      · exact List.mem_cons_self
    have targetM : target L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (fun e => tmpD _ targetM (by simpa only [e] using mem))
      (fun e => tmpD _ hostM (by simpa only [e] using mem))
  let P := if s.basis control then regValue src s.basis else 0
  -- parking data
  have Blen : (L.inputBank.take src.length).length=128 := by rw [inputLen,h128']
  have hHx : ∀h∈hosts ext,h∈ext := hosts_sub ext he
  have hHnd : (hosts ext).Nodup := hosts_nodup ext hx he
  have hHT : ∀h∈freeHosts ext,h∉(LowZero18LowK.oregs L ext src dst).T := fun h hh => host_not_oT L ext src dst hx he h128' h hh
  have hHX : ∀h∈freeHosts ext,h∉(LowZero18LowK.kg L ext src dst).X := fun h hh => host_not_X L ext src dst hx he h128' tmpE h hh
  have hH0 : ∀h∈hosts ext,h≠ext.getD 0 0 := host_ne_zero ext hx he
  have hHB : ∀h∈hosts ext,h∉(L.inputBank.take src.length) := fun h hh => extB h (hHx h hh)
  have hHD : ∀h∈hosts ext,h∉dst := fun h hh => extD h (hHx h hh)
  have hHo : ∀h∈hosts ext,h∉L.core.out := fun h hh => extOut h (hHx h hh)
  have hHs : ∀q∈src,q∉hosts ext := fun q hq hh => extSrc q (hHx q hh) hq
  have ctlH : control∉hosts ext := fun h => ctlE (hHx _ h)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have b15 : ∀q∈(L.inputBank.take src.length).take 119,q∉(L.inputBank.take src.length).drop 119 := by
    intro q h1 h5
    have nd : ((L.inputBank.take src.length).take 119++(L.inputBank.take src.length).drop 119).Nodup := by
      rw [List.take_append_drop]; exact bNd
    exact (List.nodup_append.mp nd).2.2 q h1 q h5 rfl
  have b51 : ∀q∈(L.inputBank.take src.length).drop 119,q∉(L.inputBank.take src.length).take 119 :=
    fun q h5 h1 => b15 q h1 h5
  have ndMI : ((L.inputBank.take src.length).drop 119++hosts ext).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => hHB b hb (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (hosts ext++(L.inputBank.take src.length).drop 119).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  have lenMI : ((L.inputBank.take src.length).drop 119).length=(hosts ext).length := by
    rw [List.length_drop,Blen,hosts_length]
  obtain ⟨a8,r9,e9⟩ := kseq (pA L control src++pM L ext src dst++pre L ext control src++pD ext++pMI L ext src++pB L ext body++post L ext control src dst++pCL L ext src dst) (pE L control src) records s
  obtain ⟨a7,r8,e8⟩ := kseq (pA L control src++pM L ext src dst++pre L ext control src++pD ext++pMI L ext src++pB L ext body++post L ext control src dst) (pCL L ext src dst) a8 s
  obtain ⟨a6,r7,e7⟩ := kseq (pA L control src++pM L ext src dst++pre L ext control src++pD ext++pMI L ext src++pB L ext body) (post L ext control src dst) a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (pA L control src++pM L ext src dst++pre L ext control src++pD ext++pMI L ext src) (pB L ext body) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (pA L control src++pM L ext src dst++pre L ext control src++pD ext) (pMI L ext src) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (pA L control src++pM L ext src dst++pre L ext control src) (pD ext) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (pA L control src++pM L ext src dst) (pre L ext control src) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (pA L control src) (pM L ext src dst) a2 s
  rw [program_shape,e9,e8,e7,e6,e5,e4,e3,e2]
  simp only [pA,pM,pD,pMI,pB,pCL,pE]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- hosts stay zero through the copy and the producer
  have loLen : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).1]
    rfl
  have hiLen : (LowZero18LowK.oregs L ext src dst).hi.length=64 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).2.1]
    change (L.inputBank.take src.length).length-64=64
    rw [Blen]
  have loBound : regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis<2^64 := by
    simpa only [loLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
  have hiBound : regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^64 := by
    simpa only [hiLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
  have inv1:=mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at inv1
  have inv2:=mk.2.2.2.2.2.1
  simp only [LowZero18LowK.kg,if_pos h128',LowZero18LowK.kgH] at inv2
  have itLen : (LowZero18LowK.iregs L ext src dst).T.length=66 := by
    simp only [LowZero18LowK.iregs,List.length_take,List.length_drop]
    omega
  have jtLen : (LowZero18LowK.jregsH L ext src dst).T.length=66 := by
    simp only [LowZero18LowK.jregsH,List.length_take,List.length_drop]
    omega
  have iz:=CrossBits.top_zero (LowZero18LowK.iregs L ext src dst).T itLen
    (regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis) loBound u1.basis inv1.2
  have jz:=CrossBits.top_zero (LowZero18LowK.jregsH L ext src dst).T jtLen
    (regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis) hiBound u1.basis inv2.2
  have slice_get (a n i:Nat) (hi:i<n) (ha:a+i<ext.length) :
      ((ext.drop a).take n).getD i 0=ext.getD (a+i) 0 := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take,List.length_drop];omega),
      List.getD_eq_getElem _ _ ha]
    simp only [List.getElem_take,List.getElem_drop]
  simp only [LowZero18LowK.iregs] at iz
  simp only [LowZero18LowK.jregsH] at jz
  rw [slice_get 132 66 65 (by omega) (by omega)] at iz
  rw [slice_get 232 66 65 (by omega) (by omega)] at jz
  have otLen : (LowZero18LowK.oregs L ext src dst).T.length=130 := by
    simp only [LowZero18LowK.oregs,h128',List.length_take]
    omega
  have oz:=CrossBits.outer_zero (LowZero18LowK.oregs L ext src dst).T otLen
    (regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)
    (regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis) loBound hiBound u1.basis mk.2.2.2.1
  have otget : (LowZero18LowK.oregs L ext src dst).T.getD 129 0=ext.getD 129 0 := by
    simp only [LowZero18LowK.oregs,h128']
    rw [List.take_take]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take];omega),
      List.getD_eq_getElem _ _ (by omega)]
    simp only [List.getElem_take]
  rw [otget] at oz
  have iz0:=CrossBits.low_zero (LowZero18LowK.iregs L ext src dst).T (by rw [itLen];decide)
    ((regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)%2^32)
    ((regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)/2^32) u1.basis inv1.2
  have jz0:=CrossBits.low_zero (LowZero18LowK.jregsH L ext src dst).T (by rw [jtLen];decide)
    ((regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis)%2^32)
    ((regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis)/2^32) u1.basis inv2.2
  simp only [LowZero18LowK.iregs] at iz0
  simp only [LowZero18LowK.jregsH] at jz0
  rw [slice_get 132 66 0 (by omega) (by omega)] at iz0
  rw [slice_get 232 66 0 (by omega) (by omega)] at jz0
  have hU1 : ∀h∈hosts ext,u1.basis h=false := by
    intro h hh
    rcases hosts_split ext h hh with hf|rfl|rfl|rfl|rfl|rfl
    · exact (u1s h (hHD h hh) (hHT h hf) (hHX h hf)).trans
        ((u0s h (hHB h hh)).trans (ext0 h (hHx h hh)))
    · exact iz
    · exact jz
    · exact oz
    · exact iz0
    · exact jz0
  have srcw1 : ∀q∈src,u1.basis q=s.basis q := fun q hq =>
    (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq))
  have npre : (control::(src++bank L src++ext)).Nodup := by
    change ((control::(src++bank L src))++ext).Nodup
    apply List.nodup_append'.mpr
    refine ⟨ndMask,hx,?_⟩
    intro q hq hqx
    simp only [List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hqs|hqb
    · exact ctlE hqx
    · exact extSrc q hqx hqs
    · exact extB q hqx hqb
  have jBank : regValue (LowZero18LowK.jregsH L ext src dst).bank u1.basis=
      regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    apply regValue_congr
    intro q hq
    change q∈(L.inputBank.take src.length).drop 64 at hq
    have qb:=List.mem_of_mem_drop hq
    exact u1z q (bD q qb) (fun h=>extB q h qb)
  have oldMask : regValue (bank L src) u1.basis=
      if u1.basis control then regValue src u1.basis else 0 := by
    rw [show regValue (bank L src) u1.basis=P from bank1,ctl1,src1]
  have pc:=pre_correct L hw ext src dst control he h128' u1 r3 _ jBank inv2 oldMask npre
  have pf:=pre_frame L hw ext src dst control he h128' u1 r3 _ jBank inv2 oldMask npre
  have pm:=pre_move_correct L hw ext src dst control he h128' u1 r3 r5 _ jBank inv2 oldMask npre
    ((regValue_zero _ _).mpr hU1)
  simp only [pre]
  generalize hpre : run (loan L ext src++clearMasked L control src) r3 u1=u2a at pc pf pm ⊢
  have hU2a : ∀q∈hosts ext,u2a.basis q=false := by
    intro q hq
    have neq:=hosts_away ext hx he q hq
    exact (pf q (fun h=>hHB q hq (List.mem_of_mem_take h)) neq.1 neq.2.1).trans (hU1 q hq)
  rw [dummies_run (hosts ext) u2a r4 hU2a]
  simp only [bank] at pm
  generalize hmove : run (move ((L.inputBank.take src.length).drop 119) (hosts ext)) r5 u2a=u2 at pm ⊢
  have offLoan0 : ∀q,q ∉ ext → q≠ext.getD 198 0 ∧ q≠ext.getD 199 0 := by
    intro q hq
    exact ⟨fun e=>hq (e.symm ▸ getD_mem ext 198 (by omega)),fun e=>hq (e.symm ▸ getD_mem ext 199 (by omega))⟩
  have u2s : ∀q,q ∉ dst → q ∉ ext → u2.basis q=s.basis q := by
    intro q qd qx
    by_cases qb : q∈L.inputBank.take src.length
    · exact ((regValue_zero _ _).mp pm.2.1 q qb).trans ((regValue_zero _ _).mp banks.1 q qb).symm
    · have a:=offLoan0 q qx
      exact (pm.2.2.2.2.2 q qb (fun h=>qx (hHx q h)) a.1 a.2).trans ((u1z q qd qx).trans (u0s q qb))
  have dst2 : regValue dst u2.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have qx : q ∉ ext:=fun h=>extD q h hq
    have a:=offLoan0 q qx
    exact pm.2.2.2.2.2 q (fun h=>bD q h hq) (fun h=>qx (hHx q h)) a.1 a.2
  have cb:=body_on_shadow ext dst L.core.out body hbody extD extOut s u2 r6 P V dst2 u2s callback
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r6 u2).basis (target L)=false :=
    (cb.2.2 _ (tmpOut _ targetTmp)).trans targetIn
  have e0mem : ext.getD 0 0∈ext:=getD_mem ext 0 (by omega)
  have keep0 : u2.basis (ext.getD 0 0)=u1.basis (ext.getD 0 0) :=
    pm.2.2.2.2.2 _ (extB _ e0mem) (fun h=>hH0 _ h rfl)
      (CombinedBankLoan.get_ne ext hx 0 198 (by omega) (by omega) (by decide))
      (CombinedBankLoan.get_ne ext hx 0 199 (by omega) (by omega) (by decide))
  have hostIn : u2.basis (ext.getD 0 0)=false := keep0.trans
    (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq:=fold_run_eq L hw ext body u2 r6 targetIn targetOut hostIn (hbody _ e0mem)
  rw [foldEq]
  generalize hv : run body r6 u2=v at cb ⊢
  have mid:=middle_correct L hw ext src dst control he h128' (by omega) npre extD extOut bD bOut srcOut ctlO dOut
    u1 s r3 r5 r6 [] [] r7 _ V jBank inv2 oldMask
    (by simpa only [ctl1,src1] using dst1) ((regValue_zero _ _).mpr hU1) banks.1
    (fun q qb qd qx=>(u1z q qd qx).trans (u0s q qb)) body hbody
    (by intro t m ht hf;apply callback t m;simpa only [ctl1,src1] using ht;exact hf)
  dsimp only at mid
  simp only [bank] at mid
  have researchCopy (a b : List Wire) : ParityCachedResearch.copy control (dst.headD 0) a b=
      CachedSquareCopy.copy control (dst.headD 0) a b := by cases a <;> cases b <;> rfl
  rw [show run (loan L ext src++clearMasked L control src) r3 u1=u2a from hpre,hmove,hv,researchCopy] at mid
  rw [show CachedSquareCopy.copy control (dst.headD 0) (BankMask2.mask src) (BankMask2.mask (L.inputBank.take src.length))=
      recopy L control src dst from by simp only [recopy,LowZero18Square.cacheWire,cacheFix,bank]] at mid
  have postEq:=post_run L hw ext src dst control h128' v r7
  simp only [restore,ParkCopy.pMO,bank] at postEq
  rw [←postEq] at mid
  generalize hw0 : run (post L ext control src dst) r7 v=w0 at mid ⊢
  have w0frame : ∀q,q ∉ L.core.out → w0.basis q=u1.basis q := mid.2.2
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P :=
    (regValue_congr _ _ _ (fun q hq=>w0frame q (bOut q hq))).trans bank1
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := fun q _ hq=>w0frame q hq
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q qb qo qd qx=>(w0frame q qo).trans ((u1z q qd qx).trans (u0s q qb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r8
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r8
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r8 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq=>(w1s q (srcD q hq) (fun h=>extSrc q h hq) (fun h=>tmpSrc q h hq)).trans
      ((w0frame q (srcOut q hq)).trans (srcw1 q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((w0frame _ ctlO).trans ctl1)
  obtain ⟨ep2,ef2,ev2⟩:=eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r9
    (by rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r9 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (mid.1.trans (mk.1.trans cp1))),?_,?_⟩
  · rw [←mid.2.1]
    apply regValue_congr
    intro q hq
    have o:=nK q (fun h=>dOut q h hq) (fun h=>extOut q h hq) (fun h=>tmpOut q h hq)
    rw [ef2 q (fun h=>bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2]
  · intro q hq
    by_cases qb : q∈L.inputBank.take src.length
    · exact ((regValue_zero _ _).mp ev2 q qb).trans ((regValue_zero _ _).mp banks.1 q qb).symm
    · rw [ef2 q qb]
      by_cases qd : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q qd).trans ((regValue_zero _ _).mp hzero q qd).symm
      by_cases qt : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q qt).trans (ext0 q (xT q qt)).symm
      by_cases qx : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q qx]
        rcases xX q qx with h|h
        · exact (ext0 q h).symm
        · exact (tmp0 q h).symm
      rw [cl.2.2.2.2.2 q qd qt qx,w0frame q hq,u1s q qd qt qx,u0s q qb]

#print axioms correct
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout LowZero18Square
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem cached_ne_head (control cache : Wire) (src dst : List Wire)
    (hs : 0<src.length) (hd : 0<dst.length) (hp : GatePhysical (CachedSquareCopy.copy control cache src dst)) :
    cache≠dst.headD 0 := by
  cases src with
  | nil=>simp at hs
  | cons a src=>
    cases dst with
    | nil=>simp at hd
    | cons b dst=>
      have h:=hp (.CX cache b) (by simp [CachedSquareCopy.copy])
      simpa only [List.headD_cons,RecordedQuantum.PhysicalInstr,ProperGate] using h

theorem physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (h128 : src.length=128)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q ∉ control::L.wires) (he : 300≤ext.length)
    (body : Program) (hold : GatePhysical (ParkCopy.withLowK2P L ext control src dst body)) :
    GatePhysical (program L ext control src dst body) := by
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have big:=kbig_nodup L control hn src dst hs hd ext hx hdx
  have ndCopy : (src++bank L src).Nodup := knd big (fun q=>by
    simp only [kbig,bank,List.count_cons,List.count_append];omega)
  have ndBE : (bank L src++ext).Nodup := knd big (fun q=>by
    simp only [kbig,bank,List.count_cons,List.count_append];omega)
  have ctlB : control ∉ bank L src :=
    kdis big (r:=[control]) (t:=bank L src) (fun q=>by
      simp only [kbig,bank,List.count_cons,List.count_append,List.count_nil];omega) control (by simp)
  have ln:=loan_nodup (bank L src) ext bl he ndBE
  have lp:=ParityProtocolResources.loans_physical ((bank L src).getD 64 0) ((bank L src).getD 65 0)
    ((bank L src).getD 96 0) ((bank L src).getD 97 0) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) ln
  simp only [ParkCopy.withLowK2P,gatePhysical_append] at hold
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨pa,pm⟩,pe1⟩,pd⟩,pmi⟩,pb⟩,pc⟩,pmo⟩,pcl⟩,pe⟩:=hold
  change GatePhysical (CachedSquareCopy.copy control (cacheWire L dst) (src.take 119) ((bank L src).take 119)) at pc
  have off:=cached_ne_head control (cacheWire L dst) (src.take 119) ((bank L src).take 119)
    (by simp only [List.length_take];omega) (by simp only [List.length_take];omega) pc
  rw [ParkCopy.headD_take _ 119 (by decide)] at off
  have pr:=ParityProtocolResources.cached_physical control (cacheWire L dst) (BankMask2.mask src) (BankMask2.mask (bank L src))
    (BankMask2.pair_nodup src (bank L src) ndCopy)
    (fun h=>ctlB ((BankMask2.mask_sublist (bank L src)).subset h))
    (by rw [BankMask2.mask_head];exact off)
  have copyEq (a b : List Wire) : ParityCachedResearch.copy control (cacheWire L dst) a b=CachedSquareCopy.copy control (cacheWire L dst) a b := by
    cases a <;> cases b <;> rfl
  rw [copyEq] at pr
  change GatePhysical (recopy L control src dst) at pr
  have ce:=ParityProtocolResources.clear_physical control src (bank L src)
  simp only [program,loan,restore,clearMasked,gatePhysical_append]
  tauto

#print axioms physical
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem copy_exact (c : Wire) (src dst : List Wire) (hlen : src.length=dst.length) (hs : 0<src.length) :
    wires (copyRegister (some c) src dst)=(c::(src++dst)).toFinset := by
  have h:=copyRegister_wires (some c) src dst hlen
  have ne : src.isEmpty=false := by cases src with | nil=>simp at hs | cons _ _=>rfl
  simpa [ne] using h

theorem cached_support (c cache : Wire) (src dst : List Wire) :
    wires (CachedSquareCopy.copy c cache src dst)⊆(c::cache::(src++dst)).toFinset := by
  cases src with
  | nil=>simp [CachedSquareCopy.copy,copyRegister,wires]
  | cons a src=>
    cases dst with
    | nil=>simp [CachedSquareCopy.copy,copyRegister,wires]
    | cons b dst=>
      intro q hq
      simp only [CachedSquareCopy.copy,wires_append,Finset.mem_union] at hq
      rcases hq with h|h
      · simp [wires,Instr.wires] at h
        rcases h with rfl|rfl <;> simp
      · have h:=copyRegister_wires_subset (some c) src dst h
        simp at h ⊢
        tauto

theorem cached_mem_cache (c cache : Wire) (src dst : List Wire) (hs : 0<src.length) (hd : 0<dst.length) :
    cache∈wires (CachedSquareCopy.copy c cache src dst) := by
  cases src with
  | nil=>simp at hs
  | cons a src=>
    cases dst with
    | nil=>simp at hd
    | cons b dst=>simp [CachedSquareCopy.copy,wires_append,wires,Instr.wires]

theorem loan_support (a0 a1 b0 b1 h0 h1 t : Wire) :
    wires (CombinedBankLoan.loan a0 a1 b0 b1 h0 h1 t)⊆{a0,a1,b0,b1,h0,h1,t} ∧
    wires (CombinedBankLoan.restore a0 a1 b0 b1 h0 h1 t)⊆{a0,a1,b0,b1,h0,h1,t} := by
  constructor <;> intro q hq
  all_goals
    simp [CombinedBankLoan.loan,CombinedBankLoan.restore,LinearBankLoan.loan0,LinearBankLoan.loan1,
      LinearBankLoan.restore0,LinearBankLoan.restore1,wires_append,wires,Instr.wires] at hq ⊢
    tauto

#print axioms copy_exact
#print axioms cached_support
#print axioms loan_support
end ECDSAAdd.Entrant.ParityParkCopy
namespace ECDSAAdd.Entrant.ParityParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def loanSites (ext : List Wire) : Finset Wire := {ext.getD 198 0,ext.getD 199 0,ext.getD 233 0}

theorem support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program) (h128 : src.length=128) :
    wires (program L ext control src dst body)⊆
      wires (ParkCopy.withLowK2P L ext control src dst body) ∪ loanSites ext := by
  let old:=ParkCopy.withLowK2P L ext control src dst body
  let cap:=wires old ∪ loanSites ext
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have ae : wires (ParkCopy.pA L control src)=(control::(src++bank L src)).toFinset :=
    copy_exact control src (bank L src) (by omega) (by omega)
  have inA (q : Wire) (hq : q∈(control::(src++bank L src)).toFinset) : q∈wires old := by
    have ha : q∈wires (ParkCopy.pA L control src) := by rw [ae];exact hq
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,ha,true_or,or_true]
  have cacheIn : LowZero18Square.cacheWire L dst∈wires old := by
    have hc:=cached_mem_cache control (LowZero18Square.cacheWire L dst) (src.take 119) ((bank L src).take 119)
      (by simp only [List.length_take];omega) (by simp only [List.length_take];omega)
    change LowZero18Square.cacheWire L dst∈wires (ParkCopy.pC1 L control src dst) at hc
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,hc,true_or,or_true]
  have siteIn (i : Nat) (hi : i<128) : (bank L src).getD i 0∈wires old := by
    apply inA
    have h:=ParkCopy.getD_mem (bank L src) i (by omega)
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr h)
  have loanCap (q : Wire)
      (hq : q∈({(bank L src).getD 64 0,(bank L src).getD 65 0,(bank L src).getD 96 0,(bank L src).getD 97 0,
        ext.getD 198 0,ext.getD 199 0,ext.getD 233 0}:Finset Wire)) : q∈cap := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Finset.mem_union_left _ (siteIn 64 (by decide))
    · exact Finset.mem_union_left _ (siteIn 65 (by decide))
    · exact Finset.mem_union_left _ (siteIn 96 (by decide))
    · exact Finset.mem_union_left _ (siteIn 97 (by decide))
    · exact Finset.mem_union_right _ (by simp [loanSites])
    · exact Finset.mem_union_right _ (by simp [loanSites])
    · exact Finset.mem_union_right _ (by simp [loanSites])
  have lp:=loan_support ((bank L src).getD 64 0) ((bank L src).getD 65 0)
    ((bank L src).getD 96 0) ((bank L src).getD 97 0) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)
  have ls : wires (loan L ext src)⊆cap:=fun q hq=>loanCap q (lp.1 hq)
  have rs : wires (restore L ext src)⊆cap:=fun q hq=>loanCap q (lp.2 hq)
  have es : wires (clearMasked L control src)⊆cap := by
    intro q hq
    exact Finset.mem_union_left _ (inA q (ParityProtocolResources.clear_support control src (bank L src) (by omega) hq))
  have cs : wires (recopy L control src dst)⊆cap := by
    intro q hq
    have h:=cached_support control (LowZero18Square.cacheWire L dst) (BankMask2.mask src) (BankMask2.mask (bank L src)) hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    rcases h with rfl|rfl|h|h
    · exact Finset.mem_union_left _ (inA _ (by simp))
    · exact Finset.mem_union_left _ cacheIn
    · exact Finset.mem_union_left _ (inA q (by simp [(BankMask2.mask_sublist src).subset h]))
    · exact Finset.mem_union_left _ (inA q (by simp [(BankMask2.mask_sublist (bank L src)).subset h]))
  change wires (program L ext control src dst body)⊆cap
  intro q hq
  simp only [program,wires_append,Finset.mem_union] at hq
  rcases hq with (((((((((((h|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)|h)
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]
  · exact ls h
  · exact es h
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]
  · exact cs h
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]
  · exact rs h
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]
  · apply Finset.mem_union_left
    simp only [old,ParkCopy.withLowK2P,wires_append,Finset.mem_union,h,true_or,or_true]

#print axioms support
end ECDSAAdd.Entrant.ParityParkCopy

section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
namespace ECDSAAdd.Entrant.SingleSpare
open Arithmetic

def save (bank spare : Wire) : Program := [.CX bank spare]
def restore (bank spare : Wire) : Program := [.CX spare bank,.CX bank spare]

theorem save_correct (bank spare : Wire) (h : bank≠spare) (s : State) (m : List Bool)
    (hz : s.basis spare=false) :
    (run (save bank spare) m s).phase=s.phase ∧
    (run (save bank spare) m s).basis spare=s.basis bank ∧
    ∀q,q≠spare → (run (save bank spare) m s).basis q=s.basis q := by
  obtain ⟨hp,hf,hv⟩:=copyRegister_correct none [bank] [spare] rfl (by simp [h]) (by simp) s m
  change _ at hp hf hv
  refine ⟨hp,?_,fun q hq=>hf q (by simpa using hq)⟩
  cases h1 : (run (save bank spare) m s).basis spare <;>
    cases h2 : s.basis bank <;> simp_all [regValue,copyValue,save,copyRegister,copyGate]

theorem restore_correct (bank spare : Wire) (h : bank≠spare) (s : State) (m : List Bool)
    (hz : s.basis bank=false) :
    (run (restore bank spare) m s).phase=s.phase ∧
    (run (restore bank spare) m s).basis bank=s.basis spare ∧
    (run (restore bank spare) m s).basis spare=false ∧
    ∀q,q≠bank → q≠spare → (run (restore bank spare) m s).basis q=s.basis q := by
  have r:=ParkCopy.move_correct [spare] [bank] rfl (by simp [Ne.symm h]) s m
    (by simpa [regValue] using hz)
  change _ at r
  refine ⟨r.1,?_,?_,fun q hb hs=>r.2.1 q (by simpa using hs) (by simpa using hb)⟩
  · have hv:=r.2.2.1
    cases h1 : (run (restore bank spare) m s).basis bank <;>
      cases h2 : s.basis spare <;> simp_all [regValue,restore,ParkCopy.move,copyRegister,copyGate]
  · have hv:=r.2.2.2
    cases h1 : (run (restore bank spare) m s).basis spare <;>
      simp_all [regValue,restore,ParkCopy.move,copyRegister,copyGate]

theorem restore_eq_controlled (control source bank spare : Wire)
    (bg : bank≠spare) (cg : control≠spare) (sg : source≠spare)
    (s : State) (m : List Bool) (hz : s.basis bank=false)
    (rel : s.basis spare=(s.basis control && s.basis source)) :
    run (restore bank spare) m s=
      run [.CCX control source bank] m ⟨s.phase,writeBit s.basis spare false⟩ := by
  simp only [restore,run]
  congr 1
  funext q
  by_cases qb : q=bank
  · subst q
    simp [writeBit,bg,Ne.symm bg,cg,sg,hz,rel]
  · by_cases qg : q=spare
    · subst q
      simp [writeBit,bg,Ne.symm bg,cg,sg,hz]
    · simp [writeBit,qb,qg,bg,Ne.symm bg,hz]

theorem run_clear_commute (p : Program) (g : Wire) (hg : g∉wires p)
    (s : State) (m : List Bool) :
    run p m ⟨s.phase,writeBit s.basis g false⟩=
      ⟨(run p m s).phase,writeBit (run p m s).basis g false⟩ := by
  let shadow : State:=⟨s.phase,writeBit s.basis g false⟩
  have loc:=run_local_increment p s shadow m (by
    intro q hq
    have qg : q≠g:=fun e=>hg (e ▸ hq)
    simp [shadow,writeBit,qg])
  have phase : (run p m shadow).phase=(run p m s).phase := by
    have h:=loc.1
    change ((run p m s).phase ^^ s.phase)=((run p m shadow).phase ^^ s.phase) at h
    exact (Bool.xor_left_inj.mp h).symm
  change State.mk (run p m shadow).phase (run p m shadow).basis=_
  apply congrArg₂ State.mk phase
  funext q
  by_cases qg : q=g
  · subst q
    rw [run_preserves_outside p m shadow g hg]
    simp [shadow,writeBit]
  · have eq : (run p m shadow).basis q=(run p m s).basis q := by
      by_cases used : q∈wires p
      · exact (loc.2 q used).symm
      · rw [run_preserves_outside p m shadow q used,run_preserves_outside p m s q used]
        simp [shadow,writeBit,qg]
    simpa [writeBit,qg] using eq

theorem copy_append (c : Option Wire) (a b x y : List Wire) (hlen : a.length=b.length) :
    copyRegister c (a++x) (b++y)=copyRegister c a b++copyRegister c x y := by
  induction a generalizing b with
  | nil=>cases b with
    | nil=>rfl
    | cons r b=>simp at hlen
  | cons q a ih=>
    cases b with
    | nil=>simp at hlen
    | cons r b=>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      simp only [List.cons_append,copyRegister]
      rw [ih b hlen]
      rfl

theorem cached_append (c cache : Wire) (a b : List Wire) (x y : Wire)
    (hlen : a.length=b.length) (ha : 0<a.length) :
    CachedSquareCopy.copy c cache (a++[x]) (b++[y])=
      CachedSquareCopy.copy c cache a b++[.CCX c x y] := by
  cases a with
  | nil=>simp at ha
  | cons q a=>
    cases b with
    | nil=>simp at hlen
    | cons r b=>
      have h : a.length=b.length:=by simpa using hlen
      simp only [List.cons_append,CachedSquareCopy.copy]
      rw [copy_append (some c) a b [x] [y] h]
      rfl

theorem prefix_restore_eq (p : Program) (control source bank spare : Wire)
    (bg : bank≠spare) (cg : control≠spare) (sg : source≠spare)
    (hg : spare∉wires p) (s : State) (m : List Bool)
    (hz : (run p m s).basis bank=false)
    (rel : (run p m s).basis spare=((run p m s).basis control && (run p m s).basis source)) :
    run (p++restore bank spare) m s=
      run (p++[.CCX control source bank]) m ⟨s.phase,writeBit s.basis spare false⟩ := by
  simp only [run_append,run_take]
  rw [run_clear_commute p spare hg s m]
  exact restore_eq_controlled control source bank spare bg cg sg (run p m s) _ hz rel

theorem copy_frame (c : Option Wire) (a b : List Wire) (s : State) (m : List Bool)
    (q : Wire) (hq : q∉b) : (run (copyRegister c a b) m s).basis q=s.basis q := by
  induction a generalizing b s with
  | nil=>rfl
  | cons x a ih=>
    cases b with
    | nil=>rfl
    | cons y b=>
      have qy : q≠y:=fun e=>hq (by simp [e])
      have qb : q∉b:=fun h=>hq (by simp [h])
      cases c <;> simp only [copyRegister,copyGate,List.cons_append,List.nil_append,run] <;>
        rw [ih b _ qb] <;> simp [writeBit,qy]

theorem cached_frame (c cache : Wire) (a b : List Wire) (s : State) (m : List Bool)
    (q : Wire) (hq : q∉b) : (run (CachedSquareCopy.copy c cache a b) m s).basis q=s.basis q := by
  cases a with
  | nil=>rfl
  | cons x a=>
    cases b with
    | nil=>rfl
    | cons y b=>
      have qy : q≠y:=fun e=>hq (by simp [e])
      have qb : q∉b:=fun h=>hq (by simp [h])
      simp only [CachedSquareCopy.copy,List.cons_append,List.nil_append,run]
      rw [copy_frame (some c) a b _ m q qb]
      simp [writeBit,qy]

theorem copy_mc (c : Option Wire) (a b : List Wire) : measurementCount (copyRegister c a b)=0 := by
  induction a generalizing b with
  | nil=>rfl
  | cons x a ih=>cases b with
    | nil=>rfl
    | cons y b=>cases c <;> simp [copyRegister,copyGate,measurementCount_append,measurementCount,ih]

theorem cached_mc (c cache : Wire) (a b : List Wire) :
    measurementCount (CachedSquareCopy.copy c cache a b)=0 := by
  cases a <;> cases b <;> simp [CachedSquareCopy.copy,measurementCount_append,measurementCount,copy_mc]

#print axioms copy_mc
#print axioms cached_mc
#print axioms copy_frame
#print axioms cached_frame
#print axioms prefix_restore_eq
#print axioms run_clear_commute
#print axioms copy_append
#print axioms cached_append
#print axioms restore_eq_controlled
#print axioms save_correct
#print axioms restore_correct
end ECDSAAdd.Entrant.SingleSpare

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic

def shortMask (r : List Wire) := (BankMask2.mask r).take 116

theorem shortMask_length (r : List Wire) (hr : r.length=128) : (shortMask r).length=116 := by
  simp only [shortMask,List.length_take,BankMask2.mask_length r (by omega)]
  rfl

theorem mask_last (r : List Wire) (hr : r.length=128) :
    (BankMask2.mask r).getD 116 0=r.getD 118 0 := by
  have len : (r.take 96).length=96 := by simp [hr]
  rw [List.getD_eq_getElem _ _ (by rw [BankMask2.mask_length r (by omega)];decide),
    List.getD_eq_getElem _ _ (by omega)]
  simp only [BankMask2.mask,List.getElem_append,len]
  simp only [show ¬(116<96) from by decide,if_false]
  simp only [List.getElem_take,List.getElem_drop]
  rfl

theorem mask_split (r : List Wire) (hr : r.length=128) :
    BankMask2.mask r=shortMask r++[r.getD 118 0] := by
  have len:=BankMask2.mask_length r (by omega)
  have last:=mask_last r hr
  have e:=List.take_succ_eq_append_getElem (l:=BankMask2.mask r) (i:=116) (by omega)
  have take : (BankMask2.mask r).take 117=BankMask2.mask r:=List.take_of_length_le (by omega)
  rw [take] at e
  change BankMask2.mask r=shortMask r++[_] at e
  rw [List.getD_eq_getElem _ _ (by omega)] at last
  rw [last] at e
  exact e

#print axioms mask_split
end ECDSAAdd.Entrant.SpareParity

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic

def recopy (c cache : Wire) (src bank : List Wire) : Program :=
  CachedSquareCopy.copy c cache (shortMask src) (shortMask bank)

theorem recopy_restore_eq (c cache g : Wire) (src bank : List Wire)
    (hs : src.length=128) (hb : bank.length=128)
    (bg : bank.getD 118 0≠g) (cg : c≠g) (sg : src.getD 118 0≠g)
    (free : g∉wires (recopy c cache src bank))
    (cb : c∉shortMask bank) (sb : src.getD 118 0∉shortMask bank)
    (bb : bank.getD 118 0∉shortMask bank) (gb : g∉shortMask bank)
    (s : State) (m : List Bool) (hz : s.basis (bank.getD 118 0)=false)
    (saved : s.basis g=(s.basis c && s.basis (src.getD 118 0))) :
    run (recopy c cache src bank++SingleSpare.restore (bank.getD 118 0) g) m s=
      run (CachedSquareCopy.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) m
        ⟨s.phase,writeBit s.basis g false⟩ := by
  have sl:=shortMask_length src hs
  have bl:=shortMask_length bank hb
  rw [mask_split src hs,mask_split bank hb,SingleSpare.cached_append c cache _ _ _ _ (sl.trans bl.symm) (by omega)]
  apply SingleSpare.prefix_restore_eq _ c (src.getD 118 0) (bank.getD 118 0) g bg cg sg free s m
  · dsimp only [recopy]
    rw [SingleSpare.cached_frame c cache _ _ s m _ bb]
    exact hz
  · dsimp only [recopy]
    rw [SingleSpare.cached_frame c cache _ _ s m _ gb,
      SingleSpare.cached_frame c cache _ _ s m _ cb,
      SingleSpare.cached_frame c cache _ _ s m _ sb]
    exact saved

theorem recopy_restore_context_eq (c cache g : Wire) (src bank : List Wire)
    (hs : src.length=128) (hb : bank.length=128)
    (bg : bank.getD 118 0≠g) (cg : c≠g) (sg : src.getD 118 0≠g)
    (free : g∉wires (recopy c cache src bank))
    (cb : c∉shortMask bank) (sb : src.getD 118 0∉shortMask bank)
    (bb : bank.getD 118 0∉shortMask bank) (gb : g∉shortMask bank)
    (s : State) (m : List Bool) (context : Program) (hz : s.basis (bank.getD 118 0)=false)
    (saved : s.basis g=(s.basis c && s.basis (src.getD 118 0))) :
    run ((recopy c cache src bank++SingleSpare.restore (bank.getD 118 0) g)++context) m s=
      run (CachedSquareCopy.copy c cache (BankMask2.mask src) (BankMask2.mask bank)++context) m
        ⟨s.phase,writeBit s.basis g false⟩ := by
  have hn : measurementCount (recopy c cache src bank++SingleSpare.restore (bank.getD 118 0) g)=0 := by
    simp [recopy,SingleSpare.restore,measurementCount_append,measurementCount,SingleSpare.cached_mc]
  have ho:=SingleSpare.cached_mc c cache (BankMask2.mask src) (BankMask2.mask bank)
  conv_lhs=>rw [BankMask2.run_cat]
  conv_rhs=>rw [BankMask2.run_cat]
  rw [hn,ho,List.drop_zero]
  rw [recopy_restore_eq c cache g src bank hs hb bg cg sg free cb sb bb gb s m hz saved]

#print axioms recopy_restore_context_eq

theorem body_on_shadow_spare (ext dst out : List Wire) (body : Program) (g : Wire)
    (hbody : ∀q∈ext,q∉wires body) (hg : g∉wires body)
    (ed : ∀q∈ext,q∉dst) (eo : ∀q∈ext,q∉out) (gd : g∉dst) (go : g∉out)
    (s u : State) (m : List Bool) (P V : Nat)
    (ud : regValue dst u.basis=P^2)
    (uf : ∀q,q∉dst → q∉ext → q≠g → u.basis q=s.basis q)
    (callback : ∀t : State,∀n : List Bool,regValue dst t.basis=P^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body n t).phase=t.phase ∧ regValue out (run body n t).basis=V ∧
        ∀q,q∉out → (run body n t).basis q=t.basis q) :
    (run body m u).phase=u.phase ∧ regValue out (run body m u).basis=V ∧
      ∀q,q∉out → (run body m u).basis q=u.basis q := by
  apply ParityParkCopy.body_on_shadow (ext++[g]) dst out body
    (fun q hq=>by
      rcases List.mem_append.mp hq with h|h
      · exact hbody q h
      · simpa using (List.mem_singleton.mp h) ▸ hg)
    (fun q hq=>by
      rcases List.mem_append.mp hq with h|h
      · exact ed q h
      · simpa using (List.mem_singleton.mp h) ▸ gd)
    (fun q hq=>by
      rcases List.mem_append.mp hq with h|h
      · exact eo q h
      · simpa using (List.mem_singleton.mp h) ▸ go) s u m P V ud _ callback
  intro q qd qx
  exact uf q qd (fun h=>qx (List.mem_append_left _ h))
    (fun e=>qx (List.mem_append_right _ (by simp [e])))

#print axioms body_on_shadow_spare
#print axioms recopy_restore_eq
end ECDSAAdd.Entrant.SpareParity

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem recopy_counts (c cache : Wire) (src bank : List Wire) (hs : src.length=128) (hb : bank.length=128) :
    toffoliCount (recopy c cache src bank)+1=
      toffoliCount (CachedSquareCopy.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) ∧
    measurementCount (recopy c cache src bank)=
      measurementCount (CachedSquareCopy.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) ∧
    Challenge.gateSlots (recopy c cache src bank)+1=
      Challenge.gateSlots (CachedSquareCopy.copy c cache (BankMask2.mask src) (BankMask2.mask bank)) := by
  have sl:=shortMask_length src hs
  have bl:=shortMask_length bank hb
  have ml:=BankMask2.mask_length src (by omega)
  have nl:=BankMask2.mask_length bank (by omega)
  have eq (a b : List Wire) : ParityCachedResearch.copy c cache a b=CachedSquareCopy.copy c cache a b := by
    cases a <;> cases b <;> rfl
  have sn:=ParityProtocolResources.copy_counts c cache (shortMask src) (shortMask bank) (by omega) (by omega)
  have so:=ParityProtocolResources.copy_counts c cache (BankMask2.mask src) (BankMask2.mask bank) (by omega) (by omega)
  have tn:=ParityProtocolResources.copy_slots c cache (shortMask src) (shortMask bank) (by omega)
  have oldSlots:=ParityProtocolResources.copy_slots c cache (BankMask2.mask src) (BankMask2.mask bank) (by omega)
  simp only [eq] at sn tn
  simp only [eq] at so oldSlots
  dsimp only [recopy]
  constructor
  · omega
  constructor <;> omega

def program (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (c : Wire)
    (src dst : List Wire) (body : Program) (g : Wire) : Program :=
  ParkCopy.pA L c src++ParkCopy.pM L ext src dst++
    SingleSpare.save ((ParityParkCopy.bank L src).getD 118 0) g++
    ParityParkCopy.loan L ext src++ParityParkCopy.clearMasked L c src++
    ParkCopy.pD ext++ParkCopy.pMI L ext src++ParkCopy.pB L ext body++
    recopy c (LowZero18Square.cacheWire L dst) src (ParityParkCopy.bank L src)++
    SingleSpare.restore ((ParityParkCopy.bank L src).getD 118 0) g++
    ParkCopy.pMO L ext src++ParityParkCopy.restore L ext src++ParkCopy.pCL L ext src dst++ParkCopy.pE L c src

theorem counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (c : Wire) (src dst : List Wire) (body : Program) (g : Wire) (hs : src.length=128) :
    toffoliCount (program L ext c src dst body g)+1=toffoliCount (ParityParkCopy.program L ext c src dst body) ∧
    measurementCount (program L ext c src dst body g)=measurementCount (ParityParkCopy.program L ext c src dst body) ∧
    Challenge.gateSlots (program L ext c src dst body g)=Challenge.gateSlots (ParityParkCopy.program L ext c src dst body)+2 := by
  have bl : (ParityParkCopy.bank L src).length=128 := by
    simp only [ParityParkCopy.bank,List.length_take,(L.measured_bank_widths hw).1,hs]
    rfl
  have h:=recopy_counts c (LowZero18Square.cacheWire L dst) src (ParityParkCopy.bank L src) hs bl
  have st : toffoliCount (SingleSpare.save ((ParityParkCopy.bank L src).getD 118 0) g)=0 := rfl
  have sm : measurementCount (SingleSpare.save ((ParityParkCopy.bank L src).getD 118 0) g)=0 := rfl
  have ss : Challenge.gateSlots (SingleSpare.save ((ParityParkCopy.bank L src).getD 118 0) g)=1 := rfl
  have rt : toffoliCount (SingleSpare.restore ((ParityParkCopy.bank L src).getD 118 0) g)=0 := rfl
  have rm : measurementCount (SingleSpare.restore ((ParityParkCopy.bank L src).getD 118 0) g)=0 := rfl
  have rs : Challenge.gateSlots (SingleSpare.restore ((ParityParkCopy.bank L src).getD 118 0) g)=2 := rfl
  simp only [program,ParityParkCopy.program,ParityParkCopy.recopy,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append,st,sm,ss,rt,rm,rs]
  omega

#print axioms recopy_counts
#print axioms counts
end ECDSAAdd.Entrant.SpareParity

namespace ECDSAAdd.Entrant.SingleSpare
open Arithmetic
theorem run_write_commute (p : Program) (g : Wire) (hg : g∉wires p)
    (s : State) (m : List Bool) (value : Bool) :
    run p m ⟨s.phase,writeBit s.basis g value⟩=
      ⟨(run p m s).phase,writeBit (run p m s).basis g value⟩ := by
  let shadow : State:=⟨s.phase,writeBit s.basis g value⟩
  have loc:=run_local_increment p s shadow m (by
    intro q hq
    have qg : q≠g:=fun e=>hg (e ▸ hq)
    simp [shadow,writeBit,qg])
  have phase : (run p m shadow).phase=(run p m s).phase := by
    have h:=loc.1
    change ((run p m s).phase ^^ s.phase)=((run p m shadow).phase ^^ s.phase) at h
    exact (Bool.xor_left_inj.mp h).symm
  change State.mk (run p m shadow).phase (run p m shadow).basis=_
  apply congrArg₂ State.mk phase
  funext q
  by_cases qg : q=g
  · subst q
    rw [run_preserves_outside p m shadow g hg]
    simp [shadow,writeBit]
  · have eq : (run p m shadow).basis q=(run p m s).basis q := by
      by_cases used : q∈wires p
      · exact (loc.2 q used).symm
      · rw [run_preserves_outside p m shadow q used,run_preserves_outside p m s q used]
        simp [shadow,writeBit,qg]
    simpa [writeBit,qg] using eq


theorem save_prefix_restore_eq (p : Program) (c a b g : Wire)
    (bg : b≠g) (cg : c≠g) (ag : a≠g) (hg : g∉wires p)
    (s : State) (m : List Bool) (gz : s.basis g=false)
    (initial : s.basis b=(s.basis c && s.basis a))
    (lastzero : (run p m s).basis b=false)
    (control : (run p m s).basis c=s.basis c)
    (source : (run p m s).basis a=s.basis a) :
    run (save b g++(p++restore b g)) m s=run (p++[.CCX c a b]) m s := by
  have se : run (save b g) m s=⟨s.phase,writeBit s.basis g (s.basis b)⟩ := by
    simp [save,run,gz]
  rw [BankMask2.run_cat,show measurementCount (save b g)=0 from rfl,List.drop_zero,se]
  conv_lhs=>rw [BankMask2.run_cat]
  conv_rhs=>rw [BankMask2.run_cat]
  rw [run_write_commute p g hg s m (s.basis b)]
  let u:=run p m s
  have ug : u.basis g=false:=(run_preserves_outside p m s g hg).trans gz
  have clear : (State.mk u.phase (writeBit (writeBit u.basis g (s.basis b)) g false))=u := by
    change State.mk u.phase _=State.mk u.phase u.basis
    congr 1
    funext q
    by_cases qg : q=g
    · subst q
      simp [writeBit,ug]
    · simp [writeBit,qg]
  have e:=restore_eq_controlled c a b g bg cg ag
    ⟨u.phase,writeBit u.basis g (s.basis b)⟩ (m.drop (measurementCount p))
    (by simpa [writeBit,bg,u] using lastzero)
    (by simpa [writeBit,cg,ag,u,control,source] using initial)
  rw [clear] at e
  exact e

theorem save_prefix_restore_context_eq (p : Program) (c a b g : Wire)
    (bg : b≠g) (cg : c≠g) (ag : a≠g) (hg : g∉wires p)
    (s : State) (m : List Bool) (rest : Program) (gz : s.basis g=false)
    (initial : s.basis b=(s.basis c && s.basis a))
    (lastzero : (run p m s).basis b=false)
    (control : (run p m s).basis c=s.basis c)
    (source : (run p m s).basis a=s.basis a) :
    run ((save b g++(p++restore b g))++rest) m s=run ((p++[.CCX c a b])++rest) m s := by
  have hn : measurementCount (save b g++(p++restore b g))=measurementCount p := by
    simp [save,restore,measurementCount_append,measurementCount]
  have ho : measurementCount (p++[.CCX c a b])=measurementCount p := by
    simp [measurementCount_append,measurementCount]
  conv_lhs=>rw [BankMask2.run_cat]
  conv_rhs=>rw [BankMask2.run_cat]
  rw [hn,ho,save_prefix_restore_eq p c a b g bg cg ag hg s m gz initial lastzero control source]

#print axioms save_prefix_restore_context_eq
#print axioms run_write_commute
#print axioms save_prefix_restore_eq
end ECDSAAdd.Entrant.SingleSpare

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

def front (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (c : Wire) (src dst : List Wire) : Program :=
  ParkCopy.pA L c src++ParkCopy.pM L ext src dst

def middlePrefix (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (c : Wire)
    (src dst : List Wire) (body : Program) : Program :=
  ParityParkCopy.pre L ext c src++ParkCopy.pD ext++ParkCopy.pMI L ext src++ParkCopy.pB L ext body++
    recopy c (LowZero18Square.cacheWire L dst) src (ParityParkCopy.bank L src)

def suffix (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (c : Wire) (src dst : List Wire) : Program :=
  ParkCopy.pMO L ext src++ParityParkCopy.restore L ext src++ParkCopy.pCL L ext src dst++ParkCopy.pE L c src

theorem old_program_shape (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) (body : Program) (hs : src.length=128) :
    ParityParkCopy.program L ext c src dst body=
      front L ext c src dst++
        ((middlePrefix L ext c src dst body++[.CCX c (src.getD 118 0) ((ParityParkCopy.bank L src).getD 118 0)])++
          suffix L ext c src dst) := by
  have hb : (ParityParkCopy.bank L src).length=128 := by
    simp only [ParityParkCopy.bank,List.length_take,(L.measured_bank_widths hw).1,hs]
    rfl
  have sl:=shortMask_length src hs
  have bl:=shortMask_length (ParityParkCopy.bank L src) hb
  have e : ParityParkCopy.recopy L c src dst=
      recopy c (LowZero18Square.cacheWire L dst) src (ParityParkCopy.bank L src)++
        [.CCX c (src.getD 118 0) ((ParityParkCopy.bank L src).getD 118 0)] := by
    unfold ParityParkCopy.recopy
    rw [mask_split src hs,mask_split (ParityParkCopy.bank L src) hb,
      SingleSpare.cached_append _ _ _ _ _ _ (sl.trans bl.symm) (by omega)]
    rfl
  simp only [ParityParkCopy.program,e,front,middlePrefix,suffix,ParityParkCopy.pre,List.append_assoc]

theorem new_program_shape (L : CuccaroStreamedSquareWideLayout)
    (ext : List Wire) (c : Wire) (src dst : List Wire) (body : Program) (g : Wire) :
    program L ext c src dst body g=
      front L ext c src dst++
        ((SingleSpare.save ((ParityParkCopy.bank L src).getD 118 0) g++
          (middlePrefix L ext c src dst body++SingleSpare.restore ((ParityParkCopy.bank L src).getD 118 0) g))++
            suffix L ext c src dst) := by
  simp only [program,front,middlePrefix,suffix,ParityParkCopy.pre,List.append_assoc]

theorem program_run_eq_of_boundaries (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) (body : Program) (g : Wire) (hs : src.length=128)
    (bg : (ParityParkCopy.bank L src).getD 118 0≠g) (cg : c≠g) (ag : src.getD 118 0≠g)
    (free : g∉wires (middlePrefix L ext c src dst body)) (s : State) (records : List Bool)
    (gz : (run (front L ext c src dst) records s).basis g=false)
    (initial : (run (front L ext c src dst) records s).basis ((ParityParkCopy.bank L src).getD 118 0)=
      ((run (front L ext c src dst) records s).basis c &&
        (run (front L ext c src dst) records s).basis (src.getD 118 0)))
    (lastzero : (run (middlePrefix L ext c src dst body)
      (records.drop (measurementCount (front L ext c src dst))) (run (front L ext c src dst) records s)).basis
        ((ParityParkCopy.bank L src).getD 118 0)=false)
    (control : (run (middlePrefix L ext c src dst body)
      (records.drop (measurementCount (front L ext c src dst))) (run (front L ext c src dst) records s)).basis c=
        (run (front L ext c src dst) records s).basis c)
    (source : (run (middlePrefix L ext c src dst body)
      (records.drop (measurementCount (front L ext c src dst))) (run (front L ext c src dst) records s)).basis
        (src.getD 118 0)=(run (front L ext c src dst) records s).basis (src.getD 118 0)) :
    run (program L ext c src dst body g) records s=run (ParityParkCopy.program L ext c src dst body) records s := by
  rw [new_program_shape,old_program_shape L hw ext c src dst body hs]
  conv_lhs=>rw [BankMask2.run_cat]
  conv_rhs=>rw [BankMask2.run_cat]
  exact SingleSpare.save_prefix_restore_context_eq _ c (src.getD 118 0) ((ParityParkCopy.bank L src).getD 118 0) g
    bg cg ag free _ _ (suffix L ext c src dst) gz initial lastzero control source

#print axioms program_run_eq_of_boundaries
#print axioms old_program_shape
#print axioms new_program_shape
end ECDSAAdd.Entrant.SpareParity

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic

theorem masked_bit (c : Wire) (src bank : List Wire) (s : BasisState)
    (hs : 118<src.length) (hb : 118<bank.length)
    (masked : regValue bank s=if s c then regValue src s else 0) :
    s (bank.getD 118 0)=(s c && s (src.getD 118 0)) := by
  have a:=regValue_bit src 118 0 s hs
  have b:=regValue_bit bank 118 0 s hb
  rw [masked] at b
  cases hc : s c <;> cases hd : s (bank.getD 118 0) <;>
    cases he : s (src.getD 118 0) <;> simp_all <;> omega

theorem shortMask_subset (r : List Wire) : shortMask r⊆r :=
  (List.take_sublist 116 (BankMask2.mask r)).subset.trans (BankMask2.mask_sublist r).subset

theorem last_not_short (r : List Wire) (hr : r.length=128) (hn : r.Nodup) :
    r.getD 118 0∉shortMask r := by
  have nd:=hn.sublist (BankMask2.mask_sublist r)
  rw [mask_split r hr] at nd
  have dis:=(List.nodup_append'.mp nd).2.2
  intro h
  exact dis h (List.mem_singleton_self _)

#print axioms masked_bit
#print axioms last_not_short
end ECDSAAdd.Entrant.SpareParity

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ParityParkCopy
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
theorem prefix_facts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (control cache : Wire) (he : 300≤ext.length) (h128 : src.length=128) (hd : 0<dst.length)
    (hn : (control::(src++bank L src++ext)).Nodup)
    (extDst : ∀q∈ext,q ∉ dst) (extOut : ∀q∈ext,q ∉ L.core.out)
    (bankDst : ∀q∈bank L src,q ∉ dst) (bankOut : ∀q∈bank L src,q ∉ L.core.out)
    (srcOut : ∀q∈src,q ∉ L.core.out) (ctlOut : control ∉ L.core.out)
    (dstOut : ∀q∈dst,q ∉ L.core.out)
    (p s : State) (m0 mD m1 m2 m3 : List Bool) (v V : Nat)
    (bv : regValue (LowZero18LowK.jregsH L ext src dst).bank p.basis=v)
    (inv : (LowZero18LowK.jregsH L ext src dst).invF v p.basis)
    (masked : regValue (bank L src) p.basis=if p.basis control then regValue src p.basis else 0)
    (prod : regValue dst p.basis=(if p.basis control then regValue src p.basis else 0)^2)
    (hostzero : regValue (ParkCopy.hosts ext) p.basis=0) (bankzero : regValue (bank L src) s.basis=0)
    (pframe : ∀q,q ∉ bank L src → q ∉ dst → q ∉ ext → p.basis q=s.basis q)
    (targetBank : SquareCarryLoan719.target L∉bank L src)
    (targetExt : SquareCarryLoan719.target L∉ext)
    (targetOut : SquareCarryLoan719.target L∉L.core.out)
    (targetZero : p.basis (SquareCarryLoan719.target L)=false)
    (hostZero : p.basis (ext.getD 0 0)=false)
    (body : Program) (hbody : ∀q∈ext,q ∉ ECDSAAdd.wires body)
    (callback : ∀t : State,∀n : List Bool,
      regValue dst t.basis=(if p.basis control then regValue src p.basis else 0)^2 →
      (∀q,q ∉ dst → t.basis q=s.basis q) →
      (run body n t).phase=t.phase ∧ regValue L.core.out (run body n t).basis=V ∧
        ∀q,q ∉ L.core.out → (run body n t).basis q=t.basis q) :
    let a:=run (loan L ext src++clearMasked L control src) m0 p
    let b:=run (ParkCopy.move ((bank L src).drop 119) (ParkCopy.hosts ext)) m1 a
    let c:=run (renameProgram (SquareCarryLoan719.foldPerm L ext) body) m2 b
    let w:=run (recopy control cache src (bank L src)) m3 c
    run (ParkCopy.pD ext) mD a=a ∧
    w.basis ((bank L src).getD 118 0)=false ∧
    w.basis control=p.basis control ∧ w.basis (src.getD 118 0)=p.basis (src.getD 118 0) := by
  let a:=run (loan L ext src++clearMasked L control src) m0 p
  let b:=run (ParkCopy.move ((bank L src).drop 119) (ParkCopy.hosts ext)) m1 a
  let c:=run (renameProgram (SquareCarryLoan719.foldPerm L ext) body) m2 b
  let w:=run (recopy control cache src (bank L src)) m3 c
  have pre:=pre_move_correct L hw ext src dst control he h128 p m0 m1 v bv inv masked hn hostzero
  have bl : (bank L src).length=128 := by simp [bank,(L.measured_bank_widths hw).1,h128]
  have nc:=(List.nodup_cons.mp hn).1
  have nr:=(List.nodup_cons.mp hn).2
  have nsb:=(List.nodup_append'.mp nr).1
  have nx:=(List.nodup_append'.mp nr).2.1
  have dx:=(List.nodup_append'.mp nr).2.2
  have dsb:=(List.nodup_append'.mp nsb).2.2
  have nb:=(List.nodup_append'.mp nsb).2.1
  have memX (i : Nat) (hi : i<300) : ext.getD i 0∈ext:=ParkCopy.getD_mem _ _ (by omega)
  have bX {q : Wire} (qb : q∈bank L src) (qx : q∈ext) : False:=dx (List.mem_append_right src qb) qx
  have sX {q : Wire} (qs : q∈src) (qx : q∈ext) : False:=dx (List.mem_append_left _ qs) qx
  have hostsX:=ParkCopy.hosts_sub ext he
  have keepB (q : Wire) (qb : q ∉ bank L src) (qx : q ∉ ext) : b.basis q=p.basis q :=
    pre.2.2.2.2.2 q qb (fun h=>qx (hostsX q h)) (fun h=>qx (h.symm ▸ memX 198 (by decide)))
      (fun h=>qx (h.symm ▸ memX 199 (by decide)))
  have bd : regValue dst b.basis=(if p.basis control then regValue src p.basis else 0)^2 := by
    rw [←prod]
    apply regValue_congr
    intro q hq
    exact keepB q (fun h=>bankDst q h hq) (fun h=>extDst q h hq)
  have bf : ∀q,q ∉ dst → q ∉ ext → b.basis q=s.basis q := by
    intro q qd qx
    by_cases qb : q∈bank L src
    · exact ((regValue_zero _ _).mp pre.2.1 q qb).trans ((regValue_zero _ _).mp bankzero q qb).symm
    · exact (keepB q qb qx).trans (pframe q qb qd qx)
  have rawResult:=body_on_shadow ext dst L.core.out body hbody extDst extOut s b m2
    (if p.basis control then regValue src p.basis else 0) V bd bf callback
  have tz : b.basis (SquareCarryLoan719.target L)=false := (keepB _ targetBank targetExt).trans targetZero
  have h0 := memX 0 (by decide)
  have hz : b.basis (ext.getD 0 0)=false :=
    (pre.2.2.2.2.2 _ (fun hb=>bX hb h0)
      (fun hh=>ParkCopy.host_ne_zero ext nx he _ hh rfl)
      (CombinedBankLoan.get_ne ext nx 0 198 (by omega) (by omega) (by decide))
      (CombinedBankLoan.get_ne ext nx 0 199 (by omega) (by omega) (by decide))).trans hostZero
  have fe:=SquareCarryLoan719.fold_run_eq L hw ext body b m2 tz
    ((rawResult.2.2 _ targetOut).trans tz) hz (hbody _ h0)
  have bodyResult : (run (renameProgram (SquareCarryLoan719.foldPerm L ext) body) m2 b).phase=b.phase ∧
      regValue L.core.out (run (renameProgram (SquareCarryLoan719.foldPerm L ext) body) m2 b).basis=V ∧
      ∀q,q∉L.core.out → (run (renameProgram (SquareCarryLoan719.foldPerm L ext) body) m2 b).basis q=b.basis q := by
    rw [fe]
    exact rawResult
  have keep (q : Wire) (qo : q ∉ L.core.out) (qb : q ∉ bank L src)
      (qh : q ∉ ParkCopy.hosts ext) (q0 : q≠ext.getD 198 0) (q1 : q≠ext.getD 199 0) : c.basis q=p.basis q :=
    (bodyResult.2.2 q qo).trans (pre.2.2.2.2.2 q qb qh q0 q1)
  have sourceKeep : ∀q∈src,c.basis q=p.basis q := by
    intro q hq
    exact keep q (srcOut q hq) (fun h=>dsb hq h) (fun h=>sX hq (hostsX q h))
      (fun h=>sX hq (h.symm ▸ memX 198 (by decide))) (fun h=>sX hq (h.symm ▸ memX 199 (by decide)))
  have ctlKeep : c.basis control=p.basis control := by
    have offB : control ∉ bank L src:=fun h=>nc (List.mem_append_left ext (List.mem_append_right src h))
    have offX : control ∉ ext:=fun h=>nc (List.mem_append_right (src++bank L src) h)
    exact keep control ctlOut offB (fun h=>offX (hostsX _ h))
      (fun h=>offX (h.symm ▸ memX 198 (by decide))) (fun h=>offX (h.symm ▸ memX 199 (by decide)))
  have pf:=pre_frame L hw ext src dst control he h128 p m0 v bv inv masked hn
  have hzHosts : ∀q∈ParkCopy.hosts ext,a.basis q=false := by
    intro q hq
    have away:=hosts_away ext nx he q hq
    exact (pf q (fun h=>bX (List.mem_of_mem_take h) (hostsX q hq)) away.1 away.2.1).trans
      ((regValue_zero _ _).mp hostzero q hq)
  have dummy : run (ParkCopy.pD ext) mD a=a := ParkCopy.dummies_run _ _ _ hzHosts
  have sMem : src.getD 118 0∈src:=ParkCopy.getD_mem src 118 (by omega)
  have bMem : (bank L src).getD 118 0∈bank L src:=ParkCopy.getD_mem _ 118 (by omega)
  have lastOff:=last_not_short (bank L src) bl nb
  have ctlOff : control∉bank L src:=fun h=>nc (List.mem_append_left ext (List.mem_append_right src h))
  have srcOff : src.getD 118 0∉bank L src:=fun h=>dsb sMem h
  have cz : c.basis ((bank L src).getD 118 0)=false :=
    (bodyResult.2.2 _ (bankOut _ bMem)).trans ((regValue_zero _ _).mp pre.2.1 _ bMem)
  refine ⟨dummy,?_,?_,?_⟩
  · exact (SingleSpare.cached_frame control cache (shortMask src) (shortMask (bank L src)) c m3 _ lastOff).trans cz
  · exact (SingleSpare.cached_frame control cache (shortMask src) (shortMask (bank L src)) c m3 _
      (fun h=>ctlOff (shortMask_subset _ h))).trans ctlKeep
  · exact (SingleSpare.cached_frame control cache (shortMask src) (shortMask (bank L src)) c m3 _
      (fun h=>srcOff (shortMask_subset _ h))).trans (sourceKeep _ sMem)

theorem prefix_conditions (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext src dst : List Wire) (control : Wire) (he : 300≤ext.length) (h128 : src.length=128) (hd : 0<dst.length)
    (hn : (control::(src++bank L src++ext)).Nodup)
    (extDst : ∀q∈ext,q ∉ dst) (extOut : ∀q∈ext,q ∉ L.core.out)
    (bankDst : ∀q∈bank L src,q ∉ dst) (bankOut : ∀q∈bank L src,q ∉ L.core.out)
    (srcOut : ∀q∈src,q ∉ L.core.out) (ctlOut : control ∉ L.core.out)
    (dstOut : ∀q∈dst,q ∉ L.core.out)
    (p s : State) (records : List Bool) (v V : Nat)
    (bv : regValue (LowZero18LowK.jregsH L ext src dst).bank p.basis=v)
    (inv : (LowZero18LowK.jregsH L ext src dst).invF v p.basis)
    (masked : regValue (bank L src) p.basis=if p.basis control then regValue src p.basis else 0)
    (prod : regValue dst p.basis=(if p.basis control then regValue src p.basis else 0)^2)
    (hostzero : regValue (ParkCopy.hosts ext) p.basis=0) (bankzero : regValue (bank L src) s.basis=0)
    (pframe : ∀q,q ∉ bank L src → q ∉ dst → q ∉ ext → p.basis q=s.basis q)
    (targetBank : SquareCarryLoan719.target L∉bank L src)
    (targetExt : SquareCarryLoan719.target L∉ext)
    (targetOut : SquareCarryLoan719.target L∉L.core.out)
    (targetZero : p.basis (SquareCarryLoan719.target L)=false)
    (hostZero : p.basis (ext.getD 0 0)=false)
    (body : Program) (hbody : ∀q∈ext,q ∉ ECDSAAdd.wires body)
    (callback : ∀t : State,∀n : List Bool,
      regValue dst t.basis=(if p.basis control then regValue src p.basis else 0)^2 →
      (∀q,q ∉ dst → t.basis q=s.basis q) →
      (run body n t).phase=t.phase ∧ regValue L.core.out (run body n t).basis=V ∧
        ∀q,q ∉ L.core.out → (run body n t).basis q=t.basis q) :
    (run (middlePrefix L ext control src dst body) records p).basis ((bank L src).getD 118 0)=false ∧
    (run (middlePrefix L ext control src dst body) records p).basis control=p.basis control ∧
    (run (middlePrefix L ext control src dst body) records p).basis (src.getD 118 0)=p.basis (src.getD 118 0) := by
  let A:=ParityParkCopy.pre L ext control src
  let D:=ParkCopy.pD ext
  let M:=ParkCopy.pMI L ext src
  let B:=ParkCopy.pB L ext body
  let C:=recopy control (LowZero18Square.cacheWire L dst) src (bank L src)
  obtain ⟨a3,rC,e4⟩:=kseq (A++D++M++B) C records p
  obtain ⟨a2,rB,e3⟩:=kseq (A++D++M) B a3 p
  obtain ⟨a1,rM,e2⟩:=kseq (A++D) M a2 p
  obtain ⟨rA,rD,e1⟩:=kseq A D a1 p
  have f:=prefix_facts L hw ext src dst control (LowZero18Square.cacheWire L dst) he h128 hd hn
    extDst extOut bankDst bankOut srcOut ctlOut dstOut p s rA rD rM rB rC v V bv inv masked prod
    hostzero bankzero pframe targetBank targetExt targetOut targetZero hostZero body hbody callback
  dsimp only at f
  have ep : run (middlePrefix L ext control src dst body) records p=
      run C rC (run B rB (run M rM (run A rA p))) := by
    change run (A++D++M++B++C) records p=_
    rw [e4,e3,e2,e1]
    dsimp only [A,D,M,B,C,ParityParkCopy.pre,ParkCopy.pMI,ParkCopy.pB]
    rw [f.1]
  rw [ep]
  exact f.2

#print axioms prefix_conditions
end ECDSAAdd.Entrant.SpareParity

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout ParkCopy ParityParkCopy
attribute [local irreducible] run wires
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open LowZero18Square in
theorem correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (h128' : src.length=128)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (g : Wire) (bg : (ParityParkCopy.bank L src).getD 118 0≠g) (cg : control≠g) (ag : src.getD 118 0≠g)
    (freeFront : g∉wires (front L ext control src dst))
    (freeMiddle : g∉wires (middlePrefix L ext control src dst body))
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (gZero : s.basis g=false) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (program L ext control src dst body g) records s).phase=s.phase ∧
    regValue L.core.out (run (program L ext control src dst body g) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (program L ext control src dst body g) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have cacheFix : earlyPerm L (dst.headD 0)=dst.headD 0 := by
    have mem : dst.headD 0∈dst := by
      rcases dst with _|⟨d,ds⟩
      · have hz : src.length=0 := by simpa using hlen.symm
        omega
      · exact List.mem_cons_self
    have targetM : target L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (fun e => tmpD _ targetM (by simpa only [e] using mem))
      (fun e => tmpD _ hostM (by simpa only [e] using mem))
  let P := if s.basis control then regValue src s.basis else 0
  -- parking data
  have Blen : (L.inputBank.take src.length).length=128 := by rw [inputLen,h128']
  have hHx : ∀h∈hosts ext,h∈ext := hosts_sub ext he
  have hHnd : (hosts ext).Nodup := hosts_nodup ext hx he
  have hHT : ∀h∈freeHosts ext,h∉(LowZero18LowK.oregs L ext src dst).T := fun h hh => host_not_oT L ext src dst hx he h128' h hh
  have hHX : ∀h∈freeHosts ext,h∉(LowZero18LowK.kg L ext src dst).X := fun h hh => host_not_X L ext src dst hx he h128' tmpE h hh
  have hH0 : ∀h∈hosts ext,h≠ext.getD 0 0 := host_ne_zero ext hx he
  have hHB : ∀h∈hosts ext,h∉(L.inputBank.take src.length) := fun h hh => extB h (hHx h hh)
  have hHD : ∀h∈hosts ext,h∉dst := fun h hh => extD h (hHx h hh)
  have hHo : ∀h∈hosts ext,h∉L.core.out := fun h hh => extOut h (hHx h hh)
  have hHs : ∀q∈src,q∉hosts ext := fun q hq hh => extSrc q (hHx q hh) hq
  have ctlH : control∉hosts ext := fun h => ctlE (hHx _ h)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have b15 : ∀q∈(L.inputBank.take src.length).take 119,q∉(L.inputBank.take src.length).drop 119 := by
    intro q h1 h5
    have nd : ((L.inputBank.take src.length).take 119++(L.inputBank.take src.length).drop 119).Nodup := by
      rw [List.take_append_drop]; exact bNd
    exact (List.nodup_append.mp nd).2.2 q h1 q h5 rfl
  have b51 : ∀q∈(L.inputBank.take src.length).drop 119,q∉(L.inputBank.take src.length).take 119 :=
    fun q h5 h1 => b15 q h1 h5
  have ndMI : ((L.inputBank.take src.length).drop 119++hosts ext).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => hHB b hb (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (hosts ext++(L.inputBank.take src.length).drop 119).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  have lenMI : ((L.inputBank.take src.length).drop 119).length=(hosts ext).length := by
    rw [List.length_drop,Blen,hosts_length]
  obtain ⟨r1,r2,eFront⟩:=kseq (ParkCopy.pA L control src) (ParkCopy.pM L ext src dst) records s
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize hu0 : run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize hu1 : run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- hosts stay zero through the copy and the producer
  have loLen : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).1]
    rfl
  have hiLen : (LowZero18LowK.oregs L ext src dst).hi.length=64 := by
    rw [((LowZero18LowK.oregs L ext src dst).lens w).2.1]
    change (L.inputBank.take src.length).length-64=64
    rw [Blen]
  have loBound : regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis<2^64 := by
    simpa only [loLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
  have hiBound : regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^64 := by
    simpa only [hiLen] using regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
  have inv1:=mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at inv1
  have inv2:=mk.2.2.2.2.2.1
  simp only [LowZero18LowK.kg,if_pos h128',LowZero18LowK.kgH] at inv2
  have itLen : (LowZero18LowK.iregs L ext src dst).T.length=66 := by
    simp only [LowZero18LowK.iregs,List.length_take,List.length_drop]
    omega
  have jtLen : (LowZero18LowK.jregsH L ext src dst).T.length=66 := by
    simp only [LowZero18LowK.jregsH,List.length_take,List.length_drop]
    omega
  have iz:=CrossBits.top_zero (LowZero18LowK.iregs L ext src dst).T itLen
    (regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis) loBound u1.basis inv1.2
  have jz:=CrossBits.top_zero (LowZero18LowK.jregsH L ext src dst).T jtLen
    (regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis) hiBound u1.basis inv2.2
  have slice_get (a n i:Nat) (hi:i<n) (ha:a+i<ext.length) :
      ((ext.drop a).take n).getD i 0=ext.getD (a+i) 0 := by
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take,List.length_drop];omega),
      List.getD_eq_getElem _ _ ha]
    simp only [List.getElem_take,List.getElem_drop]
  simp only [LowZero18LowK.iregs] at iz
  simp only [LowZero18LowK.jregsH] at jz
  rw [slice_get 132 66 65 (by omega) (by omega)] at iz
  rw [slice_get 232 66 65 (by omega) (by omega)] at jz
  have otLen : (LowZero18LowK.oregs L ext src dst).T.length=130 := by
    simp only [LowZero18LowK.oregs,h128',List.length_take]
    omega
  have oz:=CrossBits.outer_zero (LowZero18LowK.oregs L ext src dst).T otLen
    (regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)
    (regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis) loBound hiBound u1.basis mk.2.2.2.1
  have otget : (LowZero18LowK.oregs L ext src dst).T.getD 129 0=ext.getD 129 0 := by
    simp only [LowZero18LowK.oregs,h128']
    rw [List.take_take]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_take];omega),
      List.getD_eq_getElem _ _ (by omega)]
    simp only [List.getElem_take]
  rw [otget] at oz
  have iz0:=CrossBits.low_zero (LowZero18LowK.iregs L ext src dst).T (by rw [itLen];decide)
    ((regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)%2^32)
    ((regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis)/2^32) u1.basis inv1.2
  have jz0:=CrossBits.low_zero (LowZero18LowK.jregsH L ext src dst).T (by rw [jtLen];decide)
    ((regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis)%2^32)
    ((regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis)/2^32) u1.basis inv2.2
  simp only [LowZero18LowK.iregs] at iz0
  simp only [LowZero18LowK.jregsH] at jz0
  rw [slice_get 132 66 0 (by omega) (by omega)] at iz0
  rw [slice_get 232 66 0 (by omega) (by omega)] at jz0
  have hU1 : ∀h∈hosts ext,u1.basis h=false := by
    intro h hh
    rcases hosts_split ext h hh with hf|rfl|rfl|rfl|rfl|rfl
    · exact (u1s h (hHD h hh) (hHT h hf) (hHX h hf)).trans
        ((u0s h (hHB h hh)).trans (ext0 h (hHx h hh)))
    · exact iz
    · exact jz
    · exact oz
    · exact iz0
    · exact jz0
  have srcw1 : ∀q∈src,u1.basis q=s.basis q := fun q hq =>
    (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq))
  have npre : (control::(src++bank L src++ext)).Nodup := by
    change ((control::(src++bank L src))++ext).Nodup
    apply List.nodup_append'.mpr
    refine ⟨ndMask,hx,?_⟩
    intro q hq hqx
    simp only [List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|hqs|hqb
    · exact ctlE hqx
    · exact extSrc q hqx hqs
    · exact extB q hqx hqb
  have jBank : regValue (LowZero18LowK.jregsH L ext src dst).bank u1.basis=
      regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    apply regValue_congr
    intro q hq
    change q∈(L.inputBank.take src.length).drop 64 at hq
    have qb:=List.mem_of_mem_drop hq
    exact u1z q (bD q qb) (fun h=>extB q h qb)
  have oldMask : regValue (bank L src) u1.basis=
      if u1.basis control then regValue src u1.basis else 0 := by
    rw [show regValue (bank L src) u1.basis=P from bank1,ctl1,src1]
  have eQ : run (front L ext control src dst) records s=u1 := by
    change run (ParkCopy.pA L control src++ParkCopy.pM L ext src dst) records s=u1
    rw [eFront]
    change run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2
      (run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s)=u1
    rw [hu0,hu1]
  have targetTmp : SquareCarryLoan719.target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetZ : u1.basis (SquareCarryLoan719.target L)=false :=
    (u1z _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans
      ((u0s _ (tmpB _ targetTmp)).trans (tmp0 _ targetTmp))
  have hostZ : u1.basis (ext.getD 0 0)=false :=
    cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1
  have facts:=prefix_conditions L hw ext src dst control he h128' (by omega) npre
    extD extOut bD bOut srcOut ctlO dOut u1 s
    (records.drop (measurementCount (front L ext control src dst))) _ V jBank inv2 oldMask
    (by simpa only [ctl1,src1] using dst1) ((regValue_zero _ _).mpr hU1) banks.1
    (fun q qb qd qx=>(u1z q qd qx).trans (u0s q qb))
    (tmpB _ targetTmp) (tmpE _ targetTmp) (tmpOut _ targetTmp) targetZ hostZ body hbody
    (by intro t m ht hf;apply callback t m;simpa only [ctl1,src1] using ht;exact hf)
  have initialBit:=masked_bit control src (bank L src) u1.basis (by omega) (by change 118<(L.inputBank.take src.length).length;omega) oldMask
  have eq:=program_run_eq_of_boundaries L hw ext control src dst body g h128' bg cg ag freeMiddle s records
    ((run_preserves_outside (front L ext control src dst) records s g freeFront).trans gZero)
    (by rw [eQ];exact initialBit)
    (by rw [eQ];exact facts.1)
    (by rw [eQ];exact facts.2.1)
    (by rw [eQ];exact facts.2.2)
  rw [eq]
  exact ParityParkCopy.correct L hw control hn src dst hs hd h128 hsmax hlen h128' ext hx hdx he body hbody
    s records hc hzero hz V callback

#print axioms correct
end ECDSAAdd.Entrant.SpareParity

namespace ECDSAAdd.Entrant.SpareParity
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] run wires
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem save_physical (b g : Wire) (bg : b≠g) : GatePhysical (SingleSpare.save b g) := by
  simp [SingleSpare.save,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,bg]
theorem restore_physical (b g : Wire) (bg : b≠g) : GatePhysical (SingleSpare.restore b g) := by
  simp [SingleSpare.restore,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,bg,Ne.symm bg]

theorem physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) (body : Program) (g : Wire)
    (hs : src.length=128) (bg : (ParityParkCopy.bank L src).getD 118 0≠g)
    (old : GatePhysical (ParityParkCopy.program L ext c src dst body)) :
    GatePhysical (program L ext c src dst body g) := by
  rw [old_program_shape L hw ext c src dst body hs] at old
  simp only [gatePhysical_append] at old
  obtain ⟨fr,⟨⟨mid,cc⟩,tail⟩⟩:=old
  have saveP : GatePhysical (SingleSpare.save ((ParityParkCopy.bank L src).getD 118 0) g) := by
    exact save_physical _ _ bg
  have restoreP : GatePhysical (SingleSpare.restore ((ParityParkCopy.bank L src).getD 118 0) g) := by
    exact restore_physical _ _ bg
  rw [new_program_shape]
  simp only [gatePhysical_append]
  exact ⟨fr,⟨⟨saveP,⟨mid,restoreP⟩⟩,tail⟩⟩

theorem support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (c : Wire) (src dst : List Wire) (body : Program) (g : Wire) (hs : src.length=128) :
    wires (program L ext c src dst body g)⊆insert g (wires (ParityParkCopy.program L ext c src dst body)) := by
  let b:=(ParityParkCopy.bank L src).getD 118 0
  have sw : wires (SingleSpare.save b g)={b,g} := by
    simp [SingleSpare.save,wires,Instr.wires]
  have rw' : wires (SingleSpare.restore b g)={b,g} := by
    ext q
    simp [SingleSpare.restore,wires,Instr.wires]
  have cw : wires [.CCX c (src.getD 118 0) b]={c,src.getD 118 0,b} := by
    simp [wires,Instr.wires]
  intro q hq
  rw [new_program_shape] at hq
  rw [old_program_shape L hw ext c src dst body hs]
  change q∈wires (front L ext c src dst++
    ((SingleSpare.save b g++(middlePrefix L ext c src dst body++SingleSpare.restore b g))++suffix L ext c src dst)) at hq
  change q∈insert g (wires (front L ext c src dst++
    ((middlePrefix L ext c src dst body++[.CCX c (src.getD 118 0) b])++suffix L ext c src dst)))
  simp only [wires_append,sw,rw',cw,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hq ⊢
  tauto

theorem recopy_shape (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (src dst : List Wire) (hs : src.length=128) :
    ParityParkCopy.recopy L c src dst=
      recopy c (LowZero18Square.cacheWire L dst) src (ParityParkCopy.bank L src)++
        [.CCX c (src.getD 118 0) ((ParityParkCopy.bank L src).getD 118 0)] := by
  have hb : (ParityParkCopy.bank L src).length=128 := by
    simp only [ParityParkCopy.bank,List.length_take,(L.measured_bank_widths hw).1,hs]
    rfl
  have sl:=shortMask_length src hs
  have bl:=shortMask_length (ParityParkCopy.bank L src) hb
  unfold ParityParkCopy.recopy
  rw [mask_split src hs,mask_split (ParityParkCopy.bank L src) hb,
    SingleSpare.cached_append _ _ _ _ _ _ (sl.trans bl.symm) (by omega)]
  rfl

theorem recopy_support_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire)
    (src dst : List Wire) (hs : src.length=128) :
    wires (recopy c (LowZero18Square.cacheWire L dst) src (ParityParkCopy.bank L src))⊆
      wires (ParityParkCopy.recopy L c src dst) := by
  rw [recopy_shape L hw c src dst hs,wires_append]
  exact Finset.subset_union_left

theorem save_free (q b g : Wire) (qb : q≠b) (qg : q≠g) : q∉wires (SingleSpare.save b g) := by
  simp [SingleSpare.save,wires,Instr.wires,qb,qg]
theorem restore_free (q b g : Wire) (qb : q≠b) (qg : q≠g) : q∉wires (SingleSpare.restore b g) := by
  simp [SingleSpare.restore,wires,Instr.wires,qb,qg]

#print axioms recopy_support_subset
#print axioms physical
#print axioms support
end ECDSAAdd.Entrant.SpareParity

end -- Spare single-bit wrapper

section
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop

theorem fold_fixes_source (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)(hn:L.wires.Nodup)
 (ext:List Wire)(hlen:300≤ext.length)(away:∀q∈ext,q∉L.wires):
 LowZero18Square.foldPerm L ext (bit1 L.core.high)=bit1 L.core.high:=by
 have vy:=sourceHigh_in_y L hw
 have ht:SquareCarryLoan719.target L∈L.foldPad:=by
  apply List.mem_of_mem_drop
  exact DiagSq.getD_in (LowZero18LowK.ktmp L) 67 (by rw[LowZero18LowK.ktmp_length L hw];omega)
 have ne1:bit1 L.core.high≠SquareCarryLoan719.target L:=by
  intro e
  have a:=List.count_pos_iff.mpr vy
  have b:=List.count_pos_iff.mpr ht
  rw[←e]at b
  have h:=layoutCount L hn (bit1 L.core.high)
  omega
 have ne2:bit1 L.core.high≠ext.getD 0 0:=by
  intro e
  apply away (ext.getD 0 0) (DiagSq.getD_in ext 0 (by omega))
  rw[←e]
  simp[CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,vy]
 change SquareCarryLoan719.foldPerm L ext (bit1 L.core.high)=_
 rw[SquareCarryLoan719.foldPerm_eq L hw]
 exact Equiv.swap_apply_of_ne_of_ne ne1 ne2

theorem hosted_window_rel (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)
 (ext:List Wire)(c:Wire)(src dst:List Wire)(hsrc:src=L.core.high):
 toffoliCount (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))+1059=
  toffoliCount (LowZero18Square.withLowK2 L ext c src dst (bBody L c)) ∧
 measurementCount (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))+4=
  measurementCount (LowZero18Square.withLowK2 L ext c src dst (bBody L c)) ∧
 wires (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))⊆
  insert L.core.sumCarry (wires (LowZero18Square.withLowK2 L ext c src dst (bBody L c))) ∧
 Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (hostedBody L (LowZero18Square.foldPerm L ext) c))≤
  Challenge.gateSlots (LowZero18Square.withLowK2 L ext c src dst (bBody L c)):=by
 have h:=hosted_rel L hw (LowZero18Square.foldPerm L ext) c
 have full:=withLowK2_body_extra_two L ext c src dst _ _ 1059 4 _ _ h.1 h.2.1 h.2.2
 simp only[Equiv.apply_symm_apply]at full
 have srcLen:src.length=128:=by rw[hsrc,L.core.high_length hw.core]
 have banks:=(L.measured_bank_widths hw).1
 have cp:bit1 L.core.high∈wires (copyRegister (some c) src (L.inputBank.take src.length)):=by
  rw[copyRegister_wires _ _ _ (by simp[srcLen,banks])]
  have nonempty:src.isEmpty=false:=by rw[List.isEmpty_eq_false_iff];intro e;rw[e]at srcLen;contradiction
  rw[nonempty];simp only[Bool.false_eq_true,if_false,List.mem_toFinset,List.mem_append]
  exact Or.inl (Or.inr (by rw[hsrc];exact bit1_mem _ (by rw[L.core.high_length hw.core];decide)))
 have mem:bit1 L.core.high∈wires (LowZero18Square.withLowK2 L ext c src dst (bBody L c)):=by
  simp only[LowZero18Square.withLowK2,wires_append,Finset.mem_union]
  tauto
 refine ⟨full.1,full.2.1,?_,full.2.2.2⟩
 intro q hq
 rcases Finset.mem_insert.mp (full.2.2.1 hq)with e|h
 · exact Finset.mem_insert.mpr (Or.inl e)
 rcases Finset.mem_insert.mp h with e|h
 · exact Finset.mem_insert_of_mem (e ▸ mem)
 · exact Finset.mem_insert_of_mem h

end ECDSAAdd.Entrant.ParkCarry8Develop

namespace ECDSAAdd.Entrant.ParkCarry8Develop
open Arithmetic

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
    (hn:L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen:300≤ext.length)
    (away:∀q∈ext,q∉L.wires) :
    wires (hostedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
  rw [hosted_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away) (ParkCarry8Develop.fold_fixes_source L hw hn ext hlen away)]
  exact body_support L hw hn c

end ECDSAAdd.Entrant.ParkCarry8Develop

end -- isolated Carry8 helper


section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry8BodySubset
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem old_copy (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 (L.core.product.take 256++L.core.work.take 256).toFinset ⊆ wires (ParkCarry7Develop.body L c) := by
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
 simp only [ParkCarry7Develop.body,wires_append,Finset.mem_union]
 tauto

theorem old_prepare (L : CuccaroStreamedSquareWideLayout) (c : Wire) :
 [(mU L).headD 0,bit1 (mU L),(mR L).headD 0,bit1 (mR L),(eReg L).headD 0,cacheWire L,hostWire L].toFinset
 ⊆wires (ParkCarry7Develop.body L c) := by
 have roles (u0 u1 r0 r1 e0 cache host : Wire) :
  [u0,u1,r0,r1,e0,cache,host].toFinset⊆wires (SecondCarryLoan.prepare u0 u1 r0 r1 e0 cache host) := by
  intro q h
  simp [SecondCarryLoan.prepare,SecondCarryLoan.loan,prime,prime2,majority,wires,Instr.wires,correctionWires] at h ⊢
  tauto
 intro q h
 have used:=roles ((mU L).headD 0) (bit1 (mU L)) ((mR L).headD 0) (bit1 (mR L))
  ((eReg L).headD 0) (cacheWire L) (hostWire L) h
 simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wMidFullCC,wires_append,Finset.mem_union]
 tauto

theorem old_control (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 c∈wires (ParkCarry7Develop.body L c) := by
 have len : eReg L≠[] := by
  have h:=eReg_length L hw
  intro e
  rw [e] at h
  contradiction
 obtain ⟨q,qs,hq⟩:=List.exists_cons_of_ne_nil len
 have hm : (2^129-1)%2=1 := by norm_num
 have used : c∈wires (eFlip L c) := by
  rw [eFlip,hq,List.take_succ_cons,maskedConstant,if_pos hm,wires_append]
  exact Finset.mem_union_left _ (by simp [wires,Instr.wires])
 simp only [ParkCarry7Develop.body,eFoldTq,wires_append,Finset.mem_union]
 tauto

theorem new_roles (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 bit2 (mU L)∈wires (ParkCarry7Develop.body L c) ∧
 bit2 (mR L)∈wires (ParkCarry7Develop.body L c) ∧
 host2Wire L∈wires (ParkCarry7Develop.body L c) := by
 have cp:=old_copy L hw c
 have u : bit2 (mU L)∈L.core.product.take 256 := by
  have hu:=bit2_mem (mU L) (by rw [mU_length L hw];decide)
  change bit2 (mU L)∈(hiReg L).drop 96 at hu
  have hh:=List.mem_of_mem_drop hu
  change bit2 (mU L)∈(L.core.product.take 256).drop 128 at hh
  exact List.mem_of_mem_drop hh
 have r : bit2 (mR L)∈L.core.work.take 256 := by
  have hr:=bit2_mem (mR L) (by rw [(mLens L hw).r];decide)
  exact win_take (l:=L.core.work) (a:=128) (b:=43) (n:=256) (by simpa only [mR] using hr) (by decide)
 have h : host2Wire L∈L.core.product.take 256 := by
  unfold host2Wire eReg
  rw [bit2_append _ _ (by simp [hw.core.product])]
  have mem:=bit2_mem (L.core.product.take 128) (by simp [hw.core.product])
  have eq : (L.core.product.take 256).take 128=L.core.product.take 128 := by simp [List.take_take]
  have mem' : bit2 (L.core.product.take 128)∈(L.core.product.take 256).take 128 := by
   rw [eq]
   exact mem
  exact List.mem_of_mem_take mem'
 exact ⟨cp (by simp [u]),cp (by simp [r]),cp (by simp [h])⟩

#print axioms old_copy
#print axioms old_prepare
#print axioms old_control
#print axioms new_roles
end ECDSAAdd.Entrant.Carry8BodySubset

end -- isolated Carry8 helper


section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry8BodyRefined
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop Carry8BodySubset
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem bodyV_refined (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c v : Wire) :
 wires (ParkCarry8Develop.bodyV L c v)⊆insert v (wires (ParkCarry7Develop.body L c)) := by
 have same {P : Program} (hp : wires P⊆wires (ParkCarry7Develop.body L c)) :
  wires P⊆insert v (wires (ParkCarry7Develop.body L c)) := fun _ h=>Finset.mem_insert_of_mem (hp h)
 have roles:=old_prepare L c
 have extras:=new_roles L hw c
 have carrier : [c,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset
  ⊆insert v (wires (ParkCarry7Develop.body L c)) := by
  intro q h
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e|e|e|e|e|e|e|e|e|e
  all_goals subst q
  · exact Finset.mem_insert_of_mem (old_control L hw c)
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.2.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.2.2
 have ends:=ends3_support c v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L)
 have endEmbed {P : Program} (hp : wires P⊆[c,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset) :
  wires P⊆insert v (wires (ParkCarry7Develop.body L c)) := hp.trans carrier
 have arms :
  wires (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L))⊆insert v (wires (ParkCarry7Develop.body L c)) ∧
  wires (wInvCCC L (cacheWire L) (hostWire L) (host2Wire L))⊆insert v (wires (ParkCarry7Develop.body L c)) := by
  have f:=(fwdCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support
  have i:=(invCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support
  constructor
  · intro q h
    rcases Finset.mem_insert.mp (f h) with e|h
    · subst q;exact Finset.mem_insert_of_mem extras.2.2
    · apply same (P:=wFwdCC L (cacheWire L) (hostWire L)) _ h
      intro q h
      simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wMidFullCC,wires_append,Finset.mem_union]
      tauto
  · intro q h
    rcases Finset.mem_insert.mp (i h) with e|h
    · subst q;exact Finset.mem_insert_of_mem extras.2.2
    · apply same (P:=wInvCC L (cacheWire L) (hostWire L)) _ h
      intro q h
      simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wMidFullCC,wires_append,Finset.mem_union]
      tauto
 have mid : wires (ParkCarry8Develop.midV L c v)⊆insert v (wires (ParkCarry7Develop.body L c)) := by
  intro q h
  simp only [ParkCarry8Develop.midV,wires_append,Finset.mem_union,or_assoc] at h
  rcases h with h|h|h|h|h
  · exact endEmbed ends.1 h
  · exact arms.1 h
  · exact same (P:=wCoreK L) (by
      intro q h
      simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wMidFullCC,wires_append,Finset.mem_union]
      tauto) h
  · exact arms.2 h
  · exact endEmbed ends.2 h
 have pad : wires (padM L 746)⊆wires (padM L 748) := by
  have hp : padM L 748=padM L 746++padM L 2 := by
   change List.replicate (746+2) (Instr.measureX (eKw L) [] [])=
    List.replicate 746 (Instr.measureX (eKw L) [] [])++List.replicate 2 (Instr.measureX (eKw L) [] [])
   rw [List.replicate_add]
  rw [hp,wires_append]
  exact Finset.subset_union_left
 intro q h
 simp only [ParkCarry8Develop.bodyV,ParkCarry8Develop.foldV,ParkCarry8Develop.rebuild,
  wires_append,Finset.mem_union,or_assoc] at h
 rcases h with h|h|h|h|h|h|h|h|h|h|h|h
 · exact same (P:=measuredFoldQTq L (negP L)) (by intro q h;simp only [ParkCarry7Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=measuredFoldQTq L (rot128F L)) (by intro q h;simp only [ParkCarry7Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddLo L) (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact mid h
 · exact same (P:=unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.program (eU L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eSubK L) (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eFoldTq L c) (by intro q h;simp only [ParkCarry7Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddB L) (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.restore L) (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=padM L 748) (by intro q h;simp only [ParkCarry7Develop.body,ParkCarry7Develop.rebuild,wires_append,Finset.mem_union];tauto) (pad h)

#print axioms bodyV_refined
end ECDSAAdd.Entrant.Carry8BodyRefined

end -- isolated Carry8 helper

end -- Carry8 body support adapters

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry9Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem source2_in_y (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : bit2 L.core.high ∈ L.core.y :=
 List.mem_of_mem_drop (List.mem_of_mem_take (bit2_mem _ (by simp [CuccaroStreamedSquareLayout.high,hw.core.y])))

theorem body_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (c : Wire) :
 wires (body L c) ⊆ (c::L.wires).toFinset := by
 have h := Carry9BodyRefined.body_refined L hw c
 intro q hq
 rcases Finset.mem_insert.mp (h hq) with e|h
 · rw [e]
   have vy := source2_in_y L hw
   simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,vy]
 · exact ParkCarry8Develop.body_support L hw hn c h

theorem fold_fixes_source (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ext : List Wire) (hlen : 300 ≤ ext.length) (away : ∀ q ∈ ext, q ∉ L.wires) :
 LowZero18Square.foldPerm L ext (bit2 L.core.high) = bit2 L.core.high := by
 have vy := source2_in_y L hw
 have ht : SquareCarryLoan719.target L ∈ L.foldPad := by
  apply List.mem_of_mem_drop
  exact DiagSq.getD_in (LowZero18LowK.ktmp L) 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
 have ne1 : bit2 L.core.high ≠ SquareCarryLoan719.target L := by
  intro e
  have a := List.count_pos_iff.mpr vy
  have b := List.count_pos_iff.mpr ht
  rw [←e] at b
  have h := layoutCount L hn (bit2 L.core.high)
  omega
 have ne2 : bit2 L.core.high ≠ ext.getD 0 0 := by
  intro e
  apply away (ext.getD 0 0) (DiagSq.getD_in ext 0 (by omega))
  rw [←e]
  simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,vy]
 change SquareCarryLoan719.foldPerm L ext (bit2 L.core.high) = _
 rw [SquareCarryLoan719.foldPerm_eq L hw]
 exact Equiv.swap_apply_of_ne_of_ne ne1 ne2

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ext : List Wire) (c : Wire) (hlen : 300 ≤ ext.length) (away : ∀ q ∈ ext, q ∉ L.wires) :
 wires (hostedBody L (LowZero18Square.foldPerm L ext) c) ⊆ (c::L.wires).toFinset := by
 rw [hosted_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact body_support L hw hn c
#print axioms body_support
#print axioms fold_fixes_source
#print axioms hosted_fold_support
end ECDSAAdd.Entrant.ParkCarry9Develop

end -- Carry9 body support adapters

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry10Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem source0_in_y (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : L.core.high.headD 0 ∈ L.core.y :=
 List.mem_of_mem_drop (List.mem_of_mem_take (head_mem _ (by simp [CuccaroStreamedSquareLayout.high,hw.core.y])))

theorem body_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (c : Wire) :
 wires (body L c) ⊆ (c::L.wires).toFinset := by
 have h := Carry10BodyRefined.body_refined L hw c
 intro q hq
 rcases Finset.mem_insert.mp (h hq) with e|h
 · rw [e]
   have vy := source0_in_y L hw
   simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil]
   tauto
 · exact ParkCarry8Develop.body_support L hw hn c h

theorem fold_fixes_source (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ext : List Wire) (hlen : 300 ≤ ext.length) (away : ∀ q ∈ ext, q ∉ L.wires) :
 LowZero18Square.foldPerm L ext (L.core.high.headD 0) = L.core.high.headD 0 := by
 have vy := source0_in_y L hw
 have ht : SquareCarryLoan719.target L ∈ L.foldPad := by
  apply List.mem_of_mem_drop
  exact DiagSq.getD_in (LowZero18LowK.ktmp L) 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
 have ne1 : L.core.high.headD 0 ≠ SquareCarryLoan719.target L := by
  intro e
  have a := List.count_pos_iff.mpr vy
  have b := List.count_pos_iff.mpr ht
  rw [←e] at b
  have h := layoutCount L hn (L.core.high.headD 0)
  omega
 have ne2 : L.core.high.headD 0 ≠ ext.getD 0 0 := by
  intro e
  apply away (ext.getD 0 0) (DiagSq.getD_in ext 0 (by omega))
  rw [←e]
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
   List.mem_toFinset,List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil]
  tauto
 change SquareCarryLoan719.foldPerm L ext (L.core.high.headD 0) = _
 rw [SquareCarryLoan719.foldPerm_eq L hw]
 exact Equiv.swap_apply_of_ne_of_ne ne1 ne2

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (ext : List Wire) (c : Wire) (hlen : 300 ≤ ext.length) (away : ∀ q ∈ ext, q ∉ L.wires) :
 wires (hostedBody L (LowZero18Square.foldPerm L ext) c) ⊆ (c::L.wires).toFinset := by
 rw [hosted_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact body_support L hw hn c
#print axioms body_support
#print axioms fold_fixes_source
#print axioms hosted_fold_support
end ECDSAAdd.Entrant.ParkCarry10Develop

end -- Carry10 body support adapters
