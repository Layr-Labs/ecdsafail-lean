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

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.ParkCopyMoreDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem double_cross_bound (v h:Nat)(hv:v<2^(2*h)):
 2*(v%2^h)*(v/2^h)<2^(2*h+1):=by
 have eq:(2:Nat)^(2*h)=2^h*2^h:=by rw[show 2*h=h+h by omega,pow_add]
 have lo:v%2^h<2^h:=Nat.mod_lt _ (by positivity)
 have hi:v/2^h<2^h:=by
  rw[Nat.div_lt_iff_lt_mul (by positivity)]
  simpa only[eq]using hv
 have mul:=Nat.mul_lt_mul'' lo hi
 calc
  2*(v%2^h)*(v/2^h)=2*((v%2^h)*(v/2^h)):=by ring
  _ < 2*(2^h*2^h):=Nat.mul_lt_mul_of_pos_left mul (by decide)
  _ = 2^(2*h+1):=by rw[pow_succ,eq];ring

theorem top_bits_zero (r:List Wire)(st:BasisState)(k:Nat)(h:regValue r st<2^k)
 (q:Wire)(hq:q∈r.drop k):st q=false:=by
 by_cases hk:k≤r.length
 · have e:=regValue_append (r.take k) (r.drop k) st
   rw[List.take_append_drop,List.length_take,Nat.min_eq_left hk]at e
   have z:regValue (r.drop k) st=0:=by
    by_contra nz
    have :2^k≤2^k*regValue (r.drop k) st:=Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero nz)
    omega
   exact (regValue_zero _ _).mp z q hq
 · rw[List.drop_eq_nil_of_le (by omega)]at hq
   simp at hq

theorem inner_top_hosts_zero (L:CuccaroStreamedSquareWideLayout)(hw:L.Widths)
 (ext src dst:List Wire)(he:300≤ext.length)(hs:src.length=128)(base st:BasisState)
 (i1:(LowZero18LowK.kg L ext src dst).I1 (regValue (LowZero18LowK.oregs L ext src dst).lo base) st)
 (i2:(LowZero18LowK.kg L ext src dst).I2 (regValue (LowZero18LowK.oregs L ext src dst).hi base) st):
 st (ext.getD 197 0)=false ∧ st (ext.getD 297 0)=false:=by
 have sizes:=L.measured_bank_widths hw
 have lol:(LowZero18LowK.oregs L ext src dst).lo.length=64:=by
  simp[LowZero18LowK.oregs,KRegs.lo,sizes.1,hs]
 have hil:(LowZero18LowK.oregs L ext src dst).hi.length=64:=by
  simp[LowZero18LowK.oregs,KRegs.hi,sizes.1,hs]
 have lo:=regValue_lt (LowZero18LowK.oregs L ext src dst).lo base
 have hi:=regValue_lt (LowZero18LowK.oregs L ext src dst).hi base
 rw[lol]at lo;rw[hil]at hi
 have b1:=double_cross_bound _ 32 lo
 have b2:=double_cross_bound _ 32 hi
 have t1:regValue (LowZero18LowK.iregs L ext src dst).T st=
  2*(regValue (LowZero18LowK.oregs L ext src dst).lo base%2^32)*
    (regValue (LowZero18LowK.oregs L ext src dst).lo base/2^32):=by
  have h:(LowZero18LowK.iregs L ext src dst).invC (regValue (LowZero18LowK.oregs L ext src dst).lo base) st:=by
   simpa only[LowZero18LowK.kg,hs,if_pos rfl,LowZero18LowK.kgH]using i1
  exact h.2
 have t2:regValue (LowZero18LowK.jregsH L ext src dst).T st=
  2*(regValue (LowZero18LowK.oregs L ext src dst).hi base%2^32)*
    (regValue (LowZero18LowK.oregs L ext src dst).hi base/2^32):=by
  have h:(LowZero18LowK.jregsH L ext src dst).invF (regValue (LowZero18LowK.oregs L ext src dst).hi base) st:=by
   simpa only[LowZero18LowK.kg,hs,if_pos rfl,LowZero18LowK.kgH]using i2
  exact h.2
 rw[←t1]at b1;rw[←t2]at b2
 constructor
 · apply top_bits_zero _ st 65 b1
   simp only[LowZero18LowK.iregs]
   rw[List.getD_eq_getElem _ _ (by omega)]
   have e:ext[197]'(by omega)=(((ext.drop 132).take 66).drop 65)[0]'(by simp;omega):=by simp
   rw[e];exact List.getElem_mem _
 · apply top_bits_zero _ st 65 b2
   simp only[LowZero18LowK.jregsH]
   rw[List.getD_eq_getElem _ _ (by omega)]
   have e:ext[297]'(by omega)=(((ext.drop 232).take 66).drop 65)[0]'(by simp;omega):=by simp
   rw[e];exact List.getElem_mem _

end ECDSAAdd.Entrant.ParkCopyMoreDevelop


set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option maxHeartbeats 2000000
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy
private theorem bit_mod0 (x : Nat) : (x%4).testBit 0=x.testBit 0 := by
 simp
private theorem bit_mod1 (x : Nat) : (x%4).testBit 1=x.testBit 1 := by
 simpa using Nat.testBit_mod_two_pow x 2 1

theorem lower_two_identities (a b : Nat) :
 (a+b).testBit 0=(a.testBit 0 ^^ b.testBit 0) ∧
 ((a+b).testBit 1 ^^ (2*a*b).testBit 1)=(a.testBit 1 ^^ b.testBit 1) := by
 rw [← bit_mod0 (a+b),← bit_mod0 a,← bit_mod0 b,
     ← bit_mod1 (a+b),← bit_mod1 (2*a*b),← bit_mod1 a,← bit_mod1 b]
 rw [Nat.add_mod a b 4,Nat.mul_mod (2*a) b 4,Nat.mul_mod 2 a 4]
 have ha : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
 have hb : b%4=0 ∨ b%4=1 ∨ b%4=2 ∨ b%4=3 := by omega
 rcases ha with ha|ha|ha|ha <;> rcases hb with hb|hb|hb|hb <;> simp [ha,hb,Nat.testBit_eq_decide_div_mod_eq]
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem register_testBit (r : List Wire)(i : Nat)(st : BasisState)(hi : i<r.length) :
 st (r.getD i 0)=(regValue r st).testBit i := by
 rw [RawClearCarryProbe.register_bit r i st hi,Nat.testBit_eq_decide_div_mod_eq]
 rfl

theorem invF_bits (R : KRegs)(hh : R.h=32)(hs : 1<R.S.length)(ht : 1<R.T.length)
 (v : Nat)(st : BasisState)(inv : R.invF v st) :
 st (R.S.getD 0 0)=(v.testBit 0 ^^ v.testBit 32) ∧
 (st (R.S.getD 1 0) ^^ st (R.T.getD 1 0))=(v.testBit 1 ^^ v.testBit 33) := by
 have k:=lower_two_identities (v%2^32) (v/2^32)
 have ss:=inv.1;have tt:=inv.2
 change regValue R.S st=v%2^R.h+v/2^R.h at ss
 change regValue R.T st=2*(v%2^R.h)*(v/2^R.h) at tt
 rw [hh]at ss tt
 rw [register_testBit R.S 0 st (by omega),register_testBit R.S 1 st hs,register_testBit R.T 1 st ht,ss,tt]
 simpa only [Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,Nat.reduceLT,decide_true,Bool.true_and,Nat.reduceAdd]using k
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem upper_inner_ext_bits (L : CuccaroStreamedSquareWideLayout)(ext src dst : List Wire)
 (he : 300≤ext.length)(v : Nat)(st : BasisState)
 (inv : (LowZero18LowK.jregsH L ext src dst).invF v st) :
 st (ext.getD 198 0)=(v.testBit 0 ^^ v.testBit 32) ∧
 (st (ext.getD 199 0) ^^ st (ext.getD 233 0))=(v.testBit 1 ^^ v.testBit 33) := by
 let R:=LowZero18LowK.jregsH L ext src dst
 have sl : R.S.length=33 := by
  simp only [R,LowZero18LowK.jregsH,List.length_take,List.length_drop];omega
 have tl : R.T.length=66 := by
  simp only [R,LowZero18LowK.jregsH,List.length_take,List.length_drop];omega
 have k:=invF_bits R rfl (by omega) (by omega) v st inv
 have s0 : R.S.getD 0 0=ext.getD 198 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [sl];omega),List.getD_eq_getElem _ _ (by omega)]
  simp [R,LowZero18LowK.jregsH]
 have s1 : R.S.getD 1 0=ext.getD 199 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [sl];omega),List.getD_eq_getElem _ _ (by omega)]
  simp [R,LowZero18LowK.jregsH]
 have t1 : R.T.getD 1 0=ext.getD 233 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [tl];omega),List.getD_eq_getElem _ _ (by omega)]
  simp [R,LowZero18LowK.jregsH]
 simpa only [s0,s1,t1]using k
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem upper_inner_bank_relations (L : CuccaroStreamedSquareWideLayout)(hw : L.Widths)
 (ext src dst : List Wire)(he : 300≤ext.length)(hs : src.length=128)(base st : BasisState)
 (i2 : (LowZero18LowK.kg L ext src dst).I2
  (regValue (LowZero18LowK.oregs L ext src dst).hi base) st) :
 st (ext.getD 198 0)=(base (L.inputBank.getD 64 0) ^^ base (L.inputBank.getD 96 0)) ∧
 (st (ext.getD 199 0) ^^ st (ext.getD 233 0))=
  (base (L.inputBank.getD 65 0) ^^ base (L.inputBank.getD 97 0)) := by
 let R:=LowZero18LowK.jregsH L ext src dst
 let v:=regValue (LowZero18LowK.oregs L ext src dst).hi base
 have inv : R.invF v st := by
  simpa only [LowZero18LowK.kg,hs,if_pos rfl,LowZero18LowK.kgH,R,v]using i2
 have k:=upper_inner_ext_bits L ext src dst he v st inv
 have sizes:=L.measured_bank_widths hw
 have bl : R.bank.length=64 := by
  simp only [R,LowZero18LowK.jregsH,LowZero18LowK.oregs,KRegs.hi,List.length_drop,List.length_take,hs]
  omega
 have idx (i : Nat)(hi : i<64) : R.bank.getD i 0=L.inputBank.getD (64+i) 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [bl];omega),List.getD_eq_getElem _ _ (by omega)]
  simp [R,LowZero18LowK.jregsH,LowZero18LowK.oregs,KRegs.hi,hs]
 have val : regValue R.bank base=v := rfl
 have bit (i : Nat)(hi : i<64) : base (L.inputBank.getD (64+i) 0)=v.testBit i := by
  rw [←idx i hi,register_testBit R.bank i base (by rw [bl];omega),val]
 rw [←bit 0 (by omega),←bit 1 (by omega),←bit 32 (by omega),←bit 33 (by omega)]at k
 exact k
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem two_cnot_eq_ccx (x y c a t : Wire)(s : State)(m : List Bool)
 (hy : y≠t)(h : (s.basis x ^^ s.basis y)=(s.basis c && s.basis a)) :
 run [.CX x t,.CX y t] m s=run [.CCX c a t] m s := by
 simp only [run]
 apply congrArg (fun b : BasisState =>(⟨s.phase,b⟩ : State))
 funext q
 by_cases hq : q=t
 · subst q
   simpa [writeBit,hy,Bool.xor_assoc]using
    congrArg (fun b=>s.basis t ^^ b) h
 · simp [writeBit,hq]

theorem three_cnot_eq_ccx (x y z c a t : Wire)(s : State)(m : List Bool)
 (hy : y≠t)(hz : z≠t)
 (h : ((s.basis x ^^ s.basis y) ^^ s.basis z)=(s.basis c && s.basis a)) :
 run [.CX x t,.CX y t,.CX z t] m s=run [.CCX c a t] m s := by
 simp only [run]
 apply congrArg (fun b : BasisState =>(⟨s.phase,b⟩ : State))
 funext q
 by_cases hq : q=t
 · subst q
   simpa [writeBit,hy,hz,Bool.xor_assoc]using congrArg (fun b=>s.basis t ^^ b) h
 · simp [writeBit,hq]
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem copyRegister_append (c : Option Wire)(xs ys as bs : List Wire)(h : xs.length=ys.length) :
 copyRegister c (xs++as) (ys++bs)=copyRegister c xs ys++copyRegister c as bs := by
 induction xs generalizing ys with
 | nil => have ey : ys=[] := List.eq_nil_of_length_eq_zero h.symm;subst ys;rfl
 | cons x xs ih =>
  cases ys with
  | nil => simp at h
  | cons y ys =>
   simp only [List.length_cons,Nat.add_right_cancel_iff]at h
   simp [copyRegister,ih ys h]

theorem copyRegister_bit (c : Wire)(src dst : List Wire)(len : src.length=dst.length)
 (nd : (src++dst).Nodup)(cd : c∉dst)(s : State)(m : List Bool)(i : Nat)(hi : i<dst.length) :
 (run (copyRegister (some c) src dst) m s).basis (dst.getD i 0)=
  (s.basis (dst.getD i 0) ^^ (s.basis c && s.basis (src.getD i 0))) := by
 have z:=copyRegister_correct (some c) src dst len nd (by simpa) s m
 rw [register_testBit dst i (run (copyRegister (some c) src dst) m s).basis hi,
  z.2.2,Nat.testBit_xor,←register_testBit dst i s.basis hi]
 have bit:=register_testBit src i s.basis (by omega)
 cases h : s.basis c <;> simp [copyValue,h,←bit]

end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem cached_append (c cache : Wire)(xs ys as bs : List Wire)
 (hlen : xs.length=ys.length)(hne : 0<xs.length) :
 CachedSquareCopy.copy c cache (xs++as) (ys++bs)=
  CachedSquareCopy.copy c cache xs ys++copyRegister (some c) as bs := by
 cases xs with
 | nil => simp at hne
 | cons x xs =>
  cases ys with
  | nil => simp at hlen
  | cons y ys =>
   have h : xs.length=ys.length := by simpa using hlen
   simp [CachedSquareCopy.copy,copyRegister_append (some c) xs ys as bs h]

theorem cached_take_split (c cache : Wire)(src dst : List Wire)(n : Nat)
 (len : src.length=dst.length)(hn : 0<n)(bound : n≤src.length) :
 CachedSquareCopy.copy c cache src dst=
  CachedSquareCopy.copy c cache (src.take n) (dst.take n)++
   copyRegister (some c) (src.drop n) (dst.drop n) := by
 have z:=cached_append c cache (src.take n) (dst.take n) (src.drop n) (dst.drop n)
  (by simp only [List.length_take,len]) (by simp only [List.length_take];omega)
 simpa only [List.take_append_drop]using z
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

def middle (x y z p q u v : Wire) : Program :=
 [.CX x u,.CX p u,.CX y v,.CX z v,.CX q v]

theorem zero_take (p : Program)(hz : measurementCount p=0)(m : List Bool)(s : State) :
 run p (m.take 0) s=run p m s := by
 simpa only [hz]using run_take p m s

theorem middle_run_eq (x y z p q c a b u v : Wire)(s : State)(m : List Bool)
 (pu : p≠u)(cu : c≠u)(bu : b≠u)(yu : y≠u)(zu : z≠u)(qu : q≠u)
 (zv : z≠v)(qv : q≠v)
 (h0 : (s.basis x ^^ s.basis p)=(s.basis c && s.basis a))
 (h1 : ((s.basis y ^^ s.basis z) ^^ s.basis q)=(s.basis c && s.basis b)) :
 run (middle x y z p q u v) m s=run [.CCX c a u,.CCX c b v] m s := by
 change run ([.CX x u,.CX p u]++[.CX y v,.CX z v,.CX q v]) m s=
  run ([.CCX c a u]++[.CCX c b v]) m s
 simp only [run_append,measurementCount,List.drop_zero]
 rw [zero_take [.CX x u,.CX p u] rfl m s,zero_take [.CCX c a u] rfl m s]
 rw [two_cnot_eq_ccx x p c a u s m pu h0]
 let t:=run [.CCX c a u] m s
 have f (w : Wire)(hw : w≠u) : t.basis w=s.basis w := by
  simp [t,run,writeBit,hw]
 apply three_cnot_eq_ccx y z q c b v t m zv qv
 rw [f y yu,f z zu,f q qu,f c cu,f b bu]
 exact h1
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

def copyPrefix (c cache : Wire)(src dst : List Wire) : Program :=
 CachedSquareCopy.copy c cache (src.take 96) (dst.take 96)

def copy (c cache x y z : Wire)(src dst : List Wire) : Program :=
 copyPrefix c cache src dst++
  middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0)++
  copyRegister (some c) (src.drop 98) (dst.drop 98)

theorem drop_two (xs : List Wire)(n : Nat)(h : n+1<xs.length) :
 xs.drop n=xs.getD n 0::xs.getD (n+1) 0::xs.drop (n+2) := by
 rw [List.getD_eq_getElem xs 0 (n:=n) (by omega),List.getD_eq_getElem xs 0 (n:=n+1) h,
  List.drop_eq_getElem_cons (i:=n) (l:=xs) (by omega),
  List.drop_eq_getElem_cons (i:=n+1) (l:=xs) h]

theorem prefix_measurements (c cache : Wire)(src dst : List Wire)(len : src.length=dst.length) :
 measurementCount (copyPrefix c cache src dst)=0 := by
 rw [copyPrefix,CachedSquareCopy.measurements]
 exact (copyRegister_counts (some c) (src.take 96) (dst.take 96)
  (by simp only [List.length_take,len])).2

theorem copy_run_eq (c cache x y z : Wire)(src dst : List Wire)
 (len : src.length=dst.length)(bound : 98≤src.length)(s : State)(m : List Bool)
 (pu : dst.getD 64 0≠dst.getD 96 0)(cu : c≠dst.getD 96 0)
 (bu : src.getD 97 0≠dst.getD 96 0)(yu : y≠dst.getD 96 0)(zu : z≠dst.getD 96 0)
 (qu : dst.getD 65 0≠dst.getD 96 0)(zv : z≠dst.getD 97 0)
 (qv : dst.getD 65 0≠dst.getD 97 0)
 (h0 : let u:=run (copyPrefix c cache src dst) m s
  (u.basis x ^^ u.basis (dst.getD 64 0))=(u.basis c && u.basis (src.getD 96 0)))
 (h1 : let u:=run (copyPrefix c cache src dst) m s
  ((u.basis y ^^ u.basis z) ^^ u.basis (dst.getD 65 0))=
   (u.basis c && u.basis (src.getD 97 0))) :
 run (copy c cache x y z src dst) m s=run (CachedSquareCopy.copy c cache src dst) m s := by
 have tail : copyRegister (some c) (src.drop 96) (dst.drop 96)=
  [.CCX c (src.getD 96 0) (dst.getD 96 0),.CCX c (src.getD 97 0) (dst.getD 97 0)]++
   copyRegister (some c) (src.drop 98) (dst.drop 98) := by
  rw [drop_two src 96 (by omega),drop_two dst 96 (by omega)]
  rfl
 rw [cached_take_split c cache src dst 96 len (by omega) (by omega),tail]
 change run (copyPrefix c cache src dst++middle x y z (dst.getD 64 0) (dst.getD 65 0)
  (dst.getD 96 0) (dst.getD 97 0)++copyRegister (some c) (src.drop 98) (dst.drop 98)) m s=_
 have midZero : measurementCount (middle x y z (dst.getD 64 0) (dst.getD 65 0)
  (dst.getD 96 0) (dst.getD 97 0))=0 := rfl
 have oldMidZero : measurementCount [.CCX c (src.getD 96 0) (dst.getD 96 0),
  .CCX c (src.getD 97 0) (dst.getD 97 0)]=0 := rfl
 have append_zero (p q : Program)(hz : measurementCount p=0)(r : List Bool)(t : State) :
  run (p++q) r t=run q r (run p r t) := by
  rw [run_append,hz,List.drop_zero,zero_take p hz r t]
 rw [List.append_assoc]
 rw [append_zero (copyPrefix c cache src dst) _ (prefix_measurements c cache src dst len)]
 conv_rhs => rw [append_zero (CachedSquareCopy.copy c cache (src.take 96) (dst.take 96)) _ (prefix_measurements c cache src dst len)]
 rw [append_zero _ _ midZero,append_zero _ _ oldMidZero]
 change run (copyRegister (some c) (src.drop 98) (dst.drop 98)) m
  (run [.CX x (dst.getD 96 0),.CX (dst.getD 64 0) (dst.getD 96 0),
   .CX y (dst.getD 97 0),.CX z (dst.getD 97 0),.CX (dst.getD 65 0) (dst.getD 97 0)] m
   (run (copyPrefix c cache src dst) m s))=_
 rw [show run [.CX x (dst.getD 96 0),.CX (dst.getD 64 0) (dst.getD 96 0),
  .CX y (dst.getD 97 0),.CX z (dst.getD 97 0),.CX (dst.getD 65 0) (dst.getD 97 0)] m
  (run (copyPrefix c cache src dst) m s)=run [.CCX c (src.getD 96 0) (dst.getD 96 0),
   .CCX c (src.getD 97 0) (dst.getD 97 0)] m (run (copyPrefix c cache src dst) m s) from
  middle_run_eq x y z (dst.getD 64 0) (dst.getD 65 0) c (src.getD 96 0) (src.getD 97 0)
   (dst.getD 96 0) (dst.getD 97 0) _ m pu cu bu yu zu qu zv qv h0 h1]
 rfl
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem conditions_after_prefix (c cache x y z : Wire)(src dst : List Wire)
 (ls : src.length=119)(ld : dst.length=119)(nd : (c::(src++dst)).Nodup)
 (xn : x∉dst)(yn : y∉dst)(zn : z∉dst)(s : State)(m : List Bool)
 (bank0 : ∀q∈dst,s.basis q=false)
 (cached : s.basis cache=(s.basis c && s.basis ((src.take 96).headD 0)))
 (hx : s.basis x=((s.basis c && s.basis (src.getD 64 0)) ^^
  (s.basis c && s.basis (src.getD 96 0))))
 (hyz : (s.basis y ^^ s.basis z)=((s.basis c && s.basis (src.getD 65 0)) ^^
  (s.basis c && s.basis (src.getD 97 0)))) :
 let u:=run (copyPrefix c cache src dst) m s
 ((u.basis x ^^ u.basis (dst.getD 64 0))=(u.basis c && u.basis (src.getD 96 0))) ∧
 (((u.basis y ^^ u.basis z) ^^ u.basis (dst.getD 65 0))=
  (u.basis c && u.basis (src.getD 97 0))) := by
 have lens : (src.take 96).length=(dst.take 96).length := by simp [ls,ld]
 have nd0 : (src++dst).Nodup := (List.nodup_cons.mp nd).2
 have ndp : (src.take 96++dst.take 96).Nodup :=
  nd0.sublist (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _))
 have cn : c∉dst := fun h=>(List.nodup_cons.mp nd).1 (List.mem_append_right _ h)
 have sn (q : Wire)(hq : q∈src) : q∉dst :=
  fun hd=>List.disjoint_left.mp (List.nodup_append'.mp nd0).2.2 hq hd
 have getTake (r : List Wire)(hr : r.length=119)(i : Nat)(hi : i<96) :
  (r.take 96).getD i 0=r.getD i 0 := by
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_take,hr];omega),
   List.getD_eq_getElem _ _ (by omega)]
  simp
 let v:=run (copyRegister (some c) (src.take 96) (dst.take 96)) m s
 have eq : run (copyPrefix c cache src dst) m s=v :=
  CachedSquareCopy.run_eq c cache (src.take 96) (dst.take 96) s m cached
 have raw:=copyRegister_correct (some c) (src.take 96) (dst.take 96) lens ndp
  (by
    intro q h
    have qc : c=q := by simpa using h
    rw [←qc]
    exact fun hd=>cn (List.mem_of_mem_take hd)) s m
 have frame (q : Wire)(hn : q∉dst) : v.basis q=s.basis q :=
  raw.2.1 q (fun hd=>hn (List.mem_of_mem_take hd))
 have bit (i : Nat)(hi : i<96) : v.basis (dst.getD i 0)=
  (s.basis c && s.basis (src.getD i 0)) := by
  have h:=copyRegister_bit c (src.take 96) (dst.take 96) lens ndp
   (fun hd=>cn (List.mem_of_mem_take hd)) s m i (by simp only [List.length_take,ld];omega)
  rw [getTake dst ld i hi,getTake src ls i hi,
   bank0 (dst.getD i 0) (DiagSq.getD_in dst i (by omega))]at h
  simpa only [Bool.false_xor]using h
 have c96 : src.getD 96 0∉dst := sn _ (DiagSq.getD_in src 96 (by omega))
 have c97 : src.getD 97 0∉dst := sn _ (DiagSq.getD_in src 97 (by omega))
 have cancel (a b : Bool) : ((a^^b)^^a)=b := by cases a <;> cases b <;> rfl
 dsimp only
 rw [eq]
 constructor
 · rw [frame x xn,bit 64 (by omega),frame c cn,frame (src.getD 96 0) c96,hx]
   exact cancel _ _
 · rw [frame y yn,frame z zn,bit 65 (by omega),frame c cn,frame (src.getD 97 0) c97,hyz]
   exact cancel _ _
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem copy_correct (c cache x y z : Wire)(src dst : List Wire)
 (ls : src.length=119)(ld : dst.length=119)(nd : (c::(src++dst)).Nodup)
 (xn : x∉dst)(yn : y∉dst)(zn : z∉dst)(s : State)(m : List Bool)
 (bank0 : ∀q∈dst,s.basis q=false)
 (cached : s.basis cache=(s.basis c && s.basis ((src.take 96).headD 0)))
 (hx : s.basis x=((s.basis c && s.basis (src.getD 64 0)) ^^
  (s.basis c && s.basis (src.getD 96 0))))
 (hyz : (s.basis y ^^ s.basis z)=((s.basis c && s.basis (src.getD 65 0)) ^^
  (s.basis c && s.basis (src.getD 97 0)))) :
 run (copy c cache x y z src dst) m s=run (CachedSquareCopy.copy c cache src dst) m s := by
 have nd0 : (src++dst).Nodup := (List.nodup_cons.mp nd).2
 have dn : dst.Nodup := (List.nodup_append'.mp nd0).2.1
 have dm (i : Nat)(hi : i<119) : dst.getD i 0∈dst := DiagSq.getD_in dst i (by omega)
 have dd (i j : Nat)(hi : i<119)(hj : j<119)(ne : i≠j) : dst.getD i 0≠dst.getD j 0 := by
  intro e
  rw [List.getD_eq_getElem dst 0 (n:=i) (by omega),List.getD_eq_getElem dst 0 (n:=j) (by omega)]at e
  exact ne ((List.Nodup.getElem_inj_iff dn).mp e)
 have cn : c∉dst := fun h=>(List.nodup_cons.mp nd).1 (List.mem_append_right _ h)
 have sn : src.getD 97 0∉dst := fun h=>List.disjoint_left.mp
  (List.nodup_append'.mp nd0).2.2 (DiagSq.getD_in src 97 (by omega)) h
 have neq (q : Wire)(hn : q∉dst)(i : Nat)(hi : i<119) : q≠dst.getD i 0 := by
  intro e;apply hn;rw [e];exact dm i hi
 have cond:=conditions_after_prefix c cache x y z src dst ls ld nd xn yn zn s m bank0 cached hx hyz
 exact copy_run_eq c cache x y z src dst (by omega) (by omega) s m
  (dd 64 96 (by omega) (by omega) (by omega)) (neq c cn 96 (by omega))
  (neq _ sn 96 (by omega)) (neq y yn 96 (by omega)) (neq z zn 96 (by omega))
  (dd 65 96 (by omega) (by omega) (by omega)) (neq z zn 97 (by omega))
  (dd 65 97 (by omega) (by omega) (by omega)) cond.1 cond.2
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem masked_upper_relations (L : CuccaroStreamedSquareWideLayout)(hw : L.Widths)
 (ext src dst : List Wire)(he : 300≤ext.length)(hs : src.length=128)
 (control : Wire)(orig base st : BasisState)
 (bank : regValue (L.inputBank.take src.length) base=
  if orig control then regValue src orig else 0)
 (i2 : (LowZero18LowK.kg L ext src dst).I2
  (regValue (LowZero18LowK.oregs L ext src dst).hi base) st) :
 st (ext.getD 198 0)=((orig control && orig (src.getD 64 0)) ^^ (orig control && orig (src.getD 96 0))) ∧
 (st (ext.getD 199 0) ^^ st (ext.getD 233 0))=
  ((orig control && orig (src.getD 65 0)) ^^ (orig control && orig (src.getD 97 0))) := by
 have k:=upper_inner_bank_relations L hw ext src dst he hs base st i2
 have sizes:=L.measured_bank_widths hw
 have bl : (L.inputBank.take src.length).length=128 := by
  simp only [List.length_take,hs];omega
 have bits (i : Nat)(hi : i<128) : base (L.inputBank.getD i 0)=(orig control && orig (src.getD i 0)) := by
  have eq : (L.inputBank.take src.length).getD i 0=L.inputBank.getD i 0 := by
   rw [List.getD_eq_getElem _ _ (by rw [bl];omega),List.getD_eq_getElem _ _ (by omega)]
   simp
  rw [←eq,register_testBit (L.inputBank.take src.length) i base (by rw [bl];omega),bank]
  cases h : orig control <;> simp [←register_testBit src i orig (by omega)]
 rw [bits 64 (by omega),bits 65 (by omega),bits 96 (by omega),bits 97 (by omega)]at k
 exact k
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem cached_slots_eq (c cache : Wire)(src dst : List Wire) :
 Challenge.gateSlots (CachedSquareCopy.copy c cache src dst)=Challenge.gateSlots (copyRegister (some c) src dst) := by
 cases src <;> cases dst
 all_goals simp [CachedSquareCopy.copy,copyRegister,copyGate,Challenge.gateSlots,Challenge.instructionSlots]

theorem copy_counts (c cache x y z : Wire)(src dst : List Wire)(ls : src.length=119)(ld : dst.length=119) :
 toffoliCount (copy c cache x y z src dst)+2=toffoliCount (CachedSquareCopy.copy c cache src dst) ∧
 measurementCount (copy c cache x y z src dst)=measurementCount (CachedSquareCopy.copy c cache src dst) := by
 have lp : (src.take 96).length=(dst.take 96).length := by simp [ls,ld]
 have lt : (src.drop 98).length=(dst.drop 98).length := by simp [ls,ld]
 have cp:=copyRegister_counts (some c) (src.take 96) (dst.take 96) lp
 have ct:=copyRegister_counts (some c) (src.drop 98) (dst.drop 98) lt
 have co:=copyRegister_counts (some c) src dst (by omega)
 have pc : toffoliCount (copyPrefix c cache src dst)+1=96 := by
  have h:=CachedSquareCopy.counts_nonempty c cache (src.take 96) (dst.take 96)
   (by simp [ls]) (by simp [ld])
  have e : toffoliCount (copyRegister (some c) (src.take 96) (dst.take 96))=96 := by simpa [ls,ld]using cp.1
  exact h.trans e
 have oc : toffoliCount (CachedSquareCopy.copy c cache src dst)+1=119 := by
  have h:=CachedSquareCopy.counts_nonempty c cache src dst (by omega) (by omega)
  have e : toffoliCount (copyRegister (some c) src dst)=119 := by simpa [ls]using co.1
  exact h.trans e
 have tc : toffoliCount (copyRegister (some c) (src.drop 98) (dst.drop 98))=21 := by simpa [ls,ld]using ct.1
 have mp:=prefix_measurements c cache src dst (by omega)
 have mo : measurementCount (CachedSquareCopy.copy c cache src dst)=0 := by
  rw [CachedSquareCopy.measurements];exact co.2
 constructor
 · simp only [copy,toffoliCount_append]
   have zm : toffoliCount (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0))=0 := rfl
   rw [zm]
   omega
 · simp only [copy,measurementCount_append]
   have zm : measurementCount (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0))=0 := rfl
   rw [mp,zm,ct.2,mo]

theorem copy_slots (c cache x y z : Wire)(src dst : List Wire)(ls : src.length=119)(ld : dst.length=119) :
 Challenge.gateSlots (copy c cache x y z src dst)=Challenge.gateSlots (CachedSquareCopy.copy c cache src dst)+3 := by
 have zm : Challenge.gateSlots (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0))=5 := rfl
 simp only [copy,Challenge.gateSlots_append,copyPrefix,cached_slots_eq,
  Baselines.copyRegister_gateSlots,zm,List.length_take,List.length_drop,ls,ld]
 rfl

end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem dst_mem_copyRegister (c : Option Wire) : ∀src dst : List Wire,src.length=dst.length →
 ∀q∈dst,q∈wires (copyRegister c src dst) := by
 intro src
 induction src with
 | nil => intro dst len q h;have e:dst=[]:=List.eq_nil_of_length_eq_zero len.symm;subst dst;simp at h
 | cons a src ih =>
  intro dst len q h
  cases dst with
  | nil=>simp at h
  | cons b dst=>
   simp only [List.mem_cons]at h
   rcases h with rfl|h
   · cases c <;> simp [copyRegister,copyGate,wires,Instr.wires]
   · simp only [copyRegister,wires_append]
     exact Finset.mem_union_right _ (ih dst (by simpa using len) q h)

theorem dst_mem_cached (c cache : Wire)(src dst : List Wire)(len : src.length=dst.length) :
 ∀q∈dst,q∈wires (CachedSquareCopy.copy c cache src dst) := by
 cases src with
 | nil=>have e:dst=[]:=List.eq_nil_of_length_eq_zero len.symm;subst dst;simp
 | cons a src=>
  cases dst with
  | nil=>simp
  | cons b dst=>
   intro q h
   simp only [List.mem_cons] at h
   rcases h with rfl|h
   · simp [CachedSquareCopy.copy,wires,Instr.wires]
   · simp only [CachedSquareCopy.copy,wires_append]
     exact Finset.mem_union_right _ (dst_mem_copyRegister (some c) src dst (by simpa using len) q h)

theorem copy_wires (c cache x y z : Wire)(src dst : List Wire)(ls : src.length=119)(ld : dst.length=119) :
 wires (copy c cache x y z src dst)⊆wires (CachedSquareCopy.copy c cache src dst)∪{x,y,z} := by
 have lens:src.length=dst.length:=by omega
 have pref : wires (copyPrefix c cache src dst)⊆wires (CachedSquareCopy.copy c cache src dst) := by
  intro q h
  rw [cached_take_split c cache src dst 96 lens (by omega) (by omega),wires_append]
  exact Finset.mem_union_left _ h
 have tail : wires (copyRegister (some c) (src.drop 98) (dst.drop 98))⊆wires (CachedSquareCopy.copy c cache src dst) := by
  intro q h
  rw [cached_take_split c cache src dst 98 lens (by omega) (by omega),wires_append]
  exact Finset.mem_union_right _ h
 have bank (i : Nat)(hi : i<119) : dst.getD i 0∈wires (CachedSquareCopy.copy c cache src dst) :=
  dst_mem_cached c cache src dst lens _ (DiagSq.getD_in dst i (by omega))
 have b64:=bank 64 (by omega);have b65:=bank 65 (by omega)
 have b96:=bank 96 (by omega);have b97:=bank 97 (by omega)
 intro q h
 simp only [copy,wires_append,Finset.mem_union]at h
 rcases h with (h|h)|h
 · exact Finset.mem_union_left _ (pref h)
 · simp only [middle,wires,Instr.wires,Finset.union_empty,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton]at h
   aesop
 · exact Finset.mem_union_left _ (tail h)
end ECDSAAdd.Entrant.InnerLinearCopy

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.InnerLinearCopy

theorem copy_physical (c cache x y z : Wire)(src dst : List Wire)
 (ls : src.length=119)(ld : dst.length=119)(dn : dst.Nodup)
 (xn : x∉dst)(yn : y∉dst)(zn : z∉dst)
 (old : GatePhysical (CachedSquareCopy.copy c cache src dst)) :
 GatePhysical (copy c cache x y z src dst) := by
 have lens:src.length=dst.length:=by omega
 have pref : GatePhysical (copyPrefix c cache src dst) := by
  rw [cached_take_split c cache src dst 96 lens (by omega) (by omega),gatePhysical_append]at old
  exact old.1
 have tail : GatePhysical (copyRegister (some c) (src.drop 98) (dst.drop 98)) := by
  rw [cached_take_split c cache src dst 98 lens (by omega) (by omega),gatePhysical_append]at old
  exact old.2
 have dd (i j : Nat)(hi : i<119)(hj : j<119)(ne : i≠j) : dst.getD i 0≠dst.getD j 0 := by
  intro e
  rw [List.getD_eq_getElem dst 0 (n:=i) (by omega),List.getD_eq_getElem dst 0 (n:=j) (by omega)]at e
  exact ne ((List.Nodup.getElem_inj_iff dn).mp e)
 have neq (q : Wire)(hn : q∉dst)(i : Nat)(hi : i<119) : q≠dst.getD i 0 := by
  intro e;apply hn;rw [e];exact DiagSq.getD_in dst i (by omega)
 have mid : GatePhysical (middle x y z (dst.getD 64 0) (dst.getD 65 0) (dst.getD 96 0) (dst.getD 97 0)) := by
  have a:=neq x xn 96 (by omega)
  have b:=dd 64 96 (by omega) (by omega) (by omega)
  have d:=neq y yn 97 (by omega)
  have e:=neq z zn 97 (by omega)
  have f:=dd 65 97 (by omega) (by omega) (by omega)
  simp [middle,GatePhysical,RecordedQuantum.PhysicalInstr,ECDSAAdd.ProperGate]
  exact ⟨a,b,d,e,f⟩
 simpa only [copy,gatePhysical_append] using And.intro (And.intro pref mid) tail
end ECDSAAdd.Entrant.InnerLinearCopy
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.ParkCopyBottomDevelop

theorem even_low_zero (r : List Wire)(st : BasisState)(k : Nat)(hn : 0<r.length)
 (h : regValue r st=2*k) : st (r.getD 0 0)=false := by
 rw [InnerLinearCopy.register_testBit r 0 st hn,h]
 simp [Nat.testBit_eq_decide_div_mod_eq]

theorem inner_bottom_hosts_zero (L:CuccaroStreamedSquareWideLayout)
 (ext src dst:List Wire)(he:300≤ext.length)(hs:src.length=128)(base st:BasisState)
 (i1:(LowZero18LowK.kg L ext src dst).I1 (regValue (LowZero18LowK.oregs L ext src dst).lo base) st)
 (i2:(LowZero18LowK.kg L ext src dst).I2 (regValue (LowZero18LowK.oregs L ext src dst).hi base) st):
 st (ext.getD 132 0)=false ∧ st (ext.getD 232 0)=false:=by
 have t1:regValue (LowZero18LowK.iregs L ext src dst).T st=
  2*(regValue (LowZero18LowK.oregs L ext src dst).lo base%2^32)*
    (regValue (LowZero18LowK.oregs L ext src dst).lo base/2^32):=by
  have h:(LowZero18LowK.iregs L ext src dst).invC (regValue (LowZero18LowK.oregs L ext src dst).lo base) st:=by
   simpa only[LowZero18LowK.kg,hs,if_pos rfl,LowZero18LowK.kgH]using i1
  exact h.2
 have t2:regValue (LowZero18LowK.jregsH L ext src dst).T st=
  2*(regValue (LowZero18LowK.oregs L ext src dst).hi base%2^32)*
    (regValue (LowZero18LowK.oregs L ext src dst).hi base/2^32):=by
  have h:(LowZero18LowK.jregsH L ext src dst).invF (regValue (LowZero18LowK.oregs L ext src dst).hi base) st:=by
   simpa only[LowZero18LowK.kg,hs,if_pos rfl,LowZero18LowK.kgH]using i2
  exact h.2
 have z1:=even_low_zero (LowZero18LowK.iregs L ext src dst).T st _
  (by simp only[LowZero18LowK.iregs,List.length_take,List.length_drop];omega)
  (by simpa only[Nat.mul_assoc]using t1)
 have z2:=even_low_zero (LowZero18LowK.jregsH L ext src dst).T st _
  (by simp only[LowZero18LowK.jregsH,List.length_take,List.length_drop];omega)
  (by simpa only[Nat.mul_assoc]using t2)
 have e1:(LowZero18LowK.iregs L ext src dst).T.getD 0 0=ext.getD 132 0:=by
  rw[List.getD_eq_getElem _ _ (by simp only[LowZero18LowK.iregs,List.length_take,List.length_drop];omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp[LowZero18LowK.iregs]
 have e2:(LowZero18LowK.jregsH L ext src dst).T.getD 0 0=ext.getD 232 0:=by
  rw[List.getD_eq_getElem _ _ (by simp only[LowZero18LowK.jregsH,List.length_take,List.length_drop];omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp[LowZero18LowK.jregsH]
 exact ⟨e1 ▸ z1,e2 ▸ z2⟩
end ECDSAAdd.Entrant.ParkCopyBottomDevelop

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Bank-bit parking for the 128-bit square leaves (part A: definitions and structural facts).

Four `ext` wires are outside every register of the 128-bit leaf KG (`kgH`): the outer `T`
uses `ext[0..130)`, the inner `T` uses `ext[132..198)`, the high inner `S` uses
`ext[198..231)` and the high inner `T` uses `ext[232..298)`. The wires
`ext[131]`, `ext[231]`, `ext[298]`, `ext[299]` (`ext[130]` is the retired-760 body host) are therefore zero during the whole branch.
They hold the last four bank bits through the body, so the second controlled copy needs
four Toffoli gates fewer. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

def hostIdx : List Nat := [129,131,132,197,231,232,297,298,299]

def hosts (ext : List Wire) : List Wire := hostIdx.map (fun i => ext.getD i 0)

/-- Measurements of zero wires without corrections: they keep the record alignment. -/
def dummies (hs : List Wire) : Program := hs.map (fun h => Instr.measureX h [] [])

/-- Move a register into a zero register (and back): two CX passes. -/
def move (a b : List Wire) : Program := copyRegister none a b ++ copyRegister none b a

theorem hosts_length (ext : List Wire) : (hosts ext).length=9 := rfl

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
theorem hosts_sub : ∀h∈hosts ext,h∈ext := by
  intro h hh
  simp only [hosts,hostIdx,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact getD_mem _ _ (by omega)

include hx he in
theorem hosts_nodup : (hosts ext).Nodup := by
  have inj (i j : Nat) (hi : i<ext.length) (hj : j<ext.length) (e : ext.getD i 0=ext.getD j 0) : i=j := by
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at e
    exact (List.Nodup.getElem_inj_iff hx).mp e
  simp only [hosts,hostIdx,List.map_cons,List.map_nil,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,List.nodup_nil,and_true,not_or]
  repeat' apply And.intro
  all_goals first | trivial | (intro e; have := inj _ _ (by omega) (by omega) e;omega)

/-- Each host index avoids all four `ext` slices used by the 128-bit leaf KG and `ext[0]`. -/
theorem idx_free (i : Nat) (hi : i∈hostIdx) :
    (i≠129 → ¬ i < 131) ∧ (i≠197 → i≠132 → ¬(132 ≤ i ∧ i<132+66)) ∧ ¬(198 ≤ i ∧ i<198+33) ∧ (i≠297 → i≠232 → ¬(232 ≤ i ∧ i<232+66)) ∧ i≠0 ∧ i<300 := by
  simp only [hostIdx,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> (repeat' intro) <;> omega

include hx he in
theorem host_not_T (h : Wire) (hh : h∈hosts ext) (e : h≠ext.getD 129 0) : h∉(ext.take 132).take 130 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  have f := idx_free i hi
  have i129 : i≠129 := fun h' => e (by rw [h'])
  rw [List.take_take,show min 130 132=130 by omega,getD_mem_take ext hx i 130 (by have := f.2.2.2.2.2; omega)]
  have := f.1 i129; omega

include hx he in
theorem host_not_iT (h : Wire) (hh : h∈hosts ext) (e:h≠ext.getD 197 0) (e0:h≠ext.getD 132 0) : h∉(ext.drop 132).take 66 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [getD_mem_slice ext hx i 132 66 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.1 (fun h' => e (by rw[h'])) (fun h' => e0 (by rw[h']))

include hx he in
theorem host_not_jS (h : Wire) (hh : h∈hosts ext) : h∉((ext.drop 198).take 34).take 33 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [List.take_take,show min 33 34=33 by omega,
    getD_mem_slice ext hx i 198 33 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.2.1

include hx he in
theorem host_not_jT (h : Wire) (hh : h∈hosts ext) (e:h≠ext.getD 297 0) (e0:h≠ext.getD 232 0) : h∉(ext.drop 232).take 66 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [getD_mem_slice ext hx i 232 66 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.2.2.1 (fun h' => e (by rw[h'])) (fun h' => e0 (by rw[h']))

include hx he in
theorem host_ne_zero (h : Wire) (hh : h∈hosts ext) : h≠ext.getD 0 0 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  intro e
  have f := idx_free i hi
  rw [List.getD_eq_getElem _ _ (by have := f.2.2.2.2.2; omega),List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  exact f.2.2.2.2.1 this

end Hosts

theorem park_top_bits_zero (r : List Wire) (st : BasisState) (k : Nat) (h : regValue r st<2^k)
    (q : Wire) (hq : q∈r.drop k) : st q=false := by
  by_cases hk : k≤r.length
  · have e := regValue_append (r.take k) (r.drop k) st
    rw [List.take_append_drop,List.length_take,Nat.min_eq_left hk] at e
    have z : regValue (r.drop k) st=0 := by
      by_contra nz
      have : 2^k≤2^k*regValue (r.drop k) st := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero nz)
      omega
    exact (regValue_zero _ _).mp z q hq
  · rw [List.drop_eq_nil_of_le (by omega)] at hq
    simp at hq

section KGH
variable (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)

/-- For the 128-bit leaf, an `ext` wire outside the three inner slices is not a KG `X` wire. -/
theorem host_not_X (hx : ext.Nodup) (he : 300≤ext.length) (h128 : src.length=128)
    (hE : ∀q∈(LowZero18LowK.ktmp L),q∉ext) (h : Wire) (hh : h∈hosts ext) (e1:h≠ext.getD 197 0) (e2:h≠ext.getD 297 0) (e3:h≠ext.getD 132 0) (e4:h≠ext.getD 232 0) :
    h∉(LowZero18LowK.kg L ext src dst).X := by
  intro hX
  rw [LowZero18LowK.kg,if_pos h128] at hX
  simp only [KG.X,LowZero18LowK.kgH] at hX
  have hext := hosts_sub ext he h hh
  rcases List.mem_append.mp hX with hX|hX
  · rcases List.mem_append.mp hX with hX|hX
    · rcases List.mem_append.mp hX with hX|hX
      · exact hE h (List.mem_of_mem_drop (List.mem_of_mem_take (hX : h∈((LowZero18LowK.ktmp L).drop 66).take 33))) hext
      · exact host_not_iT ext hx he h hh e1 e3 hX
    · rcases List.mem_append.mp hX with hX|hX
      · exact host_not_jS ext hx he h hh hX
      · exact host_not_jT ext hx he h hh e2 e4 hX
  · exact List.not_mem_nil hX

theorem host_not_oT (hx : ext.Nodup) (he : 300≤ext.length) (h128 : src.length=128)
    (h : Wire) (hh : h∈hosts ext) (e : h≠ext.getD 129 0) : h∉(LowZero18LowK.oregs L ext src dst).T := by
  simp only [LowZero18LowK.oregs,h128]
  exact host_not_T ext hx he h hh e

end KGH

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
def pC1 : Program := InnerLinearCopy.copy control (LowZero18Square.cacheWire L dst) (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0) (src.take 119) ((L.inputBank.take src.length).take 119)
def pMO : Program := move (hosts ext) ((L.inputBank.take src.length).drop 119)
def pCL : Program := LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)
def pE : Program := eraseMask control src (L.inputBank.take src.length)

/-- The 128-bit leaf with its last five bank bits parked on five free `ext` wires. -/
def withLowK2P : Program :=
  pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++
    pC1 L ext control src dst++pMO L ext src++pCL L ext src dst++pE L control src

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
  have hHT : ∀h∈hosts ext,h≠ext.getD 129 0 → h∉(LowZero18LowK.oregs L ext src dst).T := fun h hh e => host_not_oT L ext src dst hx he h128' h hh e
  have hHX : ∀h∈hosts ext,h≠ext.getD 197 0 → h≠ext.getD 297 0 → h≠ext.getD 132 0 → h≠ext.getD 232 0 → h∉(LowZero18LowK.kg L ext src dst).X := fun h hh e1 e2 e3 e4 => host_not_X L ext src dst hx he h128' tmpE h hh e1 e2 e3 e4
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
  obtain ⟨a9,r10,e10⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L ext control src dst++pMO L ext src++pCL L ext src dst) (pE L control src) records s
  obtain ⟨a8,r9,e9⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L ext control src dst++pMO L ext src) (pCL L ext src dst) a9 s
  obtain ⟨a7,r8,e8⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L ext control src dst) (pMO L ext src) a8 s
  obtain ⟨a6,r7,e7⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body) (pC1 L ext control src dst) a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src) (pB L ext body) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext) (pMI L ext src) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src) (pD ext) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (pA L control src++pM L ext src dst) (pE1 L control src) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (pA L control src) (pM L ext src dst) a2 s
  rw [show withLowK2P L ext control src dst body=pA L control src++pM L ext src dst++pE1 L control src++pD ext++
    pMI L ext src++pB L ext body++pC1 L ext control src dst++pMO L ext src++pCL L ext src dst++pE L control src from rfl,
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
  -- ext[129] is the top bit of the outer T = 2*lo*hi < 2^129
  have tTop : u1.basis (ext.getD 129 0)=false := by
    have tv := mk.2.2.2.1
    have lo_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).lo u0.basis
    have hi_lt := regValue_lt (LowZero18LowK.oregs L ext src dst).hi u0.basis
    have lol : (LowZero18LowK.oregs L ext src dst).lo.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.lo,sizes.1,h128']
    have hil : (LowZero18LowK.oregs L ext src dst).hi.length=64 := by
      simp [LowZero18LowK.oregs,KRegs.hi,sizes.1,h128']
    rw [lol] at lo_lt
    rw [hil] at hi_lt
    have prod : 2*regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis*
        regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis<2^129 := by
      have := Nat.mul_lt_mul'' lo_lt hi_lt
      have e : (2:Nat)^129=2*(2^64*2^64) := by norm_num
      rw [e,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left this (by norm_num)
    rw [← tv] at prod
    apply park_top_bits_zero _ _ 129 prod
    have tl : (LowZero18LowK.oregs L ext src dst).T=ext.take 130 := by
      simp [LowZero18LowK.oregs,h128',List.take_take]
    rw [tl,List.getD_eq_getElem _ _ (by omega)]
    have : ext[129]'(by omega)=((ext.take 130).drop 129)[0]'(by simp; omega) := by simp
    rw [this]; exact List.getElem_mem _
  have tInner:=ParkCopyMoreDevelop.inner_top_hosts_zero L hw ext src dst he h128' u0.basis u1.basis
    mk.2.2.2.2.1 mk.2.2.2.2.2.1
  have bInner:=ParkCopyBottomDevelop.inner_bottom_hosts_zero L ext src dst he h128' u0.basis u1.basis
    mk.2.2.2.2.1 mk.2.2.2.2.2.1
  have hU1 : ∀h∈hosts ext,u1.basis h=false := by
    intro h hh
    by_cases e : h=ext.getD 129 0
    · rw [e]; exact tTop
    by_cases e1:h=ext.getD 197 0
    · rw[e1];exact tInner.1
    by_cases e2:h=ext.getD 297 0
    · rw[e2];exact tInner.2
    by_cases e3:h=ext.getD 132 0
    · rw[e3];exact bInner.1
    by_cases e4:h=ext.getD 232 0
    · rw[e4];exact bInner.2
    exact (u1s h (hHD h hh) (hHT h hh e) (hHX h hh e1 e2 e3 e4)).trans
      ((u0s h (hHB h hh)).trans (ext0 h (hHx h hh)))
  have srcw1 : ∀q∈src,u1.basis q=s.basis q := fun q hq =>
    (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq))
  have mask1 : regValue ((L.inputBank.take src.length).take 119) u1.basis=
      if u1.basis control then regValue (src.take 119) u1.basis else 0 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ 119 (by rw [inputLen]; omega) u1.basis,bank1,
      CuccaroStreamedSquareWideLayout.regValue_take_mod src 119 (by omega) u1.basis,ctl1,src1]
    simp only [P]
    split_ifs <;> simp
  -- erase only the first 123 bank bits
  have ndMask1 : (control::(src.take 119++(L.inputBank.take src.length).take 119)).Nodup :=
    ndMask.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _)))
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control (src.take 119) ((L.inputBank.take src.length).take 119)
    (by simp only [List.length_take,inputLen]) ndMask1 u1 r3 mask1
  generalize run (eraseMask control (src.take 119) ((L.inputBank.take src.length).take 119)) r3 u1=u2a at ep1 ef1 ev1 ⊢
  -- record-preserving dummies on the (zero) hosts
  have hU2a : ∀h∈hosts ext,u2a.basis h=false := fun h hh =>
    (ef1 h (fun hb => hHB h hh (List.mem_of_mem_take hb))).trans (hU1 h hh)
  rw [dummies_run (hosts ext) u2a r4 hU2a]
  -- park the last five bank bits on the hosts
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
  rw [cacheWire,cacheFix]
  have readFree (i : Nat)(hi : i=198 ∨ i=199 ∨ i=233) : ext.getD i 0∉hosts ext := by
    intro hh
    simp only [hosts,List.mem_map]at hh
    obtain ⟨j,hj,e⟩:=hh
    have jlt:= (idx_free j hj).2.2.2.2.2
    rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ (by omega)]at e
    have eq:=(List.Nodup.getElem_inj_iff hx).mp e
    have ni : i∉hostIdx := by rcases hi with rfl|rfl|rfl <;> decide
    exact ni (eq ▸ hj)
  have readFrame (i : Nat)(hi : i=198 ∨ i=199 ∨ i=233) : v.basis (ext.getD i 0)=u1.basis (ext.getD i 0) := by
    have mem:=DiagSq.getD_in ext i (by omega)
    exact (vIn _ mem).trans (u2ext _ mem (readFree i hi))
  have made:=InnerLinearCopy.masked_upper_relations L hw ext src dst he h128' control
    s.basis u0.basis u1.basis bank0 mk.2.2.2.2.2.1
  have takeGet (i : Nat)(hi : i<119) : (src.take 119).getD i 0=src.getD i 0 := by
    rw [List.getD_eq_getElem _ _ (by simp [h128'];omega),List.getD_eq_getElem _ _ (by omega)]
    simp
  have sourceBit (i : Nat)(hi : i<119) : v.basis ((src.take 119).getD i 0)=s.basis (src.getD i 0) := by
    rw [takeGet i hi,InnerLinearCopy.register_testBit src i v.basis (by omega),vSource,
      ←InnerLinearCopy.register_testBit src i s.basis (by omega)]
  have away (i : Nat)(hi : i<300) : ext.getD i 0∉(L.inputBank.take src.length).take 119 :=
    fun hb=>extB _ (DiagSq.getD_in ext i (by omega)) (List.mem_of_mem_take hb)
  have bankClean : ∀q∈(L.inputBank.take src.length).take 119,v.basis q=false := by
    intro q hq
    have qb:=List.mem_of_mem_take hq
    exact (vFrame q (bOut q qb)).trans (u2B q qb)
  have headEq : ((src.take 119).take 96).headD 0=src.headD 0 := by cases src <;> rfl
  have hcache : v.basis (dst.headD 0)=(v.basis control && v.basis (((src.take 119).take 96).headD 0)) := by
    simpa only [headEq]using cached
  have hxlin : v.basis (ext.getD 198 0)=
    ((v.basis control && v.basis ((src.take 119).getD 64 0)) ^^
     (v.basis control && v.basis ((src.take 119).getD 96 0))) := by
    rw [readFrame 198 (by omega),vControl,sourceBit 64 (by omega),sourceBit 96 (by omega)]
    exact made.1
  have hyzlin : (v.basis (ext.getD 199 0) ^^ v.basis (ext.getD 233 0))=
    ((v.basis control && v.basis ((src.take 119).getD 65 0)) ^^
     (v.basis control && v.basis ((src.take 119).getD 97 0))) := by
    rw [readFrame 199 (by omega),readFrame 233 (by omega),vControl,
      sourceBit 65 (by omega),sourceBit 97 (by omega)]
    exact made.2
  have linearEq:=InnerLinearCopy.copy_correct control (dst.headD 0) (ext.getD 198 0)
    (ext.getD 199 0) (ext.getD 233 0) (src.take 119) ((L.inputBank.take src.length).take 119)
    (by simp [h128']) (by simp [Blen]) ndMask1 (away 198 (by omega)) (away 199 (by omega))
    (away 233 (by omega)) v r7 bankClean hcache hxlin hyzlin
  rw [linearEq,CachedSquareCopy.run_eq control (dst.headD 0) (src.take 119) ((L.inputBank.take src.length).take 119) v r7
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

namespace ECDSAAdd.Entrant.ParkCopy
def supportHosts (ext : List Wire) : List Wire := hosts ext++[ext.getD 198 0,ext.getD 199 0,ext.getD 233 0]
end ECDSAAdd.Entrant.ParkCopy
