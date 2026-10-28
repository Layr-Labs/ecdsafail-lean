import ECDSAAdd.Arithmetic.SwapRegisters

namespace ECDSAAdd.Arithmetic

/-- Extract first-rail parity as history, swap only high rail bits, and make
the retained odd rail's low bit one. The even low bit is represented by zero
in the mathematical source word rather than physically swapping the history. -/
def skywalkRoute (a0 b0 : Wire) (ah bh : List Wire) : Program :=
  swapRegisters a0 ah bh ++ [.CX a0 b0]

theorem skywalkRoute_correct (a0 b0 : Wire) (ah bh : List Wire)
    (hlen : ah.length=bh.length) (hnd : (a0::b0::(ah++bh)).Nodup)
    (s : State) (m : List Bool) (hp : s.basis b0=(!s.basis a0)) :
    (run (skywalkRoute a0 b0 ah bh) m s).phase=s.phase ∧
    (∀ q, q∉ah → q∉bh → q≠b0 →
      (run (skywalkRoute a0 b0 ah bh) m s).basis q=s.basis q) ∧
    (run (skywalkRoute a0 b0 ah bh) m s).basis a0=s.basis a0 ∧
    (run (skywalkRoute a0 b0 ah bh) m s).basis b0=true ∧
    regValue ah (run (skywalkRoute a0 b0 ah bh) m s).basis=
      (if s.basis a0 then regValue bh s.basis else regValue ah s.basis) ∧
    regValue bh (run (skywalkRoute a0 b0 ah bh) m s).basis=
      (if s.basis a0 then regValue ah s.basis else regValue bh s.basis) := by
  have hn : (a0::(ah++bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons] at hh ⊢
    omega
  have hab0 : a0≠b0 := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have haa : a0∉ah := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hab : a0∉bh := fun h => (List.nodup_cons.mp hnd).1 (by simp [h])
  have hba : b0∉ah := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [h])
  have hbb : b0∉bh := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [h])
  let t := run (swapRegisters a0 ah bh) m s
  let out : State := ⟨t.phase,writeBit t.basis b0 (t.basis b0 ^^ t.basis a0)⟩
  have hm := (swapRegisters_resources a0 ah bh hlen hn).2.1
  have hr := run_take (swapRegisters a0 ah bh) m s
  rw [hm,List.take_zero] at hr
  have hout : run (skywalkRoute a0 b0 ah bh) m s=out := by
    rw [skywalkRoute,run_append,hm,List.take_zero,List.drop_zero,hr]
    rfl
  obtain ⟨ht,he,ha,hb⟩ := swapRegisters_correct a0 ah bh hlen hn s m
  have hc : t.basis a0=s.basis a0 := he a0 haa hab
  have hlo : t.basis b0=(!s.basis a0) := (he b0 hba hbb).trans hp
  have hav : regValue ah out.basis=regValue ah t.basis := by
    apply regValue_congr
    intro q hq
    have hqb : q≠b0 := fun h => hba (h ▸ hq)
    simp [out,writeBit,hqb]
  have hbv : regValue bh out.basis=regValue bh t.basis := by
    apply regValue_congr
    intro q hq
    have hqb : q≠b0 := fun h => hbb (h ▸ hq)
    simp [out,writeBit,hqb]
  rw [hout]
  refine ⟨ht,?_,?_,?_,hav.trans ha,hbv.trans hb⟩
  · intro q hqa hqb hq0
    simpa [out,writeBit,hq0] using he q hqa hqb
  · simpa [out,writeBit,hab0] using hc
  · simp [out,writeBit,hlo,hc]

theorem skywalkRoute_spec (a0 b0 : Wire) (ah bh : List Wire)
    (hlen : ah.length=bh.length) (hnd : (a0::b0::(ah++bh)).Nodup)
    (C : Bool) (A B : Nat) :
    {{ a0=C,b0=(!C),ah=A,bh=B }} skywalkRoute a0 b0 ah bh
    {{ a0=C,b0=true,ah=(if C then B else A),bh=(if C then A else B) }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hp : s.basis b0=(!s.basis a0) := by rw [h.1.1.1]; exact h.1.1.2
  obtain ⟨hf,_,hc,hlo,ha,hb⟩ := skywalkRoute_correct a0 b0 ah bh hlen hnd s m hp
  exact ⟨hf,⟨⟨hc.trans h.1.1.1,hlo⟩,by simpa [h.1.1.1,h.1.2,h.2] using ha⟩,
    by simpa [h.1.1.1,h.1.2,h.2] using hb⟩

theorem skywalkRoute_counts (a0 b0 : Wire) (ah bh : List Wire)
    (hlen : ah.length=bh.length) (hnd : (a0::b0::(ah++bh)).Nodup) :
    toffoliCount (skywalkRoute a0 b0 ah bh)=ah.length ∧
    measurementCount (skywalkRoute a0 b0 ah bh)=0 := by
  have hn : (a0::(ah++bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp hnd q
    simp only [List.count_cons] at hh ⊢
    omega
  have h := swapRegisters_resources a0 ah bh hlen hn
  simp [skywalkRoute,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,h.1,h.2.1]

theorem skywalkRoute_wires_subset (a0 b0 : Wire) (ah bh : List Wire)
    (hlen : ah.length=bh.length) :
    wires (skywalkRoute a0 b0 ah bh)⊆(a0::b0::(ah++bh)).toFinset := by
  have hs := swapRegisters_wires a0 ah bh hlen
  intro q hq
  have h : q∈wires (swapRegisters a0 ah bh) → q∈a0::(ah++bh) :=
    fun hh => List.mem_toFinset.mp (hs hh)
  simp only [skywalkRoute,wires_append,wires,Instr.wires,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
  simp only [List.mem_cons,List.mem_append] at h
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

end ECDSAAdd.Arithmetic
