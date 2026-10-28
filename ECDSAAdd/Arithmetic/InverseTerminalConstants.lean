import ECDSAAdd.Arithmetic.InverseCompactViews
import ECDSAAdd.Arithmetic.ConditionalXor

namespace ECDSAAdd.Arithmetic

/-- 终态u=1、s=q时清常量；同一无测量门列在逆轮前写回。 -/
def terminalConstants (I : InverseLoopLayout) (q : Nat) : Program :=
  xorConstant I.middle.u 1 ++ xorConstant I.middle.s q

/-- 不触碰r、K、记录及其它工作位；此入口也描述相同门列的写回方向。 -/
theorem terminalConstants_correct (I : InverseLoopLayout) (hn : I.wires.Nodup)
    (hl : I.first.low.length=256) (q : Nat) (hq : q<2^256) (s : State) (m : List Bool) :
    (run (terminalConstants I q) m s).phase=s.phase ∧
    regValue I.middle.u (run (terminalConstants I q) m s).basis=regValue I.middle.u s.basis ^^^ 1 ∧
    regValue I.middle.s (run (terminalConstants I q) m s).basis=regValue I.middle.s s.basis ^^^ q ∧
    ∀ w,w∉I.middle.u → w∉I.middle.s → (run (terminalConstants I q) m s).basis w=s.basis w := by
  have hd := (I.middle_nodup hn)
  have hnD : I.middle.data.wires.Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have h := List.nodup_iff_count.mp hd w
    simp only [KaliskiRoundLayout.tapeWires,KaliskiRoundLayout.sharedWires,List.count_append] at h
    omega
  have hu := I.middle.data.reg_nodup hnD .u
  have hs := I.middle.data.reg_nodup hnD .s
  have hdis := I.middle.data.reg_disjoint hnD .u .s (by decide)
  have hlen (f : RoundField) : (I.middle.data.reg f).length=257 := by
    rw [InverseLoopLayout.middle,loopEnd_data,I.first.data_reg_length,hl]
  let P := PairFrame I.middle.u I.middle.s s.basis
  let U := regValue I.middle.u s.basis
  let S := regValue I.middle.s s.basis
  have h1 : Triple (P U S) (xorConstant I.middle.u 1) (P (U^^^1) S) := by
    intro st ms h
    obtain ⟨hf,he,hv⟩ := xorConstant_correct I.middle.u hu 1
      (by
        change 1<2^(I.middle.data.reg .u).length
        rw [hlen,show (257:Nat)=256+1 from rfl,Nat.pow_succ]
        have : 0<(2:Nat)^256 := by positivity
        omega) st ms
    exact ⟨hf,PairFrame.update_temp _ _ _ _ _ U S _ hdis h he (by simpa [h.1] using hv)⟩
  have h2 : Triple (P (U^^^1) S) (xorConstant I.middle.s q) (P (U^^^1) (S^^^q)) := by
    intro st ms h
    obtain ⟨hf,he,hv⟩ := xorConstant_correct I.middle.s hs q
      (by change q<2^(I.middle.data.reg .s).length; rw [hlen]; omega) st ms
    exact ⟨hf,PairFrame.update_dst _ _ _ _ _ (U^^^1) S _ hdis h he (by simpa [h.2.1] using hv)⟩
  exact (h1.seq h2) s m ⟨rfl,rfl,fun _ _ _ => rfl⟩

/-- 清除与写回u/s都不依赖r、历史或测量记录的取值。 -/
theorem terminalConstants_spec (I : InverseLoopLayout) (hn : I.wires.Nodup)
    (hl : I.first.low.length=256) (q : Nat) (hq : q<2^256) :
    ({{ I.middle.u=1,I.middle.s=q }} terminalConstants I q {{ I.middle.u=0,I.middle.s=0 }}) ∧
    ({{ I.middle.u=0,I.middle.s=0 }} terminalConstants I q {{ I.middle.u=1,I.middle.s=q }}) := by
  constructor
  · intro s m h
    obtain ⟨hp,hu,hs,_⟩ := terminalConstants_correct I hn hl q hq s m
    simp only [Holds.holds] at h ⊢
    exact ⟨hp,by simpa [h.1] using hu,by simpa [h.2] using hs⟩
  · intro s m h
    obtain ⟨hp,hu,hs,_⟩ := terminalConstants_correct I hn hl q hq s m
    simp only [Holds.holds] at h ⊢
    exact ⟨hp,by simpa [h.1] using hu,by simpa [h.2] using hs⟩

theorem terminalConstants_resources (I : InverseLoopLayout) (q : Nat) :
    toffoliCount (terminalConstants I q)=0 ∧ measurementCount (terminalConstants I q)=0 ∧
    wires (terminalConstants I q)⊆(I.middle.u++I.middle.s).toFinset := by
  have hu := xorConstant_counts I.middle.u 1
  have hs := xorConstant_counts I.middle.s q
  refine ⟨by simp [terminalConstants,hu.1,hs.1],by simp [terminalConstants,hu.2,hs.2],?_⟩
  intro w hw
  simp only [terminalConstants,wires_append,Finset.mem_union] at hw
  rcases hw with hw|hw
  · exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp (xorConstant_wires_subset _ _ hw)))
  · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_toFinset.mp (xorConstant_wires_subset _ _ hw)))

end ECDSAAdd.Arithmetic
