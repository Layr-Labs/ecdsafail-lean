import ECDSAAdd.Arithmetic.ValueLoopProof
import ECDSAAdd.Math.ValueReplay
import ECDSAAdd.Arithmetic.InverseLoopLayout

namespace ECDSAAdd.Arithmetic

/-- 局部边界证明用：重置程序支持以外的幽灵位不改变相位或可见结果。 -/
private theorem write_agrees (W : Finset Wire) (s t : BasisState) (q : Wire) (v : Bool)
    (h : ∀ w∈W, s w=t w) :
    ∀ w∈W, writeBit s q v w=writeBit t q v w := by
  intro w hw
  by_cases he : w=q
  · subst w; simp [writeBit]
  · simp [writeBit,Function.update,he,h w hw]

private theorem correct_agrees (cs : List Correction) (W : Finset Wire)
    (hc : correctionWires cs ⊆ W) (s t : State) (hp : s.phase=t.phase)
    (hb : ∀ w∈W, s.basis w=t.basis w) :
    (correct cs s).phase=(correct cs t).phase ∧
    ∀ w∈W, (correct cs s).basis w=(correct cs t).basis w := by
  induction cs generalizing s t with
  | nil => exact ⟨hp,hb⟩
  | cons c cs ih =>
    have ht : correctionWires cs ⊆ W := by
      intro w h
      apply hc
      cases c <;> exact Finset.mem_union_right _ h
    cases c with
    | Z q =>
      apply ih ht
      · simp only [hp,hb q (hc (by simp [correctionWires]))]
      · exact hb
    | CZ a b =>
      apply ih ht
      · simp only [hp,hb a (hc (by simp [correctionWires])),hb b (hc (by simp [correctionWires]))]
      · exact hb

private theorem run_agrees (p : Program) (W : Finset Wire) (hw : wires p ⊆ W)
    (m : List Bool) (s t : State) (hp : s.phase=t.phase)
    (hb : ∀ w∈W, s.basis w=t.basis w) :
    (run p m s).phase=(run p m t).phase ∧
    ∀ w∈W, (run p m s).basis w=(run p m t).basis w := by
  induction p generalizing m s t with
  | nil => exact ⟨hp,hb⟩
  | cons c p ih =>
    have ht : wires p ⊆ W := fun _ h => hw (Finset.mem_union_right _ h)
    have hi : c.wires ⊆ W := fun _ h => hw (Finset.mem_union_left _ h)
    cases c with
    | X q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires]))]
        exact write_agrees W s.basis t.basis q _ hb
    | CX a q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires])),hb a (hi (by simp [Instr.wires]))]
        exact write_agrees W s.basis t.basis q _ hb
    | CCX a b q =>
      simp only [run]
      refine ih ht _ _ _ ?_ ?_
      · exact hp
      · rw [hb q (hi (by simp [Instr.wires])),hb a (hi (by simp [Instr.wires])),
          hb b (hi (by simp [Instr.wires]))]
        exact write_agrees W s.basis t.basis q _ hb
    | measureX q c0 c1 =>
      simp only [run]
      have hc : correctionWires (if m.headD false then c1 else c0) ⊆ W := by
        split <;> intro w hw <;> apply hi <;> simp_all [Instr.wires]
      have he := correct_agrees _ W hc
        ⟨s.phase ^^ (m.headD false && s.basis q),writeBit s.basis q false⟩
        ⟨t.phase ^^ (m.headD false && t.basis q),writeBit t.basis q false⟩
        (by simp only [hp,hb q (hi (by simp [Instr.wires]))])
        (write_agrees W s.basis t.basis q false hb)
      exact ih ht _ _ _ he.1 he.2

private theorem valueData_out_disjoint (L : RoundDataLayout) (hn : L.wires.Nodup) :
    L.valueUsedWires.Disjoint (L.reg .out) := by
  apply List.disjoint_left.mpr
  intro w hw ho
  have hd (f : RoundField) (hf : f ≠ .out) (hm : w∈L.reg f) : False :=
    List.disjoint_left.mp (L.reg_disjoint hn f .out hf) hm ho
  have he : w=L.cin ∨ w∈L.u ∨ w∈L.v ∨ w∈L.reg .y ∨ w∈L.reg .carry ∨ w∈L.reg .zero := by
    simpa [RoundDataLayout.valueUsedWires,RoundDataLayout.u,RoundDataLayout.v,
      RoundDataLayout.reg,RoundBit.valueUsedWires,RoundBit.get,and_or_left,exists_or,eq_comm] using hw
  rcases he with he|hu|hv|hy|hc|hz
  · subst w; exact L.cin_not_mem hn .out ho
  · exact hd .u (by decide) hu
  · exact hd .v (by decide) hv
  · exact hd .y (by decide) hy
  · exact hd .carry (by decide) hc
  · exact hd .zero (by decide) hz

private theorem valueTape_out_disjoint (L : KaliskiRoundLayout) (rs : List RoundRecord)
    (hn : (L.tapeWires rs).Nodup) :
    (L.valueTapeWires rs).Disjoint (L.data.reg .out) := by
  have hshared := (List.nodup_append'.mp hn).2.1
  have hdata := (List.nodup_append'.mp (List.nodup_append'.mp hshared).1).2.1
  have ho : ∀ w∈L.data.reg .out, w∈L.sharedWires := by
    intro w hw
    exact List.mem_append_left _ (List.mem_append_right _ (L.data.reg_mem .out hw))
  apply List.disjoint_left.mpr
  intro w hw hout
  simp only [KaliskiRoundLayout.valueTapeWires,KaliskiRoundLayout.valueSharedWires,List.mem_append] at hw
  rcases hw with hrec|((hctrl|hdataw)|hcounter)
  · exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hrec (ho w hout)
  · exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_append'.mp hshared).1).2.2
      hctrl (L.data.reg_mem .out hout)
  · exact List.disjoint_left.mp (valueData_out_disjoint L.data hdata) hdataw hout
  · exact List.disjoint_left.mp (List.nodup_append'.mp hshared).2.2
      (List.mem_append_right _ (L.data.reg_mem .out hout)) hcounter

/-- 可用于值走边界的全部有效寄存器；不包含旧r/s/out。 -/
structure ValueLoopState (L : KaliskiRoundLayout) (z : ValueState) (st : BasisState) : Prop where
  u : regValue L.u st=z.u
  v : regValue L.v st=z.v
  mask : regValue (L.data.reg .y) st=0
  carry : regValue (L.data.reg .carry) st=0
  zero : regValue (L.data.reg .zero) st=0
  dataCin : st L.data.cin=false
  k : regValue L.k st=z.k
  next : regValue L.kNext st=0
  counterY : regValue L.counter.y st=0
  counterCarry : regValue L.counter.carry st=0
  active : st L.active=false
  done : st L.done=decide (z.v=0)
  odd : st L.oddWork=false
  both : st L.bothWork=false
  cin : st L.compareCin=false

private def zeroGhost (L : KaliskiRoundLayout) (s : State) : State :=
  ⟨s.phase,fun w => if w∈L.data.reg .out then false else s.basis w⟩

private theorem zeroGhost_reg (L : KaliskiRoundLayout) (hn : L.data.wires.Nodup)
    (s : State) (f : RoundField) (hf : f ≠ .out) :
    regValue (L.data.reg f) (zeroGhost L s).basis=regValue (L.data.reg f) s.basis := by
  apply regValue_congr
  intro w hw
  simp only [zeroGhost,if_neg (List.disjoint_left.mp (L.data.reg_disjoint hn f .out hf) hw)]

private theorem value_reg_mem (L : RoundDataLayout) (f : RoundField)
    (hf : f ≠ .r ∧ f ≠ .s ∧ f ≠ .out) {w : Wire} (hw : w∈L.reg f) : w∈L.valueUsedWires := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨b,hb,?_⟩
  cases f <;> simp_all [RoundBit.valueUsedWires,RoundBit.get]

theorem ValueLoopState.congr (L : KaliskiRoundLayout) (z : ValueState) (s t : BasisState)
    (h : ValueLoopState L z s) (he : ∀ w∈L.valueSharedWires, t w=s w) : ValueLoopState L z t := by
  have hd (f : RoundField) (hf : f ≠ .r ∧ f ≠ .s ∧ f ≠ .out) :
      regValue (L.data.reg f) t=regValue (L.data.reg f) s := by
    apply regValue_congr
    intro w hw
    exact he w (List.mem_append_left _ (List.mem_append_right _ (value_reg_mem L.data f hf hw)))
  have hc (xs : List Wire) (hs : xs ⊆ L.counter.wires) : regValue xs t=regValue xs s := by
    apply regValue_congr
    intro w hw
    exact he w (List.mem_append_right _ (hs hw))
  have hb (w : Wire) (hw : w∈[L.done,L.oddWork,L.bothWork,L.compareCin]) : t w=s w :=
    he w (List.mem_append_left _ (List.mem_append_left _ hw))
  refine ⟨(hd .u (by decide)).trans h.u,(hd .v (by decide)).trans h.v,
    (hd .y (by decide)).trans h.mask,(hd .carry (by decide)).trans h.carry,
    (hd .zero (by decide)).trans h.zero,?_,
    (hc _ L.counter.reg_subset.1).trans h.k,
    (hc _ L.counter.reg_subset.2.2.1).trans h.next,
    (hc _ L.counter.reg_subset.2.1).trans h.counterY,
    (hc _ L.counter.reg_subset.2.2.2).trans h.counterCarry,?_,
    (hb _ (by simp)).trans h.done,(hb _ (by simp)).trans h.odd,
    (hb _ (by simp)).trans h.both,(hb _ (by simp)).trans h.cin⟩
  · exact (he _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))).trans h.dataCin
  · exact (he _ (List.mem_append_right _ List.mem_cons_self)).trans h.active

private theorem ValueLoopState.of_full (L : KaliskiRoundLayout) (z : KState) (st : BasisState)
    (h : LoopState L z st) : ValueLoopState L z.value st :=
  ⟨h.data.1 .u,h.data.1 .v,h.data.1 .y,h.data.1 .carry,h.data.1 .zero,h.data.2,
   h.k,h.next,h.y,h.carry,h.active,h.done,h.odd,h.both,h.cin⟩

private theorem zeroGhost_full (L : KaliskiRoundLayout) (rs : List RoundRecord)
    (hn : (L.tapeWires rs).Nodup) (z : ValueState) (s : State) (h : ValueLoopState L z s.basis) :
    LoopState L ⟨z.u,z.v,regValue L.r s.basis,regValue L.s s.basis,z.k⟩ (zeroGhost L s).basis := by
  have hdata := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_append'.mp hn).2.1).1).2.1
  have hs : ValueLoopState L z (zeroGhost L s).basis := h.congr L z s.basis _ (by
    intro w hw
    have he := List.disjoint_left.mp (valueTape_out_disjoint L rs hn) (List.mem_append_right _ hw)
    simp only [zeroGhost,if_neg he])
  refine ⟨⟨?_,hs.dataCin⟩,hs.k,hs.next,hs.counterY,hs.counterCarry,hs.active,
    hs.done,hs.odd,hs.both,hs.cin⟩
  intro f
  cases f with
  | u => exact hs.u
  | v => exact hs.v
  | r => exact zeroGhost_reg L hdata s .r (by decide)
  | s => exact zeroGhost_reg L hdata s .s (by decide)
  | y => exact hs.mask
  | out =>
    change regValue (L.data.reg .out) (zeroGhost L s).basis=0
    rw [regValue_zero]
    intro w hw; simp [zeroGhost,hw]
  | carry => exact hs.carry
  | zero => exact hs.zero

private theorem valueKIter_projection (n : Nat) (z : KState) :
    (valueKStep^[n] z).value=valueStep^[n] z.value := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    exact ih (valueKStep z)

private theorem valueEnd_shared_perm (L : KaliskiRoundLayout) (n : Nat) :
    (loopEndLayout L n).valueSharedWires.Perm L.valueSharedWires := by
  have hs (L : KaliskiRoundLayout) : L.swapCounter.valueSharedWires.Perm L.valueSharedWires := by
    change (_++L.swapCounter.data.valueUsedWires++L.swapCounter.counter.wires).Perm
      (_++L.data.valueUsedWires++L.counter.wires)
    rw [L.swapCounter_data,L.swapCounter_counter]
    exact List.Perm.append_left _ L.counter.swapCounter_perm
  induction n generalizing L with
  | zero => exact List.Perm.refl _
  | succ n ih => exact (ih L.swapCounter).trans (hs L)

private theorem valueCodes_trace (n : Nat) (z : KState) :
    valueCodes n z=(valueTrace n z.value).map Prod.snd := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [valueCodes,valueTrace,List.map_cons,ih,valueCode_projection]; rfl

private theorem valueKIter_ghost (n : Nat) (z : KState) :
    (valueKStep^[n] z).r=z.r ∧ (valueKStep^[n] z).s=z.s := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [Function.iterate_succ_apply',valueKStep] using ih

/-- 去掉旧out=0要求后的循环入口；幽灵工作位不属于前后置条件或实际支持。 -/
theorem valueLoop_spec (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat) (z : ValueState)
    (hn : (L.tapeWires rs).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width)
    (hlen : i+rs.length≤512) (hk : z.k ≤ i ∧ (z.v ≠ 0 → z.k=i))
    (hb : ∀ j<rs.length, (valueStep^[j] z).u<2^(valueWidth L.data.width (i+j)) ∧
      (valueStep^[j] z).v<2^(valueWidth L.data.width (i+j))) :
    Triple (fun st => ValueLoopState L z st ∧ TapeValues rs (List.replicate rs.length (false,false)) st)
      (valueLoop L i rs)
      (fun st => ValueLoopState (loopEndLayout L rs.length) (valueStep^[rs.length] z) st ∧
        TapeValues rs ((valueTrace rs.length z).map Prod.snd) st) := by
  intro s m h
  let full : KState := ⟨z.u,z.v,regValue L.r s.basis,regValue L.s s.basis,z.k⟩
  let W := (L.valueTapeWires rs).toFinset
  have he : ∀ w∈W, (zeroGhost L s).basis w=s.basis w := by
    intro w hw
    exact if_neg (List.disjoint_left.mp (valueTape_out_disjoint L rs hn) (List.mem_toFinset.mp hw))
  have ht : TapeValues rs (List.replicate rs.length (false,false)) (zeroGhost L s).basis :=
    TapeValues.congr rs _ _ _ h.2 (fun w hw => he w
      (List.mem_toFinset.mpr (List.mem_append_left _ hw)))
  have hs := zeroGhost_full L rs hn z s h.1
  have hc := (valueLoop_correct L rs i full hn hw hd hlen hk hb).1
  obtain ⟨hp,ho⟩ := hc (zeroGhost L s) m ⟨hs,ht⟩
  have hwire : wires (valueLoop L i rs) ⊆ W := by
    exact (valueLoop_wires_subset L rs i hw hd).1.1
  have hr := run_agrees (valueLoop L i rs) W hwire m (zeroGhost L s) s rfl he
  refine ⟨hr.1.symm.trans hp,?_,?_⟩
  · have hh := ValueLoopState.of_full _ _ _ ho.1
    rw [valueKIter_projection] at hh
    apply hh.congr _ _ _ _
    intro w hw
    exact (hr.2 w (List.mem_toFinset.mpr (List.mem_append_right _
      ((valueEnd_shared_perm L rs.length).mem_iff.mp hw)))).symm
  · rw [valueCodes_trace] at ho
    exact TapeValues.congr rs _ _ _ ho.2 (fun w hw => (hr.2 w
      (List.mem_toFinset.mpr (List.mem_append_left _ hw))).symm)

/-- 逆循环同样不要求旧out字为零；恢复u/v/k并清空两位记录带。 -/
theorem valueUnloop_spec (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat) (z : ValueState)
    (hn : (L.tapeWires rs).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width)
    (hlen : i+rs.length≤512) (hk : z.k ≤ i ∧ (z.v ≠ 0 → z.k=i))
    (hb : ∀ j<rs.length, (valueStep^[j] z).u<2^(valueWidth L.data.width (i+j)) ∧
      (valueStep^[j] z).v<2^(valueWidth L.data.width (i+j))) :
    Triple (fun st => ValueLoopState (loopEndLayout L rs.length) (valueStep^[rs.length] z) st ∧
        TapeValues rs ((valueTrace rs.length z).map Prod.snd) st)
      (valueUnloop L i rs)
      (fun st => ValueLoopState L z st ∧ TapeValues rs (List.replicate rs.length (false,false)) st) := by
  intro s m h
  let E := loopEndLayout L rs.length
  let full : KState := ⟨z.u,z.v,regValue L.r s.basis,regValue L.s s.basis,z.k⟩
  let W := (L.valueTapeWires rs).toFinset
  have he : ∀ w∈W, (zeroGhost L s).basis w=s.basis w := by
    intro w hw
    exact if_neg (List.disjoint_left.mp (valueTape_out_disjoint L rs hn) (List.mem_toFinset.mp hw))
  have hend : (E.tapeWires rs).Nodup :=
    (List.Perm.append_left _ (loopEnd_shared_perm L rs.length)).nodup_iff.mpr hn
  have hdata : E.data=L.data := loopEnd_data L rs.length
  have hs := zeroGhost_full E rs hend (valueStep^[rs.length] z) s h.1
  have hpj := valueKIter_projection rs.length full
  have hg := valueKIter_ghost rs.length full
  have hu' := congrArg ValueState.u hpj
  have hv' := congrArg ValueState.v hpj
  have hk' := congrArg ValueState.k hpj
  change (valueKStep^[rs.length] full).u=(valueStep^[rs.length] z).u at hu'
  change (valueKStep^[rs.length] full).v=(valueStep^[rs.length] z).v at hv'
  change (valueKStep^[rs.length] full).k=(valueStep^[rs.length] z).k at hk'
  change (valueKStep^[rs.length] full).r=regValue L.r s.basis ∧
    (valueKStep^[rs.length] full).s=regValue L.s s.basis at hg
  have hfull : (⟨(valueStep^[rs.length] z).u,(valueStep^[rs.length] z).v,
      regValue E.r s.basis,regValue E.s s.basis,(valueStep^[rs.length] z).k⟩ : KState)=valueKStep^[rs.length] full := by
    have hr : regValue E.r s.basis=regValue L.r s.basis := by change regValue E.data.r _=_; rw [hdata]; rfl
    have hs' : regValue E.s s.basis=regValue L.s s.basis := by change regValue E.data.s _=_; rw [hdata]; rfl
    rw [hr,hs']
    rw [← hu',← hv',← hk',← hg.1,← hg.2]
  rw [hfull] at hs
  have hghost : zeroGhost E s=zeroGhost L s := by simp only [zeroGhost,hdata]
  rw [hghost] at hs
  have ht : TapeValues rs (valueCodes rs.length full) (zeroGhost L s).basis := by
    rw [valueCodes_trace]
    exact TapeValues.congr rs _ _ _ h.2 (fun w hw => he w
      (List.mem_toFinset.mpr (List.mem_append_left _ hw)))
  obtain ⟨hp,ho⟩ := (valueLoop_correct L rs i full hn hw hd hlen hk hb).2 (zeroGhost L s) m ⟨hs,ht⟩
  have hwire : wires (valueUnloop L i rs) ⊆ W := by
    exact (valueLoop_wires_subset L rs i hw hd).1.2
  have hr := run_agrees (valueUnloop L i rs) W hwire m (zeroGhost L s) s rfl he
  refine ⟨hr.1.symm.trans hp,?_,?_⟩
  · exact (ValueLoopState.of_full _ _ _ ho.1).congr _ _ _ _ (fun w hw =>
      (hr.2 w (List.mem_toFinset.mpr (List.mem_append_right _ hw))).symm)
  · exact TapeValues.congr rs _ _ _ ho.2 (fun w hw => (hr.2 w
      (List.mem_toFinset.mpr (List.mem_append_left _ hw))).symm)

end ECDSAAdd.Arithmetic
