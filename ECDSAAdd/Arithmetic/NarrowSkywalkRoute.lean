import ECDSAAdd.Arithmetic.NarrowSignedRecord
import ECDSAAdd.Arithmetic.SkywalkRoute

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

/-- Sign-difference AND, computing one coherent fanout control. The sign
reference is temporarily XORed and immediately restored. -/
def skywalkSignDelta (g a b d : Wire) : Program :=
  [.CX b a,.CCX g a d,.CX b a]

/-- The XOR of both sign references is invariant when both sign banks flip.
This permits exact measured AND cleanup with the current references. -/
def skywalkSignDeltaErase (g a b d : Wire) : Program :=
  [.CX b a,.measureX d [] [.CZ g a],.CX b a]

theorem skywalkSignDelta_correct (g a b d : Wire)
    (hga : g≠a) (_hgd : g≠d) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (s : State) (m : List Bool) (hd : s.basis d=false) :
    run (skywalkSignDelta g a b d) m s=
      ⟨s.phase,writeBit s.basis d (s.basis g && (s.basis a ^^ s.basis b))⟩ := by
  have hda := had.symm
  have hba := hab.symm
  simp only [skywalkSignDelta,run]
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=d
  · subst q
    simp_all [writeBit]
  by_cases hqa : q=a
  · subst q
    cases ha : s.basis a <;> cases hb : s.basis b <;>
      simp_all [writeBit]
  · simp [writeBit,hq,hqa]

theorem skywalkSignDeltaErase_correct (g a b d : Wire)
    (hga : g≠a) (hgd : g≠d) (hab : a≠b) (had : a≠d) (hbd : b≠d)
    (s : State) (m : List Bool)
    (hd : s.basis d=(s.basis g && (s.basis a ^^ s.basis b))) :
    run (skywalkSignDeltaErase g a b d) m s=⟨s.phase,writeBit s.basis d false⟩ := by
  have hda := had.symm
  have hba := hab.symm
  simp only [skywalkSignDeltaErase,run]
  cases hm : m.headD false <;>
    simp_all [measureAndCorrect,correct,writeBit]
  all_goals
    funext q
    by_cases hq : q=a
    · subst q
      simp_all
    · simp_all [Function.update_apply]

theorem skywalkSignDelta_counts (g a b d : Wire) :
    toffoliCount (skywalkSignDelta g a b d)=1 ∧
    measurementCount (skywalkSignDelta g a b d)=0 ∧
    toffoliCount (skywalkSignDeltaErase g a b d)=0 ∧
    measurementCount (skywalkSignDeltaErase g a b d)=1 := by
  simp [skywalkSignDelta,skywalkSignDeltaErase,toffoliCount,measurementCount]

structure NarrowSkywalkSwapLayout where
  g : Wire
  delta : Wire
  sx : Wire
  sy : Wire
  xlow : List Wire
  ylow : List Wire
  xhigh : List Wire
  yhigh : List Wire

namespace NarrowSkywalkSwapLayout

def xbank (L : NarrowSkywalkSwapLayout) : List Wire := L.sx::L.xhigh
def ybank (L : NarrowSkywalkSwapLayout) : List Wire := L.sy::L.yhigh
def x (L : NarrowSkywalkSwapLayout) : List Wire := L.xlow++L.xbank
def y (L : NarrowSkywalkSwapLayout) : List Wire := L.ylow++L.ybank
def bank (L : NarrowSkywalkSwapLayout) : List Wire := L.xbank++L.ybank
def wires (L : NarrowSkywalkSwapLayout) : List Wire := L.g::L.delta::(L.x++L.y)

structure Valid (L : NarrowSkywalkSwapLayout) : Prop where
  low_lengths : L.xlow.length=L.ylow.length
  high_lengths : L.xhigh.length=L.yhigh.length
  nodup : L.wires.Nodup

/-- Current high rails are sign copies, including the chosen reference signs.
Positive powers-of-two endpoints are handled by the caller's extra route bit. -/
def Copies (L : NarrowSkywalkSwapLayout) (s : BasisState) : Prop :=
  (∀ q∈L.xbank,s q=s L.sx) ∧ (∀ q∈L.ybank,s q=s L.sy)

theorem lengths (L : NarrowSkywalkSwapLayout) (hv : L.Valid) : L.x.length=L.y.length := by
  simp only [x,y,xbank,ybank,List.length_append,List.length_cons,hv.low_lengths,hv.high_lengths]

theorem full_nodup (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    (L.g::(L.x++L.y)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,List.count_cons] at hh ⊢
  omega

theorem low_nodup (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    (L.g::(L.xlow++L.ylow)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh ⊢
  omega

theorem bank_nodup (L : NarrowSkywalkSwapLayout) (hv : L.Valid) : L.bank.Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have hh := List.nodup_iff_count.mp hv.nodup q
  simp only [wires,x,y,xbank,ybank,bank,List.count_cons,List.count_append] at hh ⊢
  omega

theorem delta_bank (L : NarrowSkywalkSwapLayout) (hv : L.Valid) : L.delta∉L.bank := by
  intro hm
  have hh := List.nodup_iff_count.mp hv.nodup L.delta
  have hp := List.count_pos_iff.mpr hm
  simp only [wires,x,y,xbank,ybank,bank,List.count_cons,List.count_append] at hh hp
  simp only [beq_self_eq_true,if_true] at hh
  omega

theorem distinct (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    L.g≠L.sx ∧ L.g≠L.delta ∧ L.sx≠L.sy ∧ L.sx≠L.delta ∧ L.sy≠L.delta := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.g
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.g
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.sx
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
    omega
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.sx
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
    omega
  · intro he
    have hh := List.nodup_iff_count.mp hv.nodup L.sy
    simp only [wires,x,y,xbank,ybank,List.count_cons,List.count_append] at hh
    simp [he] at hh
    omega

theorem outside_low (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (q : Wire)
    (hq : q∈L.g::L.delta::L.bank) : q∉L.xlow ∧ q∉L.ylow := by
  constructor <;> intro hm
  all_goals
    have hh := List.nodup_iff_count.mp hv.nodup q
    have hp := List.count_pos_iff.mpr hm
    have hb := List.count_pos_iff.mpr hq
    simp only [wires,x,y,xbank,ybank,bank,List.count_cons,List.count_append] at hh hb
    omega

end NarrowSkywalkSwapLayout

/-- Only low non-sign bits use Fredkins. Both retained signs and all omitted
high sign copies use the one coherent delta fanout, then measured cleanup. -/
def narrowSkywalkSwap (L : NarrowSkywalkSwapLayout) : Program :=
  skywalkSignDelta L.g L.sx L.sy L.delta ++ swapRegisters L.g L.xlow L.ylow ++
    signComplement L.delta L.bank ++ skywalkSignDeltaErase L.g L.sx L.sy L.delta

private theorem narrow_route_const_read (r : List Wire) (s : BasisState) (c : Bool)
    (hc : ∀ q∈r,s q=c) : regValue r s=(if c then 2^r.length-1 else 0) := by
  induction r with
  | nil => cases c <;> simp [regValue]
  | cons q r ih =>
    have hq := hc q (by simp)
    have hr := ih (by intro a ha; exact hc a (by simp [ha]))
    change (if s q then 1 else 0)+2*regValue r s=(if c then 2^(r.length+1)-1 else 0)
    rw [hq,hr]
    cases c <;> simp [pow_succ]
    all_goals have hp : 0<2^r.length := by positivity
    all_goals omega

private theorem route_prefix_no_measure (p q : Program) (hp : measurementCount p=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  have hr := run_take p m s
  rw [hp,List.take_zero] at hr
  rw [run_append,hp,List.take_zero,List.drop_zero,hr]


/-- Exact swap projection, including full source/control/work frames and
arbitrary-record phase restoration. Only redundant sign-bank premises narrow. -/
theorem narrowSkywalkSwap_correct (L : NarrowSkywalkSwapLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    (run (narrowSkywalkSwap L) m s).phase=s.phase ∧
    (∀ q,q∉L.x → q∉L.y → (run (narrowSkywalkSwap L) m s).basis q=s.basis q) ∧
    regValue L.x (run (narrowSkywalkSwap L) m s).basis=
      (if s.basis L.g then regValue L.y s.basis else regValue L.x s.basis) ∧
    regValue L.y (run (narrowSkywalkSwap L) m s).basis=
      (if s.basis L.g then regValue L.x s.basis else regValue L.y s.basis) ∧
    L.Copies (run (narrowSkywalkSwap L) m s).basis := by
  let D := s.basis L.g && (s.basis L.sx ^^ s.basis L.sy)
  let u := run (skywalkSignDelta L.g L.sx L.sy L.delta) m s
  let t := run (swapRegisters L.g L.xlow L.ylow) m u
  let v := run (signComplement L.delta L.bank) m t
  let out := run (skywalkSignDeltaErase L.g L.sx L.sy L.delta) m v
  have hn := L.distinct hv
  have hu : u=⟨s.phase,writeBit s.basis L.delta D⟩ :=
    skywalkSignDelta_correct _ _ _ _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 s m hd
  have ulow (q : Wire) (hq : q∈L.xlow ∨ q∈L.ylow) : u.basis q=s.basis q := by
    have he : q≠L.delta := by
      intro he
      subst q
      have hh := L.outside_low hv L.delta (by simp)
      tauto
    rw [hu]
    simp [writeBit,he]
  have ux : regValue L.xlow u.basis=regValue L.xlow s.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ulow q (Or.inl hq))
  have uy : regValue L.ylow u.basis=regValue L.ylow s.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ulow q (Or.inr hq))
  have uother (q : Wire) (hq : q≠L.delta) : u.basis q=s.basis q := by
    rw [hu]
    simp [writeBit,hq]
  obtain ⟨tp,tf,tx,ty⟩ := swapRegisters_correct L.g L.xlow L.ylow hv.low_lengths
    (L.low_nodup hv) u m
  change regValue L.xlow t.basis=(if u.basis L.g then regValue L.ylow u.basis else regValue L.xlow u.basis) at tx
  change regValue L.ylow t.basis=(if u.basis L.g then regValue L.xlow u.basis else regValue L.ylow u.basis) at ty
  have keep (q : Wire) (hq : q∈L.g::L.delta::L.bank) : t.basis q=u.basis q := by
    have hh := L.outside_low hv q hq
    exact tf q hh.1 hh.2
  have tg : t.basis L.g=s.basis L.g :=
    (keep L.g (by simp)).trans (uother L.g hn.2.1)
  have td : t.basis L.delta=D := by
    rw [keep L.delta (by simp),hu]
    simp [writeBit]
  have tb (q : Wire) (hq : q∈L.bank) : t.basis q=s.basis q := by
    have he : q≠L.delta := fun he => L.delta_bank hv (he ▸ hq)
    exact (keep q (by simp [hq])).trans (uother q he)
  have hvf : v=⟨t.phase,fun q => if q∈L.bank then t.basis q ^^ t.basis L.delta else t.basis q⟩ :=
    narrow_fanout_correct L.delta L.bank (L.bank_nodup hv) (L.delta_bank hv) t m
  have gb : L.g∉L.bank := by
    intro hm
    have hh := List.nodup_iff_count.mp hv.nodup L.g
    have hp := List.count_pos_iff.mpr hm
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank,NarrowSkywalkSwapLayout.bank,
      List.count_cons,List.count_append] at hh hp
    simp only [beq_self_eq_true,if_true] at hh
    omega
  have vg : v.basis L.g=s.basis L.g := by
    rw [hvf]
    simp only [if_neg gb]
    exact tg
  have vd : v.basis L.delta=D := by
    rw [hvf]
    simp only [if_neg (L.delta_bank hv)]
    exact td
  have vbank (q : Wire) (hq : q∈L.bank) : v.basis q=(s.basis q ^^ D) := by
    rw [hvf]
    simp only [if_pos hq,td,tb q hq]
  have vsx : v.basis L.sx=(s.basis L.sx ^^ D) := vbank L.sx (by
    simp [NarrowSkywalkSwapLayout.bank,NarrowSkywalkSwapLayout.xbank])
  have vsy : v.basis L.sy=(s.basis L.sy ^^ D) := vbank L.sy (by
    simp [NarrowSkywalkSwapLayout.bank,NarrowSkywalkSwapLayout.ybank])
  have hD : v.basis L.delta=(v.basis L.g && (v.basis L.sx ^^ v.basis L.sy)) := by
    rw [vd,vg,vsx,vsy]
    dsimp only [D]
    cases s.basis L.g <;> cases s.basis L.sx <;> cases s.basis L.sy <;> rfl
  have ho : out=⟨v.phase,writeBit v.basis L.delta false⟩ :=
    skywalkSignDeltaErase_correct _ _ _ _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 v m hD
  have ot (q : Wire) (hq : q∈L.xlow ∨ q∈L.ylow) : out.basis q=t.basis q := by
    have hb : q∉L.bank := by
      intro hqb
      have hh := L.outside_low hv q (by simp [hqb])
      tauto
    have he : q≠L.delta := by
      intro he
      subst q
      have hh := L.outside_low hv L.delta (by simp)
      tauto
    rw [ho,hvf]
    simp [writeBit,he,hb]
  have ox : regValue L.xlow out.basis=regValue L.xlow t.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ot q (Or.inl hq))
  have oy : regValue L.ylow out.basis=regValue L.ylow t.basis :=
    regValue_congr _ _ _ (by intro q hq; exact ot q (Or.inr hq))
  have ogx (q : Wire) (hq : q∈L.xbank) :
      out.basis q=(if s.basis L.g then s.basis L.sy else s.basis L.sx) := by
    have hb : q∈L.bank := List.mem_append_left _ hq
    have he : q≠L.delta := fun he => L.delta_bank hv (he ▸ hb)
    rw [ho]
    simp only [writeBit,Function.update_of_ne he,vbank q hb,hc.1 q hq]
    dsimp only [D]
    cases s.basis L.g <;> cases s.basis L.sx <;> cases s.basis L.sy <;> rfl
  have ogy (q : Wire) (hq : q∈L.ybank) :
      out.basis q=(if s.basis L.g then s.basis L.sx else s.basis L.sy) := by
    have hb : q∈L.bank := List.mem_append_right _ hq
    have he : q≠L.delta := fun he => L.delta_bank hv (he ▸ hb)
    rw [ho]
    simp only [writeBit,Function.update_of_ne he,vbank q hb,hc.2 q hq]
    dsimp only [D]
    cases s.basis L.g <;> cases s.basis L.sx <;> cases s.basis L.sy <;> rfl
  have obx := narrow_route_const_read L.xbank out.basis _ ogx
  have oby := narrow_route_const_read L.ybank out.basis _ ogy
  have sbx := narrow_route_const_read L.xbank s.basis _ hc.1
  have sby := narrow_route_const_read L.ybank s.basis _ hc.2
  have hbanklen : L.xbank.length=L.ybank.length := by
    simp [NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank,hv.high_lengths]
  have ug : u.basis L.g=s.basis L.g := uother L.g hn.2.1
  have hr : run (narrowSkywalkSwap L) m s=out := by
    have hsd := (skywalkSignDelta_counts L.g L.sx L.sy L.delta).2.1
    have hsw := (swapRegisters_resources L.g L.xlow L.ylow hv.low_lengths (L.low_nodup hv)).2.1
    have hsf := (signComplement_counts L.delta L.bank).2
    simp only [narrowSkywalkSwap,List.append_assoc]
    rw [route_prefix_no_measure _ _ hsd,route_prefix_no_measure _ _ hsw,
      route_prefix_no_measure _ _ hsf]
  rw [hr]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [ho,hvf]
    have hup : u.phase=s.phase := by
      have hh := congrArg State.phase hu
      exact hh
    exact tp.trans hup
  · intro q hqx hqy
    by_cases hqd : q=L.delta
    · subst q
      rw [ho]
      simp [writeBit,hd]
    have hxl : q∉L.xlow := fun h => hqx (List.mem_append_left _ h)
    have hyl : q∉L.ylow := fun h => hqy (List.mem_append_left _ h)
    have hb : q∉L.bank := by
      intro hm
      rcases List.mem_append.mp hm with hx|hy
      · exact hqx (List.mem_append_right _ hx)
      · exact hqy (List.mem_append_right _ hy)
    rw [ho,hvf]
    simp only [writeBit,Function.update_of_ne hqd,if_neg hb]
    exact (tf q hxl hyl).trans (uother q hqd)
  · simp only [NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,regValue_append,
      ox,tx,ug,ux,uy,obx,sbx,sby]
    cases s.basis L.g <;> simp [hv.low_lengths,hbanklen]
  · simp only [NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,regValue_append,
      oy,ty,ug,ux,uy,oby,sbx,sby]
    cases s.basis L.g <;> simp [hv.low_lengths,hbanklen]
  · constructor
    · intro q hq
      exact (ogx q hq).trans (ogx L.sx (by simp [NarrowSkywalkSwapLayout.xbank])).symm
    · intro q hq
      exact (ogy q hq).trans (ogy L.sy (by simp [NarrowSkywalkSwapLayout.ybank])).symm

/-- Scoped full-State equivalence with the actual wide Fredkin program.
The two record lists are independent; the temporary carry site returns to0. -/
theorem narrowSkywalkSwap_eq (L : NarrowSkywalkSwapLayout) (hv : L.Valid)
    (s : State) (m₁ m₂ : List Bool) (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    run (narrowSkywalkSwap L) m₁ s=run (swapRegisters L.g L.x L.y) m₂ s := by
  obtain ⟨np,nf,nx,ny,_⟩ := narrowSkywalkSwap_correct L hv s m₁ hd hc
  obtain ⟨wp,wf,wx,wy⟩ := swapRegisters_correct L.g L.x L.y (L.lengths hv)
    (L.full_nodup hv) s m₂
  apply congrArg₂ State.mk
  · exact np.trans wp.symm
  · funext q
    by_cases hx : q∈L.x
    · exact (regValue_eq_iff _ _ _).mp (nx.trans wx.symm) q hx
    by_cases hy : q∈L.y
    · exact (regValue_eq_iff _ _ _).mp (ny.trans wy.symm) q hy
    exact (nf q hx hy).trans (wf q hx hy).symm

/-- One sign-delta Toffoli replaces the retained sign and every high Fredkin.
Measured cleanup costs one M, with no additional Toffoli. -/
theorem narrowSkywalkSwap_counts (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    toffoliCount (narrowSkywalkSwap L)=L.xlow.length+1 ∧
    measurementCount (narrowSkywalkSwap L)=1 := by
  have hd := skywalkSignDelta_counts L.g L.sx L.sy L.delta
  have hs := swapRegisters_resources L.g L.xlow L.ylow hv.low_lengths (L.low_nodup hv)
  have hf := signComplement_counts L.delta L.bank
  simp only [narrowSkywalkSwap,toffoliCount_append,measurementCount_append,
    hd.1,hd.2.1,hd.2.2.1,hd.2.2.2,hs.1,hs.2.1,hf.1,hf.2]
  constructor
  · omega
  · trivial


private theorem route_suffix_no_measure (p q : Program) (hq : measurementCount q=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  rw [run_append,run_take]
  have h1 := run_take q (m.drop (measurementCount p)) (run p m s)
  have h2 := run_take q m (run p m s)
  rw [hq,List.take_zero] at h1 h2
  exact h1.symm.trans h2

/-- Actual Skywalk route with the original parity-history/odd-low operation. -/
def narrowSkywalkRoute (L : NarrowSkywalkSwapLayout) (b0 : Wire) : Program :=
  narrowSkywalkSwap L ++ [.CX L.g b0]

theorem narrowSkywalkRoute_eq (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (b0 : Wire)
    (s : State) (m₁ m₂ : List Bool) (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    run (narrowSkywalkRoute L b0) m₁ s=run (skywalkRoute L.g b0 L.x L.y) m₂ s := by
  rw [narrowSkywalkRoute,skywalkRoute,
    route_suffix_no_measure _ _ (by rfl : measurementCount [.CX L.g b0]=0),
    route_suffix_no_measure _ _ (by rfl : measurementCount [.CX L.g b0]=0)]
  rw [narrowSkywalkSwap_eq L hv s m₁ m₂ hd hc]
  rfl

theorem narrowSkywalkRoute_counts (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (b0 : Wire) :
    toffoliCount (narrowSkywalkRoute L b0)=L.xlow.length+1 ∧
    measurementCount (narrowSkywalkRoute L b0)=1 := by
  have h := narrowSkywalkSwap_counts L hv
  simp [narrowSkywalkRoute,toffoliCount_append,measurementCount_append,
    toffoliCount,measurementCount,h.1,h.2]

private theorem route_delta_support (g a b d : Wire) :
    wires (skywalkSignDelta g a b d)⊆[g,a,b,d].toFinset ∧
    wires (skywalkSignDeltaErase g a b d)⊆[g,a,b,d].toFinset := by
  constructor <;> intro q hq
  all_goals
    simp only [skywalkSignDelta,skywalkSignDeltaErase,wires,Instr.wires,correctionWires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,
      List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto

theorem narrowSkywalkSwap_support (L : NarrowSkywalkSwapLayout) (hv : L.Valid) :
    wires (narrowSkywalkSwap L)⊆L.wires.toFinset := by
  have hd := route_delta_support L.g L.sx L.sy L.delta
  have ha : [L.g,L.sx,L.sy,L.delta].toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      NarrowSkywalkSwapLayout.xbank,NarrowSkywalkSwapLayout.ybank,List.mem_toFinset,
      List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hs : wires (swapRegisters L.g L.xlow L.ylow)⊆L.wires.toFinset := by
    intro q hq
    have hh := swapRegisters_wires L.g L.xlow L.ylow hv.low_lengths hq
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
    tauto
  have hf : wires (signComplement L.delta L.bank)⊆L.wires.toFinset := by
    intro q hq
    have hh := signComplement_wires_subset L.delta L.bank hq
    simp only [NarrowSkywalkSwapLayout.wires,NarrowSkywalkSwapLayout.x,NarrowSkywalkSwapLayout.y,
      NarrowSkywalkSwapLayout.bank,List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
    tauto
  simp only [narrowSkywalkSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨hd.1.trans ha,hs⟩,hf⟩,hd.2.trans ha⟩

theorem narrowSkywalkRoute_support (L : NarrowSkywalkSwapLayout) (hv : L.Valid) (b0 : Wire) :
    wires (narrowSkywalkRoute L b0)⊆(b0::L.wires).toFinset := by
  have hs := narrowSkywalkSwap_support L hv
  intro q hq
  simp only [narrowSkywalkRoute,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · exact List.mem_toFinset.mpr (List.mem_cons_of_mem b0 (List.mem_toFinset.mp (hs hq)))
  · simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,NarrowSkywalkSwapLayout.wires]
    tauto

end ECDSAAdd.Arithmetic
