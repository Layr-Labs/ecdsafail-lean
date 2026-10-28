import ECDSAAdd.Arithmetic.SkywalkIntegerLayout
import ECDSAAdd.Arithmetic.SignedRecordProgram
import ECDSAAdd.Math.SkywalkTrace

namespace ECDSAAdd.Arithmetic



/-- Executable exact parity-route, signed relabelled half, native signed
record, and orientation history update. The two history bits remain coherent. -/
def skywalkIntegerTick (L : SkywalkIntegerLayout) : Program :=
  skywalkRoute L.a0 L.b0 L.ah L.bh ++
  skywalkSignedHalf L.aSign L.ext ++
  signedRecord L.ext L.bSign L.history L.half L.b L.carry ++
  [.CX L.previous L.a0]

/-- Forward inverse arithmetic, with fresh measurement records. Original low
parity is recovered before undoing the high-word routing. -/
def skywalkIntegerUntick (L : SkywalkIntegerLayout) : Program :=
  [.CX L.previous L.a0] ++
  signedUnrecord L.ext L.bSign L.history L.half L.b L.carry ++
  skywalkSignedHalf L.aSign L.ext ++ [.CX L.a0 L.b0] ++
  swapRegisters L.a0 L.ah L.bh

def SkywalkIntegerInput (L : SkywalkIntegerLayout) (A B : Int) (G : Bool)
    (s : BasisState) : Prop :=
  signedRegValue L.a s=A ∧ signedRegValue L.b s=B ∧ s L.previous=G ∧
  s L.ext=false ∧ s L.history=false ∧ regValue L.carry s=0

def SkywalkIntegerOutput (L : SkywalkIntegerLayout) (A B : Int) (G : Bool)
    (s : BasisState) : Prop :=
  let t := SkywalkRails.step ⟨A,B,G⟩
  signedRegValue L.half s=t.h ∧ signedRegValue L.b s=t.k ∧
  s L.a0=t.g ∧ s L.history=t.s ∧ s L.previous=G ∧ regValue L.carry s=0

def skywalkIntegerProjection (L : SkywalkIntegerLayout) (s : BasisState) : SkywalkRails.Tick :=
  ⟨signedRegValue L.half s,signedRegValue L.b s,s L.a0,s L.history⟩

private theorem prefix_no_measure (p q : Program) (hp : measurementCount p=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  have hr := run_take p m s
  rw [hp,List.take_zero] at hr
  rw [run_append,hp,List.take_zero,List.drop_zero,hr]

private theorem suffix_no_measure (p q : Program) (hq : measurementCount q=0)
    (s : State) (m : List Bool) : run (p++q) m s=run q m (run p m s) := by
  rw [run_append,run_take]
  have h1 := run_take q (m.drop (measurementCount p)) (run p m s)
  have h2 := run_take q m (run p m s)
  rw [hq,List.take_zero] at h1 h2
  exact h1.symm.trans h2

private theorem tick_run (L : SkywalkIntegerLayout) (hv : L.Valid) (s : State) (m : List Bool) :
    run (skywalkIntegerTick L) m s=
      run [.CX L.previous L.a0] m
        (run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m
          (run (skywalkSignedHalf L.aSign L.ext) m
            (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s))) := by
  have hr := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv)).2
  have hh := (skywalkSignedHalf_counts L.aSign L.ext).2
  simp only [skywalkIntegerTick,List.append_assoc]
  rw [prefix_no_measure _ _ hr,prefix_no_measure _ _ hh,
    suffix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0)]

private theorem route_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.ext::L.carry) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis q=s.basis q := by
  have hn : ((L.previous::L.history::L.ext::L.carry)++
      (L.a0::L.b0::(L.ah++L.bh))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  exact List.disjoint_left.mp hd hq (List.mem_toFinset.mp hh)

private theorem half_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈L.previous::L.history::L.a0::(L.b++L.carry)) :
    (run (skywalkSignedHalf L.aSign L.ext) m s).basis q=s.basis q := by
  have hne : q≠L.ext := by
    intro he
    subst q
    have hh := List.nodup_iff_count.mp hv.nodup L.ext
    have hp := List.count_pos_iff.mpr hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.b,
      List.count_cons,List.count_append] at hh hp
    simp only [beq_self_eq_true,if_true] at hh
    omega
  exact (skywalkSignedHalf_frame L.aSign L.ext s m).2 q hne

private theorem record_aux_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m : List Bool) (q : Wire) (hq : q∈[L.previous,L.a0]) :
    (run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m s).basis q=s.basis q := by
  have hn : ([L.previous,L.a0]++(L.history::(L.half++L.b++L.carry))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have hh := List.nodup_iff_count.mp hv.nodup w
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.count_cons,List.count_append,List.count_nil] at hh ⊢
    omega
  have hd := (List.nodup_append'.mp hn).2.2
  have hc := L.record_lengths hv
  exact (signedRecord_frame L.ah (L.b0::L.bMid) L.ext L.bSign L.history L.carry
    hc.1 hc.2 s m q (fun hm => List.disjoint_left.mp hd hq hm)).1

private theorem ext_outside_high (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.ext∉L.ah := by
  intro hm
  have hh := List.nodup_iff_count.mp hv.nodup L.ext
  have hp := List.count_pos_iff.mpr hm
  simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh
  simp only [beq_self_eq_true,if_true] at hh
  omega

private theorem ext_sign_ne (L : SkywalkIntegerLayout) (hv : L.Valid) : L.aSign≠L.ext := by
  intro he
  exact ext_outside_high L hv (by simp [SkywalkIntegerLayout.ah,←he])

private theorem previous_low_ne (L : SkywalkIntegerLayout) (hv : L.Valid) : L.previous≠L.a0 := by
  intro he
  have hh := List.nodup_iff_count.mp hv.nodup L.previous
  simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hh
  simp [he] at hh

private theorem route_int_values (L : SkywalkIntegerLayout) (hv : L.Valid) (A B : Int)
    (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (ha : signedRegValue L.a s.basis=A) (hb : signedRegValue L.b s.basis=B)
    (hext : s.basis L.ext=false) :
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).phase=s.phase ∧
    signedRegValue (L.ext::L.ah) (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).1 ∧
    signedRegValue L.b (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis=
      (SkywalkRails.route A B).2 ∧
    (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s).basis L.a0=SkywalkRails.odd A := by
  have hna : L.ah≠[] := by simp [SkywalkIntegerLayout.ah]
  have hnb : L.bh≠[] := by simp [SkywalkIntegerLayout.bh]
  have hA := ha.symm.trans (signedRegValue_cons L.a0 L.ah s.basis hna)
  have hB := hb.symm.trans (signedRegValue_cons L.b0 L.bh s.basis hnb)
  have hpar : s.basis L.b0=(!s.basis L.a0) := by
    cases hca : s.basis L.a0 with
    | false =>
      cases hcb : s.basis L.b0 with
      | false =>
        simp [hca,hcb] at hA hB
        omega
      | true => rfl
    | true =>
      cases hcb : s.basis L.b0 with
      | false => rfl
      | true =>
        simp [hca,hcb] at hA hB
        omega
  have hctrl : s.basis L.a0=SkywalkRails.odd A := by
    cases hc : s.basis L.a0 with
    | false =>
      have he : A%2=0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
    | true =>
      have he : A%2≠0 := by simp [hc] at hA; omega
      simp [SkywalkRails.odd,he]
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  obtain ⟨hf,_,hctl,hlo,hrawA,hrawB⟩ := skywalkRoute_correct L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv) s m hpar
  have he0 : t.basis L.ext=false :=
    (route_aux_frame L hv s m L.ext (by simp)).trans hext
  have hsa : signedRegValue L.ah t.basis=
      if s.basis L.a0 then signedRegValue L.bh s.basis else signedRegValue L.ah s.basis := by
    have hh := congrArg (signedDecode L.ah.length) hrawA
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  have hsb : signedRegValue L.bh t.basis=
      if s.basis L.a0 then signedRegValue L.ah s.basis else signedRegValue L.bh s.basis := by
    have hh := congrArg (signedDecode L.bh.length) hrawB
    cases hc : s.basis L.a0 <;>
      simpa [signedRegValue,hc,L.high_lengths hv] using hh
  refine ⟨hf,?_,?_,hctl.trans hctrl⟩
  · rw [signedRegValue_cons L.ext L.ah t.basis hna,he0,hsa]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

  · change signedRegValue (L.b0::L.bh) t.basis=_
    rw [signedRegValue_cons L.b0 L.bh t.basis hnb,hlo,hsb]
    rw [hpar] at hB
    cases hc : s.basis L.a0 <;> simp [hc] at hA hB
    all_goals simp [SkywalkRails.route,←hctrl,hc]; omega

private theorem low_outside_record (L : SkywalkIntegerLayout) (hv : L.Valid) :
    L.a0∉L.history::(L.half++L.b++L.carry) := by
  intro hm
  have hh := List.nodup_iff_count.mp hv.nodup L.a0
  have hp := List.count_pos_iff.mpr hm
  simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
    List.count_cons,List.count_append,List.count_nil] at hh hp
  simp only [beq_self_eq_true,if_true] at hh
  omega

/-- Actual routed, sign-extended and recorded bits implement the unbounded
signed tick exactly, including zero rails and both equality sign histories. -/
theorem skywalkIntegerTick_spec (L : SkywalkIntegerLayout) (hv : L.Valid)
    (A B : Int) (G : Bool) (hp : (A+B)%2=1) :
    Triple (SkywalkIntegerInput L A B G) (skywalkIntegerTick L)
      (SkywalkIntegerOutput L A B G) := by
  intro s m hin
  let E := (SkywalkRails.route A B).1
  let O := (SkywalkRails.route A B).2
  let H := E/2
  let K := signedRecordValue H O
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  let u := run (skywalkSignedHalf L.aSign L.ext) m t
  let v := run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m u
  have he : E%2=0 := SkywalkRails.route_even A B hp
  obtain ⟨htp,hE,hO,hC⟩ := route_int_values L hv A B hp s m hin.1 hin.2.1 hin.2.2.2.1
  change signedRegValue (L.ext::(L.aMid++[L.aSign])) t.basis=E at hE
  have tq : t.basis L.history=false :=
    (route_aux_frame L hv s m L.history (by simp)).trans hin.2.2.2.2.1
  have tp : t.basis L.previous=G :=
    (route_aux_frame L hv s m L.previous (by simp)).trans hin.2.2.1
  have tk : regValue L.carry t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hin.2.2.2.2.2
    intro q hq
    exact route_aux_frame L hv s m q (by simp [hq])
  have uH : signedRegValue L.half u.basis=H := by
    have hh := skywalkSignedHalf_int L.ext L.aSign L.aMid (ext_sign_ne L hv)
      (ext_outside_high L hv) t m (by rw [hE]; exact he)
    change signedRegValue L.half u.basis=
      signedRegValue (L.ext::(L.aMid++[L.aSign])) t.basis/2 at hh
    rw [hE] at hh
    exact hh
  have uO : signedRegValue L.b u.basis=O := by
    apply Eq.trans ((signedRegValue_eq_iff _ _ _).mpr ?_) hO
    intro q hq
    exact half_aux_frame L hv t m q (by simp [hq])
  have uq : u.basis L.history=false :=
    (half_aux_frame L hv t m L.history (by simp)).trans tq
  have up : u.basis L.previous=G :=
    (half_aux_frame L hv t m L.previous (by simp)).trans tp
  have uc : u.basis L.a0=SkywalkRails.odd A :=
    (half_aux_frame L hv t m L.a0 (by simp)).trans hC
  have uk : regValue L.carry u.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) tk
    intro q hq
    exact half_aux_frame L hv t m q (by simp [hq])
  have hl := L.record_lengths hv
  obtain ⟨hvp,hval⟩ := signedRecord_spec L.ah (L.b0::L.bMid) L.ext L.bSign L.history
    L.carry (L.record_nodup hv) hl.1 hl.2 H O u m ⟨uq,uH,uO,uk⟩
  have vp : v.basis L.previous=G :=
    (record_aux_frame L hv u m L.previous (by simp)).trans up
  have vc : v.basis L.a0=SkywalkRails.odd A :=
    (record_aux_frame L hv u m L.a0 (by simp)).trans uc
  have hsame : SkywalkRails.sameSign H O=SkywalkRails.sameSign E O := by
    unfold SkywalkRails.sameSign
    rw [SkywalkRails.neg_half E he]
  have hK : K=(if SkywalkRails.sameSign E O then O-H else O+H) := by
    change signedRecordValue H O=_
    rw [signedRecordValue_rails,hsame]
  rw [tick_run L hv s m]
  have keep (q : Wire) (hq : q∈L.history::(L.half++L.b++L.carry)) :
      (run [.CX L.previous L.a0] m v).basis q=v.basis q := by
    have hne : q≠L.a0 := fun he => low_outside_record L hv (he ▸ hq)
    simp [run,writeBit,hne]
  have hHfinal : signedRegValue L.half (run [.CX L.previous L.a0] m v).basis=H := by
    apply Eq.trans ((signedRegValue_eq_iff _ _ _).mpr ?_) hval.2.1
    intro q hq
    change q∈L.half at hq
    exact keep q (by simp [hq])
  have hOfinal : signedRegValue L.b (run [.CX L.previous L.a0] m v).basis=K := by
    apply Eq.trans ((signedRegValue_eq_iff _ _ _).mpr ?_) hval.2.2.1
    intro q hq
    change q∈L.b at hq
    exact keep q (by simp [hq])
  have hqfinal : (run [.CX L.previous L.a0] m v).basis L.history=
      (SkywalkRails.neg O ^^ SkywalkRails.neg K) :=
    (keep L.history (by simp)).trans hval.1
  have hpfinal : (run [.CX L.previous L.a0] m v).basis L.previous=G := by
    simpa [run,writeBit,previous_low_ne L hv] using vp
  have hkfinal : regValue L.carry (run [.CX L.previous L.a0] m v).basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hval.2.2.2
    intro q hq
    exact keep q (by simp [hq])
  have hcfinal : (run [.CX L.previous L.a0] m v).basis L.a0=
      (G ^^ SkywalkRails.odd A) := by
    simp only [run,writeBit,Function.update_self,vc,vp]
    exact Bool.xor_comm _ _
  refine ⟨hvp.trans ((skywalkSignedHalf_frame L.aSign L.ext t m).1.trans htp),?_⟩
  dsimp only [SkywalkIntegerOutput,SkywalkRails.step]
  simpa only [E,O,H,←hK] using
    (show signedRegValue L.half (run [.CX L.previous L.a0] m v).basis=H ∧
      signedRegValue L.b (run [.CX L.previous L.a0] m v).basis=K ∧
      (run [.CX L.previous L.a0] m v).basis L.a0=(G ^^ SkywalkRails.odd A) ∧
      (run [.CX L.previous L.a0] m v).basis L.history=(SkywalkRails.neg O ^^ SkywalkRails.neg K) ∧
      (run [.CX L.previous L.a0] m v).basis L.previous=G ∧
      regValue L.carry (run [.CX L.previous L.a0] m v).basis=0 from
      ⟨hHfinal,hOfinal,hcfinal,hqfinal,hpfinal,hkfinal⟩)

private theorem swap_twice (c : Wire) (a b : List Wire) (hl : a.length=b.length)
    (hn : (c::(a++b)).Nodup) (s : State) (m₁ m₂ : List Bool) :
    run (swapRegisters c a b) m₂ (run (swapRegisters c a b) m₁ s)=s := by
  let t := run (swapRegisters c a b) m₁ s
  let v := run (swapRegisters c a b) m₂ t
  obtain ⟨p1,e1,a1,b1⟩ := swapRegisters_correct c a b hl hn s m₁
  obtain ⟨p2,e2,a2,b2⟩ := swapRegisters_correct c a b hl hn t m₂
  have hc : t.basis c=s.basis c := e1 c
    (fun h => (List.nodup_cons.mp hn).1 (by simp [h]))
    (fun h => (List.nodup_cons.mp hn).1 (by simp [h]))
  have ha : regValue a v.basis=regValue a s.basis := by
    rw [a2,hc,a1,b1]
    cases s.basis c <;> rfl
  have hb : regValue b v.basis=regValue b s.basis := by
    rw [b2,hc,a1,b1]
    cases s.basis c <;> rfl
  apply congrArg₂ State.mk
  · exact p2.trans p1
  · funext q
    by_cases hqa : q∈a
    · exact (regValue_eq_iff _ _ _).mp ha q hqa
    by_cases hqb : q∈b
    · exact (regValue_eq_iff _ _ _).mp hb q hqb
    exact (e2 q hqa hqb).trans (e1 q hqa hqb)

private theorem cx_twice (c t : Wire) (hct : c≠t) (s : State) (m₁ m₂ : List Bool) :
    run [.CX c t] m₂ (run [.CX c t] m₁ s)=s := by
  apply congrArg (State.mk s.phase)
  funext q
  by_cases hq : q=t
  · subst q
    cases hc : s.basis c <;> cases ht : s.basis t <;>
      simp [run,writeBit,hct,hc,ht]
  · simp [run,writeBit,hq]

private theorem route_roundtrip (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m₁ m₂ : List Bool) :
    run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m₂
      (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m₁ s)=s := by
  have hl := L.high_lengths hv
  have hn : (L.a0::(L.ah++L.bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp (L.route_nodup hv) q
    simp only [List.count_cons] at hh ⊢
    omega
  have hne : L.a0≠L.b0 := fun h => (List.nodup_cons.mp (L.route_nodup hv)).1 (by simp [h])
  have hm := (swapRegisters_resources L.a0 L.ah L.bh hl hn).2.1
  rw [skywalkRoute,prefix_no_measure _ _ hm,
    prefix_no_measure _ _ (by rfl : measurementCount [.CX L.a0 L.b0]=0)]
  rw [cx_twice L.a0 L.b0 hne]
  exact swap_twice L.a0 L.ah L.bh hl hn s m₁ m₂

private theorem untick_run (L : SkywalkIntegerLayout) (hv : L.Valid) (s : State) (m : List Bool) :
    run (skywalkIntegerUntick L) m s=
      run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m
        (run (skywalkSignedHalf L.aSign L.ext) m
          (run (signedUnrecord L.ext L.bSign L.history L.half L.b L.carry) m
            (run [.CX L.previous L.a0] m s))) := by
  have hl := L.high_lengths hv
  have hn : (L.a0::(L.ah++L.bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp (L.route_nodup hv) q
    simp only [List.count_cons] at hh ⊢
    omega
  have hs := (swapRegisters_resources L.a0 L.ah L.bh hl hn).2.1
  have hh := (skywalkSignedHalf_counts L.aSign L.ext).2
  have ht : measurementCount (skywalkSignedHalf L.aSign L.ext++
      ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh))=0 := by
    simp [measurementCount_append,hh,hs,measurementCount]
  simp only [skywalkIntegerUntick,List.append_assoc]
  rw [prefix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0),
    suffix_no_measure _ _ ht,prefix_no_measure _ _ hh]

/-- The separately emitted inverse restores the entire physical State with
independent measurement streams. Only the history/carry clean premises are
needed for reversal; signed parity/extension premises are for interpretation. -/
theorem skywalkIntegerTick_roundtrip (L : SkywalkIntegerLayout) (hv : L.Valid)
    (s : State) (m₁ m₂ : List Bool) (hq : s.basis L.history=false)
    (hk : regValue L.carry s.basis=0) :
    run (skywalkIntegerUntick L) m₂ (run (skywalkIntegerTick L) m₁ s)=s := by
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m₁ s
  let u := run (skywalkSignedHalf L.aSign L.ext) m₁ t
  have tq : t.basis L.history=false :=
    (route_aux_frame L hv s m₁ L.history (by simp)).trans hq
  have tk : regValue L.carry t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hk
    intro q hq
    exact route_aux_frame L hv s m₁ q (by simp [hq])
  have uq : u.basis L.history=false :=
    (half_aux_frame L hv t m₁ L.history (by simp)).trans tq
  have uk : regValue L.carry u.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) tk
    intro q hq
    exact half_aux_frame L hv t m₁ q (by simp [hq])
  have hl := L.record_lengths hv
  have hr := signedRecord_roundtrip L.ah (L.b0::L.bMid) L.ext L.bSign L.history L.carry
    (L.record_nodup hv) hl.1 hl.2 u m₁ m₂ uq uk
  change run (signedUnrecord L.ext L.bSign L.history L.half L.b L.carry) m₂
    (run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m₁ u)=u at hr
  have hh : run (skywalkSignedHalf L.aSign L.ext) m₂ u=t := by
    simpa only [skywalkSignedHalf,run] using
      skywalkSignedHalf_twice L.aSign L.ext (ext_sign_ne L hv) t m₁
  rw [tick_run L hv s m₁,untick_run L hv _ m₂,
    cx_twice L.previous L.a0 (previous_low_ne L hv)]
  change run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m₂
    (run (skywalkSignedHalf L.aSign L.ext) m₂
      (run (signedUnrecord L.ext L.bSign L.history L.half L.b L.carry) m₂
        (run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m₁ u)))=s
  rw [hr,hh]
  exact route_roundtrip L hv s m₁ m₂

theorem skywalkIntegerTick_correct (L : SkywalkIntegerLayout) (hv : L.Valid)
    (A B : Int) (G : Bool) (hp : (A+B)%2=1) (s : State) (m : List Bool)
    (hin : SkywalkIntegerInput L A B G s.basis) :
    (run (skywalkIntegerTick L) m s).phase=s.phase ∧
    skywalkIntegerProjection L (run (skywalkIntegerTick L) m s).basis=
      SkywalkRails.step ⟨A,B,G⟩ := by
  obtain ⟨hf,ho⟩ := skywalkIntegerTick_spec L hv A B G hp s m hin
  refine ⟨hf,?_⟩
  apply SkywalkRails.Tick.ext
  · exact ho.1
  · exact ho.2.1
  · exact ho.2.2.1
  · exact ho.2.2.2.1

/-- The full-width tick costs one high-word swap and one unmasked addition.
All routing/sign/extension/orientation operations are Clifford-only. -/
theorem skywalkIntegerTick_counts (L : SkywalkIntegerLayout) (hv : L.Valid) :
    toffoliCount (skywalkIntegerTick L)=2*L.ah.length ∧
    measurementCount (skywalkIntegerTick L)=L.ah.length ∧
    toffoliCount (skywalkIntegerUntick L)=2*L.ah.length ∧
    measurementCount (skywalkIntegerUntick L)=L.ah.length := by
  have hl := L.high_lengths hv
  have hc := L.record_lengths hv
  have hr := skywalkRoute_counts L.a0 L.b0 L.ah L.bh hl (L.route_nodup hv)
  have hn : (L.a0::(L.ah++L.bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp (L.route_nodup hv) q
    simp only [List.count_cons] at hh ⊢
    omega
  have hs := swapRegisters_resources L.a0 L.ah L.bh hl hn
  have ha := signedRecord_counts L.ext L.bSign L.history L.half L.b L.carry hc.1 hc.2
  have hh := skywalkSignedHalf_counts L.aSign L.ext
  have hlen : L.b.length-1=L.ah.length := by simp [SkywalkIntegerLayout.b,hl]
  simp only [skywalkIntegerTick,skywalkIntegerUntick,toffoliCount_append,measurementCount_append,
    hr.1,hr.2,hs.1,hs.2.1,ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hh.1,hh.2,hlen,
    toffoliCount,measurementCount]
  omega

/-- Actual support is confined to the explicit rail/carry/history interface. -/
theorem skywalkIntegerTick_wires_subset (L : SkywalkIntegerLayout) (hv : L.Valid) :
    wires (skywalkIntegerTick L)⊆L.wires.toFinset ∧
    wires (skywalkIntegerUntick L)⊆L.wires.toFinset := by
  have hl := L.high_lengths hv
  have hc := L.record_lengths hv
  have hroute : wires (skywalkRoute L.a0 L.b0 L.ah L.bh)⊆L.wires.toFinset := by
    intro q hq
    have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh hl hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have hswap : wires (swapRegisters L.a0 L.ah L.bh)⊆L.wires.toFinset := by
    intro q hq
    have h := swapRegisters_wires L.a0 L.ah L.bh hl hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have hhalf : wires (skywalkSignedHalf L.aSign L.ext)⊆L.wires.toFinset := by
    rw [skywalkSignedHalf_wires]
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl
    · simp [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah]
    · simp [SkywalkIntegerLayout.wires]
  have hword := signedRecord_wires L.ah (L.b0::L.bMid) L.ext L.bSign L.history L.carry hc.1 hc.2
  have hsigned :
      wires (signedRecord L.ext L.bSign L.history L.half L.b L.carry)=
        (L.history::(L.half++L.b++L.carry)).toFinset ∧
      wires (signedUnrecord L.ext L.bSign L.history L.half L.b L.carry)=
        (L.history::(L.half++L.b++L.carry)).toFinset := hword
  have hown : (L.history::(L.half++L.b++L.carry)).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hrecord : wires (signedRecord L.ext L.bSign L.history L.half L.b L.carry)⊆L.wires.toFinset := by
    rw [hsigned.1]
    exact hown
  have hunrecord : wires (signedUnrecord L.ext L.bSign L.history L.half L.b L.carry)⊆L.wires.toFinset := by
    rw [hsigned.2]
    exact hown
  have hprevious : wires [.CX L.previous L.a0]⊆L.wires.toFinset := by
    simp [SkywalkIntegerLayout.wires,wires,Instr.wires]
  have hlow : wires [.CX L.a0 L.b0]⊆L.wires.toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [skywalkIntegerTick,skywalkIntegerUntick,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hroute,hhalf⟩,hrecord⟩,hprevious⟩,
    ⟨⟨⟨⟨hprevious,hunrecord⟩,hhalf⟩,hlow⟩,hswap⟩⟩

end ECDSAAdd.Arithmetic
