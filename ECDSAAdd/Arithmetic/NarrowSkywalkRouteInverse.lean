import ECDSAAdd.Arithmetic.NarrowSkywalkRouteTick

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

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


/-- Fresh measured sign-delta cleanup makes the same emitted swap its own
exact inverse on copied sign banks, without reversing any measurement. -/
theorem narrowSkywalkSwap_roundtrip (L : NarrowSkywalkSwapLayout) (hv : L.Valid)
    (s : State) (m₁ m₂ : List Bool) (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    run (narrowSkywalkSwap L) m₂ (run (narrowSkywalkSwap L) m₁ s)=s := by
  let t := run (narrowSkywalkSwap L) m₁ s
  have hout := narrowSkywalkSwap_correct L hv s m₁ hd hc
  have hdelta : L.delta∉L.x ∧ L.delta∉L.y := by
    have hn := (List.nodup_cons.mp (List.nodup_cons.mp hv.nodup).2).1
    exact ⟨fun h => hn (List.mem_append_left _ h),fun h => hn (List.mem_append_right _ h)⟩
  have hdt : t.basis L.delta=false :=
    (hout.2.1 L.delta hdelta.1 hdelta.2).trans hd
  have hct : L.Copies t.basis := hout.2.2.2.2
  rw [narrowSkywalkSwap_eq L hv t m₂ m₂ hdt hct]
  dsimp only [t]
  rw [narrowSkywalkSwap_eq L hv s m₁ m₁ hd hc]
  exact swap_twice L.g L.x L.y (L.lengths hv) (L.full_nodup hv) s m₁ m₂

/-- Independent measured inverse route: recover the original low parity
before performing the same exact sign-bank swap with a fresh record. -/
def narrowSkywalkUnroute (L : NarrowSkywalkSwapLayout) (b0 : Wire) : Program :=
  [.CX L.g b0] ++ narrowSkywalkSwap L

theorem narrowSkywalkRoute_roundtrip (L : NarrowSkywalkSwapLayout) (hv : L.Valid)
    (b0 : Wire) (hgb : L.g≠b0) (s : State) (m₁ m₂ : List Bool)
    (hd : s.basis L.delta=false) (hc : L.Copies s.basis) :
    run (narrowSkywalkUnroute L b0) m₂ (run (narrowSkywalkRoute L b0) m₁ s)=s := by
  rw [narrowSkywalkRoute,narrowSkywalkUnroute,
    suffix_no_measure _ _ (by rfl : measurementCount [.CX L.g b0]=0),
    prefix_no_measure _ _ (by rfl : measurementCount [.CX L.g b0]=0),
    cx_twice L.g b0 hgb]
  exact narrowSkywalkSwap_roundtrip L hv s m₁ m₂ hd hc

private def routedBody (L : SkywalkIntegerLayout) (na : Nat) : Program :=
  skywalkSignedHalf L.aSign L.ext ++
    narrowSignedRecord (narrowSkywalkRecordLayout L na) na ++ [.CX L.previous L.a0]

private def routedBodyInverse (L : SkywalkIntegerLayout) (na : Nat) : Program :=
  [.CX L.previous L.a0] ++ narrowSignedUnrecord (narrowSkywalkRecordLayout L na) na ++
    skywalkSignedHalf L.aSign L.ext

private theorem routedBody_roundtrip (L : SkywalkIntegerLayout) (hv : L.Valid) (na : Nat)
    (hna : 0<na) (hle : na≤L.half.length) (s : State) (m₁ m₂ : List Bool)
    (hq : s.basis L.history=false) (hk : regValue L.carry s.basis=0) :
    run (routedBodyInverse L na) m₂ (run (routedBody L na) m₁ s)=s := by
  let u := run (skywalkSignedHalf L.aSign L.ext) m₁ s
  have uq : u.basis L.history=false :=
    (half_aux_frame L hv s m₁ L.history (by simp)).trans hq
  have uk : regValue L.carry u.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hk
    intro q hq
    exact half_aux_frame L hv s m₁ q (by simp [hq])
  have vv := narrowSkywalkRecord_views L hv na hna hle
  have hr := narrowSignedRecord_roundtrip (narrowSkywalkRecordLayout L na) na
    (narrowSkywalkRecord_widths L hv na hna hle)
    (narrowSkywalkRecord_nodup L hv na hna hle) u m₁ m₂
    (by simpa only [narrowSkywalkRecordLayout] using uq) (by simpa only [vv.2.2] using uk)
  have hm := (skywalkSignedHalf_counts L.aSign L.ext).2
  simp only [routedBody,routedBodyInverse,List.append_assoc]
  rw [prefix_no_measure _ _ hm,
    suffix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0),
    prefix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0),
    suffix_no_measure _ _ hm,cx_twice L.previous L.a0 (previous_low_ne L hv)]
  change run (skywalkSignedHalf L.aSign L.ext) m₂
    (run (narrowSignedUnrecord (narrowSkywalkRecordLayout L na) na) m₂
      (run (narrowSignedRecord (narrowSkywalkRecordLayout L na) na) m₁ u))=s
  rw [hr]
  simpa only [skywalkSignedHalf,run] using
    skywalkSignedHalf_twice L.aSign L.ext (ext_sign_ne L hv) s m₁

/-- The independently emitted full untick keeps full signed half and reverses
only the actual retained-prefix arithmetic and sign-bank route streams. -/
def narrowSkywalkRoutedUntick (L : SkywalkIntegerLayout) (nr na : Nat) : Program :=
  routedBodyInverse L na ++ narrowSkywalkUnroute (narrowSkywalkRouteLayout L nr) L.b0

private theorem routed_prepare_frame (L : SkywalkIntegerLayout) (hv : L.Valid)
    (nr : Nat) (hnr : 2≤nr) (hle : nr≤L.a.length) (s : State) (m : List Bool)
    (hd : s.basis (L.carry.headD 0)=false)
    (hc : (narrowSkywalkRouteLayout L nr).Copies s.basis) (q : Wire)
    (hq : q∈L.history::L.carry) :
    (run (narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0) m s).basis q=s.basis q := by
  have vv := narrowSkywalkRoute_views L hv nr hnr hle
  have he := narrowSkywalkRoute_eq _ (narrowSkywalkRoute_valid L hv nr hnr hle) L.b0 s m [] hd hc
  simp only [vv.1,vv.2] at he
  rw [he]
  apply run_preserves_outside
  intro hm
  have hh := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) hm
  have hc1 := List.nodup_iff_count.mp hv.nodup q
  have hc2 := List.count_pos_iff.mpr hq
  have hc3 := List.count_pos_iff.mpr (List.mem_toFinset.mp hh)
  simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at hc1 hc2 hc3
  omega

/-- Complete physical State inverse. The carry supplies delta, returns to0,
and is reused by the actual arithmetic stream. The two records are independent. -/
theorem narrowSkywalkRoutedTick_roundtrip (L : SkywalkIntegerLayout) (hv : L.Valid) (nr na : Nat)
    (hnr : 2≤nr) (hrlen : nr≤L.a.length) (hna : 0<na) (halen : na≤L.half.length)
    (s : State) (m₁ m₂ : List Bool)
    (hq : s.basis L.history=false) (hk : regValue L.carry s.basis=0)
    (hc : (narrowSkywalkRouteLayout L nr).Copies s.basis) :
    run (narrowSkywalkRoutedUntick L nr na) m₂ (run (narrowSkywalkRoutedTick L nr na) m₁ s)=s := by
  let route := narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0
  have hd : s.basis (L.carry.headD 0)=false :=
    (regValue_zero _ _).mp hk _ (narrowSkywalkRoute_delta_mem L hv)
  have hgb : L.a0≠L.b0 := fun h => (List.nodup_cons.mp (L.route_nodup hv)).1 (by simp [h])
  change run (routedBodyInverse L na ++ narrowSkywalkUnroute (narrowSkywalkRouteLayout L nr) L.b0) m₂
    (run (route++routedBody L na) m₁ s)=s
  rw [run_append,run_append]
  generalize ht : run route (m₁.take (measurementCount route)) s=t
  have tq : t.basis L.history=false := by
    have hh := routed_prepare_frame L hv nr hnr hrlen s (m₁.take (measurementCount route)) hd hc L.history (by simp)
    change (run route (m₁.take (measurementCount route)) s).basis L.history=s.basis L.history at hh
    rw [ht] at hh
    exact hh.trans hq
  have tk : regValue L.carry t.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hk
    intro q hq
    have hh := routed_prepare_frame L hv nr hnr hrlen s (m₁.take (measurementCount route)) hd hc q (by simp [hq])
    change (run route (m₁.take (measurementCount route)) s).basis q=s.basis q at hh
    rw [ht] at hh
    exact hh
  have hb := routedBody_roundtrip L hv na hna halen t
    (m₁.drop (measurementCount route)) (m₂.take (measurementCount (routedBodyInverse L na))) tq tk
  rw [hb]
  have hr := narrowSkywalkRoute_roundtrip _ (narrowSkywalkRoute_valid L hv nr hnr hrlen) L.b0 hgb s
    (m₁.take (measurementCount route)) (m₂.drop (measurementCount (routedBodyInverse L na))) hd hc
  rw [ht] at hr
  exact hr


theorem narrowSkywalkRoutedTick_counts (L : SkywalkIntegerLayout) (hv : L.Valid) (nr na : Nat)
    (hnr : 2≤nr) (hrlen : nr≤L.a.length) (hna : 0<na) (halen : na≤L.half.length) :
    toffoliCount (narrowSkywalkRoutedTick L nr na)=(nr-1)+(na-1) ∧
    measurementCount (narrowSkywalkRoutedTick L nr na)=na ∧
    toffoliCount (narrowSkywalkRoutedUntick L nr na)=(nr-1)+(na-1) ∧
    measurementCount (narrowSkywalkRoutedUntick L nr na)=na := by
  let R := narrowSkywalkRouteLayout L nr
  have hvR := narrowSkywalkRoute_valid L hv nr hnr hrlen
  have hr := narrowSkywalkRoute_counts R hvR L.b0
  have hs := narrowSkywalkSwap_counts R hvR
  have hx : R.xlow.length=nr-2 := by
    have hl : L.a.length=L.ah.length+1 := by simp [SkywalkIntegerLayout.a]
    simp only [R,narrowSkywalkRouteLayout,List.length_take]
    omega
  dsimp only [R] at hr hs hx
  have ha := narrowSignedRecord_counts (narrowSkywalkRecordLayout L na) na
    (narrowSkywalkRecord_widths L hv na hna halen)
  have hh := skywalkSignedHalf_counts L.aSign L.ext
  simp only [narrowSkywalkRoutedTick,narrowSkywalkRoutedUntick,routedBodyInverse,
    narrowSkywalkUnroute,toffoliCount_append,measurementCount_append,
    hr.1,hr.2,hs.1,hs.2,ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hh.1,hh.2,hx,
    toffoliCount,measurementCount]
  and_intros <;> first | rfl | trivial | omega

private theorem routed_route_support (L : SkywalkIntegerLayout) (hv : L.Valid) (nr : Nat)
    (hnr : 2≤nr) (hrlen : nr≤L.a.length) :
    wires (narrowSkywalkRoute (narrowSkywalkRouteLayout L nr) L.b0)⊆L.wires.toFinset ∧
    wires (narrowSkywalkUnroute (narrowSkywalkRouteLayout L nr) L.b0)⊆L.wires.toFinset := by
  let R := narrowSkywalkRouteLayout L nr
  have hvR := narrowSkywalkRoute_valid L hv nr hnr hrlen
  have vv := narrowSkywalkRoute_views L hv nr hnr hrlen
  have hs := narrowSkywalkRoute_support R hvR L.b0
  have ha : (L.b0::R.wires).toFinset⊆L.wires.toFinset := by
    intro q hq
    have hm := narrowSkywalkRoute_delta_mem L hv
    dsimp only [R] at hq
    simp only [NarrowSkywalkSwapLayout.wires,vv.1,vv.2] at hq
    change q∈(L.b0::L.a0::L.carry.headD 0::(L.ah++L.bh)).toFinset at hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    rcases hq with he|he|he|he
    · subst q; simp
    · subst q; simp
    · subst q; tauto
    · tauto
  have hswap := narrowSkywalkSwap_support R hvR
  constructor
  · exact hs.trans ha
  · intro q hq
    simp only [narrowSkywalkUnroute,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · apply ha
      simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.notMem_empty,or_false] at hq
      simp only [List.mem_toFinset,List.mem_cons,NarrowSkywalkSwapLayout.wires]
      tauto
    · exact ha (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hswap hq))))

/-- Both actual new directions remain inside the existing rail/history/carry
layout. Borrowing the already-zero carry head adds no physical site. -/
theorem narrowSkywalkRoutedTick_support (L : SkywalkIntegerLayout) (hv : L.Valid) (nr na : Nat)
    (hnr : 2≤nr) (hrlen : nr≤L.a.length) (hna : 0<na) (halen : na≤L.half.length) :
    wires (narrowSkywalkRoutedTick L nr na)⊆L.wires.toFinset ∧
    wires (narrowSkywalkRoutedUntick L nr na)⊆L.wires.toFinset := by
  have hroute := routed_route_support L hv nr hnr hrlen
  have hold := narrowSkywalkTick_wires_subset L hv na hna halen
  have hbody : wires (routedBody L na)⊆L.wires.toFinset := by
    intro q hq
    apply hold.1
    simp only [narrowSkywalkTick,routedBody,wires_append,Finset.mem_union] at hq ⊢
    tauto
  have hbodyInverse : wires (routedBodyInverse L na)⊆L.wires.toFinset := by
    intro q hq
    apply hold.2
    simp only [narrowSkywalkUntick,routedBodyInverse,wires_append,Finset.mem_union] at hq ⊢
    tauto
  change wires (_++routedBody L na)⊆_ ∧ wires (routedBodyInverse L na++_)⊆_
  simp only [wires_append,Finset.union_subset_iff]
  exact ⟨⟨hroute.1,hbody⟩,hbodyInverse,hroute.2⟩

end ECDSAAdd.Arithmetic
