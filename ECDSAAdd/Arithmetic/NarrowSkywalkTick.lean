import ECDSAAdd.Arithmetic.SkywalkIntegerTick
import ECDSAAdd.Arithmetic.SkywalkIntegerLoop
import ECDSAAdd.Arithmetic.NarrowSignedRecord
import ECDSAAdd.Math.SkywalkSumWidth

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace ECDSAAdd.Arithmetic

private theorem narrow_take_msb (r : List Wire) (n : Nat) (hn : 0 < n) (hle : n ≤ r.length) :
    r.take (n-1)++[r.getD (n-1) 0]=r.take n := by
  have hidx : n-1 < r.length := by omega
  have he : n=(n-1)+1 := by omega
  conv_rhs => rw [he]
  rw [List.getD_eq_getElem _ _ hidx,List.take_add_one,List.getElem?_eq_getElem hidx]
  rfl

/-- The full258-bit route and half remain unchanged. Only post-half arithmetic
uses the retained signed prefix and Clifford high-sign restoration. -/
def narrowSkywalkRecordLayout (L : SkywalkIntegerLayout) (n : Nat) : NarrowSignedRecordLayout :=
  { xlo:=L.half.take (n-1),ylo:=L.b.take (n-1),
    sx:=L.half.getD (n-1) 0,sy:=L.b.getD (n-1) 0,q:=L.history,
    xhigh:=L.half.drop n,yhigh:=L.b.drop n,
    carryLow:=L.carry.take (n-1),carryHigh:=L.carry.drop (n-1) }

theorem narrowSkywalkRecord_views (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) :
    (narrowSkywalkRecordLayout L n).x=L.half ∧
    (narrowSkywalkRecordLayout L n).y=L.b ∧
    (narrowSkywalkRecordLayout L n).carry=L.carry := by
  have hl := L.record_lengths hv
  have hx := narrow_take_msb L.half n hn hle
  have hy := narrow_take_msb L.b n hn (by omega)
  simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.x,NarrowSignedRecordLayout.y,
    NarrowSignedRecordLayout.carry,NarrowSignedRecordLayout.xp,NarrowSignedRecordLayout.yp]
  rw [hx,hy,List.take_append_drop,List.take_append_drop,List.take_append_drop]
  exact ⟨rfl,rfl,rfl⟩

theorem narrowSkywalkRecord_widths (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) : (narrowSkywalkRecordLayout L n).Widths n := by
  have hl := L.record_lengths hv
  constructor
  · simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.xp,List.length_append,
      List.length_singleton,List.length_take]
    omega
  · simp only [narrowSkywalkRecordLayout,NarrowSignedRecordLayout.yp,List.length_append,
      List.length_singleton,List.length_take]
    omega
  · simp only [narrowSkywalkRecordLayout,List.length_take]
    omega

theorem narrowSkywalkRecord_nodup (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) : (narrowSkywalkRecordLayout L n).wires.Nodup := by
  have hf := narrowSkywalkRecord_views L hv n hn hle
  simp only [NarrowSignedRecordLayout.wires,hf.1,hf.2.1,hf.2.2]
  exact L.record_nodup hv

def narrowSkywalkTick (L : SkywalkIntegerLayout) (n : Nat) : Program :=
  skywalkRoute L.a0 L.b0 L.ah L.bh ++ skywalkSignedHalf L.aSign L.ext ++
    narrowSignedRecord (narrowSkywalkRecordLayout L n) n ++ [.CX L.previous L.a0]

def narrowSkywalkUntick (L : SkywalkIntegerLayout) (n : Nat) : Program :=
  [.CX L.previous L.a0] ++ narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n ++
    skywalkSignedHalf L.aSign L.ext ++ [.CX L.a0 L.b0] ++ swapRegisters L.a0 L.ah L.bh

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

private theorem tick_run (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat) (s : State) (m : List Bool) :
    run (narrowSkywalkTick L n) m s=
      run [.CX L.previous L.a0] m
        (run (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) m
          (run (skywalkSignedHalf L.aSign L.ext) m
            (run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s))) := by
  have hr := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv)).2
  have hh := (skywalkSignedHalf_counts L.aSign L.ext).2
  simp only [narrowSkywalkTick,List.append_assoc]
  rw [prefix_no_measure _ _ hr,prefix_no_measure _ _ hh,
    suffix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0)]


/-- Full-State equality of independently measured wide and retained-prefix
records. High target sign extension is an actual Clifford fanout. -/
theorem narrowSkywalkRecord_eq (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (A B : Int)
    (ha0 : -((2^(n-1):Nat):Int) ≤ A) (ha1 : A < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ B) (hb1 : B < ((2^(n-1):Nat):Int))
    (s : State) (m₁ m₂ : List Bool)
    (hi : SignedRecordValues L.history L.half L.b L.carry A B false s.basis) :
    run (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) m₁ s=
      run (signedRecord L.ext L.bSign L.history L.half L.b L.carry) m₂ s := by
  have hw := narrowSkywalkRecord_widths L hv n hn hle
  have hd := narrowSkywalkRecord_nodup L hv n hn hle
  have vv := narrowSkywalkRecord_views L hv n hn hle
  have hl := L.record_lengths hv
  have hs := narrowSignedRecord_spec (narrowSkywalkRecordLayout L n) n hw hd A B
    ha0 ha1 hb0 hb1 s m₁
  simp only [vv.1,vv.2.1,vv.2.2] at hs
  obtain ⟨ps,vs⟩ := hs hi
  obtain ⟨pw,vw⟩ := signedRecord_spec L.ah (L.b0::L.bMid) L.ext L.bSign L.history
    L.carry (L.record_nodup hv) hl.1 hl.2 A B s m₂ hi
  apply congrArg₂ State.mk
  · exact ps.trans pw.symm
  · funext a
    by_cases hq : a=L.history
    · subst a
      exact vs.1.trans vw.1.symm
    by_cases hx : a∈L.half
    · exact (signedRegValue_eq_iff _ _ _).mp (vs.2.1.trans vw.2.1.symm) a hx
    by_cases hy : a∈L.b
    · exact (signedRegValue_eq_iff _ _ _).mp (vs.2.2.1.trans vw.2.2.1.symm) a hy
    by_cases hc : a∈L.carry
    · exact (regValue_eq_iff _ _ _).mp (vs.2.2.2.trans vw.2.2.2.symm) a hc
    have hsframe := (narrowSignedRecord_frame (narrowSkywalkRecordLayout L n) n hw s m₁ a)
    have hnot : a∉(narrowSkywalkRecordLayout L n).wires := by
      simp only [NarrowSignedRecordLayout.wires,vv.1,vv.2.1,vv.2.2,
        List.mem_cons,List.mem_append]
      tauto
    have hwframe := signedRecord_frame L.ah (L.b0::L.bMid) L.ext L.bSign L.history
      L.carry hl.1 hl.2 s m₂ a
    exact (hsframe hnot).1.trans ((hwframe (by
      change a∉L.history::(L.half++L.b++L.carry)
      simp only [List.mem_cons,List.mem_append]
      tauto)).1.symm)

/-- The unchanged route/half prefix presents bounded H/O to the narrow adder. -/
theorem narrowSkywalkTick_eq (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (A B : Int) (G : Bool)
    (hp : (A+B)%2=1)
    (ha0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(n-1):Nat):Int))
    (s : State) (m : List Bool) (hin : SkywalkIntegerInput L A B G s.basis) :
    run (narrowSkywalkTick L n) m s=run (skywalkIntegerTick L) m s := by
  let E := (SkywalkRails.route A B).1
  let O := (SkywalkRails.route A B).2
  let H := E/2
  let t := run (skywalkRoute L.a0 L.b0 L.ah L.bh) m s
  let u := run (skywalkSignedHalf L.aSign L.ext) m t
  have he : E%2=0 := SkywalkRails.route_even A B hp
  obtain ⟨_,hE,hO,_⟩ := route_int_values L hv A B hp s m hin.1 hin.2.1 hin.2.2.2.1
  change signedRegValue (L.ext::(L.aMid++[L.aSign])) t.basis=E at hE
  have tq : t.basis L.history=false :=
    (route_aux_frame L hv s m L.history (by simp)).trans hin.2.2.2.2.1
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
  have uk : regValue L.carry u.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) tk
    intro q hq
    exact half_aux_frame L hv t m q (by simp [hq])
  have hr := narrowSkywalkRecord_eq L hv n hn hle H O ha0 ha1 hb0 hb1 u m m ⟨uq,uH,uO,uk⟩
  rw [tick_run L hv n s m,hr]
  have hmR := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv)).2
  have hmH := (skywalkSignedHalf_counts L.aSign L.ext).2
  simp only [skywalkIntegerTick,List.append_assoc]
  rw [prefix_no_measure _ _ hmR,prefix_no_measure _ _ hmH,
    suffix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0)]

/-- Same public mathematical output and arbitrary-record phase as the accepted
wide tick, with explicit post-half signed fit assumptions. -/
theorem narrowSkywalkTick_spec (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (A B : Int) (G : Bool)
    (hp : (A+B)%2=1)
    (ha0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).1/2)
    (ha1 : (SkywalkRails.route A B).1/2 < ((2^(n-1):Nat):Int))
    (hb0 : -((2^(n-1):Nat):Int) ≤ (SkywalkRails.route A B).2)
    (hb1 : (SkywalkRails.route A B).2 < ((2^(n-1):Nat):Int)) :
    Triple (SkywalkIntegerInput L A B G) (narrowSkywalkTick L n)
      (SkywalkIntegerOutput L A B G) := by
  intro s m hin
  rw [narrowSkywalkTick_eq L hv n hn hle A B G hp ha0 ha1 hb0 hb1 s m hin]
  exact skywalkIntegerTick_spec L hv A B G hp s m hin

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

private theorem untick_run (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat) (s : State) (m : List Bool) :
    run (narrowSkywalkUntick L n) m s=
      run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m
        (run (skywalkSignedHalf L.aSign L.ext) m
          (run (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n) m
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
  simp only [narrowSkywalkUntick,List.append_assoc]
  rw [prefix_no_measure _ _ (by rfl : measurementCount [.CX L.previous L.a0]=0),
    suffix_no_measure _ _ ht,prefix_no_measure _ _ hh]

/-- The separately emitted inverse restores the entire physical State with
independent measurement streams. Only the history/carry clean premises are
needed for reversal; signed parity/extension premises are for interpretation. -/
theorem narrowSkywalkTick_roundtrip (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) (s : State) (m₁ m₂ : List Bool) (hq : s.basis L.history=false)
    (hk : regValue L.carry s.basis=0) :
    run (narrowSkywalkUntick L n) m₂ (run (narrowSkywalkTick L n) m₁ s)=s := by
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
  have hvv := narrowSkywalkRecord_views L hv n hn hle
  have hr := narrowSignedRecord_roundtrip (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle)
    (narrowSkywalkRecord_nodup L hv n hn hle) u m₁ m₂
    (by simpa only [narrowSkywalkRecordLayout] using uq)
    (by simpa only [hvv.2.2] using uk)
  have hh : run (skywalkSignedHalf L.aSign L.ext) m₂ u=t := by
    simpa only [skywalkSignedHalf,run] using
      skywalkSignedHalf_twice L.aSign L.ext (ext_sign_ne L hv) t m₁
  rw [tick_run L hv n s m₁,untick_run L hv n _ m₂,
    cx_twice L.previous L.a0 (previous_low_ne L hv)]
  change run ([.CX L.a0 L.b0]++swapRegisters L.a0 L.ah L.bh) m₂
    (run (skywalkSignedHalf L.aSign L.ext) m₂
      (run (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n) m₂
        (run (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) m₁ u)))=s
  rw [hr,hh]
  exact route_roundtrip L hv s m₁ m₂


/-- The actual narrow adder stream has n-1 T/M; the route remains full width. -/
theorem narrowSkywalkTick_counts (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) :
    toffoliCount (narrowSkywalkTick L n)=L.ah.length+(n-1) ∧
    measurementCount (narrowSkywalkTick L n)=n-1 ∧
    toffoliCount (narrowSkywalkUntick L n)=L.ah.length+(n-1) ∧
    measurementCount (narrowSkywalkUntick L n)=n-1 := by
  have hl := L.high_lengths hv
  have hr := skywalkRoute_counts L.a0 L.b0 L.ah L.bh hl (L.route_nodup hv)
  have hnd : (L.a0::(L.ah++L.bh)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hh := List.nodup_iff_count.mp (L.route_nodup hv) q
    simp only [List.count_cons] at hh ⊢
    omega
  have hs := swapRegisters_resources L.a0 L.ah L.bh hl hnd
  have ha := narrowSignedRecord_counts (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle)
  have hh := skywalkSignedHalf_counts L.aSign L.ext
  simp only [narrowSkywalkTick,narrowSkywalkUntick,toffoliCount_append,measurementCount_append,
    hr.1,hr.2,hs.1,hs.2.1,ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,hh.1,hh.2,
    toffoliCount,measurementCount]
  omega
theorem narrowSkywalkTick_wires_subset (L : SkywalkIntegerLayout) (hv : L.Valid) (n : Nat)
    (hn : 0 < n) (hle : n ≤ L.half.length) :
    wires (narrowSkywalkTick L n)⊆L.wires.toFinset ∧
    wires (narrowSkywalkUntick L n)⊆L.wires.toFinset := by
  have hl := L.high_lengths hv
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
  have hword := narrowSignedRecord_support (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle)
  have vv := narrowSkywalkRecord_views L hv n hn hle
  have hsigned :
      wires (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) ⊆
        (L.history::(L.half++L.b++L.carry)).toFinset ∧
      wires (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n) ⊆
        (L.history::(L.half++L.b++L.carry)).toFinset := by
    simpa only [NarrowSignedRecordLayout.wires,vv.1,vv.2.1,vv.2.2,
      ] using hword
  have hown : (L.history::(L.half++L.b++L.carry)).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,
      List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
    tauto
  have hrecord : wires (narrowSignedRecord (narrowSkywalkRecordLayout L n) n)⊆L.wires.toFinset := by
    exact hsigned.1.trans hown
  have hunrecord : wires (narrowSignedUnrecord (narrowSkywalkRecordLayout L n) n)⊆L.wires.toFinset := by
    exact hsigned.2.trans hown
  have hprevious : wires [.CX L.previous L.a0]⊆L.wires.toFinset := by
    simp [SkywalkIntegerLayout.wires,wires,Instr.wires]
  have hlow : wires [.CX L.a0 L.b0]⊆L.wires.toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [narrowSkywalkTick,narrowSkywalkUntick,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨hroute,hhalf⟩,hrecord⟩,hprevious⟩,
    ⟨⟨⟨⟨hprevious,hunrecord⟩,hhalf⟩,hlow⟩,hswap⟩⟩

end ECDSAAdd.Arithmetic
