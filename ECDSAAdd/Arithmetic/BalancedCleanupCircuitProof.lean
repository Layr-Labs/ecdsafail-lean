import ECDSAAdd.Arithmetic.BalancedCleanupCircuitViews
import ECDSAAdd.Arithmetic.SkywalkArithmeticCore

set_option maxHeartbeats 900000
set_option maxRecDepth 4096
namespace ECDSAAdd.Arithmetic.BalancedCleanup
open BalancedField

def Except (a : Wire) (s t : State) : Prop :=
  s.phase=t.phase ∧ ∀q,q≠a → s.basis q=t.basis q

 theorem inverse_except (p : Program) (hp : ProperProgram p) (a : Wire)
    (ha : a∉wires p) (s t : State) (m n : List Bool)
    (he : Except a t (run p m s)) : Except a (run p.reverse n t) s := by
  have hr := run_reverse_proper p hp s m n
  have hc := run_proper_congr p.reverse (properProgram_reverse p hp)
    t (run p m s) n n he.1 (by
      intro q hq
      rw [wires_reverse] at hq
      exact he.2 q (fun e => ha (e ▸ hq)))
  refine ⟨hc.1.trans (congrArg State.phase hr),?_⟩
  intro q hqa
  by_cases hq : q∈wires p.reverse
  · exact (hc.2 q hq).trans (congrArg (fun u : State => u.basis q) hr)
  · have a1 := run_preserves_outside p.reverse n t q hq
    have a2 := run_preserves_outside p.reverse n (run p m s) q hq
    exact a1.trans ((he.2 q hqa).trans (a2.symm.trans (congrArg (fun u : State => u.basis q) hr)))

 theorem clifford_parity_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.parity∉wires (prepareSign L) ∧ L.parity∉wires (prepareCompare L) := by
  have a := L.flagAway hn L.parity (by simp)
  have af := (List.nodup_cons.mp (L.flagsND hn)).1
  have ar : L.parity∉L.r := fun h => a (by simp [h])
  have ay : L.parity∉L.y := fun h => a (by simp [h])
  have acL : L.parity∉wires (signComplement L.lower L.r) := by
    intro h; have hh := signComplement_wires_subset L.lower L.r h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact af (by simp [h])
    · exact ar h
  have acS : L.parity∉wires (signComplement L.sign L.y) := by
    intro h; have hh := signComplement_wires_subset L.sign L.y h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact af (by simp [h])
    · exact ay h
  have acY : L.parity∉wires (signComplement L.lower L.y) := by
    intro h; have hh := signComplement_wires_subset L.lower L.y h
    simp only [List.mem_toFinset,List.mem_cons] at hh
    rcases hh with h|h
    · exact af (by simp [h])
    · exact ay h
  have rot : L.parity∉wires (rotateLeft L.r) := by
    rw [(rotate_wires L.r).2,(widths L hw).2.1]
    simpa using ar
  have ar0 : L.parity≠L.r0 := fun e => ar (by simp [Layout.r,Layout.low,e])
  have arm : L.parity≠L.rmsb := fun e => ar (by simp [Layout.r,e])
  have aym : L.parity≠L.ymsb := fun e => ay (by simp [Layout.y,e])
  have asl : L.parity≠L.sign ∧ L.parity≠L.lower := by
    simp only [List.mem_cons,not_or] at af
    tauto
  simp [prepareSign,prepareCompare,wires_append,wires,Instr.wires,
    acL,acS,acY,rot,ar0,arm,aym,asl.1,asl.2]

 theorem unnormalize_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    let t := run (unnormalize L) m s
    t.phase=s.phase ∧
    regValue L.low t.basis=(regValue L.low s.basis+positiveLiteral+(!s.basis L.lower).toNat)%2^255 ∧
    ∀q,q∉L.low → t.basis q=s.basis q := by
  let u : State := ⟨s.phase,writeBit s.basis L.lower (!s.basis L.lower)⟩
  have nd := L.normND hn
  have la : L.lower∉L.low := fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])
  have ol : L.one≠L.lower := by
    intro e; exact (List.nodup_cons.mp nd).1 (by simp [e])
  have cl (q : Wire) (hq : q∈L.carry) : q≠L.lower := by
    intro e; exact L.flagAway hn L.lower (by simp) (by simp [←e,hq])
  have clean : ∀q∈L.carry.take 254,u.basis q=false := by
    intro q hq; simp [u,writeBit,cl q (List.mem_of_mem_take hq),hc q (List.mem_of_mem_take hq)]
  have hu : regValue L.low u.basis=regValue L.low s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [u,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
  have w := widths L hw
  have add := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one positiveLiteral
    nd (by omega) u m (by simp [u,writeBit,ol,ho]) clean
  let v := run (literalConstAdd L.low (L.carry.take 254) L.lower L.one positiveLiteral) m u
  have vl : v.basis L.lower=!s.basis L.lower := by rw [add.2.1 L.lower la]; simp [u,writeBit]
  have execute : run (unnormalize L) m s=run [.X L.lower]
      (m.drop (measurementCount (literalConstAdd L.low (L.carry.take 254) L.lower L.one positiveLiteral))) v := by
    simp only [unnormalize,List.append_assoc,run_append,run_take,measurementCount,List.drop_zero]
    rfl
  rw [execute]
  refine ⟨add.1,?_,?_⟩
  · have last (ms : List Bool) : regValue L.low (run [.X L.lower] ms v).basis=regValue L.low v.basis :=
      regValue_congr _ _ _ (fun q hq => by simp [run,writeBit,show q≠L.lower from fun e => la (e ▸ hq)])
    rw [last,add.2.2,hu,w.1]
    simp [u,writeBit]
  · intro q hq
    by_cases e : q=L.lower
    · subst q
      have hx (ms : List Bool) : (run [.X L.lower] ms v).basis L.lower=!v.basis L.lower := by
        simp only [run,writeBit,Function.update_self]
      rw [hx,vl]
      simp
    · simp only [run,writeBit,Function.update_of_ne e]
      exact (add.2.1 q hq).trans (by simp [u,writeBit,e])

 theorem literals_sum : negativeLiteral+positiveLiteral+1=2^255 := by
  have hp := constants
  have hh := Int.toNat_of_nonneg (show 0≤h by omega)
  have hl := Int.toNat_of_nonneg (show 0≤h-1 by omega)
  have hb : h.toNat≤2^255 := by norm_num at ⊢; omega
  rw [negativeLiteral_value]
  unfold positiveLiteral
  omega

 theorem states (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State)
    (m1 m2 m3 m4 m5 m6 m7 : List Bool) (s1 s2 s3 s4 s5 s6 s7 : State)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false)
    (hA : s.basis L.parity=decide (q < |2*R-signedY B Y|))
    (hs1 : run (prepareSign L) m1 s=s1) (hs2 : run (normalize L) m2 s1=s2)
    (hs3 : run (prepareCompare L) m3 s2=s3)
    (hs4 : run (compareLt none L.y L.r L.carry L.one L.parity) m4 s3=s4)
    (hs5 : run (prepareCompare L).reverse m5 s4=s5)
    (hs6 : run (unnormalize L) m6 s5=s6) (hs7 : run (prepareSign L).reverse m7 s6=s7) :
    Except L.parity s7 s ∧ s7.basis L.parity=false := by
  have w := widths L hw
  have nd := L.normND hn
  have flags := L.flagsND hn
  have pa := clifford_parity_away L hw hn
  have ar : L.parity∉L.r := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have ay : L.parity∉L.y := fun h => L.flagAway hn L.parity (by simp) (by simp [h])
  have al : L.parity≠L.lower := by have hh := (List.nodup_cons.mp flags).1; simp at hh; tauto
  have oa : L.one∉L.r := fun h => L.flagAway hn L.one (by simp) (by simp [h])
  have ol : L.one≠L.lower := by have hh := List.nodup_iff_count.mp flags L.one; simp [List.count_cons] at hh; intro e; simp [e] at hh; omega
  have sy : L.sign∉L.r := fun h => L.flagAway hn L.sign (by simp) (by simp [h])
  have sl : L.sign≠L.lower := by have hh := List.nodup_iff_count.mp flags L.sign; simp [List.count_cons] at hh; intro e; simp [←e] at hh; omega
  have ca (q : Wire) (hq : q∈L.carry) : q∉L.r ∧ q≠L.lower := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact ⟨fun h => List.disjoint_left.mp d.2.2 h (by simp [hq]),
      fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])⟩
  have v1 := prepareSign_value L hw hn R hr s m1 hR hz
  rw [hs1] at v1
  have one1 : s1.basis L.one=false := (v1.2.2 _ oa ol).trans ho
  have clean1 : ∀q∈L.carry,s1.basis q=false := fun q hq => (v1.2.2 q (ca q hq).1 (ca q hq).2).trans (hc q hq)
  have Y1 : regValue L.y s1.basis=encodeWord 256 Y := by
    have d := List.nodup_append'.mp (L.dataND hn)
    exact (regValue_congr _ _ _ (fun q hq => v1.2.2 q
      (fun r => List.disjoint_left.mp d.2.2 r (by simp [hq]))
      (fun e => L.flagAway hn L.lower (by simp) (by simp [←e,hq])))).trans hY
  have rm0 : s1.basis L.rmsb=false := by
    have hi := regValue_highBit L.low L.rmsb s1.basis
    rw [w.1] at hi
    change s1.basis L.rmsb=true ↔ 2^255≤regValue L.r s1.basis at hi
    rw [v1.1] at hi
    have b := magnitude_bounds R hr; have p := constants
    have cast := Int.toNat_of_nonneg b.1
    cases e : s1.basis L.rmsb
    · rfl
    · simp [e] at hi
      omega
  have low1 : regValue L.low s1.basis=(magnitude R).toNat := by
    have h := v1.1; rw [Layout.r,regValue_append] at h; simpa [regValue,rm0] using h
  have v2 := normalize_value L hw hn R hr s1 m2 low1 v1.2.1 one1 clean1
  rw [hs2] at v2
  have rmAway : L.rmsb∉L.low := by have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).1; exact fun h => List.disjoint_left.mp d.2.2 h (by simp)
  have R2 : regValue L.r s2.basis=encodeWord 255 (normalizedR R) := by
    rw [Layout.r,regValue_append,v2.2.1]; simp [regValue,v2.2.2 _ rmAway,rm0]
  have Y2 : regValue L.y s2.basis=encodeWord 256 Y := by
    exact (regValue_congr _ _ _ (fun q hq => v2.2.2 q (by
      intro hl; exact List.disjoint_left.mp (List.nodup_append'.mp (L.dataND hn)).2.2
        (show q∈L.r from by simp [Layout.r,hl])
        (show q∈L.y++L.carry from by simp [hq])))).trans Y1
  have S2 : s2.basis L.sign=B := (v2.2.2 _ (fun h => sy (by simp [Layout.r,h]))).trans ((v1.2.2 _ sy sl).trans hS)
  have L2 : s2.basis L.lower=negative R := (v2.2.2 _ (fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h]))).trans v1.2.1
  have v3 := prepareCompare_value L hw hn R Y B hr hy s2 m3 R2 Y2 S2 L2
  rw [hs3] at v3
  have frame2 (q : Wire) (hq : q∉L.r) : s2.basis q=s1.basis q := v2.2.2 q (fun h => hq (by simp [Layout.r,h]))
  have one3 : s3.basis L.one=false := (v3.2.2 _ oa (fun h => L.flagAway hn L.one (by simp) (by simp [h]))).trans ((frame2 _ oa).trans one1)
  have clean3 : ∀q∈L.carry,s3.basis q=false := by
    intro q hq; have d := List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).2.1
    exact (v3.2.2 q (ca q hq).1 (fun hyq => List.disjoint_left.mp d.2.2 hyq hq)).trans ((frame2 q (ca q hq).1).trans (clean1 q hq))
  have cmp := compareLt_correct none L.y L.r L.carry L.one L.parity (L.compareND hn)
    (by simp) (by omega) (by unfold Layout.Widths at hw; omega) s3 m4 one3 clean3
  rw [hs4] at cmp
  have pred : decide (regValue L.y s3.basis<regValue L.r s3.basis)=decide (q < |2*R-signedY B Y|) := by
    apply decide_eq_decide.mpr
    have interval := cleanup_interval_identity B R Y hr hy
    omega
  have A3 : s3.basis L.parity=s.basis L.parity := (v3.2.2 _ ar ay).trans ((frame2 _ ar).trans (v1.2.2 _ ar al))
  have A4 : s4.basis L.parity=false := by rw [cmp.2.2,A3,pred,hA]; simp [controlValue]
  have ex5 := inverse_except (prepareCompare L) (prepareCompare_proper L hn) L.parity pa.2 s2 s4 m3 m5 (by rw [hs3]; exact ⟨cmp.1,cmp.2.1⟩)
  rw [hs5] at ex5
  have one5 : s5.basis L.one=false := (ex5.2 _ (by intro e; have hh := (List.nodup_cons.mp flags).1; exact hh (by simp [←e]))).trans ((frame2 _ oa).trans one1)
  have clean5 : ∀q∈L.carry,s5.basis q=false := by
    intro q hq; exact (ex5.2 q (fun e => L.flagAway hn L.parity (by simp) (by simp [←e,hq]))).trans ((frame2 q (ca q hq).1).trans (clean1 q hq))
  have un := unnormalize_correct L hw hn s5 m6 one5 clean5
  rw [hs6] at un
  have raw := literalConstAdd_correct L.low (L.carry.take 254) L.lower L.one negativeLiteral nd (by omega) s1 m2 one1 (fun q hq => clean1 q (List.mem_of_mem_take hq))
  have read2 : regValue L.low s2.basis=
      (regValue L.low s1.basis+negativeLiteral+(s1.basis L.lower).toNat)%2^L.low.length := by
    rw [←hs2]
    exact raw.2.2
  have low5 : regValue L.low s5.basis=regValue L.low s2.basis := regValue_congr _ _ _ (fun q hq => ex5.2 q (fun e => ar (by simp [Layout.r,←e,hq])))
  have lower5 : s5.basis L.lower=s1.basis L.lower := (ex5.2 _ (Ne.symm al)).trans (v2.2.2 _ (fun h => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (by simp [h])))
  have low6 : regValue L.low s6.basis=regValue L.low s1.basis := by
    rw [un.2.1,low5,read2,lower5,w.1]
    have fit := regValue_lt L.low s1.basis; rw [w.1] at fit
    have sum := literals_sum
    cases b : s1.basis L.lower <;> simp only [Bool.not_false,Bool.not_true,Bool.toNat_false,Bool.toNat_true] <;> omega
  have ex6 : Except L.parity s6 s1 := by
    refine ⟨un.1.trans (ex5.1.trans v2.1),?_⟩
    intro q hq
    by_cases hl : q∈L.low
    · exact (regValue_eq_iff L.low _ _).mp low6 q hl
    · exact (un.2.2 q hl).trans ((ex5.2 q hq).trans (v2.2.2 q hl))
  have ex7 := inverse_except (prepareSign L) (prepareSign_proper L hn) L.parity pa.1 s s6 m1 m7 (by rw [hs1]; exact ex6)
  rw [hs7] at ex7
  have keep5 := run_preserves_outside (prepareCompare L).reverse m5 s4 L.parity (by rw [wires_reverse]; exact pa.2)
  have keep7 := run_preserves_outside (prepareSign L).reverse m7 s6 L.parity (by rw [wires_reverse]; exact pa.1)
  rw [hs5] at keep5; rw [hs7] at keep7
  exact ⟨ex7,keep7.trans ((un.2.2 _ (fun h => ar (by simp [Layout.r,h]))).trans (keep5.trans A4))⟩

 theorem correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R Y : Int) (B : Bool) (hr : Centered R) (hy : Centered Y) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hY : regValue L.y s.basis=encodeWord 256 Y)
    (hS : s.basis L.sign=B) (hz : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false)
    (hA : s.basis L.parity=decide (q < |2*R-signedY B Y|)) :
    run (program L) m s=⟨s.phase,writeBit s.basis L.parity false⟩ := by
  let P : State → State → Prop := fun i o =>
    regValue L.r i.basis=encodeWord 256 R → regValue L.y i.basis=encodeWord 256 Y →
    i.basis L.sign=B → i.basis L.lower=false → i.basis L.one=false →
    (∀q∈L.carry,i.basis q=false) → i.basis L.parity=decide (q < |2*R-signedY B Y|) →
    Except L.parity o i ∧ o.basis L.parity=false
  have h := skywalkRunSeven (prepareSign L) (normalize L) (prepareCompare L)
    (compareLt none L.y L.r L.carry L.one L.parity) (prepareCompare L).reverse
    (unnormalize L) (prepareSign L).reverse P
    (by intro i s1 s2 s3 s4 s5 s6 s7 m1 m2 m3 m4 m5 m6 m7 e1 e2 e3 e4 e5 e6 e7 r y b z o c a
        exact states L hw hn R Y B hr hy i m1 m2 m3 m4 m5 m6 m7 s1 s2 s3 s4 s5 s6 s7 r y b z o c a e1 e2 e3 e4 e5 e6 e7) s m
  have result : Except L.parity (run (program L) m s) s ∧ (run (program L) m s).basis L.parity=false :=
    by simpa only [program] using h hR hY hS hz ho hc hA
  apply State.extensionality
  · exact result.1.1
  · funext q
    by_cases e : q=L.parity
    · subst q; simp [writeBit,result.2]
    · simp [writeBit,e,result.1.2 q e]

end ECDSAAdd.Arithmetic.BalancedCleanup

#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.correct

#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.Except
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.inverse_except
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.clifford_parity_away
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.unnormalize_correct
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.literals_sum
#print axioms ECDSAAdd.Arithmetic.BalancedCleanup.states
