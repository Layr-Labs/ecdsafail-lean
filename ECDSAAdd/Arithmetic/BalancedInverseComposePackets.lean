import ECDSAAdd.Arithmetic.BalancedInverseComposeSeed

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

/-- Result-sign selectors reconstruct precisely the original raw controls. -/
theorem recoverSelectors_raw (L : Layout) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hh : s.basis L.rmsb=decide (halfResult T<0))
    (hl : s.basis L.lower=false) (hm : s.basis L.minus=false)
    (hu : s.basis L.plus=false) :
    run (recoverSelectors L) m s=⟨s.phase,
      writeBit (writeBit (writeBit s.basis L.minus (minusController T))
        L.plus (plusController T)) L.lower (decide (T<0))⟩ := by
  have h := recoverSelectors_run L hn (originalParity T) (decide (halfResult T<0))
    s m hp hh hl hm hu
  rw [halfResult_sign T ht] at h
  have minus : (originalParity T && !(decide (T<0) ^^ originalParity T))=minusController T := by
    unfold minusController
    cases originalParity T <;> cases decide (T<0) <;> rfl
  have plus : (originalParity T && (decide (T<0) ^^ originalParity T))=plusController T := by
    unfold plusController
    cases originalParity T <;> cases decide (T<0) <;> rfl
  have low : ((decide (T<0) ^^ originalParity T) ^^ originalParity T)=decide (T<0) := by
    cases originalParity T <;> cases decide (T<0) <;> rfl
  simpa only [minus,plus,low] using h

/-- A selector packet exposes all physical controls and its full frame. -/
theorem recoverSelectors_packet (L : Layout) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T)
    (hh : s.basis L.rmsb=decide (halfResult T<0))
    (hl : s.basis L.lower=false) (hm : s.basis L.minus=false)
    (hu : s.basis L.plus=false) :
    let t := run (recoverSelectors L) m s
    t.phase=s.phase ∧ t.basis L.lower=decide (T<0) ∧
    t.basis L.minus=minusController T ∧ t.basis L.plus=plusController T ∧
    ∀a,a≠L.lower → a≠L.minus → a≠L.plus → t.basis a=s.basis a := by
  dsimp only
  rw [recoverSelectors_raw L hn T ht s m hp hh hl hm hu]
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [writeBit]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · intro a hl hm hu; simp [writeBit,hl,hm,hu]

/-- Inverse preparation provides all selector zeros, phase restoration and
an outside-target frame in one packet. -/
theorem undoPreparation_packet (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (ht : -(2*q)≤T ∧ T≤2*q) (s : State) (m : List Bool)
    (hp : s.basis L.parity=originalParity T) (hr : s.basis L.r0=false)
    (hl : s.basis L.lower=decide (T<0))
    (hm : s.basis L.minus=minusController T) (hu : s.basis L.plus=plusController T)
    (hword : regValue (foldTarget L) s.basis=toggledWord T/2) :
    let t := run (undoPreparation L) m s
    t.phase=s.phase ∧ regValue (rawTarget L) t.basis=encodeWord 257 T ∧
    t.basis L.lower=false ∧ t.basis L.minus=false ∧ t.basis L.plus=false ∧
    ∀a,a∉rawTarget L → a≠L.lower → a≠L.minus → a≠L.plus → t.basis a=s.basis a := by
  dsimp only
  have actual := undoPreparation_run L hn (originalParity T) (decide (T<0)) s m
    hp (prepared_one L hw T ht s hword) hr hl hm hu
  have value := undoPreparation_word L hw hn T ht s m hp hr hl hm hu hword
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  refine ⟨?_,value,?_,?_,?_,?_⟩
  · rw [actual]
  · rw [actual]; simp_all [writeBit,Function.update]
  · rw [actual]; simp_all [writeBit,Function.update]
  · rw [actual]; simp_all [writeBit,Function.update]
  · intro a ha hl hm hu
    have ar : a≠L.r0 := fun e => ha (by simp [rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,←e])
    have ao : a≠L.one := fun e => ha (by simp [rawTarget,←e])
    rw [actual]
    simp [writeBit,ar,ao,hl,hm,hu]

/-- Once the restored raw word is centered, the genuine reverse seed
cleans its three sites and preserves every other physical wire. -/
theorem unseed_packet (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (s : State) (m : List Bool)
    (hr : signedRegValue (rawTarget L) s.basis=X)
    (hy : signedRegValue L.y s.basis=Y)
    (hg : s.basis L.sourceGuard=s.basis L.ymsb)
    (hp : s.basis L.parity=originalParity (rawSum B X Y)) :
    let t := run (seedViews L).reverse m s
    t.phase=s.phase ∧ t.basis L.sourceGuard=false ∧ t.basis L.one=false ∧
    t.basis L.parity=false ∧ ∀a,a≠L.sourceGuard → a≠L.one → a≠L.parity → t.basis a=s.basis a := by
  dsimp only
  have corr := unseed_correlations L hw B X Y hx s hr hy hg hp
  have actual := unseed_run L hw hn s m hg corr.1 corr.2
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rw [actual]
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [writeBit]
  · simp_all [writeBit,Function.update]
  · simp_all [writeBit,Function.update]
  · intro a hg ho hp; simp [writeBit,hg,ho,hp]

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.recoverSelectors_raw
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.undoPreparation_packet
#print axioms ECDSAAdd.Arithmetic.BalancedInverse.unseed_packet
