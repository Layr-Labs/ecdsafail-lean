import ECDSAAdd.Arithmetic.KaliskiLoopResources

namespace ECDSAAdd.Arithmetic

/-- 第一阶段的共享状态；两位历史记录单独由 TapeValues 描述。 -/
structure LoopState (L : KaliskiRoundLayout) (z : KState) (st : BasisState) : Prop where
  data : RoundValues L.data (roundDataValues z) st
  k : regValue L.k st=z.k
  next : regValue L.kNext st=0
  y : regValue L.counter.y st=0
  carry : regValue L.counter.carry st=0
  active : st L.active=false
  done : st L.done=decide (z.v=0)
  odd : st L.oddWork=false
  both : st L.bothWork=false
  cin : st L.compareCin=false

namespace LoopState

theorem round_before (L : KaliskiRoundLayout) (r : RoundRecord) (z : KState) (S T : Bool)
    (st : BasisState) (h : LoopState L z st) (hs : st r.swap=S) (ht : st r.subtract=T) :
    RoundState (L.withRecord r) z z.k 0 false (decide (z.v=0)) S T st :=
  ⟨h.data,h.k,h.next,h.y,h.carry,h.active,h.done,hs,ht,h.odd,h.both,h.cin⟩

theorem of_round_before (L : KaliskiRoundLayout) (r : RoundRecord) (z : KState) (S T : Bool)
    (st : BasisState) (h : RoundState (L.withRecord r) z z.k 0 false (decide (z.v=0)) S T st) :
    LoopState L z st := ⟨h.1,h.2.k,h.2.next,h.2.y,h.2.carry,h.2.active,h.2.done,h.2.odd,h.2.both,h.2.cin⟩

theorem round_after (L : KaliskiRoundLayout) (r : RoundRecord) (z : KState) (S T : Bool)
    (st : BasisState) (h : LoopState L.swapCounter z st) (hs : st r.swap=S) (ht : st r.subtract=T) :
    RoundState (L.withRecord r) z 0 z.k false (decide (z.v=0)) S T st := by
  have hc := L.counter.swapCounter_fields
  have hk := h.k
  have hn := h.next
  have hy := h.y
  have hcarry := h.carry
  change regValue L.swapCounter.counter.x st=z.k at hk
  change regValue L.swapCounter.counter.out st=0 at hn
  rw [L.swapCounter_counter,hc.1] at hk
  rw [L.swapCounter_counter,hc.2.1] at hn
  rw [L.swapCounter_counter,hc.2.2.1] at hy
  rw [L.swapCounter_counter,hc.2.2.2.1] at hcarry
  exact ⟨h.data,hn,hk,hy,hcarry,h.active,h.done,hs,ht,h.odd,h.both,h.cin⟩

theorem of_round_after (L : KaliskiRoundLayout) (r : RoundRecord) (z : KState) (S T : Bool)
    (st : BasisState) (h : RoundState (L.withRecord r) z 0 z.k false (decide (z.v=0)) S T st) :
    LoopState L.swapCounter z st := by
  have hc := L.counter.swapCounter_fields
  refine ⟨h.1,?_,?_,?_,?_,h.2.active,h.2.done,h.2.odd,h.2.both,h.2.cin⟩
  · change regValue L.swapCounter.counter.x st=z.k
    rw [L.swapCounter_counter,hc.1]; exact h.2.next
  · change regValue L.swapCounter.counter.out st=0
    rw [L.swapCounter_counter,hc.2.1]; exact h.2.k
  · rw [L.swapCounter_counter,hc.2.2.1]; exact h.2.y
  · rw [L.swapCounter_counter,hc.2.2.2.1]; exact h.2.carry

end LoopState

/-- 一轮在共享状态与当前记录对上的接口；便于固定长度归纳。 -/
theorem kaliskiRound_tape (L : KaliskiRoundLayout) (r : RoundRecord) (rs : List RoundRecord)
    (hnd : (L.tapeWires (r::rs)).Nodup) (hw : L.counter.width=10)
    (i p a : Nat) (z : KState) (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    Triple (fun st => LoopState L z st ∧ st r.swap=false ∧ st r.subtract=false)
      (kaliskiRound (L.withRecord r) i)
      (fun st => LoopState L.swapCounter (kaliskiStep z) st ∧
        st r.swap=(kaliskiCode z).1 ∧ st r.subtract=(kaliskiCode z).2) := by
  intro s m h
  have hs := h.1.round_before L r z false false s.basis h.2.1 h.2.2
  have hp' := (roundState_iff (L.withRecord r) z z.k 0 _ _ _ s.basis).mp hs
  obtain ⟨hphase,hout⟩ := kaliskiRound_spec (L.withRecord r) (L.withRecord_nodup r rs hnd) hw i p a z
    hi hk hinv hp hu hv s m hp'
  have he := (roundState_iff (L.withRecord r) (kaliskiStep z) 0 (kaliskiStep z).k _ _ _ _).mpr hout
  exact ⟨hphase,LoopState.of_round_after L r _ _ _ _ he,he.2.swap,he.2.subtract⟩

theorem kaliskiUnround_tape (L : KaliskiRoundLayout) (r : RoundRecord) (rs : List RoundRecord)
    (hnd : (L.tapeWires (r::rs)).Nodup) (hw : L.counter.width=10)
    (i p a : Nat) (z : KState) (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    Triple (fun st => LoopState L.swapCounter (kaliskiStep z) st ∧
        st r.swap=(kaliskiCode z).1 ∧ st r.subtract=(kaliskiCode z).2)
      (kaliskiUnround (L.withRecord r) i)
      (fun st => LoopState L z st ∧ st r.swap=false ∧ st r.subtract=false) := by
  intro s m h
  have hs := h.1.round_after L r (kaliskiStep z) _ _ s.basis h.2.1 h.2.2
  have hp' := (roundState_iff (L.withRecord r) (kaliskiStep z) 0 (kaliskiStep z).k _ _ _ s.basis).mp hs
  obtain ⟨hphase,hout⟩ := kaliskiUnround_spec (L.withRecord r) (L.withRecord_nodup r rs hnd) hw i p a z
    hi hk hinv hp hu hv s m hp'
  have he := (roundState_iff (L.withRecord r) z z.k 0 _ _ _ _).mpr hout
  exact ⟨hphase,LoopState.of_round_before L r _ _ _ _ he,he.2.swap,he.2.subtract⟩

end ECDSAAdd.Arithmetic
