import ECDSAAdd.Arithmetic.KaliskiLoopState
import ECDSAAdd.Arithmetic.OneBitRoundResources

namespace ECDSAAdd.Arithmetic

namespace KaliskiRoundLayout

/-- 共享交换临时位与逐轮减法位；不修改旧两位记录的分配。 -/
def oneBitTapeWires (L : KaliskiRoundLayout) (sw : Wire) (ts : List Wire) : List Wire :=
  sw :: (ts ++ L.sharedWires)

theorem oneBit_round_nodup (L : KaliskiRoundLayout) (sw t : Wire) (ts : List Wire)
    (hnd : (L.oneBitTapeWires sw (t::ts)).Nodup) :
    (L.withRecord ⟨sw,t⟩).wires.Nodup := by
  apply (L.withRecord_perm ⟨sw,t⟩).nodup_iff.mpr
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  simp [oneBitTapeWires,RoundRecord.wires,List.count_cons] at h ⊢
  omega

theorem oneBit_tail_nodup (L : KaliskiRoundLayout) (sw t : Wire) (ts : List Wire)
    (hnd : (L.oneBitTapeWires sw (t::ts)).Nodup) :
    (L.swapCounter.oneBitTapeWires sw ts).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  have hp := L.shared_swap_perm.count_eq w
  simp [oneBitTapeWires,List.count_cons] at h ⊢
  omega

end KaliskiRoundLayout

/-- sw 在每轮边界归零；递归始终传同一根线路。 -/
def oneBitLoop (L : KaliskiRoundLayout) (sw : Wire) (i : Nat) : List Wire → Program
  | [] => []
  | t::ts => oneBitRound (L.withRecord ⟨sw,t⟩) i ++ oneBitLoop L.swapCounter sw (i+1) ts

def oneBitUnloop (L : KaliskiRoundLayout) (sw : Wire) (i : Nat) : List Wire → Program
  | [] => []
  | t::ts => oneBitUnloop L.swapCounter sw (i+1) ts ++ oneBitUnround (L.withRecord ⟨sw,t⟩) i

/-- 只记录 subtract；共享 swap 的零值由循环边界单独断言。 -/
def OneBitTapeValues : List Wire → List (Bool×Bool) → BasisState → Prop
  | [],[],_ => True
  | t::ts,c::cs,st => st t=c.2 ∧ OneBitTapeValues ts cs st
  | _,_,_ => False

theorem OneBitTapeValues.congr (ts : List Wire) (cs : List (Bool×Bool)) (s u : BasisState)
    (h : OneBitTapeValues ts cs s) (he : ∀ w, w∈ts → u w=s w) : OneBitTapeValues ts cs u := by
  induction ts generalizing cs with
  | nil => cases cs <;> exact h
  | cons t ts ih =>
    cases cs with
    | nil => exact h
    | cons c cs =>
      exact ⟨(he t (by simp)).trans h.1,ih cs h.2 (fun w hw => he w (by simp [hw]))⟩

/-- 一轮在共享状态与当前记录对上的接口；便于固定长度归纳。 -/
theorem oneBitRound_tape (L : KaliskiRoundLayout) (sw t : Wire) (ts : List Wire)
    (hnd : (L.oneBitTapeWires sw (t::ts)).Nodup) (hw : L.counter.width=10)
    (i p a : Nat) (z : KState) (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z) (hodd : p%2=1)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    Triple (fun st => LoopState L z st ∧ st sw=false ∧ st t=false)
      (oneBitRound (L.withRecord ⟨sw,t⟩) i)
      (fun st => LoopState L.swapCounter (kaliskiStep z) st ∧
        st sw=false ∧ st t=(kaliskiCode z).2) := by
  intro s m h
  have hs := h.1.round_before L ⟨sw,t⟩ z false false s.basis h.2.1 h.2.2
  have hp' := (roundState_iff (L.withRecord ⟨sw,t⟩) z z.k 0 _ _ _ s.basis).mp hs
  obtain ⟨hphase,hout⟩ := oneBitRound_spec (L.withRecord ⟨sw,t⟩) (L.oneBit_round_nodup sw t ts hnd) hw i p a z
    hi hk hinv hodd hp hu hv s m hp'
  have he := (roundState_iff (L.withRecord ⟨sw,t⟩) (kaliskiStep z) 0 (kaliskiStep z).k _ _ _ _).mpr hout
  exact ⟨hphase,LoopState.of_round_after L ⟨sw,t⟩ _ _ _ _ he,he.2.swap,he.2.subtract⟩

theorem oneBitUnround_tape (L : KaliskiRoundLayout) (sw t : Wire) (ts : List Wire)
    (hnd : (L.oneBitTapeWires sw (t::ts)).Nodup) (hw : L.counter.width=10)
    (i p a : Nat) (z : KState) (hi : i<512) (hk : KRoundCount i z) (hinv : KInvariant p a z) (hodd : p%2=1)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    Triple (fun st => LoopState L.swapCounter (kaliskiStep z) st ∧
        st sw=false ∧ st t=(kaliskiCode z).2)
      (oneBitUnround (L.withRecord ⟨sw,t⟩) i)
      (fun st => LoopState L z st ∧ st sw=false ∧ st t=false) := by
  intro s m h
  have hs := h.1.round_after L ⟨sw,t⟩ (kaliskiStep z) _ _ s.basis h.2.1 h.2.2
  have hp' := (roundState_iff (L.withRecord ⟨sw,t⟩) (kaliskiStep z) 0 (kaliskiStep z).k _ _ _ s.basis).mp hs
  obtain ⟨hphase,hout⟩ := oneBitUnround_spec (L.withRecord ⟨sw,t⟩) (L.oneBit_round_nodup sw t ts hnd) hw i p a z
    hi hk hinv hodd hp hu hv s m hp'
  have he := (roundState_iff (L.withRecord ⟨sw,t⟩) z z.k 0 _ _ _ _).mpr hout
  exact ⟨hphase,LoopState.of_round_before L ⟨sw,t⟩ _ _ _ _ he,he.2.swap,he.2.subtract⟩


/-- 循环只触及共享临时位、减法记录与轮共享区。 -/
theorem oneBitLoop_wires_subset (L : KaliskiRoundLayout) (sw : Wire) (ts : List Wire) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    wires (oneBitLoop L sw i ts) ⊆ (L.oneBitTapeWires sw ts).toFinset ∧
    wires (oneBitUnloop L sw i ts) ⊆ (L.oneBitTapeWires sw ts).toFinset := by
  induction ts generalizing L i with
  | nil => simp [oneBitLoop,oneBitUnloop,wires]
  | cons t ts ih =>
    have hnw : L.swapCounter.counter.width=10 := by
      rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := ih L.swapCounter (i+1) hnw hd
    have hr := oneBitRound_wires (L.withRecord ⟨sw,t⟩) hw hd i
    have roundMem (w : Wire) (h : w∈(L.withRecord ⟨sw,t⟩).usedWires.toFinset) :
        w∈(L.oneBitTapeWires sw (t::ts)).toFinset := by
      have hh := (L.withRecord ⟨sw,t⟩).usedWires_sublist.subset (List.mem_toFinset.mp h)
      have hh' := (L.withRecord_perm ⟨sw,t⟩).mem_iff.mp hh
      simp only [RoundRecord.wires,List.mem_append,List.mem_cons] at hh'
      simp only [List.mem_toFinset,KaliskiRoundLayout.oneBitTapeWires,List.mem_cons,List.mem_append]
      aesop
    have tailMem (w : Wire) (h : w∈(L.swapCounter.oneBitTapeWires sw ts).toFinset) :
        w∈(L.oneBitTapeWires sw (t::ts)).toFinset := by
      have hp : w∈L.swapCounter.sharedWires ↔ w∈L.sharedWires := L.shared_swap_perm.mem_iff
      simp only [List.mem_toFinset,KaliskiRoundLayout.oneBitTapeWires,List.mem_cons,List.mem_append] at h ⊢
      aesop
    constructor
    · intro w h
      simp only [oneBitLoop,wires_append,Finset.mem_union] at h
      exact h.elim (fun h => roundMem w (hr.1 ▸ h)) (fun h => tailMem w (ht.1 h))
    · intro w h
      simp only [oneBitUnloop,wires_append,Finset.mem_union] at h
      exact h.elim (fun h => tailMem w (ht.2 h)) (fun h => roundMem w (hr.2 ▸ h))

private theorem oneBit_partition (L : KaliskiRoundLayout) (sw t : Wire) (ts : List Wire)
    (hnd : (L.oneBitTapeWires sw (t::ts)).Nodup) :
    (t::L.swapCounter.oneBitTapeWires sw ts).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  have hp := L.shared_swap_perm.count_eq w
  simp [KaliskiRoundLayout.oneBitTapeWires,List.count_cons] at h ⊢
  omega

private theorem oneBit_rest_disjoint (L : KaliskiRoundLayout) (sw t : Wire) (ts : List Wire)
    (hnd : (L.oneBitTapeWires sw (t::ts)).Nodup) :
    ts.Disjoint (L.withRecord ⟨sw,t⟩).wires := by
  apply (List.nodup_append'.mp ?_).2.2
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  have hp := (L.withRecord_perm ⟨sw,t⟩).count_eq w
  simp [KaliskiRoundLayout.oneBitTapeWires,RoundRecord.wires,List.count_cons] at h hp ⊢
  omega

private theorem oneBit_step_uv (z : KState) : (kaliskiStep z).u≤z.u ∧ (kaliskiStep z).v≤z.v := by
  unfold kaliskiStep
  split_ifs <;> (try dsimp) <;> omega

/-- 任意固定长度的共享交换位循环：全部测量记录下正向写历史，逆向清历史。 -/
theorem oneBitLoop_correct (L : KaliskiRoundLayout) (sw : Wire) (ts : List Wire) (i p a : Nat) (z : KState)
    (hnd : (L.oneBitTapeWires sw ts).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width)
    (hlen : i+ts.length≤512) (hk : KRoundCount i z) (hinv : KInvariant p a z) (hodd : p%2=1)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    Triple (fun st => (LoopState L z st ∧ st sw=false) ∧ OneBitTapeValues ts (List.replicate ts.length (false,false)) st)
      (oneBitLoop L sw i ts)
      (fun st => (LoopState (loopEndLayout L ts.length) ((kaliskiStep^[ts.length]) z) st ∧ st sw=false) ∧ OneBitTapeValues ts (kaliskiCodes ts.length z) st) ∧
    Triple (fun st => (LoopState (loopEndLayout L ts.length) ((kaliskiStep^[ts.length]) z) st ∧ st sw=false) ∧ OneBitTapeValues ts (kaliskiCodes ts.length z) st)
      (oneBitUnloop L sw i ts)
      (fun st => (LoopState L z st ∧ st sw=false) ∧ OneBitTapeValues ts (List.replicate ts.length (false,false)) st) := by
  induction ts generalizing L i z with
  | nil => constructor <;> intro s m h <;> exact ⟨rfl,h⟩
  | cons t ts ih =>
    have hi : i<512 := by simp only [List.length_cons] at hlen; omega
    have hnw : L.swapCounter.counter.width=10 := by rw [L.swapCounter_counter,L.counter.swapCounter_fields.2.2.2.2.2,hw]
    have ht := ih L.swapCounter (i+1) (kaliskiStep z) (L.oneBit_tail_nodup sw t ts hnd) hnw hd
      (by simp only [List.length_cons] at hlen; omega) (kaliski_round_count_step i z hk)
      (kaliski_invariant p a z hinv) hp ((oneBit_step_uv z).1.trans_lt hu) ((oneBit_step_uv z).2.trans_lt hv)
    have hround := oneBitRound_tape L sw t ts hnd hw i p a z hi hk hinv hodd hp hu hv
    have hunround := oneBitUnround_tape L sw t ts hnd hw i p a z hi hk hinv hodd hp hu hv
    have hrw := oneBitRound_wires (L.withRecord ⟨sw,t⟩) hw hd i
    have htw := oneBitLoop_wires_subset L.swapCounter sw ts (i+1) hnw hd
    have hdis := oneBit_rest_disjoint L sw t ts hnd
    have hhead := (List.nodup_cons.mp (oneBit_partition L sw t ts hnd)).1
    have restFrame (circ : Program) (hcirc : wires circ=(L.withRecord ⟨sw,t⟩).usedWires.toFinset)
        (cs : List (Bool×Bool)) (s u : BasisState) (he : ∀ w, w∉wires circ → s w=u w)
        (h : OneBitTapeValues ts cs s) : OneBitTapeValues ts cs u := by
      apply OneBitTapeValues.congr ts cs s u h
      intro w hw
      exact (he w (by rw [hcirc]; exact fun hm => List.disjoint_left.mp hdis hw ((L.withRecord ⟨sw,t⟩).usedWires_sublist.subset (List.mem_toFinset.mp hm)))).symm
    have headFrame (circ : Program) (hcirc : wires circ ⊆ (L.swapCounter.oneBitTapeWires sw ts).toFinset)
        (T : Bool) (s u : BasisState) (he : ∀ w, w∉wires circ → s w=u w)
        (h : s t=T) : u t=T := by
      exact (he t (fun hm => hhead (List.mem_toFinset.mp (hcirc hm)))).symm.trans h
    have hf1 := hround.frame (restFrame _ hrw.1 (List.replicate ts.length (false,false)))
    have hf2 := ht.1.frame (headFrame _ htw.1 (kaliskiCode z).2)
    have hb1 := ht.2.frame (headFrame _ htw.2 (kaliskiCode z).2)
    have hb2 := hunround.frame (restFrame _ hrw.2 (List.replicate ts.length (false,false)))
    let P0 := fun st => (LoopState L z st ∧ st sw=false) ∧ OneBitTapeValues (t::ts) ((false,false)::List.replicate ts.length (false,false)) st
    let PM := fun st => ((LoopState L.swapCounter (kaliskiStep z) st ∧ st sw=false) ∧ OneBitTapeValues ts (List.replicate ts.length (false,false)) st) ∧ st t=(kaliskiCode z).2
    let PF := fun st => (LoopState (loopEndLayout L.swapCounter ts.length) ((kaliskiStep^[ts.length]) (kaliskiStep z)) st ∧ st sw=false) ∧ OneBitTapeValues (t::ts) (kaliskiCode z::kaliskiCodes ts.length (kaliskiStep z)) st
    let PB := fun st => (LoopState L.swapCounter (kaliskiStep z) st ∧ st sw=false ∧ st t=(kaliskiCode z).2) ∧ OneBitTapeValues ts (List.replicate ts.length (false,false)) st
    constructor
    · have h1 : Triple P0 (oneBitRound (L.withRecord ⟨sw,t⟩) i) PM := hf1.conseq
        (fun st h => ⟨⟨h.1.1,h.1.2,h.2.1⟩,h.2.2⟩)
        (fun st h => ⟨⟨⟨h.1.1,h.1.2.1⟩,h.2⟩,h.1.2.2⟩)
      have h2 : Triple PM (oneBitLoop L.swapCounter sw (i+1) ts) PF := hf2.conseq (fun _ h => h)
        (fun st h => ⟨h.1.1,h.2,h.1.2⟩)
      have h := h1.seq h2
      simpa only [P0,PF,oneBitLoop,List.length_cons,List.replicate_succ,kaliskiCodes,OneBitTapeValues,
        loopEndLayout,Function.iterate_succ_apply] using h
    · have h1 : Triple PF (oneBitUnloop L.swapCounter sw (i+1) ts) PB := hb1.conseq
        (fun st h => ⟨⟨h.1,h.2.2⟩,h.2.1⟩)
        (fun st h => ⟨⟨h.1.1.1,h.1.1.2,h.2⟩,h.1.2⟩)
      have h2 : Triple PB (oneBitUnround (L.withRecord ⟨sw,t⟩) i) P0 := hb2.conseq (fun _ h => h)
        (fun st h => ⟨⟨h.1.1,h.1.2.1⟩,h.1.2.2,h.2⟩)
      have h := h1.seq h2
      simpa only [P0,PF,oneBitUnloop,List.length_cons,List.replicate_succ,kaliskiCodes,OneBitTapeValues,
        loopEndLayout,Function.iterate_succ_apply] using h

end ECDSAAdd.Arithmetic
