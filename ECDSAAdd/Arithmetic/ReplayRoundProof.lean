import ECDSAAdd.Arithmetic.ReplayLoop

namespace ECDSAAdd.Arithmetic
namespace ReplayState

private theorem active_outside (L : ReplayLayout) (n : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) : L.active∉L.payload.wires := by
  have h := (List.nodup_cons.mp hv.nodup).1
  intro hm; exact h (by simp [hm])

private theorem count_outside (L : ReplayLayout) (n : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (q : Wire) (hq : q∈L.counter.x) :
    q∉L.payload.z ∧ q∉L.payload.a ∧ q≠L.active := by
  have h := List.nodup_iff_count.mp hv.nodup q
  have hc := List.count_pos_iff.mpr hq
  simp only [ReplayLayout.wires,ModInPlaceLayout.wires,List.count_cons,List.count_append] at h
  refine ⟨?_,?_,?_⟩
  · intro hm; have := List.count_pos_iff.mpr hm; omega
  · intro hm; have := List.count_pos_iff.mpr hm; omega
  · intro he; subst q; simp only [beq_self_eq_true,if_true] at h; omega

/-- 比较只异或活动位，所有借用工作位在边界恢复为零。 -/
theorem activity (L : ReplayLayout) (n : Nat) (rs : List RoundRecord)
    (hv : L.Valid n rs) (ref : BasisState) (K i X Y : Nat) (C : Bool)
    (hK : regValue L.counter.x ref=K) (hi : i<512) :
    Triple (ReplayState L ref C X Y) (counterActiveXor L.counter L.active i)
      (ReplayState L ref (C ^^ decide (i<K)) X Y) := by
  intro s m h
  have hx : regValue L.counter.x s.basis=K := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hK
    intro q hq
    have ho := count_outside L n rs hv q hq
    exact h.2.2.2.2 q ho.1 ho.2.1 ho.2.2
  have clean := (regValue_zero _ _).mp h.2.2.2.1
  have hy : regValue L.counter.y s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hv.constant hq))
  have hc : regValue L.counter.carry s.basis=0 := (regValue_zero _ _).mpr
    (fun q hq => clean q (hv.carry hq))
  have hi0 : s.basis L.counter.cin=false := clean _ hv.cin
  obtain ⟨hf,ho⟩ := counterActiveXor_spec L.counter L.active hv.counterNodup hv.counterWidth
    K i C hi s m ⟨⟨⟨⟨h.1,hx⟩,hy⟩,hi0⟩,hc⟩
  have keep := counterActiveXor_frame L.counter L.active hv.counterNodup hv.counterWidth
    i K hi C s m h.1 hx hy hi0 hc
  have hz : L.active∉L.payload.z := fun hm => active_outside L n rs hv (by simp [ModInPlaceLayout.wires,hm])
  have ha : L.active∉L.payload.a := fun hm => active_outside L n rs hv (by simp [ModInPlaceLayout.wires,hm])
  have hw : L.active∉L.payload.work := fun hm => active_outside L n rs hv (by simp [ModInPlaceLayout.wires,hm])
  refine ⟨hf,ho.1.1.1.1,?_,?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq => keep q (fun he => hz (he ▸ hq)))).trans h.2.1
  · exact (regValue_congr _ _ _ (fun q hq => keep q (fun he => ha (he ▸ hq)))).trans h.2.2.1
  · exact (regValue_congr _ _ _ (fun q hq => keep q (fun he => hw (he ▸ hq)))).trans h.2.2.2.1
  · intro q hqz hqa hneq
    exact (keep q hneq).trans (h.2.2.2.2 q hqz hqa hneq)

private theorem record_values (L : ReplayLayout) (n : Nat) (rs : List RoundRecord)
    (r : RoundRecord) (hv : L.Valid n rs) (hr : r∈rs) (ref s : BasisState)
    (C : Bool) (X Y : Nat) (h : ReplayState L ref C X Y s) :
    s r.swap=ref r.swap ∧ s r.subtract=ref r.subtract := by
  have hn := hv.cell L n rs r hr
  have hs := ReplayValues.control_outside L.active r.swap r.subtract L.payload hn r.swap (by simp)
  have ht := ReplayValues.control_outside L.active r.swap r.subtract L.payload hn r.subtract (by simp)
  have hne : r.swap≠L.active ∧ r.subtract≠L.active := by
    have hh := (List.nodup_cons.mp hn).1
    exact ⟨fun he => hh (by simp [he]),fun he => hh (by simp [he])⟩
  exact ⟨h.2.2.2.2 _ hs.1 hs.2 hne.1,h.2.2.2.2 _ ht.1 ht.2 hne.2⟩


theorem cell (L : ReplayLayout) (n p : Nat) (rs : List RoundRecord) (r : RoundRecord)
    (hv : L.Valid n rs) (hr : r∈rs) (ref : BasisState) (C : Bool) (X Y : Nat)
    (hp : p%2=1) (hpn : p<2^n) (hX : X<p) (hY : Y<p) :
    Triple (ReplayState L ref C X Y) (replayCell L.active r.swap r.subtract L.payload p)
      (ReplayState L ref C (replayNatStep p C (ref r.swap) (ref r.subtract) X Y).1
        (replayNatStep p C (ref r.swap) (ref r.subtract) X Y).2) := by
  intro s m h
  have hn := hv.cell L n rs r hr
  have ht := record_values L n rs r hv hr ref s.basis C X Y h
  have hh : ReplayValues L.active r.swap r.subtract L.payload C (ref r.swap) (ref r.subtract) X Y s.basis :=
    ⟨h.1,ht.1,ht.2,h.2.1,h.2.2.1,h.2.2.2.1⟩
  obtain ⟨hf,ho⟩ := replayCell_spec L.active r.swap r.subtract L.payload n p X Y C
    (ref r.swap) (ref r.subtract) hv.widths hn hp hpn hX hY s m hh
  refine ⟨hf,ho.1,ho.2.2.2.1,ho.2.2.2.2.1,ho.2.2.2.2.2,?_⟩
  intro q hz ha hne
  exact (replayCell_frame L.active r.swap r.subtract L.payload n p X Y C
    (ref r.swap) (ref r.subtract) hv.widths hn hp hpn hX hY s m hh q hz ha).trans
      (h.2.2.2.2 q hz ha hne)


theorem uncell (L : ReplayLayout) (n p : Nat) (rs : List RoundRecord) (r : RoundRecord)
    (hv : L.Valid n rs) (hr : r∈rs) (ref : BasisState) (C : Bool) (X Y : Nat)
    (hp : p%2=1) (hpn : p<2^n) (hX : X<p) (hY : Y<p) :
    Triple (ReplayState L ref C X Y) (replayUncell L.active r.swap r.subtract L.payload p)
      (ReplayState L ref C (replayNatUnstep p C (ref r.swap) (ref r.subtract) X Y).1
        (replayNatUnstep p C (ref r.swap) (ref r.subtract) X Y).2) := by
  intro s m h
  have hn := hv.cell L n rs r hr
  have ht := record_values L n rs r hv hr ref s.basis C X Y h
  have hh : ReplayValues L.active r.swap r.subtract L.payload C (ref r.swap) (ref r.subtract) X Y s.basis :=
    ⟨h.1,ht.1,ht.2,h.2.1,h.2.2.1,h.2.2.2.1⟩
  obtain ⟨hf,ho⟩ := replayUncell_spec L.active r.swap r.subtract L.payload n p X Y C
    (ref r.swap) (ref r.subtract) hv.widths hn hp hpn hX hY s m hh
  refine ⟨hf,ho.1,ho.2.2.2.1,ho.2.2.2.2.1,ho.2.2.2.2.2,?_⟩
  intro q hz ha hne
  exact (replayUncell_frame L.active r.swap r.subtract L.payload n p X Y C
    (ref r.swap) (ref r.subtract) hv.widths hn hp hpn hX hY s m hh q hz ha).trans
      (h.2.2.2.2 q hz ha hne)

end ReplayState


theorem replayRound_spec (L : ReplayLayout) (n p : Nat) (rs : List RoundRecord) (r : RoundRecord)
    (hv : L.Valid n rs) (hr : r∈rs) (ref : BasisState) (K i X Y : Nat)
    (hp : p%2=1) (hpn : p<2^n) (hX : X<p) (hY : Y<p)
    (hK : regValue L.counter.x ref=K) (hi : i<512) :
    Triple (ReplayState L ref false X Y) (replayRound L r p i)
      (ReplayState L ref false (replayNatStep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).1
        (replayNatStep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).2) := by
  have h1 := ReplayState.activity L n rs hv ref K i X Y false hK hi
  have h2 := ReplayState.cell L n p rs r hv hr ref (decide (i<K)) X Y hp hpn hX hY
  have h3 := ReplayState.activity L n rs hv ref K i
    (replayNatStep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).1
    (replayNatStep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).2 (decide (i<K)) hK hi
  simp only [Bool.false_xor] at h1
  simp only [Bool.xor_self] at h3
  simpa only [replayRound,List.append_assoc] using (h1.seq h2).seq h3


theorem replayUnround_spec (L : ReplayLayout) (n p : Nat) (rs : List RoundRecord) (r : RoundRecord)
    (hv : L.Valid n rs) (hr : r∈rs) (ref : BasisState) (K i X Y : Nat)
    (hp : p%2=1) (hpn : p<2^n) (hX : X<p) (hY : Y<p)
    (hK : regValue L.counter.x ref=K) (hi : i<512) :
    Triple (ReplayState L ref false X Y) (replayUnround L r p i)
      (ReplayState L ref false (replayNatUnstep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).1
        (replayNatUnstep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).2) := by
  have h1 := ReplayState.activity L n rs hv ref K i X Y false hK hi
  have h2 := ReplayState.uncell L n p rs r hv hr ref (decide (i<K)) X Y hp hpn hX hY
  have h3 := ReplayState.activity L n rs hv ref K i
    (replayNatUnstep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).1
    (replayNatUnstep p (decide (i<K)) (ref r.swap) (ref r.subtract) X Y).2 (decide (i<K)) hK hi
  simp only [Bool.false_xor] at h1
  simp only [Bool.xor_self] at h3
  simpa only [replayUnround,List.append_assoc] using (h1.seq h2).seq h3

end ECDSAAdd.Arithmetic
