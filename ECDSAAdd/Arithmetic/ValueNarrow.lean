import ECDSAAdd.Arithmetic.KaliskiLoopState
import ECDSAAdd.Arithmetic.ValueSpec
import ECDSAAdd.Arithmetic.Reduction

namespace ECDSAAdd.Arithmetic

/-! Value-walk width envelope: a round runs only on the first m data bits. The dropped high bits are not
in the gate support and are preserved wire by wire; u/v high bits are zero by the width
envelope, r/s high bits keep their values. -/

namespace KaliskiRoundLayout

/-- Narrow view: keep only the first m data bits; counter, control and record wires are unchanged. -/
def narrow (L : KaliskiRoundLayout) (m : Nat) : KaliskiRoundLayout :=
  { L with low := (L.low++[L.high]).take (m-1), high := (L.low++[L.high]).getD (m-1) L.high }

private theorem take_getD {α : Type} (l : List α) (n : Nat) (d : α) (h : n<l.length) :
    l.take n++[l.getD n d]=l.take (n+1) := by
  rw [List.take_add_one,List.getElem?_eq_getElem h,List.getD_eq_getElem _ _ h]
  rfl

theorem narrow_data (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width) :
    (L.narrow m).data=⟨L.data.bits.take m,L.data.cin⟩ := by
  have hlt : m-1<(L.low++[L.high]).length := by
    simp only [data,RoundDataLayout.width] at hm; omega
  simp only [narrow,data]
  rw [take_getD _ _ _ hlt,Nat.sub_add_cancel h1]

theorem narrow_width (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width) :
    (L.narrow m).data.width=m := by
  rw [narrow_data L m h1 hm]
  simp only [RoundDataLayout.width,List.length_take]
  exact min_eq_left hm

theorem narrow_full (L : KaliskiRoundLayout) : L.narrow L.data.width=L := by
  cases L
  simp [narrow,data,RoundDataLayout.width]

theorem narrow_withRecord (L : KaliskiRoundLayout) (r : RoundRecord) (m : Nat) :
    (L.withRecord r).narrow m=(L.narrow m).withRecord r := rfl

/-- The full layout wires are a permutation of the narrow-view wires and the dropped data bits. -/
theorem narrow_wires_perm (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width) :
    L.wires.Perm ((L.narrow m).wires++(L.data.bits.drop m).flatMap RoundBit.wires) := by
  have hb : L.data.bits.flatMap RoundBit.wires=
      (L.data.bits.take m).flatMap RoundBit.wires++(L.data.bits.drop m).flatMap RoundBit.wires := by
    rw [← List.flatMap_append,List.take_append_drop]
  have hn : (L.narrow m).wires=[L.done,L.swap,L.subtract,L.oddWork,L.bothWork,L.compareCin]++
      (L.data.cin::(L.data.bits.take m).flatMap RoundBit.wires)++L.counter.wires := by
    simp only [wires,narrow_data L m h1 hm,RoundDataLayout.wires]
    rfl
  rw [hn]
  apply List.perm_iff_count.mpr
  intro w
  simp only [wires,RoundDataLayout.wires,hb,List.count_append,List.count_cons]
  omega

theorem narrow_nodup (L : KaliskiRoundLayout) (m : Nat) (h1 : 1≤m) (hm : m≤L.data.width)
    (hnd : L.wires.Nodup) :
    (L.narrow m).wires.Nodup ∧ ((L.narrow m).wires.Disjoint ((L.data.bits.drop m).flatMap RoundBit.wires)) := by
  have h := List.nodup_append'.mp ((L.narrow_wires_perm m h1 hm).nodup_iff.mp hnd)
  exact ⟨h.1,h.2.2⟩

end KaliskiRoundLayout

namespace RoundDataLayout

private theorem reg_split (D : RoundDataLayout) (m : Nat) (f : RoundField) :
    D.reg f=(⟨D.bits.take m,D.cin⟩ : RoundDataLayout).reg f++(D.bits.drop m).map (·.get f) := by
  simp only [reg]
  rw [← List.map_append,List.take_append_drop]

private theorem take_reg_length (D : RoundDataLayout) (m : Nat) (hm : m≤D.width) (f : RoundField) :
    ((⟨D.bits.take m,D.cin⟩ : RoundDataLayout).reg f).length=m := by
  simp only [reg,List.length_map,List.length_take]
  exact min_eq_left hm

private theorem high_mem (D : RoundDataLayout) (m : Nat) (f : RoundField) {w : Wire}
    (hw : w∈(D.bits.drop m).map (·.get f)) : w∈(D.bits.drop m).flatMap RoundBit.wires := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hw
  exact List.mem_flatMap.mpr ⟨b,hb,by cases f <;> simp [RoundBit.wires,RoundBit.get]⟩

/-- The narrow-view values are the full-width values modulo 2^m. -/
theorem RoundValues.narrow_down (D : RoundDataLayout) (m : Nat) (hm : m≤D.width)
    (v : RoundField → Nat) (s : BasisState) (h : RoundValues D v s) :
    RoundValues ⟨D.bits.take m,D.cin⟩ (fun f => v f%2^m) s := by
  refine ⟨fun f => ?_,h.2⟩
  have e := regValue_append ((⟨D.bits.take m,D.cin⟩ : RoundDataLayout).reg f)
    ((D.bits.drop m).map (·.get f)) s
  rw [← reg_split,h.1 f,take_reg_length D m hm] at e
  have ha := regValue_lt ((⟨D.bits.take m,D.cin⟩ : RoundDataLayout).reg f) s
  rw [take_reg_length D m hm] at ha
  dsimp only
  rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha]

/-- After a narrow-view update, unchanged high bits reassemble the full-width values. -/
theorem RoundValues.narrow_up (D : RoundDataLayout) (m : Nat) (hm : m≤D.width)
    (v v' : RoundField → Nat) (s t : BasisState) (hs : RoundValues D v s)
    (ht : RoundValues ⟨D.bits.take m,D.cin⟩ v' t)
    (he : ∀ w∈(D.bits.drop m).flatMap RoundBit.wires, t w=s w) :
    RoundValues D (fun f => v' f+2^m*(v f/2^m)) t := by
  refine ⟨fun f => ?_,ht.2⟩
  have es := regValue_append ((⟨D.bits.take m,D.cin⟩ : RoundDataLayout).reg f)
    ((D.bits.drop m).map (·.get f)) s
  have et := regValue_append ((⟨D.bits.take m,D.cin⟩ : RoundDataLayout).reg f)
    ((D.bits.drop m).map (·.get f)) t
  rw [← reg_split,hs.1 f,take_reg_length D m hm] at es
  rw [← reg_split,take_reg_length D m hm,ht.1 f] at et
  have hh : regValue ((D.bits.drop m).map (·.get f)) t=regValue ((D.bits.drop m).map (·.get f)) s :=
    regValue_congr _ _ _ (fun w hw => he w (high_mem D m f hw))
  have ha := regValue_lt ((⟨D.bits.take m,D.cin⟩ : RoundDataLayout).reg f) s
  rw [take_reg_length D m hm] at ha
  have hq : v f/2^m=regValue ((D.bits.drop m).map (·.get f)) s := by
    rw [es,Nat.add_mul_div_left _ _ (Nat.two_pow_pos m),Nat.div_eq_of_lt ha,Nat.zero_add]
  dsimp only
  rw [et,hh,hq]

end RoundDataLayout

/-- The narrow view keeps counter, control and record wires, so the auxiliary round assertions transfer directly. -/
theorem RoundAuxValues.narrow_iff (L : KaliskiRoundLayout) (m K N : Nat) (A D S T : Bool)
    (st : BasisState) :
    RoundAuxValues (L.narrow m) K N A D S T st ↔ RoundAuxValues L K N A D S T st :=
  ⟨fun h => ⟨h.k,h.next,h.y,h.carry,h.active,h.done,h.swap,h.subtract,h.odd,h.both,h.cin⟩,
   fun h => ⟨h.k,h.next,h.y,h.carry,h.active,h.done,h.swap,h.subtract,h.odd,h.both,h.cin⟩⟩

/-- State seen by the narrow view: r/s reduced to their low m bits, other fields unchanged. -/
def narrowK (m : Nat) (z : KState) : KState := {z with r:=z.r%2^m, s:=z.s%2^m}

private theorem narrowK_down (m : Nat) (z : KState) (hu : z.u<2^m) (hv : z.v<2^m) :
    roundDataValues (narrowK m z)=fun f => roundDataValues z f%2^m := by
  funext f
  cases f <;> simp [roundDataValues,narrowK,Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt hv]

private theorem narrowK_up (m : Nat) (z1 z2 : KState) (hu : z1.u<2^m) (hv : z1.v<2^m)
    (hr : z2.r=z1.r) (hs : z2.s=z1.s) :
    (fun f => roundDataValues (narrowK m z2) f+2^m*(roundDataValues z1 f/2^m))=roundDataValues z2 := by
  funext f
  cases f <;> simp [roundDataValues,narrowK,Nat.div_eq_of_lt hu,Nat.div_eq_of_lt hv,hr,hs,Nat.mod_add_div]

private theorem valueKStep_narrowK (m : Nat) (z : KState) :
    valueKStep (narrowK m z)=narrowK m (valueKStep z) := rfl

private theorem valueKStep_le (z : KState) : (valueKStep z).u≤z.u ∧ (valueKStep z).v≤z.v :=
  valueStep_le z.value

/-- Shared frame fact: the narrowed round support is disjoint from the dropped data bits. -/
private theorem narrow_round_outside (L : KaliskiRoundLayout) (m : Nat) (h2 : 2≤m) (hm : m≤L.data.width)
    (hnd : L.wires.Nodup) (hw : L.counter.width=10) (i : Nat) :
    (∀ w∈(L.data.bits.drop m).flatMap RoundBit.wires, w∉wires (valueRound (L.narrow m) i)) ∧
    (∀ w∈(L.data.bits.drop m).flatMap RoundBit.wires, w∉wires (valueUnround (L.narrow m) i)) := by
  have hn := L.narrow_nodup m (by omega) hm hnd
  have hd : 2≤(L.narrow m).data.width := by rw [L.narrow_width m (by omega) hm]; exact h2
  have hr := valueRound_wires (L.narrow m) hw hd i
  have hout (w : Wire) (hw : w∈(L.data.bits.drop m).flatMap RoundBit.wires) :
      w∉(L.narrow m).valueUsedWires.toFinset := fun hm' =>
    List.disjoint_right.mp hn.2 hw ((L.narrow m).valueUsedWires_sublist.subset (List.mem_toFinset.mp hm'))
  exact ⟨fun w h => by rw [hr.1]; exact hout w h,fun w h => by rw [hr.2]; exact hout w h⟩

/-- Narrowed forward round: run the round on the narrow view; the full-width LoopState is carried across. -/
theorem valueNarrowRound_tape (L : KaliskiRoundLayout) (r : RoundRecord) (rs : List RoundRecord)
    (hnd : (L.tapeWires (r::rs)).Nodup) (hw : L.counter.width=10)
    (i : Nat) (z : KState) (hi : i<512) (hk : KRoundCount i z)
    (m : Nat) (h2 : 2≤m) (hm : m≤L.data.width) (hu : z.u<2^m) (hv : z.v<2^m) :
    Triple (fun st => LoopState L z st ∧ st r.swap=false ∧ st r.subtract=false)
      (valueRound ((L.withRecord r).narrow m) i)
      (fun st => LoopState L.swapCounter (valueKStep z) st ∧
        st r.swap=(kaliskiCode z).1 ∧ st r.subtract=(kaliskiCode z).2) := by
  let W := L.withRecord r
  have hW : W.wires.Nodup := L.withRecord_nodup r rs hnd
  have hm' : m≤W.data.width := hm
  have hN := (W.narrow_nodup m (by omega) hm' hW).1
  have hNw := W.narrow_width m (by omega) hm'
  have hND := W.narrow_data m (by omega) hm'
  intro s mm h
  have hs := h.1.round_before L r z false false s.basis h.2.1 h.2.2
  have hsN : RoundState (W.narrow m) (narrowK m z) z.k 0 false (decide (z.v=0)) false false s.basis := by
    refine ⟨?_,(RoundAuxValues.narrow_iff W m _ _ _ _ _ _ _).mpr hs.2⟩
    rw [hND,narrowK_down m z hu hv]
    exact RoundDataLayout.RoundValues.narrow_down W.data m hm' _ _ hs.1
  obtain ⟨hp,ho⟩ := valueRound_state (W.narrow m) hN hw i (narrowK m z) hi hk
    (by rw [hNw]; exact hu) (by rw [hNw]; exact hv) s mm hsN
  have hkeep (w : Wire) (hw' : w∈(W.data.bits.drop m).flatMap RoundBit.wires) :
      (run (valueRound (W.narrow m) i) mm s).basis w=s.basis w :=
    run_preserves_outside _ _ _ _ ((narrow_round_outside W m h2 hm' hW hw i).1 w hw')
  have hdata : RoundValues W.data (roundDataValues (valueKStep z)) (run (valueRound (W.narrow m) i) mm s).basis := by
    have hup := RoundDataLayout.RoundValues.narrow_up W.data m hm' _
      (roundDataValues (valueKStep (narrowK m z))) _ _ hs.1 (by rw [← hND]; exact ho.1) hkeep
    rwa [valueKStep_narrowK,narrowK_up m z (valueKStep z) hu hv rfl rfl] at hup
  have hR : RoundState W (valueKStep z) 0 (valueKStep z).k false (decide ((valueKStep z).v=0))
      (kaliskiCode z).1 (kaliskiCode z).2 (run (valueRound (W.narrow m) i) mm s).basis :=
    ⟨hdata,(RoundAuxValues.narrow_iff W m _ _ _ _ _ _ _).mp ho.2⟩
  exact ⟨hp,LoopState.of_round_after L r _ _ _ _ hR,hR.2.swap,hR.2.subtract⟩

/-- Narrowed reverse round: on the same narrow view, clear the records and restore the full-width LoopState. -/
theorem valueNarrowUnround_tape (L : KaliskiRoundLayout) (r : RoundRecord) (rs : List RoundRecord)
    (hnd : (L.tapeWires (r::rs)).Nodup) (hw : L.counter.width=10)
    (i : Nat) (z : KState) (hi : i<512) (hk : KRoundCount i z)
    (m : Nat) (h2 : 2≤m) (hm : m≤L.data.width) (hu : z.u<2^m) (hv : z.v<2^m) :
    Triple (fun st => LoopState L.swapCounter (valueKStep z) st ∧
        st r.swap=(kaliskiCode z).1 ∧ st r.subtract=(kaliskiCode z).2)
      (valueUnround ((L.withRecord r).narrow m) i)
      (fun st => LoopState L z st ∧ st r.swap=false ∧ st r.subtract=false) := by
  let W := L.withRecord r
  have hW : W.wires.Nodup := L.withRecord_nodup r rs hnd
  have hm' : m≤W.data.width := hm
  have hN := (W.narrow_nodup m (by omega) hm' hW).1
  have hNw := W.narrow_width m (by omega) hm'
  have hND := W.narrow_data m (by omega) hm'
  have hu1 := lt_of_le_of_lt (valueKStep_le z).1 hu
  have hv1 := lt_of_le_of_lt (valueKStep_le z).2 hv
  intro s mm h
  have hs := h.1.round_after L r (valueKStep z) _ _ s.basis h.2.1 h.2.2
  have hsN : RoundState (W.narrow m) (valueKStep (narrowK m z)) 0 (valueKStep z).k false
      (decide ((valueKStep z).v=0)) (kaliskiCode z).1 (kaliskiCode z).2 s.basis := by
    refine ⟨?_,(RoundAuxValues.narrow_iff W m _ _ _ _ _ _ _).mpr hs.2⟩
    rw [hND,valueKStep_narrowK,narrowK_down m _ hu1 hv1]
    exact RoundDataLayout.RoundValues.narrow_down W.data m hm' _ _ hs.1
  obtain ⟨hp,ho⟩ := valueUnround_state (W.narrow m) hN hw i (narrowK m z) hi hk
    (by rw [hNw]; exact hu) (by rw [hNw]; exact hv) s mm hsN
  have hkeep (w : Wire) (hw' : w∈(W.data.bits.drop m).flatMap RoundBit.wires) :
      (run (valueUnround (W.narrow m) i) mm s).basis w=s.basis w :=
    run_preserves_outside _ _ _ _ ((narrow_round_outside W m h2 hm' hW hw i).2 w hw')
  have hdata : RoundValues W.data (roundDataValues z) (run (valueUnround (W.narrow m) i) mm s).basis := by
    have hup := RoundDataLayout.RoundValues.narrow_up W.data m hm' _
      (roundDataValues (narrowK m z)) _ _ hs.1 (by rw [← hND]; exact ho.1) hkeep
    rwa [narrowK_up m (valueKStep z) z hu1 hv1 rfl rfl] at hup
  have hR : RoundState W z z.k 0 false (decide (z.v=0)) false false
      (run (valueUnround (W.narrow m) i) mm s).basis :=
    ⟨hdata,(RoundAuxValues.narrow_iff W m _ _ _ _ _ _ _).mp ho.2⟩
  exact ⟨hp,LoopState.of_round_before L r _ _ _ _ hR,hR.2.swap,hR.2.subtract⟩

end ECDSAAdd.Arithmetic
