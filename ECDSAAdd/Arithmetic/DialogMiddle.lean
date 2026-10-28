import ECDSAAdd.Arithmetic.DialogWalk

namespace ECDSAAdd.Arithmetic
open Secp256k1

theorem dialogPrepared_change_payload (L : DialogLayout) (hn : L.wires.Nodup)
    (S : Nat) (B : Bool) (X Y Z Y' Z' : Nat) (s t : BasisState)
    (h : DialogPrepared L S B X Y Z s)
    (he : ∀ q,q∉L.y → q∉L.z → t q=s q)
    (hy : regValue L.y t=Y') (hz : regValue L.z t=Z') :
    DialogPrepared L S B X Y' Z' t := by
  have keep (q : Wire) (hq : q∈L.first.valueTapeWires L.records) : t q=s q := by
    apply he
    · intro hh; exact List.disjoint_left.mp (L.external_value_disjoint hn)
        (by simp [DialogLayout.external,hh]) hq
    · intro hh; exact List.disjoint_left.mp (L.external_value_disjoint hn)
        (by simp [DialogLayout.external,hh]) hq
  have ex (q : Wire) (hq : q∈L.control::L.x) : t q=s q := by
    have hc := List.nodup_iff_count.mp (L.external_nodup hn) q
    have hx := List.count_pos_iff.mpr hq
    simp only [DialogLayout.external,List.count_cons,List.count_append] at hc hx
    apply he
    · intro hh; have hy := List.count_pos_iff.mpr hh; omega
    · intro hh; have hz := List.count_pos_iff.mpr hh; omega
  exact ⟨⟨h.1.1.congr _ _ _ _ (fun q hq => keep q (List.mem_append_right _ hq)),
    TapeValues.congr _ _ _ _ h.1.2 (fun q hq => keep q (List.mem_append_left _ hq))⟩,
    (ex _ (by simp)).trans h.2.1,
    (regValue_congr _ _ _ (fun q hq => ex q (by simp [hq]))).trans h.2.2.1,hy,hz⟩

theorem dialogExchange_spec (L : DialogLayout) (hn : L.wires.Nodup)
    (S : Nat) (B : Bool) (X Y Z : Nat) :
    Triple (DialogPrepared L S B X Y Z) (exchangeRegisters L.y L.z)
      (DialogPrepared L S B X Z Y) := by
  have hl : L.y.length=L.z.length := by
    simp [DialogLayout.y,DialogLayout.z,KaliskiRoundLayout.s,RoundDataLayout.s,RoundDataLayout.reg]
  have hd : (L.y++L.z).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have hc := List.nodup_iff_count.mp (L.external_nodup hn) q
    simp only [DialogLayout.external,List.count_cons,List.count_append] at hc ⊢
    omega
  intro s m h
  have hf := exchangeRegisters_spec L.y L.z hl hd Y Z s m ⟨h.2.2.2.1,h.2.2.2.2⟩
  refine ⟨hf.1,dialogPrepared_change_payload L hn S B X Y Z Z Y _ _ h ?_ hf.2.1 hf.2.2⟩
  intro q hy hz
  apply run_preserves_outside
  intro hm
  have hh := exchangeRegisters_wires _ _ hl hm
  simp [hy,hz] at hh

/-- 正反回放保留完整值走历史，并作用于同一对载荷字。 -/
theorem dialogReplay_specs (L : DialogLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (S : Nat) (hs0 : 0<S) (hs : S<p) (B : Bool) (X Y : Nat) (hy : Y<p) :
    Triple (DialogPrepared L S B X 0 Y) (replayLoop L.replay p 0 L.records)
      (DialogPrepared L S B X (((Y:Fp)/(S:Fp)).val) 0) ∧
    Triple (DialogPrepared L S B X Y 0) (replayUnloop L.replay p 0 L.records)
      (DialogPrepared L S B X 0 (((Y:Fp)*(S:Fp)).val)) := by
  have hv := L.replay_valid hw hn
  have hpn : p<2^256 := by decide
  have mk (s : BasisState) (A C : Nat) (h : DialogPrepared L S B X A C s) :
      ReplayState L.replay s false A C s :=
    ⟨h.1.1.active,by simpa only [show L.replay.payload.z=L.y from L.payload_fields.1] using h.2.2.2.1,
      by simpa only [show L.replay.payload.a=L.z from L.payload_fields.2] using h.2.2.2.2,
      L.payload_work_zero _ _ h.1.1,fun _ _ _ _ => rfl⟩
  have finish (s t : BasisState) (A C A' C' : Nat) (h : DialogPrepared L S B X A C s)
      (ht : ReplayState L.replay s false A' C' t) : DialogPrepared L S B X A' C' t := by
    apply dialogPrepared_change_payload L hn S B X A C A' C' s t h
    · intro q hqy hqz
      by_cases ha : q=L.first.active
      · subst q; exact ht.1.trans h.1.1.active.symm
      · exact ht.2.2.2.2 q (by simpa only [show L.replay.payload.z=L.y from L.payload_fields.1] using hqy)
          (by simpa only [show L.replay.payload.a=L.z from L.payload_fields.2] using hqz) ha
    · simpa only [show L.replay.payload.z=L.y from L.payload_fields.1] using ht.2.1
    · simpa only [show L.replay.payload.a=L.z from L.payload_fields.2] using ht.2.2.1
  constructor
  · intro s m h
    have hf := replayLoop_spec L.replay 256 p (valueStep^[512] (valueInit p S)).k 0 L.records hv
      s.basis 0 Y (by decide) hpn (by decide) hy h.1.1.k (by simp [hw.records]) s m (mk _ _ _ h)
    rw [dialogReplay_division L.records s.basis S Y hw.records hs0 hs hy h.1.2] at hf
    exact ⟨hf.1,finish _ _ _ _ _ _ h hf.2⟩
  · intro s m h
    have hf := replayUnloop_spec L.replay 256 p (valueStep^[512] (valueInit p S)).k 0 L.records hv
      s.basis Y 0 (by decide) hpn hy (by decide) h.1.1.k (by simp [hw.records]) s m (mk _ _ _ h)
    rw [dialogReplay_multiplication L.records s.basis S Y hw.records hs0 hs hy h.1.2] at hf
    exact ⟨hf.1,finish _ _ _ _ _ _ h hf.2⟩

end ECDSAAdd.Arithmetic
