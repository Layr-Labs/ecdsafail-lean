import ECDSAAdd.Arithmetic.DialogReady

namespace ECDSAAdd.Arithmetic
open Secp256k1

def DialogExternal (L : DialogLayout) (B : Bool) (X Y Z : Nat) (s : BasisState) : Prop :=
  s L.control=B ∧ regValue L.x s=X ∧ regValue L.y s=Y ∧ regValue L.z s=Z

def DialogPrepared (L : DialogLayout) (S : Nat) (B : Bool) (X Y Z : Nat) (s : BasisState) : Prop :=
  (ValueLoopState L.first (valueStep^[512] (valueInit p S)) s ∧
    TapeValues L.records ((valueTrace 512 (valueInit p S)).map Prod.snd) s) ∧
  DialogExternal L B X Y Z s

theorem dialogWalk_specs (L : DialogLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (S : Nat) (hs0 : 0<S) (hs : S<p) (B : Bool) (X Y Z : Nat) :
    Triple (DialogValues L B X Y Z p S) (valueLoop L.first 0 L.records)
      (DialogPrepared L S B X Y Z) ∧
    Triple (DialogPrepared L S B X Y Z) (valueUnloop L.first 0 L.records)
      (DialogValues L B X Y Z p S) := by
  have hd : L.first.data.width=257 := by simp [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low]
  have hb : ∀ j<L.records.length, (valueStep^[j] (valueInit p S)).u<2^(valueWidth L.first.data.width (0+j)) ∧
      (valueStep^[j] (valueInit p S)).v<2^(valueWidth L.first.data.width (0+j)) := by
    intro j hj
    rw [hd,Nat.zero_add]
    exact dialogWalk_width S j hs0 hs (by rw [hw.records] at hj; exact hj)
  have f := valueLoop_spec L.first L.records 0 (valueInit p S) hn hw.counter (by omega)
    (by simp [hw.records]) (by simp [valueInit]) hb
  have b := valueUnloop_spec L.first L.records 0 (valueInit p S) hn hw.counter (by omega)
    (by simp [hw.records]) (by simp [valueInit]) hb
  have hend : loopEndLayout L.first L.records.length=L.first := by
    rw [hw.records]; exact valueEnd_even L.first 256
  rw [hend,hw.records] at f b
  have wires := (valueLoop_wires_subset L.first L.records 0 hw.counter (by omega)).1
  have frame (P : Program) (hP : ECDSAAdd.wires P⊆(L.first.valueTapeWires L.records).toFinset)
      (s t : BasisState) (ht : ∀ q,q∉ECDSAAdd.wires P → s q=t q)
      (h : DialogExternal L B X Y Z s) : DialogExternal L B X Y Z t := by
    have keep (q : Wire) (hq : q∈L.external) : t q=s q := by
      apply (ht q ?_).symm
      intro hh
      exact List.disjoint_left.mp (L.external_value_disjoint hn) hq (List.mem_toFinset.mp (hP hh))
    exact ⟨(keep _ (by simp [DialogLayout.external])).trans h.1,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [DialogLayout.external,hq]))).trans h.2.1,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [DialogLayout.external,hq]))).trans h.2.2.1,
      (regValue_congr _ _ _ (fun q hq => keep q (by simp [DialogLayout.external,hq]))).trans h.2.2.2⟩
  have hf := f.frame (frame _ wires.1)
  have hb := b.frame (frame _ wires.2)
  constructor
  · apply hf.conseq
    · intro st h
      have ready := (dialogReady_iff L p S (by omega) st).mpr
        ⟨h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
      rw [hw.records] at ready
      exact ⟨ready,h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
    · intro st h; exact h
  · apply hb.conseq
    · intro st h; exact h
    · intro st h
      have ready := (dialogReady_iff L p S (by omega) st).mp (by simpa only [hw.records,valueInit] using h.1)
      exact ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,ready.1,ready.2.1,ready.2.2⟩

end ECDSAAdd.Arithmetic
