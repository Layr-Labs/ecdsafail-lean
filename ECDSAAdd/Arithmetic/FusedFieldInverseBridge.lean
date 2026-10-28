import ECDSAAdd.Arithmetic.FusedFieldBridge
import ECDSAAdd.Arithmetic.FusedSharedInverse

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Exact correspondence between the independent canonical inverse and the
recorded Skywalk inverse cell, before its separate swap undo. -/
theorem fusedFieldInverse_result (G : Bool) (X Y : Nat) (hX : X<p) (hY : Y<p) :
    FusedSignedHalf.inverseValue (!G) X Y=(skywalkFieldUnnat p G false X Y).1 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hl := FusedSignedHalf.inverseValue_field (!G) X Y
  have hr := congrArg Prod.fst (skywalkFieldUnnat_field G false X Y hX hY)
  have he : (FusedSignedHalf.inverseValue (!G) X Y : Fp)=
      ((skywalkFieldUnnat p G false X Y).1 : Fp) := by
    cases G <;> simp [skywalkPayloadUncell,sub_eq_add_neg] at hl hr ⊢
    all_goals exact hl.trans hr.symm
  have hb : (skywalkFieldUnnat p G false X Y).1<p := by
    cases G <;> simp only [skywalkFieldUnnat,skywalkSignedNat,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true]
    all_goals exact Nat.mod_lt _ p_prime.pos
  have hv := congrArg (fun z : Fp => z.val) he
  dsimp only at hv
  rw [ZMod.val_natCast_of_lt (FusedSignedHalf.inverseValue_bound (!G) X Y),
    ZMod.val_natCast_of_lt hb] at hv
  exact hv

theorem fusedFieldInverse_correct (L : ModInPlaceLayout) (unused : List Wire)
    (g : Wire) (kernel : Program) (X Y : Nat) (hX : X<p) (hY : Y<p)
    (hn : (g::L.wires).Nodup) (hgu : g∉unused)
    (hkernel : ∀ st : State, ∀ ms : List Bool,
      regValue L.a st.basis=Y → regValue L.z st.basis=X →
      regValue L.work st.basis=0 → regValue unused st.basis=0 →
      (run kernel ms st).phase=st.phase ∧
      (∀ q,q∉L.z → (run kernel ms st).basis q=st.basis q) ∧
      regValue L.z (run kernel ms st).basis=FusedSignedHalf.inverseValue (st.basis g) X Y)
    (s : State) (record : List Bool) (hy : regValue L.a s.basis=Y)
    (hx : regValue L.z s.basis=X) (hk : regValue L.work s.basis=0)
    (hu : regValue unused s.basis=0) :
    (run (fusedFieldSignedHalf g kernel) record s).phase=s.phase ∧
    (∀ q,q∉L.z → (run (fusedFieldSignedHalf g kernel) record s).basis q=s.basis q) ∧
    regValue L.z (run (fusedFieldSignedHalf g kernel) record s).basis=
      (skywalkFieldUnnat p (s.basis g) false X Y).1 := by
  have hg := (List.nodup_cons.mp hn).1
  have gaway (q : Wire) (hq : q∈L.wires) : q≠g := by
    intro he
    exact hg (he ▸ hq)
  have gz : g∉L.z := by intro h; exact hg (by simp [ModInPlaceLayout.wires,h])
  obtain ⟨st1,hst1⟩ : ∃ st1 : State,run [.X g] record s=st1 := ⟨_,rfl⟩
  have fixed1 (q : Wire) (hq : q≠g) : st1.basis q=s.basis q := by
    rw [←hst1]
    simp [run,writeBit,hq]
  have sign1 : st1.basis g= !s.basis g := by rw [←hst1]; simp [run,writeBit]
  have phase1 : st1.phase=s.phase := by rw [←hst1]; rfl
  have hy1 : regValue L.a st1.basis=Y := (regValue_congr _ _ _ (fun q hq =>
    fixed1 q (gaway q (by simp [ModInPlaceLayout.wires,hq])))).trans hy
  have hx1 : regValue L.z st1.basis=X := (regValue_congr _ _ _ (fun q hq =>
    fixed1 q (gaway q (by simp [ModInPlaceLayout.wires,hq])))).trans hx
  have hk1 : regValue L.work st1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    fixed1 q (gaway q (by simp [ModInPlaceLayout.wires,hq])))).trans hk
  have hu1 : regValue unused st1.basis=0 := (regValue_congr _ _ _ (fun q hq =>
    fixed1 q (fun he => hgu (he ▸ hq)))).trans hu
  obtain ⟨st2,hst2⟩ : ∃ st2 : State,run kernel record st1=st2 := ⟨_,rfl⟩
  have h2 := hkernel st1 record hy1 hx1 hk1 hu1
  rw [hst2] at h2
  have sign2 : st2.basis g= !s.basis g := (h2.2.1 g gz).trans sign1
  let tail := record.drop (measurementCount kernel)
  obtain ⟨st3,hst3⟩ : ∃ st3 : State,run [.X g] tail st2=st3 := ⟨_,rfl⟩
  have fixed3 (q : Wire) (hq : q≠g) : st3.basis q=st2.basis q := by
    rw [←hst3]
    simp [run,writeBit,hq]
  have sign3 : st3.basis g=s.basis g := by
    rw [←hst3]
    simp only [run,writeBit,Function.update_self,sign2,Bool.not_not]
  have hrun : run (fusedFieldSignedHalf g kernel) record s=st3 := by
    rw [fusedFieldSignedHalf,List.append_assoc,run_append,run_take]
    simp only [measurementCount,List.drop_zero]
    rw [hst1,run_append,run_take,hst2]
    exact hst3
  rw [hrun]
  refine ⟨?_,?_,?_⟩
  · rw [←hst3]
    exact h2.1.trans phase1
  · intro q hq
    by_cases hqg : q=g
    · subst q; exact sign3
    · exact (fixed3 q hqg).trans ((h2.2.1 q hq).trans (fixed1 q hqg))
  · have hz3 := regValue_congr L.z st3.basis st2.basis (fun q hq =>
      fixed3 q (gaway q (by simp [ModInPlaceLayout.wires,hq])))
    rw [hz3,h2.2.2,sign1]
    exact fusedFieldInverse_result (s.basis g) X Y hX hY

end ECDSAAdd.Arithmetic
