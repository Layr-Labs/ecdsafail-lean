import ECDSAAdd.Arithmetic.FusedSharedInput
import ECDSAAdd.Arithmetic.SkywalkPayloadProgram

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Toggle the recorded sign convention around an independently verified
kernel. The generic Program boundary keeps gate streams opaque to proofs. -/
def fusedFieldSignedHalf (g : Wire) (kernel : Program) : Program :=
  [.X g]++kernel++[.X g]

theorem fusedFieldSignedHalf_counts (g : Wire) (kernel : Program) (t m : Nat)
    (hc : toffoliCount kernel=t ∧ measurementCount kernel=m) :
    toffoliCount (fusedFieldSignedHalf g kernel)=t ∧
    measurementCount (fusedFieldSignedHalf g kernel)=m := by
  have ht : toffoliCount [.X g]=0 := rfl
  have hm : measurementCount [.X g]=0 := rfl
  simp only [fusedFieldSignedHalf,toffoliCount_append,measurementCount_append,
    ht,hm,hc.1,hc.2,Nat.zero_add,Nat.add_zero]
  trivial

/-- The packed canonical answer equals the existing natural signed-half
answer, including zero, ties and either recorded sign. -/
theorem fusedField_result (G : Bool) (X Y : Nat) (hX : X<p) (hY : Y<p) :
    FusedSignedHalf.result p (!G) X Y=(skywalkFieldNat p G false X Y).1 := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  have hp0 : 0<p := p_prime.pos
  have hpo : p%2=1 := by norm_num [p]
  have hr := (FusedSignedHalf.result_spec p X Y (!G) hpo hX hY).1
  have hd : skywalkSignedNat p G X Y<p := by
    cases G <;> simp only [skywalkSignedNat,Bool.false_eq_true,if_false,if_true]
    all_goals exact Nat.mod_lt _ hp0
  have hh : (skywalkFieldNat p G false X Y).1<p := by
    simpa only [skywalkFieldNat,Bool.false_eq_true,if_false] using halve_mod_bound p _ hpo hd
  have hleft := FusedSignedHalf.field_identity X Y (!G) hX hY
  have hright := congrArg Prod.fst (skywalkFieldNat_field G false X Y hY)
  have he : (FusedSignedHalf.result p (!G) X Y : Fp)=
      ((skywalkFieldNat p G false X Y).1 : Fp) := by
    cases G <;> simpa only [skywalkPayloadCell,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,if_false,if_true] using hleft.trans hright.symm
  have hv := congrArg (fun z : Fp => z.val) he
  simp only at hv
  rw [ZMod.val_natCast_of_lt hr,ZMod.val_natCast_of_lt hh] at hv
  exact hv

/-- Restore the live sign record and every original non-target bit. This
argument quantifies over a Program, rather than reducing a concrete packed run. -/
theorem fusedFieldSignedHalf_correct (L : ModInPlaceLayout) (unused : List Wire)
    (g : Wire) (kernel : Program) (X Y : Nat) (hX : X<p) (hY : Y<p)
    (hn : (g::L.wires).Nodup) (hgu : g∉unused)
    (hkernel : ∀ st : State, ∀ ms : List Bool,
      regValue L.a st.basis=Y → regValue L.z st.basis=X →
      regValue L.work st.basis=0 → regValue unused st.basis=0 →
      (run kernel ms st).phase=st.phase ∧
      (∀ q,q∉L.z → (run kernel ms st).basis q=st.basis q) ∧
      regValue L.z (run kernel ms st).basis=FusedSignedHalf.result p (st.basis g) X Y)
    (s : State) (record : List Bool) (hy : regValue L.a s.basis=Y)
    (hx : regValue L.z s.basis=X) (hk : regValue L.work s.basis=0)
    (hu : regValue unused s.basis=0) :
    (run (fusedFieldSignedHalf g kernel) record s).phase=s.phase ∧
    (∀ q,q∉L.z → (run (fusedFieldSignedHalf g kernel) record s).basis q=s.basis q) ∧
    regValue L.z (run (fusedFieldSignedHalf g kernel) record s).basis=
      (skywalkFieldNat p (s.basis g) false X Y).1 := by
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
    exact fusedField_result (s.basis g) X Y hX hY

end ECDSAAdd.Arithmetic
