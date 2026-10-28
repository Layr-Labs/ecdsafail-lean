import ECDSAAdd.Arithmetic.DialogMiddle

namespace ECDSAAdd.Arithmetic
open Secp256k1

private theorem dialogWork_zero (L : DialogLayout) (s : BasisState) :
    regValue L.work s=0 ↔ regValue L.first.u s=0 ∧ regValue L.first.v s=0 ∧
      regValue L.rest s=0 ∧ regValue L.z s=0 := by
  have perm : (L.first.u++L.first.v++L.rest++L.z).Perm L.work := by
    apply List.perm_iff_count.mpr
    intro w
    have h1 := L.ready_perm.count_eq w
    have h2 := L.external_value_perm.count_eq w
    simp only [DialogLayout.external,DialogLayout.work,List.count_append,List.count_cons] at h1 h2 ⊢
    omega
  have hz : regValue L.work s=0 ↔ regValue (L.first.u++L.first.v++L.rest++L.z) s=0 := by
    simp only [regValue_zero]
    constructor <;> intro h w hw
    · exact h w (perm.mem_iff.mp hw)
    · exact h w (perm.mem_iff.mpr hw)
  rw [hz]
  simp only [regValue_zero,List.mem_append,or_imp,forall_and,and_assoc]

private theorem dialog_values_specs (L : DialogLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Nat) (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) :
    Triple (DialogValues L B X Y 0 0 0) (dialogDivide L p)
      (DialogValues L B X (if B then ((Y:Fp)/(X:Fp)).val else Y) 0 0 0) ∧
    Triple (DialogValues L B X Y 0 0 0) (dialogMultiply L p)
      (DialogValues L B X (if B then ((Y:Fp)*(X:Fp)).val else Y) 0 0 0) := by
  let S := if B then X else 1
  have hs0 : 0<S := by dsimp [S]; split; exact Nat.pos_of_ne_zero (hX0 ‹B=true›); decide
  have hs : S<p := by dsimp [S]; split; exact hX; decide
  have hp256 : p<2^256 := by decide
  have hp : p<2^L.first.u.length := by
    have hl : L.first.u.length=257 := by
      simp [KaliskiRoundLayout.u,KaliskiRoundLayout.data,RoundDataLayout.u,RoundDataLayout.reg,hw.low]
    rw [hl,show (257:Nat)=256+1 from rfl,pow_succ]; norm_num [p]
  have load : Triple (DialogValues L B X Y 0 0 0) (dialogLoad L p)
      (DialogValues L B X Y 0 p S) := by
    simpa only [Nat.zero_xor] using dialogLoad_values L p hw hn hp B X Y 0 0 0 (by decide)
  have unload (V : Nat) : Triple (DialogValues L B X V 0 p S) (dialogLoad L p)
      (DialogValues L B X V 0 0 0) := by
    simpa only [S,Nat.xor_self] using dialogLoad_values L p hw hn hp B X V 0 p S (hs.trans hp256)
  have walk (A C : Nat) := dialogWalk_specs L hw hn S hs0 hs B X A C
  have rep := dialogReplay_specs L hw hn S hs0 hs B X Y hY
  have qval : ((Y:Fp)/(S:Fp)).val=(if B then ((Y:Fp)/(X:Fp)).val else Y) := by
    cases B <;> simp [S,ZMod.val_natCast_of_lt hY]
  have pval : ((Y:Fp)*(S:Fp)).val=(if B then ((Y:Fp)*(X:Fp)).val else Y) := by
    cases B <;> simp [S,ZMod.val_natCast_of_lt hY]
  constructor
  · have hh := load.seq ((walk Y 0).1.seq ((dialogExchange_spec L hn S B X Y 0).seq
      (rep.1.seq ((walk _ 0).2.seq (unload _)))))
    rw [qval] at hh
    simpa only [dialogDivide,List.append_assoc] using hh
  · have hh := load.seq ((walk Y 0).1.seq (rep.2.seq ((dialogExchange_spec L hn S B X 0 _).seq
      ((walk _ 0).2.seq (unload _)))))
    rw [pval] at hh
    simpa only [dialogMultiply,List.append_assoc] using hh

/-- 启用时原地除法；控制为假时保持Y，全部工作位归零，不另要求Y非零。 -/
theorem dialogDivide_spec (L : DialogLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Nat) (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) :
    {{ L.control=B,L.x=X,L.y=Y,L.work=0 }} dialogDivide L p
    {{ L.control=B,L.x=X,L.y=(if B then ((Y:Fp)/(X:Fp)).val else Y),L.work=0 }} := by
  apply (dialog_values_specs L hw hn B X Y hX hX0 hY).1.conseq
  · intro s h
    have hz := (dialogWork_zero L s).mp h.2
    exact ⟨h.1.1.1,h.1.1.2,h.1.2,hz.2.2.2,hz.1,hz.2.1,hz.2.2.1⟩
  · intro s h
    exact ⟨⟨⟨h.1,h.2.1⟩,h.2.2.1⟩,(dialogWork_zero L s).mpr
      ⟨h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2,h.2.2.2.1⟩⟩

/-- 启用时原地乘法；非零条件只作用于启用的X，与除法共用可逆历史。 -/
theorem dialogMultiply_spec (L : DialogLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Nat) (hX : X<p) (hX0 : B=true → X≠0) (hY : Y<p) :
    {{ L.control=B,L.x=X,L.y=Y,L.work=0 }} dialogMultiply L p
    {{ L.control=B,L.x=X,L.y=(if B then ((Y:Fp)*(X:Fp)).val else Y),L.work=0 }} := by
  apply (dialog_values_specs L hw hn B X Y hX hX0 hY).2.conseq
  · intro s h
    have hz := (dialogWork_zero L s).mp h.2
    exact ⟨h.1.1.1,h.1.1.2,h.1.2,hz.2.2.2,hz.1,hz.2.1,hz.2.2.1⟩
  · intro s h
    exact ⟨⟨⟨h.1,h.2.1⟩,h.2.2.1⟩,(dialogWork_zero L s).mpr
      ⟨h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2,h.2.2.2.1⟩⟩

end ECDSAAdd.Arithmetic
