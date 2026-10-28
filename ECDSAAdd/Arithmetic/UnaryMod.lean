import ECDSAAdd.Arithmetic.ModularXorSteps

namespace ECDSAAdd.Arithmetic
open ExternalMod

/-- 载入一组外部输入，复制模运算结果后以同一 XOR 程序清理。 -/
def unaryModXor (L : ModLayout) (f : ModField) (operation : Program) (src dst : List Wire) : Program :=
  copyRegister none src (L.reg f) ++ operation ++ copyRegister none L.out dst ++
    operation ++ copyRegister none src (L.reg f)

def reduceXor (L : ModLayout) (q : Nat) (src dst : List Wire) : Program :=
  unaryModXor L .x (modAdd L q) src dst

def negateXor (L : ModLayout) (q : Nat) (src dst : List Wire) : Program :=
  unaryModXor L .y (modSub L q) src dst

private theorem unary_values (L : ModLayout) (f : ModField) (hf : f ≠ .out)
    (operation : Program) (src dst : List Wire) (hnd : (src ++ dst ++ L.wires).Nodup)
    (hs : src.length=L.width+1) (hd : dst.length=L.width+1) (X O R : Nat)
    (hop : ∀ B Z, Triple (Values L src dst X B (Function.update (Function.update (fun _ => 0) f X) .out Z))
      operation (Values L src dst X B (Function.update (Function.update (fun _ => 0) f X) .out (Z ^^^ R)))) :
    Triple (Values L src dst X O (fun _ => 0)) (unaryModXor L f operation src dst)
      (Values L src dst X (O ^^^ R) (fun _ => 0)) := by
  let v0 : ModField → Nat := fun _ => 0
  let v1 := Function.update v0 f X
  let v2 := Function.update v1 .out R
  let v3 := Function.update v2 .out 0
  let v4 := Function.update v3 f 0
  have hv1 : Function.update v1 .out 0 = v1 := by
    apply Function.update_eq_self_iff.mpr
    simp [v1,v0,Ne.symm hf]
  have h0 : Triple (Values L src dst X O v0) (copyRegister none src (L.reg f))
      (Values L src dst X O v1) := by
    simpa [v1,v0] using copy_into L src dst hnd hs X O v0 f
  have h1 : Triple (Values L src dst X O v1) operation (Values L src dst X O v2) := by
    have h := hop O 0
    change Triple (Values L src dst X O (Function.update v1 .out 0)) operation
      (Values L src dst X O (Function.update v1 .out (0 ^^^ R))) at h
    simpa only [Nat.zero_xor,hv1] using h
  have h2 : Triple (Values L src dst X O v2) (copyRegister none L.out dst)
      (Values L src dst X (O ^^^ R) v2) := by
    simpa [v2] using copy_out L src dst hnd hd X O v2
  have h3 : Triple (Values L src dst X (O ^^^ R) v2) operation
      (Values L src dst X (O ^^^ R) v3) := by
    simpa only [v3,v2,v1,v0,Nat.xor_self,Function.update_idem] using hop (O ^^^ R) R
  have h4 : Triple (Values L src dst X (O ^^^ R) v3) (copyRegister none src (L.reg f))
      (Values L src dst X (O ^^^ R) v4) := by
    simpa [v4,v3,v2,v1,v0,hf] using copy_into L src dst hnd hs X (O ^^^ R) v3 f
  have hv4 : v4=v0 := by
    funext g
    by_cases hg : g=f
    · subst g; simp [v4,v0]
    · by_cases ho : g=.out
      · subst g; simp [v4,v3,v2,v1,v0,Ne.symm hf]
      · simp [v4,v3,v2,v1,v0,hg,ho]
  simpa only [unaryModXor,List.append_assoc,hv4,v0] using h0.seq (h1.seq (h2.seq (h3.seq h4)))

theorem reduceXor_spec (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (hs : src.length=L.width+1)
    (hd : dst.length=L.width+1) (q X O : Nat) (hq0 : 0<q) (hq : q<2^L.width) (hx : X<2*q) :
    {{ src=X, dst=O, L.wires=0 }} reduceXor L q src dst
    {{ src=X, dst=(O ^^^ (X%q)), L.wires=0 }} := by
  apply Triple.conseq (fun st h => ⟨h.1.1,h.1.2,(zeros_iff L st).mpr h.2⟩)
    (unary_values L .x (by decide) (modAdd L q) src dst hnd hs hd X O (X%q) ?_)
    (fun st h => ⟨⟨h.1,h.2.1⟩,(zeros_iff L st).mp h.2.2⟩)
  intro B Z
  simpa using ExternalMod.mod_add L src dst hnd X B q
    (Function.update (Function.update (fun _ => 0) .x X) .out Z) hq0 hq (by simpa using hx)
    (by intro f hf _ ho; simp [hf,ho])

theorem negateXor_spec (L : ModLayout) (src dst : List Wire)
    (hnd : (src ++ dst ++ L.wires).Nodup) (hs : src.length=L.width+1)
    (hd : dst.length=L.width+1) (q X O : Nat) (hq0 : 0<q) (hq : q<2^L.width) (hx : X<q) :
    {{ src=X, dst=O, L.wires=0 }} negateXor L q src dst
    {{ src=X, dst=(O ^^^ ((q-X)%q)), L.wires=0 }} := by
  apply Triple.conseq (fun st h => ⟨h.1.1,h.1.2,(zeros_iff L st).mpr h.2⟩)
    (unary_values L .y (by decide) (modSub L q) src dst hnd hs hd X O ((q-X)%q) ?_)
    (fun st h => ⟨⟨h.1,h.2.1⟩,(zeros_iff L st).mp h.2.2⟩)
  intro B Z
  simpa using ExternalMod.mod_sub L src dst hnd X B q
    (Function.update (Function.update (fun _ => 0) .y X) .out Z) hq0 hq
    (by simpa using hq0) (by simpa using hx) (by intro f _ hf ho; simp [hf,ho])

end ECDSAAdd.Arithmetic
