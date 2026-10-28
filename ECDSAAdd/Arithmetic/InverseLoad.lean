import ECDSAAdd.Arithmetic.InverseLayout

namespace ECDSAAdd.Arithmetic

/-- 装载证明使用的六个不交寄存器；rest 包括输入与输出的内部高位。 -/
inductive InverseField where
  | x | u | v | s | out | rest
  deriving DecidableEq

def InverseLayout.reg (L : InverseLayout) : InverseField → List Wire
  | .x => L.x | .u => L.inner.first.u | .v => L.vLow
  | .s => L.inner.first.s | .out => L.out | .rest => L.rest

def InverseValues (L : InverseLayout) (v : InverseField → Nat) (st : BasisState) : Prop :=
  ∀ f, regValue (L.reg f) st=v f

namespace InverseLayout

theorem reg_count (L : InverseLayout) (f : InverseField) (w : Wire) :
    (L.reg f).count w ≤ L.wires.count w := by
  cases f <;> simp only [reg,wires,work,List.count_append] <;> omega

theorem reg_nodup (L : InverseLayout) (hnd : L.wires.Nodup) (f : InverseField) : (L.reg f).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  exact (L.reg_count f w).trans (List.nodup_iff_count.mp hnd w)

theorem reg_disjoint (L : InverseLayout) (hnd : L.wires.Nodup) (f g : InverseField) (hne : f≠g) :
    (L.reg f).Disjoint (L.reg g) := by
  apply (List.nodup_append'.mp ?_).2.2
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  cases f <;> cases g <;> (try contradiction) <;>
    simp only [reg,wires,work,List.count_append] at h ⊢ <;> omega

end InverseLayout

theorem InverseValues.update (L : InverseLayout) (hnd : L.wires.Nodup)
    (v : InverseField → Nat) (f : InverseField) (V : Nat) (s t : BasisState)
    (hv : InverseValues L v s) (he : ∀ w,w∉L.reg f → t w=s w)
    (hz : regValue (L.reg f) t=V) : InverseValues L (Function.update v f V) t := by
  intro g
  by_cases hg : g=f
  · subst g; simpa using hz
  · rw [Function.update_of_ne hg]
    exact (regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp (L.reg_disjoint hnd g f hg) hw))).trans (hv g)

theorem inverseConstant_values (L : InverseLayout) (hnd : L.wires.Nodup)
    (v : InverseField → Nat) (f : InverseField) (k : Nat) (hk : k<2^(L.reg f).length) :
    Triple (InverseValues L v) (xorConstant (L.reg f) k)
      (InverseValues L (Function.update v f (v f ^^^ k))) := by
  intro s m h
  obtain ⟨hp,he,hz⟩ := xorConstant_correct (L.reg f) (L.reg_nodup hnd f) k hk s m
  exact ⟨hp,InverseValues.update L hnd v f _ s.basis _ h he (by simpa only [h f] using hz)⟩

theorem inverseInput_values (L : InverseLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (v : InverseField → Nat) :
    Triple (InverseValues L v) (copyRegister none L.x L.vLow)
      (InverseValues L (Function.update v .v (v .v ^^^ v .x))) := by
  intro s m h
  have hn : (L.x++L.vLow).Nodup := List.nodup_append'.mpr
    ⟨L.reg_nodup hnd .x,L.reg_nodup hnd .v,L.reg_disjoint hnd .x .v (by decide)⟩
  obtain ⟨hp,he,hz⟩ := copyRegister_correct none L.x L.vLow
    (by simp [InverseLayout.vLow,hw.input,hw.low]) hn (by simp) s m
  exact ⟨hp,InverseValues.update L hnd v .v _ s.basis _ h he
    (by simpa only [copyValue,show regValue L.x s.basis=v .x from h .x,
      show regValue L.vLow s.basis=v .v from h .v] using hz)⟩

def inverseValues (X U V S O : Nat) : InverseField → Nat
  | .x => X | .u => U | .v => V | .s => S | .out => O | .rest => 0

set_option exponentiation.threshold 257 in
theorem inverseLoad_values (L : InverseLayout) (hnd : L.wires.Nodup) (hw : L.Widths)
    (X O : Nat) :
    Triple (InverseValues L (inverseValues X 0 0 0 O)) (inverseLoad L)
      (InverseValues L (inverseValues X p X 1 O)) ∧
    Triple (InverseValues L (inverseValues X p X 1 O)) (inverseUnload L)
      (InverseValues L (inverseValues X 0 0 0 O)) := by
  have hu : p<2^(L.reg .u).length := by
    change p<2^(L.inner.first.data.reg .u).length
    rw [L.inner.first.data.reg_length]
    simp only [KaliskiRoundLayout.data,RoundDataLayout.width,List.length_append,List.length_cons,List.length_nil,hw.low]
    have hp : p<2^256 := by norm_num [p]
    exact hp.trans (Nat.pow_lt_pow_right (by decide) (show 256<256+1 from Nat.lt_succ_self _))
  have hs : 1<2^(L.reg .s).length := by
    change 1<2^(L.inner.first.data.reg .s).length
    rw [L.inner.first.data.reg_length]
    norm_num [KaliskiRoundLayout.data,RoundDataLayout.width,hw.low]
  have eqv (X U V S O K : Nat) : Function.update (inverseValues X U V S O) .v K=inverseValues X U K S O := by
    funext f; cases f <;> simp [inverseValues]
  have equ (X U V S O K : Nat) : Function.update (inverseValues X U V S O) .u K=inverseValues X K V S O := by
    funext f; cases f <;> simp [inverseValues]
  have eqs (X U V S O K : Nat) : Function.update (inverseValues X U V S O) .s K=inverseValues X U V K O := by
    funext f; cases f <;> simp [inverseValues]
  have hc (U V S : Nat) := inverseInput_values L hnd hw (inverseValues X U V S O)
  have hcu (U V S : Nat) := inverseConstant_values L hnd (inverseValues X U V S O) .u p hu
  have hcs (U V S : Nat) := inverseConstant_values L hnd (inverseValues X U V S O) .s 1 hs
  simp only [inverseValues,eqv,equ,eqs] at hc hcu hcs
  have hf1 := hc 0 0 0
  have hf2 := hcu 0 X 0
  have hf3 := hcs p X 0
  have hb1 := hcs p X 1
  have hb2 := hcu p X 0
  have hb3 := hc 0 X 0
  simp only [Nat.zero_xor,Nat.xor_self] at hf1 hf2 hf3 hb1 hb2 hb3
  constructor
  · simpa only [inverseLoad] using (hf1.seq hf2).seq hf3
  · simpa only [inverseUnload] using (hb1.seq hb2).seq hb3

end ECDSAAdd.Arithmetic
