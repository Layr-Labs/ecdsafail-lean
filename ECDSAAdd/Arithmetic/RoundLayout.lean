import ECDSAAdd.Arithmetic.MaskedAdder
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.ZeroControl
import ECDSAAdd.Arithmetic.Shift

namespace ECDSAAdd.Arithmetic

/-- 四份 EEA 数据与一份共用算术/零检测工作区。 -/
inductive RoundField where
  | u | v | r | s | y | out | carry | zero
  deriving DecidableEq

structure RoundBit where
  u : Wire
  v : Wire
  r : Wire
  s : Wire
  y : Wire
  out : Wire
  carry : Wire
  zero : Wire

def RoundBit.get (b : RoundBit) : RoundField → Wire
  | .u => b.u | .v => b.v | .r => b.r | .s => b.s
  | .y => b.y | .out => b.out | .carry => b.carry | .zero => b.zero

def RoundBit.wires (b : RoundBit) : List Wire :=
  [b.u,b.v,b.r,b.s,b.y,b.out,b.carry,b.zero]

structure RoundDataLayout where
  bits : List RoundBit
  cin : Wire

namespace RoundDataLayout

def width (L : RoundDataLayout) : Nat := L.bits.length
def reg (L : RoundDataLayout) (f : RoundField) : List Wire := L.bits.map (fun b => b.get f)
def u (L : RoundDataLayout) : List Wire := L.reg .u
def v (L : RoundDataLayout) : List Wire := L.reg .v
def r (L : RoundDataLayout) : List Wire := L.reg .r
def s (L : RoundDataLayout) : List Wire := L.reg .s
def work (L : RoundDataLayout) : List Wire :=
  L.cin :: (L.reg .y ++ L.reg .out ++ L.reg .carry ++ L.reg .zero)
def wires (L : RoundDataLayout) : List Wire := L.cin :: L.bits.flatMap RoundBit.wires

/-- 只更换加法器的数据来源，y/out/carry 始终是同一组物理工作线。 -/
def adder (L : RoundDataLayout) (f : RoundField) : AdderLayout :=
  ⟨L.bits.map (fun b => ⟨b.get f,b.y,b.out,b.carry⟩),L.cin⟩

def zeroBits (L : RoundDataLayout) (f : RoundField) : List ZeroBit :=
  L.bits.map (fun b => ⟨b.get f,b.zero⟩)

theorem reg_length (L : RoundDataLayout) (f : RoundField) : (L.reg f).length=L.width := by
  simp [reg, width]

theorem reg_mem (L : RoundDataLayout) (f : RoundField) {w : Wire} (h : w∈L.reg f) : w∈L.wires := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨b,hb,?_⟩
  cases f <;> simp [RoundBit.get, RoundBit.wires]

set_option maxHeartbeats 2000000 in
theorem reg_count (L : RoundDataLayout) (f : RoundField) (w : Wire) :
    (L.reg f).count w ≤ L.wires.count w := by
  rcases L with ⟨bs,cin⟩
  induction bs with
  | nil => simp [reg, wires]
  | cons b bs ih =>
    cases f <;> simp [reg, wires, RoundBit.get, RoundBit.wires, List.count_cons] at ih ⊢ <;> omega

set_option maxHeartbeats 4000000 in
theorem pair_count (L : RoundDataLayout) (f g : RoundField) (hne : f≠g) (w : Wire) :
    (L.reg f).count w + (L.reg g).count w ≤ L.wires.count w := by
  rcases L with ⟨bs,cin⟩
  induction bs with
  | nil => simp [reg, wires]
  | cons b bs ih =>
    cases f <;> cases g <;> (try contradiction) <;>
      simp [reg, wires, RoundBit.get, RoundBit.wires, List.count_cons] at ih ⊢ <;> omega

theorem reg_nodup (L : RoundDataLayout) (hnd : L.wires.Nodup) (f : RoundField) : (L.reg f).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  exact (L.reg_count f w).trans (List.nodup_iff_count.mp hnd w)

theorem reg_disjoint (L : RoundDataLayout) (hnd : L.wires.Nodup) (f g : RoundField) (hne : f≠g) :
    (L.reg f).Disjoint (L.reg g) := by
  apply (List.nodup_append'.mp ?_).2.2
  apply List.nodup_iff_count.mpr
  intro w
  rw [List.count_append]
  exact (L.pair_count f g hne w).trans (List.nodup_iff_count.mp hnd w)

theorem cin_not_mem (L : RoundDataLayout) (hnd : L.wires.Nodup) (f : RoundField) : L.cin∉L.reg f := by
  intro h
  obtain ⟨b,hb,hc⟩ := List.mem_map.mp h
  apply (List.nodup_cons.mp hnd).1
  apply List.mem_flatMap.mpr
  refine ⟨b,hb,?_⟩
  rw [← hc]
  cases f <;> simp [RoundBit.get, RoundBit.wires]

theorem adder_fields (L : RoundDataLayout) (f : RoundField) :
    (L.adder f).x = L.reg f ∧ (L.adder f).y = L.reg .y ∧
    (L.adder f).out = L.reg .out ∧ (L.adder f).carry = L.reg .carry ∧
    (L.adder f).cin = L.cin ∧ (L.adder f).width = L.width := by
  simp [adder, AdderLayout.x, AdderLayout.y, AdderLayout.out, AdderLayout.carry,
    AdderLayout.width, reg, width, List.map_map, Function.comp_def, RoundBit.get]

/-- 算术目标只能是四份数据之一，不能与临时寄存器重叠。 -/
def DataField (f : RoundField) : Prop := f=.u ∨ f=.v ∨ f=.r ∨ f=.s

theorem adder_count (L : RoundDataLayout) (f : RoundField) (hf : DataField f) (w : Wire) :
    (L.adder f).wires.count w ≤ L.wires.count w := by
  rcases L with ⟨bs,cin⟩
  induction bs with
  | nil => simp [adder, AdderLayout.wires, wires, addWires]
  | cons b bs ih =>
    rcases hf with rfl | rfl | rfl | rfl <;>
      simp [adder, AdderLayout.wires, wires, addWires, RoundBit.wires, RoundBit.get, List.count_cons] at ih ⊢ <;> omega

theorem adder_nodup (L : RoundDataLayout) (hnd : L.wires.Nodup) (f : RoundField) (hf : DataField f) :
    (L.adder f).wires.Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  exact (L.adder_count f hf w).trans (List.nodup_iff_count.mp hnd w)

set_option maxHeartbeats 4000000 in
theorem source_adder_count (L : RoundDataLayout) (f g : RoundField)
    (hf : DataField f) (hg : DataField g) (hne : f≠g) (w : Wire) :
    (L.reg g ++ (L.adder f).wires).count w ≤ L.wires.count w := by
  rcases L with ⟨bs,cin⟩
  induction bs with
  | nil => simp [reg, adder, AdderLayout.wires, wires, addWires]
  | cons b bs ih =>
    rcases hf with rfl | rfl | rfl | rfl <;>
      rcases hg with rfl | rfl | rfl | rfl <;> (try contradiction) <;>
      simp [reg, adder, AdderLayout.wires, wires, addWires, RoundBit.wires,
        RoundBit.get, List.count_cons] at ih ⊢ <;> omega

theorem source_adder_nodup (L : RoundDataLayout) (hnd : L.wires.Nodup) (f g : RoundField)
    (hf : DataField f) (hg : DataField g) (hne : f≠g) :
    (L.reg g ++ (L.adder f).wires).Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  exact (L.source_adder_count f g hf hg hne w).trans (List.nodup_iff_count.mp hnd w)

end RoundDataLayout

/-- 寄存器值表用于组合局部更新；cin 始终是零工作位。 -/
def RoundValues (L : RoundDataLayout) (v : RoundField → Nat) (st : BasisState) : Prop :=
  (∀ f, regValue (L.reg f) st=v f) ∧ st L.cin=false

theorem RoundValues.update (L : RoundDataLayout) (hnd : L.wires.Nodup)
    (v : RoundField → Nat) (f : RoundField) (X : Nat) (s t : BasisState)
    (hv : RoundValues L v s) (he : ∀ w, w∉L.reg f → t w=s w)
    (hx : regValue (L.reg f) t=X) : RoundValues L (Function.update v f X) t := by
  refine ⟨?_, (he L.cin (L.cin_not_mem hnd f)).trans hv.2⟩
  intro g
  by_cases hgf : g=f
  · subst g; simpa using hx
  · rw [Function.update_of_ne hgf]
    exact (regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp
      (L.reg_disjoint hnd g f hgf) hw))).trans (hv.1 g)

theorem RoundValues.update_two (L : RoundDataLayout) (hnd : L.wires.Nodup)
    (v : RoundField → Nat) (f g : RoundField) (X Y : Nat) (s t : BasisState)
    (hv : RoundValues L v s) (he : ∀ w, w∉L.reg f → w∉L.reg g → t w=s w)
    (hx : regValue (L.reg f) t=X) (hy : regValue (L.reg g) t=Y) :
    RoundValues L (Function.update (Function.update v f X) g Y) t := by
  refine ⟨?_, (he L.cin (L.cin_not_mem hnd f) (L.cin_not_mem hnd g)).trans hv.2⟩
  intro k
  by_cases hkg : k=g
  · subst k; simpa using hy
  · rw [Function.update_of_ne hkg]
    by_cases hkf : k=f
    · subst k; simpa using hx
    · rw [Function.update_of_ne hkf]
      exact (regValue_congr _ _ _ (fun w hw => he w (List.disjoint_left.mp
        (L.reg_disjoint hnd k f hkf) hw) (List.disjoint_left.mp (L.reg_disjoint hnd k g hkg) hw))).trans (hv.1 k)

end ECDSAAdd.Arithmetic
