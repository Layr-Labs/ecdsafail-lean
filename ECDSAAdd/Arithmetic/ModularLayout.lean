import ECDSAAdd.Arithmetic.Layout
import ECDSAAdd.Arithmetic.Select
import ECDSAAdd.Arithmetic.Constant

namespace ECDSAAdd.Arithmetic

/-- 两个输入、和、模数、候选差、输出，以及两组进位工作线。 -/
inductive ModField where
  | x | y | total | modulus | diff | out | carrySum | carryDiff
  deriving DecidableEq

structure ModBit where
  x : Wire
  y : Wire
  total : Wire
  modulus : Wire
  diff : Wire
  out : Wire
  carrySum : Wire
  carryDiff : Wire

def ModBit.get (b : ModBit) : ModField → Wire
  | .x => b.x | .y => b.y | .total => b.total | .modulus => b.modulus
  | .diff => b.diff | .out => b.out | .carrySum => b.carrySum | .carryDiff => b.carryDiff

def ModBit.all (b : ModBit) : List Wire :=
  [b.x, b.y, b.total, b.modulus, b.diff, b.out, b.carrySum, b.carryDiff]

/-- high 是额外的最高位，候选差的这个位直接用于选择，不另存 flag。 -/
structure ModLayout where
  low : List ModBit
  high : ModBit
  cinSum : Wire
  cinDiff : Wire

namespace ModLayout

def bits (L : ModLayout) : List ModBit := L.low ++ [L.high]
def width (L : ModLayout) : Nat := L.low.length
def reg (L : ModLayout) (f : ModField) : List Wire := L.bits.map (fun b => b.get f)
def lowReg (L : ModLayout) (f : ModField) : List Wire := L.low.map (fun b => b.get f)
def x (L : ModLayout) : List Wire := L.reg .x
def y (L : ModLayout) : List Wire := L.reg .y
def out (L : ModLayout) : List Wire := L.reg .out
def work (L : ModLayout) : List Wire :=
  L.reg .total ++ L.reg .modulus ++ L.reg .diff ++ L.reg .carrySum ++ L.reg .carryDiff ++
    [L.cinSum, L.cinDiff]
def wires (L : ModLayout) : List Wire := L.cinSum :: L.cinDiff :: L.bits.flatMap ModBit.all

def adder (L : ModLayout) (a b target carry : ModField) (cin : Wire) : AdderLayout :=
  ⟨L.bits.map (fun bit => ⟨bit.get a, bit.get b, bit.get target, bit.get carry⟩), cin⟩

def selector (L : ModLayout) : List SelectBit :=
  L.low.map (fun b => ⟨b.diff, b.total, b.out⟩)

end ModLayout

private theorem get_mem (b : ModBit) (f : ModField) : b.get f ∈ b.all := by
  cases f <;> simp [ModBit.get, ModBit.all]

private theorem get_ne (b : ModBit) (hb : b.all.Nodup) (f g : ModField) (hfg : f ≠ g) :
    b.get f ≠ b.get g := by
  cases f <;> cases g <;> simp_all [ModBit.get, ModBit.all, List.nodup_cons] <;> exact Ne.symm (by tauto)

private theorem select_blocks_nodup (bs : List ModBit) (h : (bs.flatMap ModBit.all).Nodup)
    (f : ModBit → List Wire) (hsub : ∀ b, f b ⊆ b.all)
    (hlocal : ∀ b, b.all.Nodup → (f b).Nodup) : (bs.flatMap f).Nodup := by
  obtain ⟨hn, hp⟩ := List.nodup_flatMap.mp h
  apply List.nodup_flatMap.mpr
  refine ⟨fun b hb => hlocal b (hn b hb), hp.imp ?_⟩
  intro a b hab
  apply List.disjoint_left.mpr
  intro w hw hw'
  exact List.disjoint_left.mp hab (hsub a hw) (hsub b hw')

private theorem field_disjoint (bs : List ModBit) (h : (bs.flatMap ModBit.all).Nodup)
    (f g : ModField) (hfg : f ≠ g) :
    (bs.map (fun b => b.get f)).Disjoint (bs.map (fun b => b.get g)) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨hb, ht, hd⟩ := List.nodup_append'.mp h
    apply List.disjoint_left.mpr
    intro w hw hw'
    simp only [List.map_cons, List.mem_cons] at hw hw'
    rcases hw with rfl | hw
    · rcases hw' with he | hw'
      · exact get_ne b hb f g hfg he
      · obtain ⟨c, hc, he⟩ := List.mem_map.mp hw'
        exact List.disjoint_left.mp hd (get_mem b f)
          (he ▸ List.mem_flatMap.mpr ⟨c, hc, get_mem c g⟩)
    · rcases hw' with rfl | hw'
      · obtain ⟨c, hc, he⟩ := List.mem_map.mp hw
        exact List.disjoint_left.mp hd (get_mem b g)
          (he ▸ List.mem_flatMap.mpr ⟨c, hc, get_mem c f⟩)
      · exact List.disjoint_left.mp (ih ht) hw hw'

theorem ModLayout.reg_length (L : ModLayout) (f : ModField) : (L.reg f).length = L.width + 1 := by
  simp [ModLayout.reg, ModLayout.bits, ModLayout.width]

theorem ModLayout.reg_mem (L : ModLayout) (f : ModField) {w : Wire} (hw : w ∈ L.reg f) :
    w ∈ L.bits.flatMap ModBit.all := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
  exact List.mem_flatMap.mpr ⟨b, hb, get_mem b f⟩

theorem ModLayout.reg_nodup (L : ModLayout) (hnd : L.wires.Nodup) (f : ModField) :
    (L.reg f).Nodup := by
  have hn := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
  have h := select_blocks_nodup L.bits hn (fun b => [b.get f])
    (by
      intro b w hw
      have he : w = b.get f := by simpa using hw
      subst w
      exact get_mem b f)
    (by intro b _; simp)
  have he : L.bits.flatMap (fun b => [b.get f]) = L.bits.map (fun b => b.get f) := by
    induction L.bits with
    | nil => rfl
    | cons b bs ih => simp [ih]
  rw [he] at h
  exact h

theorem ModLayout.reg_disjoint (L : ModLayout) (hnd : L.wires.Nodup)
    (f g : ModField) (hfg : f ≠ g) : (L.reg f).Disjoint (L.reg g) :=
  field_disjoint L.bits (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2 f g hfg

theorem ModLayout.cinSum_not_reg (L : ModLayout) (hnd : L.wires.Nodup) (f : ModField) :
    L.cinSum ∉ L.reg f := by
  intro h
  exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ (L.reg_mem f h))

theorem ModLayout.cinDiff_not_reg (L : ModLayout) (hnd : L.wires.Nodup) (f : ModField) :
    L.cinDiff ∉ L.reg f := by
  intro h
  exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (L.reg_mem f h)

theorem addWires_map (bs : List ModBit) (a b target carry : ModField) :
    addWires (bs.map (fun bit => AddBit.mk (bit.get a) (bit.get b) (bit.get target) (bit.get carry))) =
      bs.flatMap (fun bit => [bit.get a, bit.get b, bit.get target, bit.get carry]) := by
  induction bs with
  | nil => rfl
  | cons bit bs ih => simp [addWires, ih]

/-- 任取互异的四类线路组成加法器，其线路互异从总布局导出。 -/
theorem ModLayout.adder_nodup (L : ModLayout) (hnd : L.wires.Nodup)
    (a b target carry : ModField) (hf : [a, b, target, carry].Nodup)
    (cin : Wire) (hc : cin = L.cinSum ∨ cin = L.cinDiff) :
    (L.adder a b target carry cin).wires.Nodup := by
  have hn := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
  have hs (bit : ModBit) : [bit.get a, bit.get b, bit.get target, bit.get carry] ⊆ bit.all := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl <;> exact get_mem _ _
  have hlocal (bit : ModBit) (hbit : bit.all.Nodup) :
      [bit.get a, bit.get b, bit.get target, bit.get carry].Nodup := by
    have hinj : Function.Injective bit.get := fun f g he => by
      by_contra hfg
      exact get_ne bit hbit f g hfg he
    exact hf.map hinj
  change (cin :: addWires _).Nodup
  simp only [ModLayout.adder]
  rw [addWires_map]
  refine List.nodup_cons.mpr ⟨?_, select_blocks_nodup L.bits hn _ hs hlocal⟩
  intro hm
  obtain ⟨bit, hb, hm⟩ := List.mem_flatMap.mp hm
  have hall := List.mem_flatMap.mpr ⟨bit, hb, hs bit hm⟩
  rcases hc with rfl | rfl
  · exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hall)
  · exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hall

@[simp] theorem ModLayout.adder_x (L : ModLayout) (a b target carry : ModField) (cin : Wire) :
    (L.adder a b target carry cin).x = L.reg a := by
  simp [ModLayout.adder, AdderLayout.x, ModLayout.reg, List.map_map]

@[simp] theorem ModLayout.adder_y (L : ModLayout) (a b target carry : ModField) (cin : Wire) :
    (L.adder a b target carry cin).y = L.reg b := by
  simp [ModLayout.adder, AdderLayout.y, ModLayout.reg, List.map_map]

@[simp] theorem ModLayout.adder_out (L : ModLayout) (a b target carry : ModField) (cin : Wire) :
    (L.adder a b target carry cin).out = L.reg target := by
  simp [ModLayout.adder, AdderLayout.out, ModLayout.reg, List.map_map]

@[simp] theorem ModLayout.adder_carry (L : ModLayout) (a b target carry : ModField) (cin : Wire) :
    (L.adder a b target carry cin).carry = L.reg carry := by
  simp [ModLayout.adder, AdderLayout.carry, ModLayout.reg, List.map_map]

@[simp] theorem ModLayout.adder_width (L : ModLayout) (a b target carry : ModField) (cin : Wire) :
    (L.adder a b target carry cin).width = L.width + 1 := by
  simp [ModLayout.adder, AdderLayout.width, ModLayout.bits, ModLayout.width]

@[simp] theorem ModLayout.selector_no (L : ModLayout) :
    L.selector.map SelectBit.no = L.lowReg .diff := by
  simp [ModLayout.selector, ModLayout.lowReg, ModBit.get, List.map_map]

@[simp] theorem ModLayout.selector_yes (L : ModLayout) :
    L.selector.map SelectBit.yes = L.lowReg .total := by
  simp [ModLayout.selector, ModLayout.lowReg, ModBit.get, List.map_map]

@[simp] theorem ModLayout.selector_out (L : ModLayout) :
    L.selector.map SelectBit.out = L.lowReg .out := by
  simp [ModLayout.selector, ModLayout.lowReg, ModBit.get, List.map_map]

theorem selectWires_map (bs : List ModBit) :
    selectWires (bs.map (fun b => SelectBit.mk b.diff b.total b.out)) =
      bs.flatMap (fun b => [b.diff, b.total, b.out]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [selectWires, ih]

theorem ModLayout.selector_nodup (L : ModLayout) (hnd : L.wires.Nodup) :
    (selectWires L.selector).Nodup := by
  rw [ModLayout.selector, selectWires_map]
  have hall := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
  simp only [ModLayout.bits, List.flatMap_append] at hall
  have hlo : (L.low.flatMap ModBit.all).Nodup := (List.nodup_append'.mp hall).1
  apply select_blocks_nodup L.low hlo
  · intro b w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp [ModBit.all]
  · intro b hb
    have hdt := get_ne b hb .diff .total (by decide)
    have hdo := get_ne b hb .diff .out (by decide)
    have hto := get_ne b hb .total .out (by decide)
    simpa [List.nodup_cons, ModBit.get] using And.intro (And.intro hdt hdo) hto

theorem ModLayout.high_diff_mem (L : ModLayout) : L.high.diff ∈ L.reg .diff := by
  simp [ModLayout.reg, ModLayout.bits, ModBit.get]

theorem ModLayout.flag_not_output (L : ModLayout) (hnd : L.wires.Nodup) :
    L.high.diff ∉ L.selector.map SelectBit.out := by
  rw [ModLayout.selector_out]
  intro hw
  apply List.disjoint_left.mp (L.reg_disjoint hnd .diff .out (by decide)) L.high_diff_mem
  simpa [ModLayout.reg, ModLayout.bits, ModLayout.lowReg] using Or.inl (b := L.high.diff = L.high.get .out) hw

theorem ModLayout.reg_eq (L : ModLayout) (f : ModField) :
    L.reg f = L.lowReg f ++ [L.high.get f] := by
  simp [ModLayout.reg, ModLayout.lowReg, ModLayout.bits]

theorem ModLayout.lowReg_subset (L : ModLayout) (f : ModField) : L.lowReg f ⊆ L.reg f := by
  rw [L.reg_eq]
  exact List.subset_append_left _ _

/-- 选择位来自额外高位，不与任何低位门的输入或输出重合。 -/
theorem ModLayout.flag_not_selector (L : ModLayout) (hnd : L.wires.Nodup) :
    L.high.diff ∉ selectWires L.selector := by
  intro hw
  rw [ModLayout.selector, selectWires_map] at hw
  obtain ⟨b, hb, hm⟩ := List.mem_flatMap.mp hw
  have hlow : L.high.diff ∈ L.low.flatMap ModBit.all := by
    apply List.mem_flatMap.mpr
    refine ⟨b, hb, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm <;> simp [ModBit.all, hm]
  have hn := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2
  simp only [ModLayout.bits, List.flatMap_append] at hn
  exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 hlow (by simp [ModBit.all])

end ECDSAAdd.Arithmetic
