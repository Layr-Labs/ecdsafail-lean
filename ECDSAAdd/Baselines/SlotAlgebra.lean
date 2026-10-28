import ECDSAAdd.Baselines.NormalizedEntries

namespace ECDSAAdd.Baselines
open Challenge Arithmetic

@[simp] theorem gateSlots_nil : gateSlots [] = 0 := rfl
@[simp] theorem gateSlots_cons (i : Instr) (p : Program) :
    gateSlots (i :: p) = instructionSlots i + gateSlots p := rfl

@[simp] theorem normalize_gateSlots (p : Program) :
    gateSlots (normalizeProgram p) = gateSlots p := by
  induction p with
  | nil => rfl
  | cons i p ih =>
    cases i with
    | CCX a b t => by_cases h : a = b <;>
        simp [normalizeProgram, normalizeInstr, h, gateSlots_cons, instructionSlots] at ih ⊢ <;> exact ih
    | measureX t cs ds =>
        simpa [normalizeProgram, normalizeInstr, gateSlots_cons, instructionSlots] using congrArg (fun n => 1 + cs.length + ds.length + n) ih
    | X t => simpa [normalizeProgram, normalizeInstr, gateSlots_cons, instructionSlots] using ih
    | CX c t => simpa [normalizeProgram, normalizeInstr, gateSlots_cons, instructionSlots] using ih

@[simp] theorem gateSlots_flatMap {α : Type} (f : α → Program) (xs : List α) :
    gateSlots (xs.flatMap f) = (xs.map (fun x => gateSlots (f x))).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

 theorem xorConstant_gateSlots_le (r : List Wire) (k : Nat) :
    gateSlots (xorConstant r k) ≤ r.length := by
  induction r generalizing k with
  | nil => simp [xorConstant]
  | cons w ws ih =>
    simp only [xorConstant, gateSlots_append, List.length_cons]
    split <;> simp only [gateSlots_cons, gateSlots_nil, instructionSlots] <;> have := ih (k / 2) <;> omega

 theorem maskedConstant_gateSlots_le (c : Wire) (r : List Wire) (k : Nat) :
    gateSlots (maskedConstant c r k) ≤ r.length := by
  induction r generalizing k with
  | nil => simp [maskedConstant]
  | cons w ws ih =>
    simp only [maskedConstant, gateSlots_append, List.length_cons]
    split <;> simp only [gateSlots_cons, gateSlots_nil, instructionSlots] <;> have := ih (k / 2) <;> omega

@[simp] theorem zeroControlled_gateSlots (c t : Wire) (bs : List ZeroBit) :
    gateSlots (zeroControlled c t bs) = 7 * bs.length + 1 := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    change gateSlots ([.X b.input, .CCX c b.input b.work, .X b.input] ++
      zeroControlled b.work t bs ++ [.X b.input, .measureX b.work [] [.CZ c b.input], .X b.input]) = _
    simp [ih, gateSlots_cons, instructionSlots]
    omega

theorem equalConstant_gateSlots_le (c t : Wire) (bs : List ZeroBit) (k : Nat) :
    gateSlots (equalConstant c t bs k) ≤ 9 * bs.length + 1 := by
  have h := xorConstant_gateSlots_le (bs.map ZeroBit.input) k
  simp only [List.length_map] at h
  simp only [equalConstant, gateSlots_append, zeroControlled_gateSlots]
  omega

@[simp] theorem copyRegister_gateSlots (c : Option Wire) (a b : List Wire) :
    gateSlots (copyRegister c a b) = min a.length b.length := by
  induction a generalizing b with
  | nil => simp [copyRegister]
  | cons a as ih =>
    cases b with
    | nil => simp [copyRegister]
    | cons b bs => cases c <;> simp [copyRegister, copyGate, gateSlots_cons, instructionSlots, ih, Nat.add_comm]

@[simp] theorem swapRegisters_gateSlots (c : Wire) (a b : List Wire) :
    gateSlots (swapRegisters c a b) = 3 * min a.length b.length := by
  simp [swapRegisters, Nat.min_comm]; omega

@[simp] theorem exchangeRegisters_gateSlots (a b : List Wire) :
    gateSlots (exchangeRegisters a b) = 3 * min a.length b.length := by
  simp [exchangeRegisters, Nat.min_comm]; omega

@[simp] theorem notRegister_gateSlots (r : List Wire) :
    gateSlots (notRegister r) = r.length := by
  induction r with
  | nil => rfl
  | cons w r ih =>
      change 1 + gateSlots (notRegister r) = r.length + 1
      omega

@[simp] theorem majority_gateSlots (a b c t : Wire) : gateSlots (majority a b c t) = 6 := rfl
@[simp] theorem eraseCarry_gateSlots (a b c t : Wire) : gateSlots (eraseCarry a b c t) = 4 := rfl
@[simp] theorem fullAdder_gateSlots (a b c o t : Wire) : gateSlots (fullAdder a b c o t) = 9 := rfl

@[simp] theorem rippleAdder_gateSlots (bs : List AddBit) (c : Wire) :
    gateSlots (rippleAdder bs c) = 13 * bs.length := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => simp [rippleAdder, ih]; omega

 theorem addInPlace_gateSlots_le (x y cs : List Wire) (c : Wire) :
    gateSlots (addInPlace x y cs c) ≤ 12 * x.length := by
  induction x, y, cs, c using addInPlace.induct with
  | case1 a a' as b b' bs d ds c ih =>
      simp only [addInPlace, gateSlots_append, majority_gateSlots, eraseCarry_gateSlots,
        gateSlots_cons, gateSlots_nil, instructionSlots, List.length_cons] at *
      omega
  | case2 a b cs c => simp [addInPlace, gateSlots_cons, instructionSlots]
  | case3 x y cs c h => simp [addInPlace]

 theorem subInPlace_gateSlots_le (x y cs : List Wire) (c : Wire) :
    gateSlots (subInPlace x y cs c) ≤ 12 * x.length + 2 * y.length := by
  have h := addInPlace_gateSlots_le x y cs c
  simp only [subInPlace, gateSlots_append, notRegister_gateSlots]; omega

@[simp] theorem eraseMask_gateSlots (c : Wire) (a b : List Wire) :
    gateSlots (eraseMask c a b) = 2 * min a.length b.length := by
  induction a generalizing b with
  | nil => simp [eraseMask]
  | cons a as ih =>
    cases b with
    | nil => simp [eraseMask]
    | cons b bs => simp [eraseMask, gateSlots_cons, instructionSlots, ih]; omega

 theorem compareChain_gateSlots_le (ctrl : Option Wire) (x y cs : List Wire) (c t : Wire) :
    gateSlots (compareChain ctrl x y cs c t) ≤ 10 * x.length + 2 := by
  induction x generalizing y cs c with
  | nil => cases y <;> cases cs <;> cases ctrl <;> simp [compareChain, flipBelow, gateSlots_cons, instructionSlots]
  | cons a as ih =>
    cases y with
    | nil => simp [compareChain]
    | cons b bs =>
      cases cs with
      | nil => simp [compareChain]
      | cons d ds =>
        have h := ih bs ds d
        simp only [compareChain, gateSlots_append, majority_gateSlots, eraseCarry_gateSlots, List.length_cons]
        omega

 theorem compareLt_gateSlots_le (ctrl : Option Wire) (x y cs : List Wire) (c t : Wire) :
    gateSlots (compareLt ctrl x y cs c t) ≤ 10 * x.length + 2 * y.length + 4 := by
  have h := compareChain_gateSlots_le ctrl x y cs c t
  simp only [compareLt, gateSlots_append, notRegister_gateSlots, List.length_cons]; omega

 theorem compareLtConst_gateSlots_le (ctrl : Option Wire) (x y cs : List Wire) (c t k : Nat) :
    gateSlots (compareLtConst ctrl x y cs c t k) ≤ 10 * x.length + 4 * y.length + 4 := by
  have h := compareLt_gateSlots_le ctrl x y cs c t
  have hk := xorConstant_gateSlots_le y k
  simp only [compareLtConst, gateSlots_append]; omega

theorem shift_gateSlots (c : Wire) (r : List Wire) :
    gateSlots (shiftRight c r) = 3 * (r.length - 1) ∧
    gateSlots (shiftLeft c r) = 3 * (r.length - 1) := by
  induction r with
  | nil => constructor <;> rfl
  | cons a as ih =>
    cases as with
    | nil => constructor <;> rfl
    | cons b bs =>
      simp only [shiftRight, shiftLeft, gateSlots_append, ih.1, ih.2, List.length_cons]
      have h : gateSlots (cswap c a b) = 3 := rfl
      rw [h]; constructor <;> omega

theorem measuredMasked_gateSlots_le (c : Wire) (src t y cs : List Wire) (cin : Wire) :
    gateSlots (measuredMaskedAddInPlace c src t y cs cin) ≤ 15 * t.length ∧
    gateSlots (measuredMaskedSubInPlace c src t y cs cin) ≤ 15 * t.length + 2 * y.length := by
  have ha := addInPlace_gateSlots_le t y cs cin
  have hs := subInPlace_gateSlots_le t y cs cin
  have hm := Nat.min_le_right src.length t.length
  simp only [measuredMaskedAddInPlace, measuredMaskedSubInPlace, gateSlots_append,
    copyRegister_gateSlots, eraseMask_gateSlots]
  constructor <;> omega

theorem maskedConst_gateSlots_le (c : Wire) (t y cs : List Wire) (cin k : Nat) :
    gateSlots (maskedAddConst c t y cs cin k) ≤ 14 * t.length ∧
    gateSlots (maskedSubConst c t y cs cin k) ≤ 14 * t.length + 2 * y.length := by
  have ha := addInPlace_gateSlots_le t y cs cin
  have hs := subInPlace_gateSlots_le t y cs cin
  have hm := maskedConstant_gateSlots_le c t k
  simp only [maskedAddConst, maskedSubConst, gateSlots_append]
  constructor <;> omega

theorem modAddCore_gateSlots_le (L : ModAddCoreLayout) (p : Nat) :
    gateSlots (modAddCore L p) ≤
      14 * L.a.length + 14 * L.constant.length + 26 * L.low.length + 7 := by
  have ha := addInPlace_gateSlots_le L.a L.z L.carry L.cin
  have hs := subInPlace_gateSlots_le L.constant L.z L.carry L.cin
  have hx := xorConstant_gateSlots_le L.constant p
  have hm := (maskedConst_gateSlots_le L.high (L.constant.take L.low.length) L.low
    (L.carry.take (L.low.length-1)) L.cin p).1
  have hc := compareLt_gateSlots_le none L.low (L.a.take L.low.length) L.carry L.cin L.high
  simp only [List.length_take] at hm hc
  have h1 := Nat.min_le_right L.low.length L.constant.length
  have h2 := Nat.min_le_left L.low.length L.constant.length
  have h3 := Nat.min_le_right L.low.length L.a.length
  have hz : L.z.length = L.low.length + 1 := by simp [ModAddCoreLayout.z]
  simp only [modAddCore, gateSlots_append, gateSlots_cons, gateSlots_nil, instructionSlots]
  omega

theorem negRaw_gateSlots_le (L : ModInPlaceLayout) (p : Nat) :
    gateSlots (negRaw L p) ≤ L.a.length + 14 * L.constant.length := by
  have ha := addInPlace_gateSlots_le L.constant L.a L.carry L.cin
  have hx := xorConstant_gateSlots_le L.constant (p+1)
  simp only [negRaw, gateSlots_append, notRegister_gateSlots]; omega

end ECDSAAdd.Baselines
