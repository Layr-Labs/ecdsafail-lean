import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Arithmetic.MappedSources
import ECDSAAdd.Arithmetic.ConstantBorrow
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem borrowMajority_physical (x y cin target : Wire) (hn : [x,y,cin,target].Nodup) :
    GatePhysical (borrowMajority x y cin target) := by
  simp only [borrowMajority,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate],majority_physical x y cin target hn⟩,
    by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem eraseBorrow_physical (x y cin target : Wire) :
    GatePhysical (eraseBorrow x y cin target) := by
  simp [eraseBorrow,GatePhysical,eraseCarry,PhysicalInstr,ProperGate]

theorem mappedMajority_physical (b : MappedBit) (y cin target : Wire)
    (hn : [y,cin,target].Nodup) (ha : ∀ q ∈ b.wire, q ∉ [y,cin,target]) :
    GatePhysical (mappedMajority b y cin target) := by
  cases hw : b.wire with
  | none =>
    cases hf : b.flip <;>
      simp_all [mappedMajority,GatePhysical,PhysicalInstr,ProperGate,List.nodup_cons]
  | some a =>
    have h4 : [a,y,cin,target].Nodup := List.nodup_cons.mpr ⟨ha a (by simp [hw]),hn⟩
    cases hf : b.flip
    · simpa [mappedMajority,hw,hf] using majority_physical a y cin target h4
    · simpa [mappedMajority,hw,hf] using borrowMajority_physical a y cin target h4

theorem mappedEraseCarry_physical (b : MappedBit) (y cin target : Wire) :
    GatePhysical (mappedEraseCarry b y cin target) := by
  cases hw : b.wire with
  | none => simp [mappedEraseCarry,hw,GatePhysical,PhysicalInstr]
  | some a =>
    cases hf : b.flip
    · simpa [mappedEraseCarry,hw,hf] using eraseCarry_physical a y cin target
    · simpa [mappedEraseCarry,hw,hf] using eraseBorrow_physical a y cin target

theorem mappedSum_physical (b : MappedBit) (y cin : Wire)
    (hn : cin ≠ y) (ha : ∀ q ∈ b.wire, q ≠ y) : GatePhysical (mappedSum b y cin) := by
  cases hw : b.wire <;> cases hf : b.flip <;>
    simp_all [mappedSum,GatePhysical,PhysicalInstr,ProperGate]

theorem mappedAdd_physical (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hn : (cin :: ys ++ carry).Nodup)
    (ha : ∀ b ∈ bits, ∀ q ∈ b.wire, q ∉ cin :: ys ++ carry) :
    GatePhysical (mappedAdd bits ys carry cin) := by
  induction bits generalizing ys carry cin with
  | nil => simp [mappedAdd,GatePhysical]
  | cons b bs ih =>
    cases bs with
    | nil =>
      cases ys with
      | nil => simp [mappedAdd,GatePhysical]
      | cons y rest =>
        cases rest with
        | cons z zs => simp [mappedAdd,GatePhysical]
        | nil =>
          apply mappedSum_physical
          · intro he; subst cin
            exact (List.nodup_cons.mp hn).1 (by simp)
          · intro q hq he; subst q
            exact ha b (by simp) y hq (by simp)
    | cons b' bs =>
      cases ys with
      | nil => simp [mappedAdd,GatePhysical]
      | cons y rest =>
        cases rest with
        | nil => simp [mappedAdd,GatePhysical]
        | cons y' ys =>
          cases carry with
          | nil => simp [mappedAdd,GatePhysical]
          | cons k ks =>
            have hs : [y,cin,k].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
            have ht : (k :: (y'::ys) ++ ks).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢; omega
            have hb : ∀ q ∈ b.wire, q ∉ [y,cin,k] := by
              intro q hq hmem
              apply ha b (by simp) q hq
              simp only [List.mem_cons,List.mem_append,List.not_mem_nil] at hmem ⊢
              tauto
            have hat : ∀ z ∈ b'::bs, ∀ q ∈ z.wire, q ∉ k :: (y'::ys) ++ ks := by
              intro z hz q hq hm
              apply ha z (by simp [hz]) q hq
              simp only [List.mem_cons,List.mem_append] at hm ⊢
              tauto
            rw [mappedAdd]
            simp only [gatePhysical_append]
            refine ⟨⟨⟨mappedMajority_physical b y cin k hs hb,ih _ _ _ ht hat⟩,
              mappedEraseCarry_physical b y cin k⟩,?_⟩
            apply mappedSum_physical
            · intro he; subst cin
              exact (List.nodup_cons.mp hs).1 (by simp)
            · intro q hq he; subst q; exact hb y hq (by simp)


private theorem mappedConstant_source (c : Option Wire) (n k : Nat) (b : MappedBit)
    (hb : b ∈ mappedConstant c n k) (q : Wire) (hq : q ∈ b.wire) : q ∈ c := by
  induction n generalizing k with
  | zero => simp [mappedConstant] at hb
  | succ n ih =>
    simp only [mappedConstant,List.mem_cons] at hb
    rcases hb with rfl | hb
    · cases h : decide (k%2=1) <;> simp_all [mappedConstantBit]
    · exact ih (k/2) hb

theorem mappedConstAdd_physical (c : Option Wire) (ys carry : List Wire) (cin k : Nat)
    (hn : (cin :: ys ++ carry).Nodup) (hc : ∀ q ∈ c, q ∉ cin :: ys ++ carry) :
    GatePhysical (mappedConstAdd c ys carry cin k) := by
  apply mappedAdd_physical _ _ _ _ hn
  intro b hb q hq
  exact hc q (mappedConstant_source c _ _ b hb q hq)

theorem constantBorrow_physical (bit : Bool) (x cin target : Wire)
    (hn : [x,cin,target].Nodup) : GatePhysical (constantBorrow bit x cin target) := by
  simp only [constantBorrow,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate],
    mappedMajority_physical _ _ _ _ hn (by simp)⟩,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem constantBorrowErase_physical (bit : Bool) (x cin target : Wire) :
    GatePhysical (constantBorrowErase bit x cin target) := by
  simp only [constantBorrowErase,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate],
    mappedEraseCarry_physical _ _ _ _⟩,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩

theorem compareConstantLt_physical (xs carry : List Wire) (cin target k : Nat)
    (hn : ([cin,target] ++ xs ++ carry).Nodup) :
    GatePhysical (compareConstantLt xs carry cin target k) := by
  induction xs generalizing carry cin k with
  | nil => simp [compareConstantLt,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      apply constantBorrow_physical
      apply List.nodup_iff_count.mpr; intro q
      have h := List.nodup_iff_count.mp hn q
      simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
    | cons x' xs =>
      cases carry with
      | nil => simp [compareConstantLt,GatePhysical]
      | cons c cs =>
        have hs : [x,cin,c].Nodup := by
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
        have ht : ([c,target] ++ (x'::xs) ++ cs).Nodup := by
          apply List.nodup_iff_count.mpr; intro q
          have h := List.nodup_iff_count.mp hn q
          simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
        rw [compareConstantLt]
        simp only [gatePhysical_append]
        exact ⟨⟨constantBorrow_physical _ _ _ _ hs,ih _ _ _ ht⟩,
          constantBorrowErase_physical _ _ _ _⟩

theorem compareConstantGe_physical (xs carry : List Wire) (cin target k : Nat)
    (hn : ([cin,target] ++ xs ++ carry).Nodup) :
    GatePhysical (compareConstantGe xs carry cin target k) := by
  simp only [compareConstantGe,gatePhysical_append]
  exact ⟨compareConstantLt_physical _ _ _ _ _ hn,by simp [GatePhysical,PhysicalInstr,ProperGate]⟩


theorem eraseLtChain_physical (xs ys carry : List Wire) (cin target : Wire)
    (hn : (cin :: xs ++ ys ++ carry).Nodup) :
    GatePhysical (eraseLtChain xs ys carry cin target) := by
  induction xs generalizing ys carry cin with
  | nil => simp [eraseLtChain,GatePhysical]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [eraseLtChain,GatePhysical]
      | cons y rest =>
        cases rest with
        | nil => exact eraseBorrow_physical _ _ _ _
        | cons y' ys => simp [eraseLtChain,GatePhysical]
    | cons x' xs =>
      cases ys with
      | nil => simp [eraseLtChain,GatePhysical]
      | cons y rest =>
        cases rest with
        | nil => simp [eraseLtChain,GatePhysical]
        | cons y' ys =>
          cases carry with
          | nil => simp [eraseLtChain,GatePhysical]
          | cons c cs =>
            have hs : [x,y,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
            have ht : (c :: (x'::xs) ++ (y'::ys) ++ cs).Nodup := by
              apply List.nodup_iff_count.mpr; intro q
              have h := List.nodup_iff_count.mp hn q
              simp only [List.count_cons,List.count_append] at h ⊢; omega
            rw [eraseLtChain]
            simp only [gatePhysical_append]
            exact ⟨⟨borrowMajority_physical _ _ _ _ hs,ih _ _ _ ht⟩,
              eraseBorrow_physical _ _ _ _⟩


theorem MeasuredCanonicalModLayout.physical (L : MeasuredCanonicalModLayout)
    (c p : Nat) (hn : L.wires.Nodup) : GatePhysical (L.program c p) := by
  have count := List.nodup_iff_count.mp hn
  have ndsum : (L.cin :: L.extended ++ L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    simp only [wires,extended,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have ndcmp : ([L.cin,L.flag] ++ L.out ++ L.carry.take (L.out.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    have ht := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  have hsum : GatePhysical L.sum := by
    apply mappedAdd_physical _ _ _ _ ndsum
    intro b hb q hq hm
    simp only [mappedRead,List.mem_append,List.mem_map,List.mem_singleton] at hb
    rcases hb with ⟨r,hr,rfl⟩ | rfl
    · have eq : q = r := by simpa [eq_comm] using hq
      subst q
      have h := count r
      have hs := List.count_pos_iff.mpr hr
      have hh := List.count_pos_iff.mpr hm
      simp only [wires,extended,List.count_cons,List.count_append,List.count_nil] at h hh
      omega
    · simp at hq
  have hfc : ∀ q ∈ some L.flag, q ∉ L.cin :: L.extended ++ L.carry := by
    intro q hq hm
    have eq : q = L.flag := by simpa [eq_comm] using hq
    subst q
    have h := count L.flag
    have hh := List.count_pos_iff.mpr hm
    simp only [wires,extended,List.count_cons,List.count_append,List.count_nil,
      beq_self_eq_true,ite_true] at h hh
    omega
  have hf : L.high ≠ L.flag := by
    intro he
    have h := count L.high
    simp only [wires,List.count_cons,List.count_append,List.count_nil,he,
      beq_self_eq_true,ite_true] at h
    omega
  have nderase : (L.cin :: L.out ++ L.src ++ L.carry.take (L.out.length-1)).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := count q
    have ht := (List.take_sublist (L.out.length-1) L.carry).count_le q
    simp only [wires,List.count_cons,List.count_append,List.count_nil] at h ⊢; omega
  simp only [program,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨hsum,compareConstantGe_physical _ _ _ _ _ ndcmp⟩,
    by simpa [GatePhysical,PhysicalInstr,ProperGate] using hf⟩,
    mappedConstAdd_physical _ _ _ _ _ ndsum hfc⟩,
    by simpa [GatePhysical,PhysicalInstr,ProperGate] using Ne.symm hf⟩,
    eraseLtChain_physical _ _ _ _ _ nderase⟩

end ECDSAAdd.Arithmetic
