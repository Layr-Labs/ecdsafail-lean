import ECDSAAdd.Arithmetic.KnownOutputAdder
import ECDSAAdd.Arithmetic.MappedArithmeticPhysical
namespace ECDSAAdd.Arithmetic.KnownOutputAdder
open RecordedQuantum

theorem xorBit_physical (b : MappedBit) (t : Wire) (ha : ∀q∈b.wire,q≠t) :
    GatePhysical (xorBit b t) := by
  cases h : b.wire <;> cases f : b.flip <;>
    simp_all [xorBit,GatePhysical,PhysicalInstr,ProperGate]

theorem prepare_physical (b d : MappedBit) (y c : Wire) (hy : y≠c)
    (hb : ∀q∈b.wire,q≠c) (hd : ∀q∈d.wire,q≠c) : GatePhysical (prepare b d y c) := by
  simp only [prepare,gatePhysical_append]
  exact ⟨⟨by simp [GatePhysical,PhysicalInstr,ProperGate,hy],xorBit_physical b c hb⟩,xorBit_physical d c hd⟩

theorem program_physical (bits sums : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (hl : bits.length=ys.length) (hs : sums.length=ys.length)
    (hc : carry.length+1=ys.length) (hn : (cin::ys++carry).Nodup)
    (hb : ∀b∈bits,∀q∈b.wire,q∉cin::ys++carry)
    (hd : ∀b∈sums,∀q∈b.wire,q∉cin::ys++carry) :
    GatePhysical (program bits ys sums carry cin) := by
  induction ys generalizing bits sums carry cin with
  | nil => simp at hc
  | cons y ys ih =>
    cases bits with
    | nil => simp at hl
    | cons b bs =>
      cases sums with
      | nil => simp at hs
      | cons d ds =>
        have sm : GatePhysical (mappedSum b y cin) := by
          apply mappedSum_physical
          · intro eq; subst cin
            exact (List.nodup_cons.mp hn).1 (by simp)
          · intro q hq eq; subst q
            exact hb b (by simp) y hq (by simp)
        cases ys with
        | nil =>
          have be : bs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
          have de : ds=[] := List.eq_nil_of_length_eq_zero (by simpa using hs)
          subst bs; subst ds
          exact sm
        | cons y' ys =>
          cases bs with
          | nil => simp at hl
          | cons b' bs =>
            cases ds with
            | nil => simp at hs
            | cons d' ds =>
              cases carry with
              | nil => simp at hc
              | cons c cs =>
                have tailnd : (c::(y'::ys)++cs).Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro w
                  have h := List.nodup_iff_count.mp hn w
                  simp only [List.count_cons,List.count_append] at h ⊢
                  omega
                have tailbits : ∀z∈b'::bs,∀q∈z.wire,q∉c::(y'::ys)++cs := by
                  intro z hz q hq hm
                  apply hb z (List.mem_cons_of_mem _ hz) q hq
                  simp only [List.mem_cons,List.mem_append] at hm ⊢
                  tauto
                have tailsums : ∀z∈d'::ds,∀q∈z.wire,q∉c::(y'::ys)++cs := by
                  intro z hz q hq hm
                  apply hd z (List.mem_cons_of_mem _ hz) q hq
                  simp only [List.mem_cons,List.mem_append] at hm ⊢
                  tauto
                have py : y'≠c := by
                  intro eq; subst c
                  exact (List.nodup_cons.mp tailnd).1 (by simp)
                have pb : ∀q∈b'.wire,q≠c := by
                  intro q hq eq; subst q
                  exact hb b' (by simp) c hq (by simp)
                have pd : ∀q∈d'.wire,q≠c := by
                  intro q hq eq; subst q
                  exact hd d' (by simp) c hq (by simp)
                have pr := prepare_physical b' d' y' c py pb pd
                have tl := ih (b'::bs) (d'::ds) cs c
                  (by simpa using hl) (by simpa using hs) (by simpa using hc)
                  tailnd tailbits tailsums
                simp only [program,gatePhysical_append]
                exact ⟨⟨⟨pr,tl⟩,mappedEraseCarry_physical _ _ _ _⟩,sm⟩
end ECDSAAdd.Arithmetic.KnownOutputAdder
