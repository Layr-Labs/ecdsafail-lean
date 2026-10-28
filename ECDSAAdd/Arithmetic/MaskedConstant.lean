import ECDSAAdd.Arithmetic.Constant

namespace ECDSAAdd.Arithmetic

/-- 经典位为 1 时执行 CX；控制位不属于目标寄存器。 -/
def maskedConstant (c : Wire) : List Wire → Nat → Program
  | [],_ => []
  | w::ws,k => (if k%2=1 then [.CX c w] else [])++maskedConstant c ws (k/2)

theorem maskedConstant_run (c : Wire) (r : List Wire) (k : Nat) (hc : c∉r)
    (s : State) (m : List Bool) :
    run (maskedConstant c r k) m s = if s.basis c then run (xorConstant r k) m s else s := by
  induction r generalizing s k with
  | nil => cases s.basis c <;> simp [maskedConstant,xorConstant,run]
  | cons w ws ih =>
    have hcw : c≠w := fun h => hc (by simp [h])
    have hcs : c∉ws := fun h => hc (by simp [h])
    by_cases hk : k%2=1
    · simp only [maskedConstant,xorConstant,hk,if_true,List.singleton_append,run]
      rw [ih (k/2) hcs]
      cases hs : s.basis c <;> simp [hs,writeBit,hcw]
    · simp only [maskedConstant,xorConstant,hk,if_false,List.nil_append]
      exact ih (k/2) hcs s

theorem maskedConstant_correct (c : Wire) (r : List Wire) (k : Nat)
    (hn : r.Nodup) (hc : c∉r) (hk : k<2^r.length) (s : State) (m : List Bool) :
    (run (maskedConstant c r k) m s).phase=s.phase ∧
    (∀ w∉r,(run (maskedConstant c r k) m s).basis w=s.basis w) ∧
    regValue r (run (maskedConstant c r k) m s).basis=
      regValue r s.basis ^^^ (if s.basis c then k else 0) := by
  rw [maskedConstant_run c r k hc]
  cases hs : s.basis c
  · simp
  · exact xorConstant_correct r hn k hk s m

theorem maskedConstant_counts (c : Wire) (r : List Wire) (k : Nat) :
    toffoliCount (maskedConstant c r k)=0 ∧ measurementCount (maskedConstant c r k)=0 := by
  induction r generalizing k with
  | nil => simp [maskedConstant,toffoliCount,measurementCount]
  | cons w ws ih =>
    by_cases hk : k%2=1 <;> simp [maskedConstant,hk,toffoliCount,measurementCount,ih]

theorem maskedConstant_wires_subset (c : Wire) (r : List Wire) (k : Nat) :
    wires (maskedConstant c r k) ⊆ (c::r).toFinset := by
  induction r generalizing k with
  | nil => simp [maskedConstant,wires]
  | cons w ws ih =>
    intro v hv
    by_cases hk : k%2=1
    · simp only [maskedConstant,hk,if_true,wires_append,wires,Instr.wires,
        Finset.union_empty,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with (rfl|rfl)|hv
      · simp
      · simp
      · have hh := ih (k/2) hv
        simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
        tauto
    · simp only [maskedConstant,hk,if_false,List.nil_append] at hv
      have hh := ih (k/2) hv
      simp only [List.mem_toFinset,List.mem_cons] at hh ⊢
      tauto

end ECDSAAdd.Arithmetic
