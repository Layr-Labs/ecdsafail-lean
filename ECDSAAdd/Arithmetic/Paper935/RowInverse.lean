import ECDSAAdd.Arithmetic.Paper935.Arena
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.Paper935

/-- The unmeasured shared-carry subtraction is the gatewise adjoint. This
reversal is justified only for this k=0, measurement-free path. -/
def rowSub (c : Wire) (a b : List Wire) (k : Wire) : Program :=
  (rowAdd c a b k).reverse

theorem rowAdd_proper (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) : ProperProgram (rowAdd c a b k) := by
  induction a generalizing b with
  | nil => cases b <;> simp [rowAdd,ProperProgram]
  | cons x xs ih =>
    cases b with
    | nil => cases xs <;> simp [rowAdd,ProperProgram]
    | cons y ys =>
      have hc := List.nodup_iff_count.mp hn
      have h4 : [c,k,x,y].Nodup := by
        apply List.nodup_iff_count.mpr
        intro q
        have h := hc q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
      have ht : (c::k::(xs++ys)).Nodup := by
        apply List.nodup_iff_count.mpr
        intro q
        have h := hc q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      have ht' := ih ys ht
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
        not_or,not_false_eq_true,and_true] at h4
      obtain ⟨⟨hck,hcx,hcy⟩,⟨hkx,hky⟩,hxy⟩ := h4
      cases xs <;> cases ys <;>
        simp_all [rowAdd,rowMaj,cuccaroMaj,rowUma,rowTop,
          ProperProgram,ProperGate,Ne.symm]
      all_goals aesop

theorem rowSub_roundtrip (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (s : State) (m n : List Bool) :
    run (rowSub c a b k) n (run (rowAdd c a b k) m s)=s :=
  run_reverse_proper _ (rowAdd_proper c k a b hn) s m n

theorem rowAdd_roundtrip (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (s : State) (m n : List Bool) :
    run (rowAdd c a b k) n (run (rowSub c a b k) m s)=s := by
  simpa [rowSub] using run_reverse_proper (rowAdd c a b k).reverse
    (properProgram_reverse _ (rowAdd_proper c k a b hn)) s m n

/-- The output is the unique width-bounded residue whose controlled sum
returns the input target. Source, control, carry and phase are restored. -/
theorem rowSub_run (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (hl : a.length=b.length) (s : State) (m : List Bool) :
    let t := run (rowSub c a b k) m s
    t.phase=s.phase ∧ (∀ q,q∉b → t.basis q=s.basis q) ∧
    (if s.basis c then
      (regValue a s.basis+regValue b t.basis+(s.basis k).toNat)%2^b.length
      else regValue b t.basis)=regValue b s.basis := by
  let t := run (rowSub c a b k) m s
  have h := rowAdd_run c k a b hn hl t []
  have hr := rowAdd_roundtrip c k a b hn s m []
  change run (rowAdd c a b k) [] t=s at hr
  rw [hr] at h
  have hf : ∀ q,q∉b → t.basis q=s.basis q := fun q hq => (h.2.1 q hq).symm
  have hc : c∉b := (List.nodup_cons.mp hn).1 ∘ List.mem_cons_of_mem k ∘ List.mem_append_right _
  have hk : k∉b := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 ∘ List.mem_append_right _
  have hab : List.Disjoint a b :=
    (List.nodup_append'.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).2.2
  have ha : regValue a t.basis=regValue a s.basis := by
    apply regValue_congr
    intro q hq
    exact hf q (List.disjoint_left.mp hab hq)
  refine ⟨h.1.symm,hf,?_⟩
  simpa only [hf c hc,hf k hk,ha] using h.2.2.symm

theorem rowSub_measurements (c k : Wire) (a b : List Wire) :
    measurementCount (rowSub c a b k)=0 := by
  simp [rowSub,measurementCount_reverse]

theorem rowSub_toffolis (c k : Wire) (a b : List Wire) (hl : a.length=b.length) :
    toffoliCount (rowSub c a b k)=3*b.length-2 := by
  rw [rowSub,toffoliCount_reverse,rowAdd_toffolis c k a b hl]

theorem rowSub_support (c k : Wire) (a b : List Wire) :
    wires (rowSub c a b k)⊆(c::k::(a++b)).toFinset := by
  rw [rowSub,wires_reverse]
  exact rowAdd_support c k a b

/-- The modular subtraction equation determines exactly one register value. -/
theorem rowSub_unique (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (hl : a.length=b.length) (s : State) (m : List Bool)
    (v : Nat) (hv : v<2^b.length)
    (he : (if s.basis c then
      (regValue a s.basis+v+(s.basis k).toNat)%2^b.length else v)=regValue b s.basis) :
    regValue b (run (rowSub c a b k) m s).basis=v := by
  have h := (rowSub_run c k a b hn hl s m).2.2
  cases hc : s.basis c
  · simpa [hc] using h.trans he.symm
  · simp only [hc,if_true] at h he
    have hm : Nat.ModEq (2^b.length)
        (regValue a s.basis+regValue b (run (rowSub c a b k) m s).basis+(s.basis k).toNat)
        (regValue a s.basis+v+(s.basis k).toNat) := h.trans he.symm
    have hh := (hm.add_right_cancel' (s.basis k).toNat)
    have hh' := hh.add_left_cancel' (regValue a s.basis)
    change _ % _ = _ % _ at hh'
    simpa only [Nat.mod_eq_of_lt (regValue_lt b _),Nat.mod_eq_of_lt hv] using hh'

theorem rowSub_carry_clean (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (hl : a.length=b.length) (s : State) (m : List Bool)
    (hk : s.basis k=false) : (run (rowSub c a b k) m s).basis k=false := by
  apply ((rowSub_run c k a b hn hl s m).2.1 k _).trans hk
  exact (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 ∘ List.mem_append_right _

theorem rowSub_in_arena (c k : Wire) (a b : List Wire)
    (h : (c::k::(a++b)).toFinset⊆arenaWires) :
    wires (rowSub c a b k)⊆arenaWires := (rowSub_support c k a b).trans h

end ECDSAAdd.Arithmetic.Paper935
