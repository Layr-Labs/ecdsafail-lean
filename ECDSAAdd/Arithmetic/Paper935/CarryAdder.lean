import ECDSAAdd.Arithmetic.CuccaroAdder
import ECDSAAdd.Arithmetic.SignedWordBits

namespace ECDSAAdd.Arithmetic.Paper935

/-- The paper generator's shared-carry MAJ, with no per-bit carry allocation. -/
def rowMaj (a b k : Wire) : Program := cuccaroMaj k a b

/-- Undo the MAJ and conditionally write the sum. This is the k=0 path
of the author's `ctrl_add_rows`, not a gatewise control of an adder. -/
def rowUma (c a b k : Wire) : Program :=
  [.CCX b a k,.CX k b,.CCX c a b,.CX k a]

def rowTop (c a b k : Wire) : Program := [.CX k a,.CCX c a b,.CX k a]

def rowAdd (c : Wire) : List Wire → List Wire → Wire → Program
  | [a], [b], k => rowTop c a b k
  | a::a'::as, b::b'::bs, k =>
      rowMaj a b k ++ (rowAdd c (a'::as) (b'::bs) k ++ rowUma c a b k)
  | _, _, _ => []

private theorem maj_run (a b k : Wire) (hn : [k,a,b].Nodup) (s : State) (m : List Bool) :
    let t := run (rowMaj a b k) m s
    t.phase=s.phase ∧ t.basis k=carryBit (s.basis a) (s.basis b) (s.basis k) ∧
    t.basis a=(s.basis a ^^ s.basis k) ∧ t.basis b=(s.basis b ^^ s.basis k) ∧
    ∀ q,q∉[k,a,b] → t.basis q=s.basis q := by
  have h := cuccaroMaj_correct k a b hn s m
  refine ⟨h.1,?_,?_,?_,h.2.2.2.2⟩
  · rw [rowMaj,h.2.1]; cases s.basis a <;> cases s.basis b <;> cases s.basis k <;> rfl
  · exact h.2.2.1.trans (Bool.xor_comm _ _)
  · exact h.2.2.2.1.trans (Bool.xor_comm _ _)

private theorem uma_run (c a b k : Wire) (hn : [c,k,a,b].Nodup)
    (s : State) (m : List Bool) (A B C : Bool)
    (hk : s.basis k=carryBit A B C) (ha : s.basis a=(A ^^ C)) (hb : s.basis b=(B ^^ C)) :
    let t := run (rowUma c a b k) m s
    t.phase=s.phase ∧ t.basis a=A ∧ t.basis k=C ∧
    t.basis b=(if s.basis c then sumBit A B C else B) ∧
    ∀ q,q∉[k,a,b] → t.basis q=s.basis q := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at hn
  obtain ⟨⟨hck,hca,hcb⟩,⟨hka,hkb⟩,hab⟩ := hn
  have bits : (run (rowUma c a b k) m s).basis a=A ∧
      (run (rowUma c a b k) m s).basis k=C ∧
      (run (rowUma c a b k) m s).basis b=(if s.basis c then sumBit A B C else B) := by
    dsimp [rowUma,run]
    cases A <;> cases B <;> cases C <;> cases h : s.basis c <;>
      simp_all [writeBit,Ne.symm hka,
        Ne.symm hkb,Ne.symm hab,carryBit,sumBit]
  refine ⟨rfl,bits.1,bits.2.1,bits.2.2,?_⟩
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
  simp [rowUma,run,writeBit,hq.1,hq.2.1,hq.2.2]

@[simp] theorem rowAdd_measurements (c : Wire) (a b : List Wire) (k : Wire) :
    measurementCount (rowAdd c a b k)=0 := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases xs with
    | nil => cases b with
      | nil => rfl
      | cons y ys => cases ys <;> rfl
    | cons x' xs => cases b with
      | nil => rfl
      | cons y ys => cases ys with
        | nil => rfl
        | cons y' ys => simp [rowAdd,rowMaj,ih,rowUma,measurementCount]

/-- One shared carry is restored, every source/control bit is restored, and
only the target changes. The initial carry need not be zero. -/
theorem rowAdd_run (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (hl : a.length=b.length) (s : State) (m : List Bool) :
    let t := run (rowAdd c a b k) m s
    t.phase=s.phase ∧
    (∀ q,q∉b → t.basis q=s.basis q) ∧
    regValue b t.basis=(if s.basis c then
      (regValue a s.basis+regValue b s.basis+(s.basis k).toNat)%2^b.length
      else regValue b s.basis) := by
  induction b generalizing a s with
  | nil =>
    have ha : a=[] := List.eq_nil_of_length_eq_zero hl
    subst a
    simp [rowAdd,run,regValue,Nat.mod_one]
  | cons y ys ih =>
    cases a with
    | nil => simp at hl
    | cons x xs =>
      have htail : xs.length=ys.length := by simpa using hl
      have cnt := List.nodup_iff_count.mp hn
      have h4 : [c,k,x,y].Nodup := by
        apply List.nodup_iff_count.mpr; intro q
        have h := cnt q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
      have cn : c∉y::ys := (List.nodup_cons.mp hn).1 ∘ List.mem_cons_of_mem k ∘ List.mem_append_right _
      have kn : k∉y::ys := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1 ∘ List.mem_append_right _
      have xn : x∉y::ys := by
        have h := (List.nodup_append'.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).2.2
        exact fun hy => List.disjoint_left.mp h (by simp) hy
      have yn : y∉ys := (List.nodup_cons.mp
        (List.nodup_append'.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).2.1).1
      have h3 : [k,x,y].Nodup := (List.nodup_cons.mp h4).2
      cases ys with
      | nil =>
        have hx : xs=[] := List.eq_nil_of_length_eq_zero htail
        subst xs
        have nd := h4
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
          not_or,not_false_eq_true,and_true] at nd
        obtain ⟨⟨hck,hcx,hcy⟩,⟨hkx,hky⟩,hxy⟩ := nd
        refine ⟨rfl,?_,?_⟩
        · intro q hq
          have hqy : q≠y := by simpa using hq
          by_cases hqx : q=x
          · subst q
            simp [rowAdd,rowTop,run,writeBit,hxy,hky,hkx]
          · simp [rowAdd,rowTop,run,writeBit,hqy,hqx]
        · cases hC : s.basis c <;> cases hK : s.basis k <;>
            cases hX : s.basis x <;> cases hY : s.basis y <;>
            simp [rowAdd,rowTop,run,writeBit,regValue,hC,hK,hX,hY,hcx,hkx,hky,hxy,
              Ne.symm hxy]
      | cons y' ys =>
        cases xs with
        | nil => simp at htail
        | cons x' xs =>
          let atail := x'::xs
          let btail := y'::ys
          have htnd : (c::k::(atail++btail)).Nodup := by
            apply List.nodup_iff_count.mpr; intro q
            have h := cnt q
            simp only [atail,btail,List.count_cons,List.count_append] at h ⊢
            omega
          have away (q : Wire) (hq : q∈atail++btail) : q∉[k,x,y] := by
            have pos := List.count_pos_iff.mpr hq
            have h := cnt q
            simp only [atail,btail,List.count_append,List.count_cons] at pos h
            simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
            constructor
            · intro e; subst q; simp only [beq_self_eq_true,if_true] at h; omega
            constructor
            · intro e; subst q; simp only [beq_self_eq_true,if_true] at h; omega
            · intro e; subst q; simp only [beq_self_eq_true,if_true] at h; omega
          have cn3 : c∉[k,x,y] := (List.nodup_cons.mp h4).1
          let u := run (rowMaj x y k) m s
          have hu := maj_run x y k h3 s m
          have uc : u.basis c=s.basis c := hu.2.2.2.2 c cn3
          have ua : regValue atail u.basis=regValue atail s.basis :=
            regValue_congr _ _ _ (fun q hq => hu.2.2.2.2 q (away q (List.mem_append_left _ hq)))
          have ub : regValue btail u.basis=regValue btail s.basis :=
            regValue_congr _ _ _ (fun q hq => hu.2.2.2.2 q (away q (List.mem_append_right _ hq)))
          let v := run (rowAdd c atail btail k) m u
          have hv := ih atail htnd htail u
          have vk : v.basis k=carryBit (s.basis x) (s.basis y) (s.basis k) :=
            (hv.2.1 k (fun h => kn (List.mem_cons_of_mem y h))).trans hu.2.1
          have vx : v.basis x=(s.basis x ^^ s.basis k) :=
            (hv.2.1 x (fun h => xn (List.mem_cons_of_mem y h))).trans hu.2.2.1
          have vy : v.basis y=(s.basis y ^^ s.basis k) := (hv.2.1 y yn).trans hu.2.2.2.1
          have vc : v.basis c=s.basis c :=
            (hv.2.1 c (fun h => cn (List.mem_cons_of_mem y h))).trans uc
          let out := run (rowUma c x y k) m v
          have ho := uma_run c x y k h4 v m (s.basis x) (s.basis y) (s.basis k) vk vx vy
          have tailval : regValue btail out.basis = if s.basis c then
              (regValue atail s.basis+regValue btail s.basis+
                (carryBit (s.basis x) (s.basis y) (s.basis k)).toNat)%2^btail.length
              else regValue btail s.basis := by
            rw [regValue_congr btail out.basis v.basis
              (fun q hq => ho.2.2.2.2 q (away q (List.mem_append_right _ hq)))]
            rw [hv.2.2,uc,ua,ub,hu.2.1]
          have frame (q : Wire) (hq : q∉y::btail) : out.basis q=s.basis q := by
            by_cases hqx : q=x
            · subst q; exact ho.2.1
            by_cases hqk : q=k
            · subst q; exact ho.2.2.1
            have hn3 : q∉[k,x,y] := by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or];
                                                     exact ⟨hqk,hqx,fun e => hq (by simp [e])⟩
            exact (ho.2.2.2.2 q hn3).trans
              ((hv.2.1 q (fun h => hq (List.mem_cons_of_mem y h))).trans (hu.2.2.2.2 q hn3))
          have exec : run (rowAdd c (x::atail) (y::btail) k) m s=out := by
            change run (rowMaj x y k ++ (rowAdd c atail btail k ++ rowUma c x y k)) m s=out
            rw [run_append,run_take,run_append,run_take]
            simp only [rowMaj,cuccaroMaj_measurementCount,rowAdd_measurements,List.drop_zero]
            rfl
          rw [exec]
          refine ⟨ho.1.trans (hv.1.trans hu.1),frame,?_⟩
          change (if out.basis y then 1 else 0)+2*regValue btail out.basis=_
          rw [ho.2.2.2.1,vc,tailval]
          cases hc : s.basis c
          · change (if s.basis y then 1 else 0)+2*regValue btail s.basis=regValue (y::btail) s.basis
            rfl
          · simpa only [hc,if_true,regValue,List.foldr_cons,Bool.toNat,Bool.cond_eq_ite,
              List.length_cons] using sum_value_step (s.basis x) (s.basis y)
              (s.basis k) (regValue atail s.basis) (regValue btail s.basis) btail.length

/-- Signed row semantics, conditional only on the result fitting its selected
window. The gate stream itself computes modular addition for every input. -/
theorem rowAdd_signed (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (hl : a.length=b.length) (s : State) (m : List Bool)
    (hk : s.basis k=false) (hw : 0<b.length)
    (hlo : -((2^(b.length-1):Nat):Int) ≤ signedRegValue b s.basis+
      (if s.basis c then signedRegValue a s.basis else 0))
    (hhi : signedRegValue b s.basis+(if s.basis c then signedRegValue a s.basis else 0)<
      ((2^(b.length-1):Nat):Int)) :
    let t := run (rowAdd c a b k) m s
    t.phase=s.phase ∧ (∀ q,q∉b → t.basis q=s.basis q) ∧
    signedRegValue b t.basis=signedRegValue b s.basis+
      (if s.basis c then signedRegValue a s.basis else 0) := by
  have hh := rowAdd_run c k a b hn hl s m
  refine ⟨hh.1,hh.2.1,?_⟩
  unfold signedRegValue
  rw [hh.2.2,hk]
  cases hc : s.basis c
  · simp
  · have hx : regValue a s.basis<2^b.length := by simpa only [hl] using regValue_lt a s.basis
    have hh := signedWordValue_lift b.length false (regValue a s.basis) (regValue b s.basis)
      hw hx
      (by simpa [signedIntegerValue,signedRegValue,hl,hc] using hlo)
      (by simpa [signedIntegerValue,signedRegValue,hl,hc] using hhi)
    simpa [signedWordValue,signedIntegerValue,signedRegValue,hl,Nat.add_comm] using hh

theorem rowAdd_toffolis (c k : Wire) (a b : List Wire) (hl : a.length=b.length) :
    toffoliCount (rowAdd c a b k)=3*b.length-2 := by
  induction b generalizing a with
  | nil => have ha : a=[] := List.eq_nil_of_length_eq_zero hl; subst a; rfl
  | cons y ys ih =>
    cases a with
    | nil => simp at hl
    | cons x xs =>
      cases ys with
      | nil =>
        have hx : xs=[] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst xs; rfl
      | cons y' ys =>
        cases xs with
        | nil => simp at hl
        | cons x' xs =>
          have ht : (x'::xs).length=(y'::ys).length := by simpa using hl
          simp only [rowAdd,toffoliCount_append,rowMaj,cuccaroMaj,rowUma,toffoliCount]
          rw [ih _ ht]
          simp only [List.length_cons]
          omega

theorem rowAdd_support (c k : Wire) (a b : List Wire) :
    wires (rowAdd c a b k)⊆(c::k::(a++b)).toFinset := by
  induction a generalizing b with
  | nil => cases b <;> simp [rowAdd,wires]
  | cons x xs ih =>
    cases xs with
    | nil => cases b with
      | nil => simp [rowAdd,wires]
      | cons y ys => cases ys with
        | nil =>
          intro q hq
          simp [rowAdd,rowTop,wires,Instr.wires] at hq ⊢
          tauto
        | cons y' ys => simp [rowAdd,wires]
    | cons x' xs => cases b with
      | nil => simp [rowAdd,wires]
      | cons y ys => cases ys with
        | nil => simp [rowAdd,wires]
        | cons y' ys =>
          intro q hq
          simp only [rowAdd,wires_append,Finset.mem_union] at hq
          rcases hq with hq|(hq|hq)
          · simp only [rowMaj,cuccaroMaj,wires,Instr.wires,Finset.mem_union,
              Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
            simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
            tauto
          · have hh := ih (y'::ys) hq
            simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hh ⊢
            tauto
          · simp only [rowUma,wires,Instr.wires,Finset.mem_union,
              Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
            simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
            tauto

/-- Total includes both n-bit operands, the control, and one shared carry. -/
theorem rowAdd_qubits (c k : Wire) (a b : List Wire) (hl : a.length=b.length) :
    qubitCount (rowAdd c a b k)≤2*b.length+2 := by
  have h := (Finset.card_le_card (rowAdd_support c k a b)).trans
    (List.toFinset_card_le (c::k::(a++b)))
  simp only [List.length_cons,List.length_append,hl] at h
  exact h.trans (by omega)

/-- A cleared shared carry is available for the next subprocedure. -/
theorem rowAdd_carry_clean (c k : Wire) (a b : List Wire)
    (hn : (c::k::(a++b)).Nodup) (hl : a.length=b.length)
    (s : State) (m : List Bool) (hk : s.basis k=false) :
    (run (rowAdd c a b k) m s).basis k=false := by
  have kn : k∉b := fun h => (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
    (List.mem_append_right _ h)
  exact ((rowAdd_run c k a b hn hl s m).2.1 k kn).trans hk

end ECDSAAdd.Arithmetic.Paper935
