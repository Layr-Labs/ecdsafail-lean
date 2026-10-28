import ECDSAAdd.Arithmetic.Paper935.Arena

namespace ECDSAAdd.Arithmetic.Paper935

/-- One CX both seeds a newly borrowed high bit and clears a redundant high
bit before release. The sign has a separate physical address. -/
def resizeBit (sign top : Wire) : Program := [.CX sign top]

private theorem signed_split (lo : List Wire) (sign : Wire) (s : BasisState) :
    signedRegValue (lo++[sign]) s=(regValue lo s:Int)-
      (if s sign then ((2^lo.length:Nat):Int) else 0) := by
  rw [signedRegValue_msb,regValue_append]
  cases hs : s sign <;>
    simp [regValue,hs,Nat.pow_succ,Nat.cast_add,Nat.cast_mul]
  all_goals ring

private theorem resize_frame (sign top : Wire) (s : State) (m : List Bool) :
    (run (resizeBit sign top) m s).phase=s.phase ∧
    ∀ q,q≠top → (run (resizeBit sign top) m s).basis q=s.basis q := by
  constructor
  · rfl
  · intro q hq; simp [resizeBit,run,writeBit,hq]

/-- Sign-extension preserves the represented integer and changes only the
borrowed zero high bit. The caller owns its allocation proof. -/
theorem rowGrow_run (lo : List Wire) (sign top : Wire)
    (ht : top∉lo) (hne : sign≠top) (s : State) (m : List Bool)
    (hz : s.basis top=false) :
    let t := run (resizeBit sign top) m s
    t.phase=s.phase ∧ (∀ q,q≠top → t.basis q=s.basis q) ∧
    signedRegValue ((lo++[top])++[sign]) t.basis=signedRegValue (lo++[sign]) s.basis := by
  have hf := resize_frame sign top s m
  refine ⟨hf.1,hf.2,?_⟩
  have hlo : regValue lo (run (resizeBit sign top) m s).basis=regValue lo s.basis := by
    apply regValue_congr
    intro q hq
    exact hf.2 q (fun h => ht (h ▸ hq))
  have hs := hf.2 sign hne
  have hb : (run (resizeBit sign top) m s).basis top=s.basis sign := by
    simp [resizeBit,run,writeBit,hz]
  rw [signed_split,signed_split,regValue_append,hlo]
  simp only [List.length_append,List.length_singleton]
  cases h : s.basis sign <;>
    simp [regValue,hb,hs,h,Nat.pow_succ,Nat.cast_add,Nat.cast_mul]
  all_goals ring

/-- Shrinking requires the removed high bit to equal the sign. The CX then
actually clears it, allowing a subsequent arena release. -/
theorem rowShrink_run (lo : List Wire) (sign top : Wire)
    (ht : top∉lo) (hne : sign≠top) (s : State) (m : List Bool)
    (he : s.basis top=s.basis sign) :
    let t := run (resizeBit sign top) m s
    t.phase=s.phase ∧ (∀ q,q≠top → t.basis q=s.basis q) ∧
    t.basis top=false ∧
    signedRegValue (lo++[sign]) t.basis=signedRegValue ((lo++[top])++[sign]) s.basis := by
  have hf := resize_frame sign top s m
  refine ⟨hf.1,hf.2,?_,?_⟩
  · simp [resizeBit,run,writeBit,he]
  · have hlo : regValue lo (run (resizeBit sign top) m s).basis=regValue lo s.basis := by
      apply regValue_congr
      intro q hq
      exact hf.2 q (fun h => ht (h ▸ hq))
    rw [signed_split,signed_split,regValue_append,hlo]
    have hs := hf.2 sign hne
    simp only [List.length_append,List.length_singleton]
    cases h : s.basis sign <;>
      simp [regValue,he,hs,h,Nat.pow_succ,Nat.cast_add,Nat.cast_mul]
    all_goals ring

/-- The signed window law discharges the redundant-sign-bit precondition;
it is not an unchecked assertion by the allocator. -/
theorem rowShrink_bit_of_fits (lo : List Wire) (sign top : Wire) (s : BasisState)
    (hlo : -((2^lo.length:Nat):Int) ≤ signedRegValue ((lo++[top])++[sign]) s)
    (hhi : signedRegValue ((lo++[top])++[sign]) s < ((2^lo.length:Nat):Int)) :
    s top=s sign := by
  have hr : (regValue lo s:Int)<((2^lo.length:Nat):Int) := by exact_mod_cast regValue_lt lo s
  have hz := Int.natCast_nonneg (regValue lo s)
  rw [signed_split,regValue_append] at hlo hhi
  cases ht : s top <;> cases hs : s sign <;>
    simp_all [regValue,Nat.pow_succ,Nat.cast_add,Nat.cast_mul] <;> omega

theorem resize_support (sign top : Wire) : wires (resizeBit sign top)={sign,top} := by
  simp [resizeBit,wires,Instr.wires]

theorem resize_in_arena (sign top : Wire) (hs : sign∈arenaWires) (ht : top∈arenaWires) :
    wires (resizeBit sign top)⊆arenaWires := by
  rw [resize_support]
  simpa using (show {sign,top}⊆arenaWires from by
    intro q hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> assumption)

theorem resize_cost (sign top : Wire) :
    toffoliCount (resizeBit sign top)=0 ∧ measurementCount (resizeBit sign top)=0 := by
  exact ⟨rfl,rfl⟩

/-- A physical shrink may return the high wire to the same bounded arena;
all remaining unowned wires stay clean. -/
theorem rowShrink_release (A : Arena) (lo : List Wire) (sign top : Wire)
    (ht : top∉lo) (hne : sign≠top) (s : State) (m : List Bool)
    (hr : A.Ready s.basis) (ho : top∈A.live)
    (he : s.basis top=s.basis sign) :
    ∃ B, A.release {top} (run (resizeBit sign top) m s).basis=some B ∧
      B.Ready (run (resizeBit sign top) m s).basis := by
  have hv := rowShrink_run lo sign top ht hne s m he
  have hclean : A.Ready (run (resizeBit sign top) m s).basis := by
    intro q hq hn
    rw [hv.2.1 q (fun h => hn (h ▸ ho))]
    exact hr q hq hn
  have hex := (A.release_success {top} (run (resizeBit sign top) m s).basis).mpr
    ⟨by simpa using ho,by simpa using hv.2.2.1⟩
  obtain ⟨B,hB⟩ := hex
  exact ⟨B,hB,A.release_ready B {top} _ hclean hB⟩

/-- Reservation supplies the clean bit and disjointness needed by physical
sign extension, and extension preserves readiness of the enlarged arena. -/
theorem rowGrow_reserved (A B : Arena) (lo : List Wire) (sign top : Wire)
    (hs : sign∈A.live) (hl : lo.toFinset⊆A.live) (s : State) (m : List Bool)
    (hr : A.Ready s.basis) (hres : A.reserve {top}=some B) :
    B.Ready (run (resizeBit sign top) m s).basis ∧
    signedRegValue ((lo++[top])++[sign]) (run (resizeBit sign top) m s).basis=
      signedRegValue (lo++[sign]) s.basis := by
  have hv := (A.reserve_success {top}).mp ⟨B,hres⟩
  have hn : top∉A.live := fun h => Finset.disjoint_left.mp hv.2 h (by simp)
  have ht : top∉lo := fun h => hn (hl (List.mem_toFinset.mpr h))
  have hne : sign≠top := fun h => hn (h ▸ hs)
  have hb := A.reserve_ready B {top} s.basis hr hres
  have hz : s.basis top=false := hb.2 top (by simp)
  have hout := rowGrow_run lo sign top ht hne s m hz
  have hown : top∈B.live := by
    simp only [Arena.reserve,dif_pos hv,Option.some.injEq] at hres
    cases hres
    simp
  refine ⟨?_,hout.2.2⟩
  intro q hq hnot
  rw [hout.2.1 q (fun h => hnot (h ▸ hown))]
  exact hb.1 q hq hnot

end ECDSAAdd.Arithmetic.Paper935
