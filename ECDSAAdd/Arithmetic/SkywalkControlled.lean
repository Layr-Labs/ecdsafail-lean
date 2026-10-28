import ECDSAAdd.Arithmetic.SkywalkPointPool
import ECDSAAdd.Arithmetic.MaskedConstant

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- Reversible divisor load: source when enabled, one otherwise. -/
def skywalkSafeDivisor (back : Bool) (c : Wire) (src dst : List Wire) : Program :=
  if back then maskedConstant c dst 1 ++ xorConstant dst 1 ++ copyRegister (some c) src dst
  else copyRegister (some c) src dst ++ xorConstant dst 1 ++ maskedConstant c dst 1

private def SafeFrame (dst : List Wire) (base : BasisState) (O : Nat) (s : BasisState) : Prop :=
  regValue dst s=O ∧ ∀q,q∉dst → s q=base q

/-- Both directions XOR the same exact safe divisor into the scratch word.
Every caller bit outside that scratch is restored and phase is preserved. -/
theorem skywalkSafeDivisor_correct (back : Bool) (c : Wire) (src dst : List Wire)
    (hl : src.length=dst.length) (hn : (c::src++dst).Nodup)
    (hbit : 1<2^dst.length) (s : State) (m : List Bool) :
    (run (skywalkSafeDivisor back c src dst) m s).phase=s.phase ∧
    (∀q,q∉dst → (run (skywalkSafeDivisor back c src dst) m s).basis q=s.basis q) ∧
    regValue dst (run (skywalkSafeDivisor back c src dst) m s).basis=
      regValue dst s.basis ^^^ (if s.basis c then regValue src s.basis else 1) := by
  have hpair := (List.nodup_cons.mp hn).2
  have hc : c∉dst := fun h => (List.nodup_cons.mp hn).1 (List.mem_append_right _ h)
  have hd := (List.nodup_append'.mp hpair).2.1
  have hsd := (List.nodup_append'.mp hpair).2.2
  let X := regValue src s.basis
  let C := s.basis c
  let P := SafeFrame dst s.basis
  have copy (O : Nat) : Triple (P O) (copyRegister (some c) src dst)
      (P (O ^^^ (if C then X else 0))) := by
    intro st ms h
    have hs : regValue src st.basis=X := regValue_congr _ _ _
      (fun q hq => h.2 q (List.disjoint_left.mp hsd hq))
    obtain ⟨hp,hf,hv⟩ := copyRegister_correct (some c) src dst hl hpair (by simpa using hc) st ms
    refine ⟨hp,?_,fun q hq => (hf q hq).trans (h.2 q hq)⟩
    simpa only [copyValue,h.1,hs,h.2 c hc,C] using hv
  have constant (O : Nat) : Triple (P O) (xorConstant dst 1) (P (O ^^^ 1)) := by
    intro st ms h
    obtain ⟨hp,hf,hv⟩ := xorConstant_correct dst hd 1 hbit st ms
    exact ⟨hp,by simpa only [h.1] using hv,fun q hq => (hf q hq).trans (h.2 q hq)⟩
  have mask (O : Nat) : Triple (P O) (maskedConstant c dst 1)
      (P (O ^^^ (if C then 1 else 0))) := by
    intro st ms h
    obtain ⟨hp,hf,hv⟩ := maskedConstant_correct c dst 1 hd hc hbit st ms
    refine ⟨hp,?_,fun q hq => (hf q hq).trans (h.2 q hq)⟩
    simpa only [h.1,h.2 c hc,C] using hv
  let O := regValue dst s.basis
  have hi : P O s.basis := ⟨rfl,fun _ _ => rfl⟩
  cases back with
  | false =>
    have h := (copy O).seq ((constant _).seq (mask _))
    have hcircuit : Triple (P O) (skywalkSafeDivisor false c src dst)
        (P (((O ^^^ (if C then X else 0)) ^^^ 1) ^^^ (if C then 1 else 0))) := by
      simpa only [skywalkSafeDivisor,Bool.false_eq_true,if_false,List.append_assoc] using h
    obtain ⟨hp,hv⟩ := hcircuit s m hi
    refine ⟨hp,hv.2,?_⟩
    change regValue dst (run (skywalkSafeDivisor false c src dst) m s).basis=O ^^^ (if C then X else 1)
    cases hC : C <;> simpa [hC,Nat.xor_assoc] using hv.1
  | true =>
    have h := ((mask O).seq (constant _)).seq (copy _)
    have hcircuit : Triple (P O) (skywalkSafeDivisor true c src dst)
        (P (((O ^^^ (if C then 1 else 0)) ^^^ 1) ^^^ (if C then X else 0))) := by
      simpa only [skywalkSafeDivisor,if_true,List.append_assoc] using h
    obtain ⟨hp,hv⟩ := hcircuit s m hi
    refine ⟨hp,hv.2,?_⟩
    change regValue dst (run (skywalkSafeDivisor true c src dst) m s).basis=O ^^^ (if C then X else 1)
    cases hC : C <;> simpa [hC,Nat.xor_assoc] using hv.1

theorem skywalkSafeDivisor_counts (back : Bool) (c : Wire) (src dst : List Wire)
    (hl : src.length=dst.length) :
    toffoliCount (skywalkSafeDivisor back c src dst)=src.length ∧
    measurementCount (skywalkSafeDivisor back c src dst)=0 := by
  have hc := copyRegister_counts (some c) src dst hl
  have hx := xorConstant_counts dst 1
  have hm := maskedConstant_counts c dst 1
  cases back <;> simp [skywalkSafeDivisor,toffoliCount_append,measurementCount_append,hc,hx,hm]

theorem skywalkSafeDivisor_support (back : Bool) (c : Wire) (src dst : List Wire)
    (hl : src.length=dst.length) :
    wires (skywalkSafeDivisor back c src dst) ⊆ (c::src++dst).toFinset := by
  have hc : wires (copyRegister (some c) src dst) ⊆ (c::src++dst).toFinset := by
    rw [copyRegister_wires _ _ _ hl]
    split
    · exact Finset.empty_subset _
    · simp
  have hx := xorConstant_wires_subset dst 1
  have hm := maskedConstant_wires_subset c dst 1
  have hx' : wires (xorConstant dst 1) ⊆ (c::src++dst).toFinset := by
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
    exact Or.inr (Or.inr (List.mem_toFinset.mp (hx hq)))
  have hm' : wires (maskedConstant c dst 1) ⊆ (c::src++dst).toFinset := by
    intro q hq
    have hh := List.mem_toFinset.mp (hm hq)
    simp only [List.mem_cons] at hh
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc]
    rcases hh with rfl|hh
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hh)
  cases back <;> simp only [skywalkSafeDivisor,Bool.false_eq_true,if_false,if_true,wires_append,
    Finset.union_subset_iff] <;> tauto

/-- Exact controlled wrapping of a divisor-preserving arithmetic kernel. -/
def skywalkControlledProgram (kernel : Program) (c : Wire) (src scratch : List Wire) : Program :=
  skywalkSafeDivisor false c src scratch ++
    (kernel ++ skywalkSafeDivisor true c src scratch)

attribute [local irreducible] skywalkSafeDivisor skywalkControlledProgram run

/-- Generic composition helper. The kernel contract is an explicit theorem
hypothesis, to be supplied by the verified concrete arithmetic port. -/
theorem skywalkControlled_core_correct (kernel : Program) (c : Wire)
    (x d y work : List Wire) (hl : x.length=d.length)
    (hn : (c::x++d++y++work).Nodup) (hbit : 1<2^d.length)
    (X Y R : Nat) (C : Bool)
    (hk : ∀ (st : State) (ms : List Bool),
      regValue d st.basis=(if C then X else 1) → regValue y st.basis=Y → regValue work st.basis=0 →
      (run kernel ms st).phase=st.phase ∧ regValue y (run kernel ms st).basis=R ∧
        ∀q,q∉y → (run kernel ms st).basis q=st.basis q)
    (s : State) (m : List Bool) (hc : s.basis c=C)
    (hxs : regValue x s.basis=X) (hys : regValue y s.basis=Y)
    (hd0 : regValue d s.basis=0) (hw0 : regValue work s.basis=0) :
    (run (skywalkControlledProgram kernel c x d) m s).phase=s.phase ∧
    regValue y (run (skywalkControlledProgram kernel c x d) m s).basis=R ∧
    ∀q,q∉y → (run (skywalkControlledProgram kernel c x d) m s).basis q=s.basis q := by
  let D := if C then X else 1
  let P := PairFrame d y s.basis
  have nsafe : (c::x++d).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have ncD : c∉d := fun hm => (List.nodup_cons.mp nsafe).1 (List.mem_append_right _ hm)
  have ncy : c∉y := by
    intro hm
    have h := List.nodup_cons.mp hn
    exact h.1 (by simp [hm])
  have disjoint (a b : List Wire) (hab : ∀q,a.count q+b.count q≤x.count q+d.count q+y.count q+work.count q) : a.Disjoint b := by
    apply List.disjoint_left.mpr
    intro q hqa hqb
    have h := List.nodup_iff_count.mp hn q
    have h1 := List.count_pos_iff.mpr hqa
    have h2 := List.count_pos_iff.mpr hqb
    have hs := hab q
    simp only [List.count_cons,List.count_append] at h
    omega
  have ndy : d.Disjoint y := disjoint d y (by intro q; omega)
  have xdy : x.Disjoint d ∧ x.Disjoint y :=
    ⟨disjoint x d (by intro q; omega),
      disjoint x y (by intro q; omega)⟩
  have wdy : work.Disjoint d ∧ work.Disjoint y :=
    ⟨disjoint work d (by intro q; omega),
      disjoint work y (by intro q; omega)⟩
  have reads (O Z : Nat) (st : BasisState) (h : P O Z st) :
      regValue x st=X ∧ st c=C ∧ regValue work st=0 := by
    refine ⟨?_,(h.2.2 c ncD ncy).trans hc,?_⟩
    · exact (PairFrame.read d y x s.basis st O Z h xdy.1 xdy.2).trans hxs
    · exact (PairFrame.read d y work s.basis st O Z h wdy.1 wdy.2).trans hw0
  have load : Triple (P 0 Y) (skywalkSafeDivisor false c x d) (P D Y) := by
    intro st ms h
    have hr := reads 0 Y st.basis h
    obtain ⟨hf,he,hv⟩ := skywalkSafeDivisor_correct false c x d hl nsafe hbit st ms
    refine ⟨hf,PairFrame.update_temp d y _ _ _ 0 Y D ndy h he ?_⟩
    simpa only [h.1,hr.1,hr.2.1,Nat.zero_xor,D] using hv
  have arithmetic : Triple (P D Y) kernel (P D R) := by
    intro st ms h
    have hr := reads D Y st.basis h
    obtain ⟨hf,hv,he⟩ := hk st ms h.1 h.2.1 hr.2.2
    exact ⟨hf,PairFrame.update_dst d y _ _ _ D Y R ndy h he hv⟩
  have unload : Triple (P D R) (skywalkSafeDivisor true c x d) (P 0 R) := by
    intro st ms h
    have hr := reads D R st.basis h
    obtain ⟨hf,he,hv⟩ := skywalkSafeDivisor_correct true c x d hl nsafe hbit st ms
    refine ⟨hf,PairFrame.update_temp d y _ _ _ D R 0 ndy h he ?_⟩
    simpa only [h.1,hr.1,hr.2.1,D,Nat.xor_self] using hv
  have hi : P 0 Y s.basis := ⟨hd0,hys,fun _ _ _=>rfl⟩
  have all := load.seq (arithmetic.seq unload)
  have hall : Triple (P 0 Y) (skywalkControlledProgram kernel c x d) (P 0 R) := by
    simpa only [skywalkControlledProgram] using all
  obtain ⟨hf,hv⟩ := hall s m hi
  refine ⟨hf,hv.2.1,?_⟩
  intro q hq
  by_cases hqd : q∈d
  · exact ((regValue_zero _ _).mp hv.1 q hqd).trans ((regValue_zero _ _).mp hd0 q hqd).symm
  · exact hv.2.2 q hqd hq

theorem skywalkControlled_core_counts (kernel : Program) (c : Wire) (src dst : List Wire)
    (hl : src.length=dst.length) :
    toffoliCount (skywalkControlledProgram kernel c src dst)=toffoliCount kernel+2*src.length ∧
    measurementCount (skywalkControlledProgram kernel c src dst)=measurementCount kernel := by
  have h1 := skywalkSafeDivisor_counts false c src dst hl
  have h2 := skywalkSafeDivisor_counts true c src dst hl
  simp only [skywalkControlledProgram,toffoliCount_append,measurementCount_append,h1.1,h1.2,h2.1,h2.2]
  omega

theorem skywalkControlled_core_support (kernel : Program) (c : Wire) (src dst : List Wire)
    (hl : src.length=dst.length) :
    wires (skywalkControlledProgram kernel c src dst) ⊆ (c::src++dst).toFinset ∪ wires kernel := by
  have h1 := skywalkSafeDivisor_support false c src dst hl
  have h2 := skywalkSafeDivisor_support true c src dst hl
  simp only [skywalkControlledProgram,wires_append]
  intro q hq
  rcases Finset.mem_union.mp hq with hq|hq
  · exact Finset.mem_union_left _ (h1 hq)
  · rcases Finset.mem_union.mp hq with hq|hq
    · exact Finset.mem_union_right _ hq
    · exact Finset.mem_union_left _ (h2 hq)

end ECDSAAdd.Arithmetic
