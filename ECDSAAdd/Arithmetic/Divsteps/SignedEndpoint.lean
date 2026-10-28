import ECDSAAdd.Arithmetic.Divsteps.EndpointConstant
import ECDSAAdd.Arithmetic.SignedWordBits

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Compile unsigned little-endian weights directly as canonical constants. -/
def endpointUnsignedTerms (p weight : Nat) : List Wire → List (Wire × Nat)
  | [] => []
  | q::qs => (q,weight%p)::endpointUnsignedTerms p (2*weight) qs

theorem endpointUnsignedTerms_wires (p weight : Nat) (qs : List Wire) :
    (endpointUnsignedTerms p weight qs).map Prod.fst=qs := by
  induction qs generalizing weight with
  | nil => rfl
  | cons q qs ih => simp [endpointUnsignedTerms,ih]

theorem endpointUnsignedTerms_canonical (p weight : Nat) (qs : List Wire) (hp : 0<p) :
    ∀ t∈endpointUnsignedTerms p weight qs,t.2<p := by
  induction qs generalizing weight with
  | nil => simp [endpointUnsignedTerms]
  | cons q qs ih =>
    intro t ht
    rcases (List.mem_cons.mp ht) with rfl|ht
    · exact Nat.mod_lt _ hp
    · exact ih _ t ht

theorem endpointUnsignedTerms_value (p weight : Nat) (qs : List Wire) (s : BasisState) :
    (endpointWeightedValue (endpointUnsignedTerms p weight qs) s : ZMod p)=
      (weight : ZMod p)*(regValue qs s : ZMod p) := by
  induction qs generalizing weight with
  | nil => simp [endpointUnsignedTerms,endpointWeightedValue,regValue]
  | cons q qs ih =>
    change (((if s q then weight%p else 0)+endpointWeightedValue
      (endpointUnsignedTerms p (2*weight) qs) s : Nat) : ZMod p)=_
    rw [Nat.cast_add,ih]
    cases hq : s q <;> simp [hq,regValue,ZMod.natCast_mod] <;> ring

/-- The sign bit has negative weight, so no wide coefficient copy or extra
sign-correction term is needed. Source bits are read in place. -/
def endpointSignedTerms (p : Nat) (lo : List Wire) (sign : Wire) : List (Wire × Nat) :=
  endpointUnsignedTerms p 1 lo ++ [(sign,(p-2^lo.length%p)%p)]

theorem endpointSignedTerms_wires (p : Nat) (lo : List Wire) (sign : Wire) :
    (endpointSignedTerms p lo sign).map Prod.fst=lo++[sign] := by
  simp [endpointSignedTerms,endpointUnsignedTerms_wires]

theorem endpointSignedTerms_canonical (p : Nat) (lo : List Wire) (sign : Wire) (hp : 0<p) :
    ∀ t∈endpointSignedTerms p lo sign,t.2<p := by
  intro t ht
  simp only [endpointSignedTerms,List.mem_append,List.mem_singleton] at ht
  rcases ht with ht|rfl
  · exact endpointUnsignedTerms_canonical p 1 lo hp t ht
  · exact Nat.mod_lt _ hp

theorem endpointSignedTerms_value (p : Nat) (lo : List Wire) (sign : Wire)
    (hp : 0<p) (s : BasisState) :
    (endpointWeightedValue (endpointSignedTerms p lo sign) s : ZMod p)=
      (signedRegValue (lo++[sign]) s : ZMod p) := by
  have hneg : (((p-2^lo.length%p)%p : Nat) : ZMod p)=-(2 : ZMod p)^lo.length := by
    rw [ZMod.natCast_mod,Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ hp)),
      ZMod.natCast_self,ZMod.natCast_mod]
    simp
  have hu := endpointUnsignedTerms_value p 1 lo s
  simp only [Nat.cast_one,one_mul] at hu
  rw [endpointSignedTerms,endpointWeightedValue,List.map_append,List.sum_append,Nat.cast_add]
  change (endpointWeightedValue (endpointUnsignedTerms p 1 lo) s : ZMod p)+
    ((if s sign then (p-2^lo.length%p)%p else 0 : Nat) : ZMod p)=_
  rw [hu,signedRegValue_msb,regValue_append]
  cases hs : s sign <;> simp [hs,hneg,regValue,Nat.pow_succ]
  ring

/-- Reduce the actual signed physical row into the existing accumulator. -/
def endpointSigned (U : ModUnaryLayout) (p : Nat) (lo : List Wire) (sign : Wire) : Program :=
  endpointWeighted U p (endpointSignedTerms p lo sign)

theorem endpointSigned_run (U : ModUnaryLayout) (n p : Nat) (lo : List Wire) (sign : Wire)
    (hw : U.Widths n) (hU : U.wires.Nodup) (hsep : List.Disjoint (lo++[sign]) U.wires)
    (hp : 0<p) (hpn : p<2^n) (s : State) (m : List Bool)
    (hz : regValue U.z s.basis=0) (hwork : regValue U.work s.basis=0) :
    let out := run (endpointSigned U p lo sign) m s
    out.phase=s.phase ∧ regValue U.z out.basis<p ∧
    (regValue U.z out.basis : ZMod p)=(signedRegValue (lo++[sign]) s.basis : ZMod p) ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have hn : ∀ t∈endpointSignedTerms p lo sign,(t.1::U.wires).Nodup := by
    intro t ht
    apply List.nodup_cons.mpr
    refine ⟨?_,hU⟩
    intro hq
    apply List.disjoint_left.mp hsep _ hq
    rw [←endpointSignedTerms_wires p lo sign]
    exact List.mem_map.mpr ⟨t,ht,rfl⟩
  have hh := endpointWeighted_run U n p 0 (endpointSignedTerms p lo sign) hw hn hp hpn
    (endpointSignedTerms_canonical p lo sign hp) hp s m hz hwork
  dsimp only at hh ⊢
  refine ⟨hh.1,?_,?_,hh.2.2⟩
  · change regValue U.z (run (endpointWeighted U p (endpointSignedTerms p lo sign)) m s).basis<p
    rw [hh.2.1]
    exact Nat.mod_lt _ hp
  · change (regValue U.z (run (endpointWeighted U p (endpointSignedTerms p lo sign)) m s).basis : ZMod p)=_
    rw [hh.2.1,ZMod.natCast_mod,Nat.zero_add]
    exact endpointSignedTerms_value p lo sign hp s.basis

theorem endpointSigned_counts (U : ModUnaryLayout) (n p : Nat) (lo : List Wire) (sign : Wire)
    (hw : U.Widths n) (hn : 0<n) :
    toffoliCount (endpointSigned U p lo sign)=(lo.length+1)*(4*n-1) ∧
    measurementCount (endpointSigned U p lo sign)=(lo.length+1)*(4*n-1) := by
  have hl : (endpointSignedTerms p lo sign).length=lo.length+1 := by
    have hh := congrArg List.length (endpointSignedTerms_wires p lo sign)
    simpa using hh
  simpa only [endpointSigned,hl] using
    endpointWeighted_counts U n p (endpointSignedTerms p lo sign) hw hn

theorem endpointSigned_support (U : ModUnaryLayout) (n p : Nat) (lo : List Wire) (sign : Wire)
    (hw : U.Widths n) (hn : 0<n) :
    wires (endpointSigned U p lo sign)⊆(lo++[sign]++U.wires).toFinset := by
  simpa only [endpointSigned,endpointSignedTerms_wires] using
    endpointWeighted_support U n p (endpointSignedTerms p lo sign) hw hn

/-- The output is the canonical nonnegative integer remainder, including for
negative source rows, not only an unconstrained modular representative. -/
theorem endpointSigned_remainder (U : ModUnaryLayout) (n p : Nat) (lo : List Wire) (sign : Wire)
    (hw : U.Widths n) (hU : U.wires.Nodup) (hsep : List.Disjoint (lo++[sign]) U.wires)
    (hp : 0<p) (hpn : p<2^n) (s : State) (m : List Bool)
    (hz : regValue U.z s.basis=0) (hwork : regValue U.work s.basis=0) :
    let out := run (endpointSigned U p lo sign) m s
    out.phase=s.phase ∧ (regValue U.z out.basis : Int)=signedRegValue (lo++[sign]) s.basis%p ∧
    regValue U.work out.basis=0 ∧ ∀ q, q∉U.z → out.basis q=s.basis q := by
  have hh := endpointSigned_run U n p lo sign hw hU hsep hp hpn s m hz hwork
  letI : NeZero p := ⟨by omega⟩
  refine ⟨hh.1,?_,hh.2.2.2⟩
  have he := congrArg (fun z : ZMod p => (z.val : Int)) hh.2.2.1
  simpa only [ZMod.val_natCast_of_lt hh.2.1,ZMod.val_intCast] using he

theorem endpointSigned_qubits (U : ModUnaryLayout) (n p : Nat) (lo : List Wire) (sign : Wire)
    (hw : U.Widths n) (hn : 0<n) :
    qubitCount (endpointSigned U p lo sign)≤lo.length+1+U.wires.length := by
  have hh := (Finset.card_le_card (endpointSigned_support U n p lo sign hw hn)).trans
    (List.toFinset_card_le (lo++[sign]++U.wires))
  simpa only [List.length_append,List.length_singleton] using hh

/-- Cost of reducing the current conservative 592-bit coefficient into the
256-bit-field accumulator. This is additional endpoint work, not a saving. -/
theorem endpointSigned592_counts (U : ModUnaryLayout) (p : Nat) (lo : List Wire) (sign : Wire)
    (hw : U.Widths 256) (hl : lo.length=591) :
    toffoliCount (endpointSigned U p lo sign)=605616 ∧
    measurementCount (endpointSigned U p lo sign)=605616 := by
  have hh := endpointSigned_counts U 256 p lo sign hw (by omega)
  simpa only [hl] using hh

end ECDSAAdd.Arithmetic.Divsteps
