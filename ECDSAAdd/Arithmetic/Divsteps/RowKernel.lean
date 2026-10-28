import ECDSAAdd.Arithmetic.Divsteps.SignedNegate
import ECDSAAdd.Arithmetic.Divsteps.MaskedSignedAdd

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Shared row arithmetic after routing: conditionally negate the target, then
add the parity-masked source. The mask doubles as the clean negation source. -/
def rowKernel (swap parity cin : Wire) (src mask target carry : List Wire) : Program :=
  negateSigned swap mask target carry ++
  measuredMaskedAddInPlace parity src mask target carry cin

/-- All non-target wires, including controls, source, mask and carries, are
restored. Only explicit signed-fit obligations remain for the calling walk. -/
theorem rowKernel_correct (q c cin : Wire) (src mask y carry : List Wire)
    (hn : (q::c::cin::(src++mask++y++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) (Q C : Bool) (A B : Int)
    (hneglo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -B else B))
    (hneghi : (if Q then -B else B) < ((2^(y.length-1):Nat):Int))
    (hlo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -B else B)+(if C then A else 0))
    (hhi : (if Q then -B else B)+(if C then A else 0) < ((2^(y.length-1):Nat):Int))
    (s : State) (m : List Bool) (hq : s.basis q=Q) (hcc : s.basis c=C)
    (hi : s.basis cin=false) (ha : signedRegValue src s.basis=A)
    (hb : signedRegValue y s.basis=B) (hm : regValue mask s.basis=0)
    (hk : regValue carry s.basis=0) :
    (run (rowKernel q c cin src mask y carry) m s).phase=s.phase ∧
    (∀ w, w∉y → (run (rowKernel q c cin src mask y carry) m s).basis w=s.basis w) ∧
    signedRegValue y (run (rowKernel q c cin src mask y carry) m s).basis=
      (if Q then -B else B)+(if C then A else 0) := by
  have hn1 : (q::(mask++y++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at this ⊢
    omega
  have hn2 := (List.nodup_cons.mp hn).2
  have outside (w : Wire) (hw : w=c ∨ w=cin ∨ w∈src) : w∉y := by
    intro hy
    have hh := List.nodup_iff_count.mp hn w
    have hy' := List.count_pos_iff.mpr hy
    simp only [List.count_cons,List.count_append] at hh
    rcases hw with rfl | rfl | hw
    · simp only [beq_self_eq_true,if_true] at hh; omega
    · simp only [beq_self_eq_true,if_true] at hh; omega
    · have := List.count_pos_iff.mpr hw; omega
  let t := run (negateSigned q mask y carry) m s
  let rest := m.drop (measurementCount (negateSigned q mask y carry))
  obtain ⟨hp1,ho1⟩ := negateSigned_int_spec q mask y carry hn1 ht hc Q B hneglo hneghi
    s m ⟨hq,hm,hb,hk⟩
  have keep1 := negateSigned_frame q mask y carry hn1 ht hc s m hm hk
  have tc : t.basis c=C := (keep1 c (outside c (by tauto))).trans hcc
  have ti : t.basis cin=false := (keep1 cin (outside cin (by tauto))).trans hi
  have ta : signedRegValue src t.basis=A := by
    unfold signedRegValue
    rw [regValue_congr src t.basis s.basis (fun w hw => keep1 w (outside w (by tauto)))]
    exact ha
  obtain ⟨hp2,ho2⟩ := maskedAdd_signed_spec c cin src mask y carry hn2 hs ht hc C A
    (if Q then -B else B) hlo hhi t rest ⟨tc,ta,ho1.2.1,ho1.2.2.1,ti,ho1.2.2.2⟩
  have keep2 := measuredMaskedAddInPlace_frame c cin src mask y carry hn2 hs ht hc
    t rest ho1.2.1 ti ho1.2.2.2
  rw [rowKernel,run_append,run_take]
  exact ⟨hp2.trans hp1,(fun w hw => (keep2 w hw).trans (keep1 w hw)),ho2.2.2.2.1⟩

theorem rowKernel_counts (q c cin : Wire) (src mask y carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) :
    toffoliCount (rowKernel q c cin src mask y carry)=3*y.length-2 ∧
    measurementCount (rowKernel q c cin src mask y carry)=3*y.length-2 := by
  have hn := negateSigned_counts q mask y carry ht hc
  have ha := (measuredMaskedInPlace_counts c src mask y carry cin hs ht hc).1
  simp only [rowKernel,toffoliCount_append,measurementCount_append,hn.1,hn.2,ha.1,ha.2]
  constructor <;> omega

theorem rowKernel_wires (q c cin : Wire) (src mask y carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) :
    wires (rowKernel q c cin src mask y carry)=
      (q::c::cin::(src++mask++y++carry)).toFinset := by
  rw [rowKernel,wires_append,negateSigned_wires q mask y carry ht hc,
    (measuredMaskedInPlace_wires c src mask y carry cin hs ht hc).1]
  ext w
  simp only [Finset.mem_union,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto

theorem rowKernel_qubits (q c cin : Wire) (src mask y carry : List Wire)
    (hn : (q::c::cin::(src++mask++y++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) :
    qubitCount (rowKernel q c cin src mask y carry)=4*y.length+2 := by
  simp only [qubitCount,rowKernel_wires q c cin src mask y carry hs ht hc,
    List.toFinset_card_of_nodup hn,List.length_cons,List.length_append]
  omega

end ECDSAAdd.Arithmetic.Divsteps
