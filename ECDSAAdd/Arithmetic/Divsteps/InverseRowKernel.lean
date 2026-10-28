import ECDSAAdd.Arithmetic.Divsteps.RowKernel
import ECDSAAdd.Arithmetic.Divsteps.MaskedSignedSub
import ECDSAAdd.Arithmetic.SignedRecordProgram

namespace ECDSAAdd.Arithmetic.Divsteps

/-- Constructive inverse arithmetic: subtract the masked source first, then
conditionally negate. This is not a reversal of measured instructions. -/
def inverseRowKernel (swap parity cin : Wire) (src mask target carry : List Wire) : Program :=
  measuredMaskedSubInPlace parity src mask target carry cin ++
    negateSigned swap mask target carry

theorem inverseRowKernel_correct (q c cin : Wire) (src mask y carry : List Wire)
    (hn : (q::c::cin::(src++mask++y++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) (Q C : Bool) (A B : Int)
    (hsublo : -((2^(y.length-1):Nat):Int) ≤ B-(if C then A else 0))
    (hsubhi : B-(if C then A else 0) < ((2^(y.length-1):Nat):Int))
    (hlo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -(B-(if C then A else 0)) else B-(if C then A else 0)))
    (hhi : (if Q then -(B-(if C then A else 0)) else B-(if C then A else 0)) < ((2^(y.length-1):Nat):Int))
    (s : State) (m : List Bool) (hq : s.basis q=Q) (hcc : s.basis c=C)
    (hi : s.basis cin=false) (ha : signedRegValue src s.basis=A)
    (hb : signedRegValue y s.basis=B) (hm : regValue mask s.basis=0)
    (hk : regValue carry s.basis=0) :
    (run (inverseRowKernel q c cin src mask y carry) m s).phase=s.phase ∧
    (∀ w, w∉y → (run (inverseRowKernel q c cin src mask y carry) m s).basis w=s.basis w) ∧
    signedRegValue y (run (inverseRowKernel q c cin src mask y carry) m s).basis=
      (if Q then -(B-(if C then A else 0)) else B-(if C then A else 0)) := by
  have hn1 := (List.nodup_cons.mp hn).2
  have hn2 : (q::(mask++y++carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have := List.nodup_iff_count.mp hn w
    simp only [List.count_cons,List.count_append] at this ⊢
    omega
  have hqy : q∉y := by
    intro hy
    apply (List.nodup_cons.mp hn).1
    simp only [List.mem_cons,List.mem_append]
    tauto
  let t := run (measuredMaskedSubInPlace c src mask y carry cin) m s
  let rest := m.drop (measurementCount (measuredMaskedSubInPlace c src mask y carry cin))
  obtain ⟨hp1,ho1⟩ := maskedSub_signed_spec c cin src mask y carry hn1 hs ht hc C A B hsublo hsubhi
    s m ⟨hcc,ha,hm,hb,hi,hk⟩
  have keep1 := measuredMaskedSubInPlace_frame c cin src mask y carry hn1 hs ht hc s m hm hi hk
  obtain ⟨hp2,ho2⟩ := negateSigned_int_spec q mask y carry hn2 ht hc Q (B-(if C then A else 0))
    hlo hhi t rest ⟨(keep1 q hqy).trans hq,ho1.2.2.1,ho1.2.2.2.1,ho1.2.2.2.2.2⟩
  have keep2 := negateSigned_frame q mask y carry hn2 ht hc t rest ho1.2.2.1 ho1.2.2.2.2.2
  rw [inverseRowKernel,run_append,run_take]
  exact ⟨hp2.trans hp1,(fun w hw => (keep2 w hw).trans (keep1 w hw)),ho2.2.2.1⟩

theorem inverseRowKernel_counts (q c cin : Wire) (src mask y carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) :
    toffoliCount (inverseRowKernel q c cin src mask y carry)=3*y.length-2 ∧
    measurementCount (inverseRowKernel q c cin src mask y carry)=3*y.length-2 := by
  have hn := negateSigned_counts q mask y carry ht hc
  have ha := (measuredMaskedInPlace_counts c src mask y carry cin hs ht hc).2
  simp only [inverseRowKernel,toffoliCount_append,measurementCount_append,hn.1,hn.2,ha.1,ha.2]
  constructor <;> omega

/-- Forward and inverse arithmetic restore the entire state. Their measurement
records may be unrelated; neither program relies on replaying outcomes. -/
theorem inverseRowKernel_after (q c cin : Wire) (src mask y carry : List Wire)
    (hn : (q::c::cin::(src++mask++y++carry)).Nodup)
    (hs : src.length=mask.length) (ht : mask.length=y.length)
    (hc : carry.length+1=y.length) (Q C : Bool) (A B : Int)
    (hBlo : -((2^(y.length-1):Nat):Int)≤B) (hBhi : B<((2^(y.length-1):Nat):Int))
    (hneglo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -B else B))
    (hneghi : (if Q then -B else B) < ((2^(y.length-1):Nat):Int))
    (hlo : -((2^(y.length-1):Nat):Int) ≤ (if Q then -B else B)+(if C then A else 0))
    (hhi : (if Q then -B else B)+(if C then A else 0) < ((2^(y.length-1):Nat):Int))
    (s : State) (mf mi : List Bool) (hq : s.basis q=Q) (hcc : s.basis c=C)
    (hi : s.basis cin=false) (ha : signedRegValue src s.basis=A)
    (hb : signedRegValue y s.basis=B) (hm : regValue mask s.basis=0)
    (hk : regValue carry s.basis=0) :
    run (inverseRowKernel q c cin src mask y carry) mi
      (run (rowKernel q c cin src mask y carry) mf s)=s := by
  let t := run (rowKernel q c cin src mask y carry) mf s
  obtain ⟨hfp,hff,hfv⟩ := rowKernel_correct q c cin src mask y carry hn hs ht hc Q C A B
    hneglo hneghi hlo hhi s mf hq hcc hi ha hb hm hk
  have away (w : Wire) (hw : w∈q::c::cin::(src++mask++carry)) : w∉y := by
    intro hy
    have hh := List.nodup_iff_count.mp hn w
    have hw' := List.count_pos_iff.mpr hw
    have hy' := List.count_pos_iff.mpr hy
    simp only [List.count_cons,List.count_append] at hh hw'
    omega
  have kq := hff q (away q (by simp))
  have kc := hff c (away c (by simp))
  have ki := hff cin (away cin (by simp))
  have ka : signedRegValue src t.basis=A := by
    unfold signedRegValue
    rw [regValue_congr src t.basis s.basis
      (fun w hw => hff w (away w (by simp only [List.mem_cons,List.mem_append]; tauto)))]
    exact ha
  have km := regValue_congr mask t.basis s.basis
    (fun w hw => hff w (away w (by simp only [List.mem_cons,List.mem_append]; tauto)))
  have kk := regValue_congr carry t.basis s.basis
    (fun w hw => hff w (away w (by simp only [List.mem_cons,List.mem_append]; tauto)))
  have hcancel : (if Q then -(((if Q then -B else B)+(if C then A else 0))-(if C then A else 0))
      else ((if Q then -B else B)+(if C then A else 0))-(if C then A else 0))=B := by
    cases Q <;> simp
  obtain ⟨hip,hif,hiv⟩ := inverseRowKernel_correct q c cin src mask y carry hn hs ht hc Q C A
    ((if Q then -B else B)+(if C then A else 0))
    (by simpa using hneglo) (by simpa using hneghi)
    (by simpa only [hcancel] using hBlo) (by simpa only [hcancel] using hBhi)
    t mi (kq.trans hq) (kc.trans hcc) (ki.trans hi) ka hfv (km.trans hm) (kk.trans hk)
  rw [hcancel] at hiv
  apply congrArg₂ State.mk (hip.trans hfp)
  funext w
  by_cases hw : w∈y
  · exact (signedRegValue_eq_iff y _ _).mp (hiv.trans hb.symm) w hw
  · exact (hif w hw).trans (hff w hw)

theorem inverseRowKernel_wires_eq (q c cin : Wire) (src mask y carry : List Wire)
    (hs : src.length=mask.length) (ht : mask.length=y.length) (hc : carry.length+1=y.length) :
    wires (inverseRowKernel q c cin src mask y carry)=wires (rowKernel q c cin src mask y carry) := by
  rw [inverseRowKernel,rowKernel,wires_append,wires_append,
    (measuredMaskedInPlace_wires c src mask y carry cin hs ht hc).1,
    (measuredMaskedInPlace_wires c src mask y carry cin hs ht hc).2]
  exact Finset.union_comm _ _

end ECDSAAdd.Arithmetic.Divsteps
