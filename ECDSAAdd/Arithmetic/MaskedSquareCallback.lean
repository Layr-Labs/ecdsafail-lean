import ECDSAAdd.Arithmetic.MaskedSquareAction

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def maskedSquareCallback (control : Wire) (src bank dst pad carry : List Wire)
    (cin : Wire) (body : Program) : Program :=
  maskedSquareAction false control src bank dst pad carry cin++body++
    maskedSquareAction true control src bank dst pad carry cin

/-- The square can be produced, used by an output-only callback, and
independently erased with fresh measurement records. This contract does not
reverse a measurement stream or assume any sampled input distribution. -/
theorem maskedSquareCallback_correct (control cin : Wire)
    (src bank dst pad carry output : List Wire) (body : Program)
    (hn : (control::cin::src++bank++dst++pad++carry++output).Nodup)
    (hsrc : src.length=bank.length) (hx : 2≤bank.length) (hd : dst.length=2*bank.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hbank : regValue bank s.basis=0)
    (hpad : regValue pad s.basis=0) (hcarry : regValue carry s.basis=0)
    (hcin : s.basis cin=false) (hdst : regValue dst s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue output (run body m t).basis=V ∧
        ∀q,q∉output → (run body m t).basis q=t.basis q) :
    (run (maskedSquareCallback control src bank dst pad carry cin body) records s).phase=s.phase ∧
    regValue output (run (maskedSquareCallback control src bank dst pad carry cin body) records s).basis=V ∧
    ∀q,q∉output → (run (maskedSquareCallback control src bank dst pad carry cin body) records s).basis q=s.basis q := by
  let make := maskedSquareAction false control src bank dst pad carry cin
  let clear := maskedSquareAction true control src bank dst pad carry cin
  let rest := records.drop (measurementCount make)
  let u := run make (records.take (measurementCount make)) s
  let v := run body (rest.take (measurementCount body)) u
  let out := run clear (rest.drop (measurementCount body)) v
  let P := (if s.basis control then regValue src s.basis else 0)^2
  have maskedNd : (control::cin::src++bank++dst++pad++carry).Nodup := by
    apply List.nodup_iff_count.mpr;intro q;have h := List.nodup_iff_count.mp hn q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have dstAway (q : Wire) (hq : q∈control::cin::src++bank++pad++carry++output) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  have outputAway (q : Wire) (hq : q∈control::cin::src++bank++dst++pad++carry) : q∉output := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    simp only [List.count_cons,List.count_append] at h a
    omega
  have produce := maskedSquareAction_correct false control cin src bank dst pad carry maskedNd
    hsrc hx hd hp hc s (records.take (measurementCount make)) hbank hpad hcarry hcin hdst
  have used := callback u (rest.take (measurementCount body)) produce.2.1 produce.2.2
  have clean (q : Wire) (hq : q∈control::cin::src++bank++pad++carry) : v.basis q=s.basis q :=
    (used.2.2 q (outputAway q (by simp only [List.mem_cons,List.mem_append] at hq ⊢;tauto))).trans
      (produce.2.2 q (dstAway q (by simp only [List.mem_cons,List.mem_append] at hq ⊢;tauto)))
  have bankV : regValue bank v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => clean q (by simp [hq]))).trans hbank
  have padV : regValue pad v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => clean q (by simp [hq]))).trans hpad
  have carryV : regValue carry v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => clean q (by simp [hq]))).trans hcarry
  have cinV : v.basis cin=false := (clean cin (by simp)).trans hcin
  have srcV : regValue src v.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => clean q (by simp [hq]))
  have ctrlV : v.basis control=s.basis control := clean control (by simp)
  have dstV : regValue dst v.basis=P :=
    (regValue_congr _ _ _ (fun q hq => used.2.2 q (outputAway q (by simp [hq])))).trans produce.2.1
  have ready : regValue dst v.basis=
      (if v.basis control then regValue src v.basis else 0)^2 := by
    rw [dstV,ctrlV,srcV]
  have erased := maskedSquareAction_correct true control cin src bank dst pad carry maskedNd
    hsrc hx hd hp hc v (rest.drop (measurementCount body)) bankV padV carryV cinV ready
  have value : regValue output out.basis=V :=
    (regValue_congr _ _ _ (fun q hq => erased.2.2 q (dstAway q (by simp [hq])))).trans used.2.1
  have final : out.phase=s.phase ∧ regValue output out.basis=V ∧
      ∀q,q∉output → out.basis q=s.basis q := by
    refine ⟨erased.1.trans (used.1.trans produce.1),value,?_⟩
    intro q hq
    by_cases inDst : q∈dst
    · exact ((regValue_zero _ _).mp erased.2.1 q inDst).trans ((regValue_zero _ _).mp hdst q inDst).symm
    · exact (erased.2.2 q inDst).trans ((used.2.2 q hq).trans (produce.2.2 q inDst))
  simpa [maskedSquareCallback,make,clear,rest,u,v,out,P,run_append] using final

end ECDSAAdd.Arithmetic
