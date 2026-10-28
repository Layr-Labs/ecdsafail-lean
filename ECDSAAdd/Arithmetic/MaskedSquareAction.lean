import ECDSAAdd.Arithmetic.MappedSignedSquare
import ECDSAAdd.Arithmetic.MeasuredMaskedAdder

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

def maskedSquareBody (clear : Bool) (bank dst pad carry : List Wire) (cin : Wire) : Program :=
  if clear then mappedSignedSquareClear bank dst pad carry cin
    else mappedSignedSquare bank dst pad carry cin

def maskedSquareAction (clear : Bool) (control : Wire) (src bank dst pad carry : List Wire)
    (cin : Wire) : Program :=
  copyRegister (some control) src bank++maskedSquareBody clear bank dst pad carry cin++
    eraseMask control src bank

/-- Either produce or independently clean a controlled square. The input
mask itself is measured out, so it can be reused by the following fold. -/
theorem maskedSquareAction_correct (clear : Bool) (control cin : Wire)
    (src bank dst pad carry : List Wire)
    (hn : (control::cin::src++bank++dst++pad++carry).Nodup)
    (hsrc : src.length=bank.length) (hx : 2≤bank.length) (hd : dst.length=2*bank.length)
    (hp : 1≤pad.length) (hc : dst.length-1≤carry.length)
    (s : State) (records : List Bool) (hbank : regValue bank s.basis=0)
    (hpad : regValue pad s.basis=0) (hcarry : regValue carry s.basis=0) (hcin : s.basis cin=false)
    (hdst : regValue dst s.basis=if clear then (if s.basis control then regValue src s.basis else 0)^2 else 0) :
    (run (maskedSquareAction clear control src bank dst pad carry cin) records s).phase=s.phase ∧
    regValue dst (run (maskedSquareAction clear control src bank dst pad carry cin) records s).basis=
      (if clear then 0 else (if s.basis control then regValue src s.basis else 0)^2) ∧
    ∀q,q∉dst → (run (maskedSquareAction clear control src bank dst pad carry cin) records s).basis q=s.basis q := by
  let copy := copyRegister (some control) src bank
  let body := maskedSquareBody clear bank dst pad carry cin
  let erase := eraseMask control src bank
  let tailRecords := records.drop (measurementCount copy)
  let u := run copy (records.take (measurementCount copy)) s
  let v := run body (tailRecords.take (measurementCount body)) u
  let out := run erase (tailRecords.drop (measurementCount body)) v
  let V := if s.basis control then regValue src s.basis else 0
  have cnt := List.nodup_iff_count.mp hn
  have notBank (q : Wire) (hq : q∈control::cin::src++dst++pad++carry) : q∉bank := by
    intro bad
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have h := cnt q
    simp only [List.count_cons,List.count_append] at h a
    omega
  have notDst (q : Wire) (hq : q∈control::cin::src++bank++pad++carry) : q∉dst := by
    intro bad
    have a := List.count_pos_iff.mpr hq
    have b := List.count_pos_iff.mpr bad
    have h := cnt q
    simp only [List.count_cons,List.count_append] at h a
    omega
  have copyNd : (src++bank).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := cnt q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have maskNd : (control::src++bank).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := cnt q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have squareNd : (cin::bank++dst++pad++carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro q; have h := cnt q
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  obtain ⟨cp,ce,cv⟩ := copyRegister_correct (some control) src bank hsrc copyNd
    (by intro q hq; have eq : q=control := by simpa [eq_comm] using hq
        subst q; exact notBank control (by simp)) s (records.take (measurementCount copy))
  have bankU : regValue bank u.basis=V := by
    rw [cv,hbank,Nat.zero_xor]
    rfl
  have controlU : u.basis control=s.basis control := ce control (notBank control (by simp))
  have srcU : regValue src u.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => ce q (notBank q (by simp [hq])))
  have carryU : regValue carry u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ce q (notBank q (by simp [hq])))).trans hcarry
  have padU : regValue pad u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ce q (notBank q (by simp [hq])))).trans hpad
  have cinU : u.basis cin=false := (ce cin (notBank cin (by simp))).trans hcin
  have dstU : regValue dst u.basis=if clear then V^2 else 0 :=
    (regValue_congr _ _ _ (fun q hq => ce q (notBank q (by simp [hq])))).trans hdst
  have inner : v.phase=u.phase ∧ regValue dst v.basis=(if clear then 0 else V^2) ∧
      ∀q,q∉dst → v.basis q=u.basis q := by
    cases h : clear
    · have run := mappedSignedSquare_correct cin bank dst pad carry squareNd hx hd hp hc u
        (tailRecords.take (measurementCount body)) (by simpa [h] using dstU) padU carryU cinU
      simpa [v,body,maskedSquareBody,h,bankU] using run
    · have run := mappedSignedSquareClear_correct cin bank dst pad carry squareNd hx hd hp hc u
        (tailRecords.take (measurementCount body)) (by simpa [h,bankU] using dstU) padU carryU cinU
      simpa [v,body,maskedSquareBody,h] using run
  have bankV : regValue bank v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => inner.2.2 q (notDst q (by simp [hq])))).trans bankU
  have srcV : regValue src v.basis=regValue src s.basis :=
    (regValue_congr _ _ _ (fun q hq => inner.2.2 q (notDst q (by simp [hq])))).trans srcU
  have ctlV : v.basis control=s.basis control :=
    (inner.2.2 control (notDst control (by simp))).trans controlU
  have relation : regValue bank v.basis=if v.basis control then regValue src v.basis else 0 := by
    rw [bankV,ctlV,srcV]
  obtain ⟨ep,ee,ev⟩ := eraseMask_correct control src bank hsrc maskNd v
    (tailRecords.drop (measurementCount body)) relation
  have result : out.phase=s.phase ∧ regValue dst out.basis=(if clear then 0 else V^2) ∧
      ∀q,q∉dst → out.basis q=s.basis q := by
    refine ⟨ep.trans (inner.1.trans cp),?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => ee q (notBank q (by simp [hq])))).trans inner.2.1
    · intro q hq
      by_cases inBank : q∈bank
      · exact ((regValue_zero _ _).mp ev q inBank).trans ((regValue_zero _ _).mp hbank q inBank).symm
      · exact (ee q inBank).trans ((inner.2.2 q hq).trans (ce q inBank))
  simpa [maskedSquareAction,copy,body,erase,tailRecords,u,v,out,V,run_append] using result

end ECDSAAdd.Arithmetic
