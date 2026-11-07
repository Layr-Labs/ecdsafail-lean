import ECDSAAdd.Submission.Entrant.MainBase
import ECDSAAdd.Submission.Entrant.Fast01
import ECDSAAdd.Submission.Entrant.Fast02
import ECDSAAdd.Submission.Entrant.Fast03
import ECDSAAdd.Submission.Entrant.Fast04
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
namespace ECDSAAdd.Entrant.ZeroFill
open Arithmetic

theorem pre_invariants_research (a : Nat) (aL aH : Bool) (one U V F xlo xhi el eh : Wire)
    (top mid low : List (Nat × Wire × Wire))
    (hUV : U ≠ V) (hUF : U ≠ F) (hVF : V ≠ F)
    (hlU : xlo ≠ U) (hlV : xlo ≠ V) (hlF : xlo ≠ F) (hhU : xhi ≠ U) (hhV : xhi ≠ V) (hhF : xhi ≠ F)
    (heU : el ≠ U) (heV : el ≠ V) (heF : el ≠ F) (hEU : eh ≠ U) (hEV : eh ≠ V) (hEF : eh ≠ F)
    (hoU : one ≠ U) (hoV : one ≠ V) (hoF : one ≠ F) (hlo : xlo ≠ one) (hho : xhi ≠ one)
    (hT : ∀ x ∈ top ++ mid ++ low, (x.2.1 ≠ U ∧ x.2.2 ≠ U) ∧ (x.2.1 ≠ V ∧ x.2.2 ≠ V) ∧
      (x.2.1 ≠ F ∧ x.2.2 ≠ F))
    (s : State) (hU : s.basis U = false) (hV : s.basis V = false) (hF : s.basis F = false) :
    let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
    t.basis F = (((t.basis xhi == aH) && t.basis V) ^^ parityAt t.basis (correctionWires a top) ^^
       (t.basis eh && (t.basis xhi && !aH))) ∧
    t.basis V = (((t.basis xlo == aL) && t.basis U) ^^ parityAt t.basis (correctionWires a mid) ^^
       (t.basis el && (t.basis xlo && !aL))) := by
  let st := writeBit s.basis one (!s.basis one)
  let t := run (pre a aL aH one U V F xlo xhi el eh top mid low) [] s
  have out (q : Wire) (qu : q ≠ U) (qv : q ≠ V) (qf : q ≠ F) : t.basis q = st q := by
    exact pre_outside_research a aL aH one U V F xlo xhi el eh top mid low q qu qv qf
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hu : t.basis U = accVal a st low := by
    exact pre_U_research a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hv : t.basis V = (((st xlo == aL) && accVal a st low) ^^ accVal a st mid ^^ (st el && (st xlo && !aL))) := by
    exact pre_V_research a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have hf : t.basis F = (((st xhi == aH) && (((st xlo == aL) && accVal a st low) ^^ accVal a st mid ^^
    (st el && (st xlo && !aL)))) ^^ accVal a st top ^^ (st eh && (st xhi && !aH))) := by
    exact pre_F a aL aH one U V F xlo xhi el eh top mid low
      hUV hUF hVF hlU hlV hlF hhU hhV hhF heU heV heF hEU hEV hEF hoU hoV hoF hlo hho hT s hU hV hF
  have htop : accVal a t.basis top = accVal a st top := by
    apply accVal_congr_research
    intro x hx
    have h := hT x (by simp [hx])
    exact ⟨out x.2.1 h.1.1 h.2.1.1 h.2.2.1, out x.2.2 h.1.2 h.2.1.2 h.2.2.2⟩
  have hmid : accVal a t.basis mid = accVal a st mid := by
    apply accVal_congr_research
    intro x hx
    have h := hT x (by simp [hx])
    exact ⟨out x.2.1 h.1.1 h.2.1.1 h.2.2.1, out x.2.2 h.1.2 h.2.1.2 h.2.2.2⟩
  have hh := out xhi hhU hhV hhF
  have he := out eh hEU hEV hEF
  have hl := out xlo hlU hlV hlF
  have hel := out el heU heV heF
  change t.basis F = (((t.basis xhi == aH) && t.basis V) ^^ parityAt t.basis (correctionWires a top) ^^
       (t.basis eh && (t.basis xhi && !aH))) ∧
    t.basis V = (((t.basis xlo == aL) && t.basis U) ^^ parityAt t.basis (correctionWires a mid) ^^
       (t.basis el && (t.basis xlo && !aL)))
  constructor
  · simpa only [correctionWires_parity, htop, hh, he, hv] using hf
  · simpa only [correctionWires_parity, hmid, hl, hel, hu] using hv
end ECDSAAdd.Entrant.ZeroFill
