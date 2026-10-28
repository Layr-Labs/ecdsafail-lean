import ECDSAAdd.Arithmetic.BalancedCoreComposeProof
import ECDSAAdd.Arithmetic.BalancedCleanupCircuitProof

set_option maxRecDepth 4096
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField

/-- Complete actual forward field kernel, including final parity and
source-guard cleanup. Every measurement record restores incoming phase. -/
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hr : signedRegValue L.r s.basis=X) (hyr : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧
    regValue L.r t.basis=encodeWord 256 (halfResult (rawSum B X Y)) ∧
    (∀q∈work L,t.basis q=false) ∧
    (∀q,q∉L.r → t.basis q=s.basis q) := by
  let R := halfResult (rawSum B X Y)
  let ms := m.drop (measurementCount (coreProgram L))
  generalize ec : run (coreProgram L) m s=c
  have core := core_correct L hw hn B X Y hx hy s m hs hr hyr hc
  rw [ec] at core
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  have sgp : L.sourceGuard≠L.parity := by tauto
  have ysg : L.ymsb≠L.sourceGuard := Ne.symm (by tauto)
  have ypa : L.ymsb≠L.parity := Ne.symm (by tauto)
  have n0 : L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have rcenter : Centered R := (halfResult_spec _ (rawSum_bounds B X Y hx hy)).1
  have qflag (q f : Wire) (hq : q∈L.y)
      (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠f := by
    intro e
    have mem : f∈L.y := e ▸ hq
    exact flagAway L hn f hf (by simp [mem])
  have yr (q : Wire) (hq : q∈L.y) : q∉L.r := by
    have a := compose_raw_away L hn q (by simp [hq])
    exact fun h => a (by simp [rawTarget,h])
  have cY : regValue L.y c.basis=encodeWord 256 Y := by
    have same := regValue_congr L.y c.basis s.basis
      (fun q hq => core.2.2.2.2.2 q (yr q hq) (qflag q L.parity hq (by simp))
        (qflag q L.sourceGuard hq (by simp)))
    exact same.trans (word_encoding L.y 256 (BalancedCleanup.widths L.toLayout hw).2.2.1 s.basis Y hyr)
  have signAway : L.sign∉L.r := by
    exact fun h => flagAway L hn L.sign (by simp) (by simp [h])
  have cS : c.basis L.sign=B :=
    (core.2.2.2.2.2 L.sign signAway (Ne.symm (by tauto)) (Ne.symm (by tauto))).trans hs
  have parity : originalParity (rawSum B X Y)=decide (q < |2*R-signedY B Y|) := by
    apply decide_eq_decide.mpr
    exact halfResult_parity_interval B X Y hx hy
  have cl := BalancedCleanup.correct L.toLayout hw n0 R Y B rcenter hy c ms
    core.2.1 cY cS (core.2.2.2.2.1 _ (by simp [coreClean]))
    (core.2.2.2.2.1 _ (by simp [coreClean]))
    (fun q hq => core.2.2.2.2.1 q (by simp [coreClean,hq]))
    (core.2.2.1.trans parity)
  let d : State := ⟨c.phase,writeBit c.basis L.parity false⟩
  have dp : d.basis L.sourceGuard=s.basis L.ymsb := by
    exact (show d.basis L.sourceGuard=c.basis L.sourceGuard from by simp [d,writeBit,sgp]).trans core.2.2.2.1
  have dy : d.basis L.ymsb=s.basis L.ymsb := by
    have hy0 : L.ymsb∈L.y := by simp [BalancedCleanup.Layout.y]
    exact (show d.basis L.ymsb=c.basis L.ymsb from by simp [d,writeBit,ypa]).trans
      (core.2.2.2.2.2 L.ymsb (yr _ hy0) ypa ysg)
  let t : State := ⟨c.phase,writeBit d.basis L.sourceGuard false⟩
  have actual : run (program L) m s=t := by
    rw [program_eq_core,List.append_assoc,run_append,run_take,ec]
    change run (BalancedCleanup.program L.toLayout++[.CX L.ymsb L.sourceGuard]) ms c=t
    rw [run_append,run_take,cl]
    change ⟨c.phase,writeBit d.basis L.sourceGuard
      (d.basis L.sourceGuard ^^ d.basis L.ymsb)⟩=t
    rw [dp,dy,Bool.xor_self]
  have frame (q : Wire) (hq : q∉L.r) : t.basis q=s.basis q := by
    by_cases hp : q=L.parity
    · subst q
      simp only [t,d,writeBit,Function.update_of_ne (Ne.symm sgp),Function.update_self]
      exact (hc _ (by simp [work])).symm
    by_cases hg : q=L.sourceGuard
    · subst q
      simp only [t,writeBit,Function.update_self]
      exact (hc _ (by simp [work])).symm
    simp only [t,d,writeBit,Function.update_of_ne hg,Function.update_of_ne hp]
    exact core.2.2.2.2.2 q hq hp hg
  rw [actual]
  refine ⟨core.1,?_,?_,frame⟩
  · exact (regValue_congr L.r t.basis c.basis (by
      intro q hq
      have np : q≠L.parity := fun e => flagAway L hn L.parity (by simp) (by simp [e ▸ hq])
      have ng : q≠L.sourceGuard := fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ hq])
      simp only [t,d,writeBit,Function.update_of_ne ng,Function.update_of_ne np])).trans core.2.1
  · intro q hq
    have outside : q∉L.r := by
      intro qr
      have h := List.nodup_iff_count.mp hn q
      have a := List.count_pos_iff.mpr hq
      have b := List.count_pos_iff.mpr qr
      simp only [Layout.wires,BalancedCleanup.Layout.wires,work,
        BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
        List.count_append,List.count_cons,List.count_nil] at h a b
      omega
    exact (frame q outside).trans (hc q hq)

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.program_correct
