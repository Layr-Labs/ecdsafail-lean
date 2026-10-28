import ECDSAAdd.Arithmetic.BalancedCoreSeedProof
import ECDSAAdd.Arithmetic.BalancedCoreFoldProof
import ECDSAAdd.Arithmetic.BalancedCleanupCircuitViews

set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedCircuit
open BalancedField BalancedFold

private theorem toggle_upper_arithmetic (E B H : Nat) (P N : Bool)
    (he : E=P.toNat+2*(B+H*N.toNat)) :
    B+H*(N ^^ P).toNat=(if P then if N then E-2*H else E+2*H else E)/2 := by
  cases P <;> cases N <;> simp only [Bool.toNat_true,Bool.toNat_false,
    Bool.false_eq_true,if_false,if_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero,
    Nat.zero_add,Bool.xor_true,Bool.xor_false,Bool.not_true,Bool.not_false] at he ⊢ <;> omega

/-- Physical preparation computes the sparse selectors, flips bit 256 and
clears the raw parity bit. The remaining 256-bit view is the proved upper word. -/
theorem prepare_upper (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (T : Int) (s : State) (m : List Bool) (hr : signedRegValue (rawTarget L) s.basis=T)
    (hp : s.basis L.parity=originalParity T)
    (hl : s.basis L.lower=false) (hm : s.basis L.minus=false) (hu : s.basis L.plus=false) :
    regValue (foldTarget L) (run (prepareFold L) m s).basis=toggledWord T/2 := by
  let P := originalParity T
  let N := decide (T<0)
  have one : s.basis L.one=N := word_sign L.r L.one s.basis T hr
  have hrs : signedRegValue (L.r0::(L.rtail++[L.rmsb,L.one])) s.basis=T := by
    simpa [rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,List.append_assoc] using hr
  have low : s.basis L.r0=P := word_parity L.r0 (L.rtail++[L.rmsb,L.one]) s.basis T hrs
  have he := prepareFold_run L hn P N s m hp one low hl hm hu
  let B := regValue (L.rtail++[L.rmsb]) s.basis
  have enc := word_encoding (rawTarget L) 257 (widths L hw).2.1 s.basis T hr
  have shape : encodeWord 257 T=P.toNat+2*(B+2^255*N.toNat) := by
    symm
    change _=encodeWord 257 T at enc
    change (if s.basis L.r0 then 1 else 0)+
      2*regValue ((L.rtail++[L.rmsb])++[L.one]) s.basis=encodeWord 257 T at enc
    rw [regValue_append,show (L.rtail++[L.rmsb]).length=255 by simp [hw.1]] at enc
    simpa [B,low,one,regValue,Bool.toNat,Bool.cond_eq_ite] using enc
  have rawnd := rawTargetND L hn
  change (L.r0::((L.rtail++[L.rmsb])++[L.one])).Nodup at rawnd
  have rAway := (List.nodup_cons.mp rawnd).1
  have same : regValue (L.rtail++[L.rmsb]) (run (prepareFold L) m s).basis=B := by
    apply regValue_congr
    intro q hq
    have member : q∈L.r++L.y++L.carry := by
      have rq : q∈L.r := by
        change q∈L.r0::(L.rtail++[L.rmsb])
        exact List.mem_cons_of_mem L.r0 hq
      exact List.mem_append_left _ (List.mem_append_left _ rq)
    have away (a : Wire) (ha : a∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : q≠a :=
      fun e => flagAway L hn a ha (e ▸ member)
    have qr : q≠L.r0 := fun e => rAway (List.mem_append_left _ (e ▸ hq))
    rw [he]
    simp [writeBit,qr,away L.lower (by simp),away L.minus (by simp),
      away L.plus (by simp),away L.one (by simp)]
  have fs := scalarND L hn
  have oo : L.one≠L.r0 := by
    have mem : L.one∈(L.rtail++[L.rmsb])++[L.one] := by simp
    exact fun e => rAway (e ▸ mem)
  have high : (run (prepareFold L) m s).basis L.one=(N ^^ P) := by
    rw [he]
    simp only [writeBit,Function.update_of_ne oo,Function.update_self]
  have value : regValue (foldTarget L) (run (prepareFold L) m s).basis=B+2^255*(N ^^ P).toNat := by
    rw [show foldTarget L=(L.rtail++[L.rmsb])++[L.one] by simp [foldTarget,List.append_assoc]]
    rw [regValue_append,same,show (L.rtail++[L.rmsb]).length=255 by simp [hw.1]]
    simp only [regValue,List.foldr_cons,List.foldr_nil,high,Nat.mul_zero,Nat.add_zero]
    cases N <;> cases P <;> rfl
  rw [value]
  change _=(if P then if N then encodeWord 257 T-modulusWord else encodeWord 257 T+modulusWord
    else encodeWord 257 T)/2
  have pow : modulusWord=2*2^255 := by norm_num [modulusWord]
  rw [pow]
  exact toggle_upper_arithmetic _ _ _ P N shape

end ECDSAAdd.Arithmetic.BalancedCircuit

#print axioms ECDSAAdd.Arithmetic.BalancedCircuit.prepare_upper
