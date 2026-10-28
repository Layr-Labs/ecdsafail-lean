import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalEnvironment
import ECDSAAdd.Arithmetic.OffsetBorrowedFieldProof
import ECDSAAdd.Arithmetic.BalancedFieldCircuitProof
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedCanonical
open Secp256k1 BalancedField
attribute [local irreducible] run BalancedCircuit.program OffsetBorrowedField.program

def body (w : Nat → Wire) (sign effS : Wire) : Program :=
  [.X sign]++OffsetBorrowedField.program w sign++[.X sign]++
    swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y

def cell (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))

theorem kernel_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (B : Bool) (X Y : Int)
    (hx : Centered X) (hy : Centered Y) (s : State) (m n : List Bool)
    (hs : s.basis sign=B)
    (hr : signedRegValue (balancedSharedPorts w sign).r s.basis=X)
    (hyv : signedRegValue (balancedSharedPorts w sign).y s.basis=Y) (he : Env w s.basis) :
    run (OffsetBorrowedField.program w sign) m s=
      run (BalancedCircuit.program (balancedSharedPorts w sign)) n s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have fresh := OffsetBorrowedField.program_correct w sign hn ho B X Y hx hy s m hs hr hyv
    he.1 he.2.1 he.2.2
  have old := BalancedCircuit.program_correct L (balancedSharedPorts_widths w sign) nd B X Y
    hx hy s n hs hr hyv (balancedSharedPorts_clean w sign s.basis he.1 he.2.1)
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    · exact (fresh.2.2.2 q hq).trans (old.2.2.2 q hq).symm

theorem zero_records (p : Program) (h : measurementCount p=0) (s : State) (m n : List Bool) :
    run p m s=run p n s := by
  have a := run_take p m s
  have b := run_take p n s
  rw [h,List.take_zero] at a b
  exact a.symm.trans b

/-- Whole-body equality permits reuse of the already verified half/swap
frame theorem. Different kernel record counts do not affect the unitary tail. -/
theorem body_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (body w sign effS) m s=run (balancedTranscriptBody (balancedSharedPorts w sign) effS) m s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have aw := BalancedCircuit.flagAway L nd sign (by simp [L,balancedSharedPorts])
  have sa : sign∉L.r ∧ sign∉L.y := ⟨fun h => aw (by simp [h]),fun h => aw (by simp [h])⟩
  have se := pair_env w sign hn base s.basis _ _ he h
  generalize eu : run [.X sign] m s=u
  have us := BalancedCleanupOffset.x_run sign s m
  rw [eu] at us
  have uf (q : Wire) (hq : q≠sign) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ue : Env w u.basis := by
    rw [us]
    exact env_write w sign ho s.basis (!s.basis sign) se
  have ug : u.basis sign= !base sign := by
    rw [us]
    simp only [writeBit,Function.update_self,h.2.2 sign sa.1 sa.2]
  have uv (r : List Wire) (a : sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => uf q (fun e => a (e ▸ hq)))
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout
      (balancedSharedPorts_widths w sign)).2.2.1,centerWord_decode]
  have eq := kernel_eq w sign hn ho (!base sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m m ug ur uy ue
  let tail := [.X sign]++swapRegisters effS L.r L.y
  have tm : measurementCount tail=0 := by
    have sw := swapRegisters_resources effS L.r L.y
      ((BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)).2.1.trans
        (BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)).2.2.1.symm) hsw
    simp only [tail,measurementCount_append,sw.2.1,measurementCount]
  simp only [body,balancedTranscriptBody,List.append_assoc]
  change run ([.X sign]++(OffsetBorrowedField.program w sign++tail)) m s=
    run ([.X sign]++(BalancedCircuit.program L++tail)) m s
  simp only [run_append]
  simp only [run_take]
  simp only [show measurementCount [.X sign]=0 from rfl,List.drop_zero]
  rw [eu,eq]
  exact zero_records tail tm _ _ _

theorem body_frame (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (body w sign effS)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadCell (base sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadCell (base sign) (base effS) (X,Y)).2)) := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have old := balancedTranscriptBody_frame (balancedSharedPorts w sign) effS
    (balancedSharedPorts_widths w sign) (balancedSharedPorts_nodup w sign hn own) hsw base
    (balancedSharedPorts_clean w sign base he.1 he.2.1) X Y
  intro s m h
  rw [body_eq w sign effS hn ho hsw base he X Y s m h]
  exact old s m h

theorem cell_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hsw : (effS::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup) :
    toffoliCount (cell w b g swap sign effS ig is)=1280 ∧
    measurementCount (cell w b g swap sign effS ig is)=1025 := by
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have sw := swapRegisters_resources effS _ _ (width.2.1.trans width.2.2.1.symm) hsw
  have k := OffsetBorrowedField.counts w sign
  have si := transcriptSelectWindow_counts b swap effS is (body w sign effS)
  have so := transcriptSelectWindow_counts b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))
  change toffoliCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1280 ∧
    measurementCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1025
  rw [so.1,so.2,si.1,si.2]
  simp only [body,toffoliCount_append,measurementCount_append,k.1,k.2,
    sw.1,sw.2.1,width.2.1]
  norm_num [toffoliCount,measurementCount]
end ECDSAAdd.Arithmetic.OffsetBorrowedCanonical

#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.kernel_eq
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.body_frame
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedCanonical.cell_counts
