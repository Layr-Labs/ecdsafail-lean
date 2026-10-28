import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalEnvironment
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseProof
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptReplay

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run BalancedInverse.program OffsetBorrowedInverse.program

def double (w : Nat → Wire) (sign : Wire) : Program :=
  [.X sign]++OffsetBorrowedInverse.program w sign++[.X sign]

def body (w : Nat → Wire) (sign effS : Wire) : Program :=
  swapRegisters effS (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y++double w sign

def cell (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool) : Program :=
  transcriptSelectWindow b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))

/-- Fresh inverse and original inverse have identical complete States,
including arbitrary input phase and independent measurement records. -/
theorem kernel_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (B : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) (s : State) (m n : List Bool)
    (hs : s.basis sign=B)
    (hR : signedRegValue (balancedSharedPorts w sign).r s.basis=R)
    (hY : signedRegValue (balancedSharedPorts w sign).y s.basis=Y) (he : Env w s.basis) :
    run (OffsetBorrowedInverse.program w sign) m s=
      run (BalancedInverse.program (balancedSharedPorts w sign)) n s := by
  let L := balancedSharedPorts w sign
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have fresh := OffsetBorrowedInverse.program_correct w sign hn ho R Y B hr hy s m hR hY hs
    he.1 he.2.1 he.2.2
  have old := BalancedInverse.program_correct L (balancedSharedPorts_widths w sign) nd B R Y
    hr hy s n hs hR hY (balancedSharedPorts_clean w sign s.basis he.1 he.2.1)
  apply State.extensionality
  · exact fresh.1.trans old.1.symm
  · funext q
    by_cases hq : q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (fresh.2.1.trans old.2.1.symm) q hq
    · exact (fresh.2.2.2.2.2 q hq).trans (old.2.2.2 q hq).symm

private theorem zero_records (p : Program) (h : measurementCount p=0)
    (s : State) (m n : List Bool) : run p m s=run p n s := by
  have a := run_take p m s
  have b := run_take p n s
  rw [h,List.take_zero] at a b
  exact a.symm.trans b

/-- The control polarity wrapper preserves both selected control and phase. -/
theorem double_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (double w sign) m s=
      run ([.X sign]++BalancedInverse.program (balancedSharedPorts w sign)++[.X sign]) m s := by
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
  simp only [double,List.append_assoc]
  rw [run_append,run_take]
  change run (OffsetBorrowedInverse.program w sign++[.X sign]) m
    (run [.X sign] m s)=_
  rw [eu,run_append,run_take,eq]
  rw [run_append,run_take]
  change _=run (BalancedInverse.program L++[.X sign]) m (run [.X sign] m s)
  rw [eu,run_append,run_take]
  exact zero_records [.X sign] (by simp only [measurementCount]) _ _ _

private theorem swap_pair (r y : List Wire) (c : Wire) (hlen : r.length=y.length)
    (hn : (c::r++y).Nodup) (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have ca : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c ca.1 ca.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

/-- Swap is executed first. Whole-State equality then reuses the original
inverse field-cell frame, without assuming a phase oracle. -/
theorem body_eq (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run (body w sign effS) m s=
      run (balancedInverseTranscriptBody (balancedSharedPorts w sign) effS) m s := by
  let L := balancedSharedPorts w sign
  have len := BalancedCleanup.widths L.toLayout (balancedSharedPorts_widths w sign)
  have sw := swap_pair L.r L.y effS (len.2.1.trans len.2.2.1.symm) hsw base
    (centerWord X) (centerWord Y) s m h
  generalize eu : run (swapRegisters effS L.r L.y) m s=u at sw
  let A := if base effS then Y else X
  let B := if base effS then X else Y
  have view : PairFrame L.r L.y base (centerWord A) (centerWord B) u.basis := by
    cases e : base effS <;> simpa only [A,B,e,Bool.false_eq_true,if_true,if_false] using sw.2
  have eq := double_eq w sign hn ho base he A B u m view
  have zero := (swapRegisters_resources effS L.r L.y (len.2.1.trans len.2.2.1.symm) hsw).2.1
  have fresh : run (body w sign effS) m s=run (double w sign) m u := by
    rw [body,run_append,run_take,zero,List.drop_zero,eu]
  have old : run (balancedInverseTranscriptBody L effS) m s=
      run ([.X sign]++BalancedInverse.program L++[.X sign]) m u := by
    simp only [balancedInverseTranscriptBody,List.append_assoc]
    rw [run_append,run_take,zero,List.drop_zero,eu]
    simp only [L,balancedSharedPorts]
  rw [fresh,old]
  exact eq

theorem body_frame (w : Nat → Wire) (sign effS : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (hsw : (effS::(balancedSharedPorts w sign).r++
      (balancedSharedPorts w sign).y).Nodup) (base : BasisState) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y)) (body w sign effS)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (skywalkPayloadUncell (base sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadUncell (base sign) (base effS) (X,Y)).2)) := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have old := balancedInverseTranscriptBody_frame (balancedSharedPorts w sign) effS
    (balancedSharedPorts_widths w sign) (balancedSharedPorts_nodup w sign hn own) hsw base
    (balancedSharedPorts_clean w sign base he.1 he.2.1) X Y
  intro s m h
  rw [body_eq w sign effS hn ho hsw base he X Y s m h]
  exact old s m h

theorem cell_counts (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hsw : (effS::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup) :
    toffoliCount (cell w b g swap sign effS ig is)=1281 ∧
    measurementCount (cell w b g swap sign effS ig is)=1025 := by
  have width := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have sw := swapRegisters_resources effS _ _ (width.2.1.trans width.2.2.1.symm) hsw
  have k := OffsetBorrowedInverse.counts w sign
  have si := transcriptSelectWindow_counts b swap effS is (body w sign effS)
  have so := transcriptSelectWindow_counts b g sign ig (transcriptSelectWindow b swap effS is (body w sign effS))
  change toffoliCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1281 ∧
    measurementCount (transcriptSelectWindow b g sign ig
      (transcriptSelectWindow b swap effS is (body w sign effS)))=1025
  rw [so.1,so.2,si.1,si.2]
  simp only [body,double,toffoliCount_append,measurementCount_append,
    k.1,k.2,sw.1,sw.2.1,width.2.1]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical.kernel_eq
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical.body_frame
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonical.cell_counts
