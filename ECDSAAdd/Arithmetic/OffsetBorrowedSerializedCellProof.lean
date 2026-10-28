import ECDSAAdd.Arithmetic.OffsetBorrowedSerializedCellProgram
import ECDSAAdd.Arithmetic.OffsetBorrowedCanonicalReplay
import ECDSAAdd.Arithmetic.OffsetBorrowedInverseCanonicalCell
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedSerialized
open Secp256k1 BalancedField OffsetBorrowedCanonical
attribute [local irreducible] run BalancedCircuit.program BalancedInverse.program
  OffsetBorrowedField.program OffsetBorrowedInverse.program
theorem half_eq (w : Nat → Wire) (sign : Wire) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (he : Env w base)
    (X Y : Fp) (s : State) (m : List Bool)
    (h : PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y) s.basis) :
    run ([.X sign]++OffsetBorrowedField.program w sign++[.X sign]) m s=
      run ([.X sign]++BalancedCircuit.program (balancedSharedPorts w sign)++[.X sign]) m s := by
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
  have eq := OffsetBorrowedCanonical.kernel_eq w sign hn ho (!base sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m m ug ur uy ue
  simp only [List.append_assoc]
  rw [run_append,run_take]
  change run (OffsetBorrowedField.program w sign++[.X sign]) m
    (run [.X sign] m s)=_
  rw [eu,run_append,run_take,eq]
  rw [run_append,run_take]
  change _=run (BalancedCircuit.program L++[.X sign]) m (run [.X sign] m s)
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


private theorem field_frame (divide : Bool) (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkSharedWires w)
    (base : BasisState) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      ([.X sign]++(if divide then OffsetBorrowedField.program w sign
        else OffsetBorrowedInverse.program w sign)++[.X sign])
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then (X+(if base sign then Y else -Y))/2
          else 2*X+(if base sign then -Y else Y))) (centerWord Y)) := by
  have own : sign∉balancedSharedIds.map w := fun h =>
    ho (balancedSharedLayout_mapSubset w balancedSharedIds balancedSharedIds_bound h)
  have nd := balancedSharedPorts_nodup w sign hn own
  have clean := balancedSharedPorts_clean w sign base he.1 he.2.1
  cases divide
  · have old := balancedTranscriptDouble_frame (balancedSharedPorts w sign)
      (balancedSharedPorts_widths w sign) nd base clean X Y
    intro s m h
    simp only [Bool.false_eq_true,if_false]
    rw [← OffsetBorrowedInverseCanonical.double,
      OffsetBorrowedInverseCanonical.double_eq w sign hn ho base he X Y s m h]
    exact old s m h
  · have old := balancedTranscriptHalf_frame (balancedSharedPorts w sign)
      (balancedSharedPorts_widths w sign) nd base clean X Y
    intro s m h
    simp only [if_true]
    rw [half_eq w sign hn ho base he X Y s m h]
    exact old s m h

private theorem field_window (divide : Bool) (w : Nat → Wire) (b src sign : Wire)
    (constant : Bool) (hn : (skywalkSharedWires w).Nodup)
    (ho : sign∉skywalkSharedWires w) (nd : [b,src,sign].Nodup)
    (hb : b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y)
    (hs : src∉(balancedSharedPorts w sign).r ∧ src∉(balancedSharedPorts w sign).y)
    (hf : sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y)
    (base : BasisState) (hz : base sign=false) (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (transcriptSelectWindow b src sign constant ([.X sign]++
        (if divide then OffsetBorrowedField.program w sign else OffsetBorrowedInverse.program w sign)++[.X sign]))
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then (X+(if mixedTranscriptBit base b src constant then Y else -Y))/2
          else 2*X+(if mixedTranscriptBit base b src constant then -Y else Y))) (centerWord Y)) := by
  have f := field_frame divide w sign hn ho (mixedTranscriptBase base b src sign constant)
    (env_write w sign ho base _ he) X Y
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at f
  exact transcriptSelectWindow_pairFrame b src sign constant _ _ nd hb hs hf base hz _ _ _ _ _ f

private theorem swap_window (w : Nat → Wire) (b src sign : Wire) (constant : Bool)
    (nd : [b,src,sign].Nodup)
    (hb : b∉(balancedSharedPorts w sign).r ∧ b∉(balancedSharedPorts w sign).y)
    (hs : src∉(balancedSharedPorts w sign).r ∧ src∉(balancedSharedPorts w sign).y)
    (hf : sign∉(balancedSharedPorts w sign).r ∧ sign∉(balancedSharedPorts w sign).y)
    (sw : (sign::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup)
    (base : BasisState) (hz : base sign=false) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (transcriptSelectWindow b src sign constant
        (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y))
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if mixedTranscriptBit base b src constant then Y else X))
        (centerWord (if mixedTranscriptBit base b src constant then X else Y))) := by
  have len := BalancedCleanup.widths (balancedSharedPorts w sign).toLayout (balancedSharedPorts_widths w sign)
  have f := swap_pair _ _ sign (len.2.1.trans len.2.2.1.symm) sw
    (mixedTranscriptBase base b src sign constant) (centerWord X) (centerWord Y)
  simp only [mixedTranscriptBase,writeBit,Function.update_self] at f
  have f' : Triple
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        (mixedTranscriptBase base b src sign constant) (centerWord X) (centerWord Y))
      (swapRegisters sign (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      (mixedTranscriptBase base b src sign constant)
      (centerWord (if mixedTranscriptBit base b src constant then Y else X))
      (centerWord (if mixedTranscriptBit base b src constant then X else Y))) := by
    cases hbit : mixedTranscriptBit base b src constant <;>
      simpa only [mixedTranscriptBase,writeBit,hbit,if_true,if_false,Bool.false_eq_true] using f
  exact transcriptSelectWindow_pairFrame b src sign constant _ _ nd hb hs hf base hz _ _ _ _ _ f'

theorem cell_frame (divide : Bool) (w : Nat → Wire) (b g swap sign effS : Wire) (ig is : Bool)
    (hn : (skywalkSharedWires w).Nodup)
    (hl : BalancedTranscriptLayout (balancedSharedPorts w sign) b g swap effS)
    (ho : sign∉skywalkSharedWires w) (base : BasisState) (hz : base sign=false)
    (he : Env w base) (X Y : Fp) :
    Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
      (centerWord X) (centerWord Y))
      (if divide then forward w b g swap sign ig is else inverse w b g swap sign ig is)
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y base
        (centerWord (if divide then skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y) else skywalkPayloadUncell
          (mixedTranscriptBit base b g ig) (mixedTranscriptBit base b swap is) (X,Y)).1)
        (centerWord (if divide then skywalkPayloadCell (mixedTranscriptBit base b g ig)
          (mixedTranscriptBit base b swap is) (X,Y) else skywalkPayloadUncell
          (mixedTranscriptBit base b g ig) (mixedTranscriptBit base b swap is) (X,Y)).2)) := by
  have flags := hl.controls
  simp only [balancedSharedPorts,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at flags
  have sg : [b,g,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ss : [b,swap,sign].Nodup := by simp [List.nodup_cons]; tauto
  have ba := hl.outside b (by simp)
  have ga := hl.outside g (by simp)
  have sa := hl.outside swap (by simp)
  have fa := hl.outside sign (by simp [balancedSharedPorts])
  have sw : (sign::(balancedSharedPorts w sign).r++(balancedSharedPorts w sign).y).Nodup :=
    List.nodup_cons.mpr ⟨by
      intro h
      rcases List.mem_append.mp h with h|h
      · exact fa.1 h
      · exact fa.2 h,
      balancedSharedLayout_pairND w sign hn⟩
  cases divide
  · let A := if mixedTranscriptBit base b swap is then Y else X
    let B := if mixedTranscriptBit base b swap is then X else Y
    have first := swap_window w b swap sign is ss ba sa fa sw base hz X Y
    have last := field_window false w b g sign ig hn ho sg ba ga fa base hz he A B
    have result := first.seq last
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [inverse,skywalkPayloadUncell,A,B,hswap,if_true,if_false,Bool.false_eq_true] using result
  · let H := (X+(if mixedTranscriptBit base b g ig then Y else -Y))/2
    have first := field_window true w b g sign ig hn ho sg ba ga fa base hz he X Y
    have last := swap_window w b swap sign is ss ba sa fa sw base hz H Y
    have result := first.seq last
    cases hswap : mixedTranscriptBit base b swap is <;>
      simpa only [forward,skywalkPayloadCell,H,hswap,if_true,if_false,Bool.false_eq_true] using result
end ECDSAAdd.Arithmetic.OffsetBorrowedSerialized
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSerialized.half_eq
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSerialized.cell_frame
