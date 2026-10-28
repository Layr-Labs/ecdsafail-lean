import ECDSAAdd.Arithmetic.BalancedInverseComposeProof
import ECDSAAdd.Arithmetic.BalancedTranscriptReplay
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField
attribute [local irreducible] centerWord

/-- A fresh measured inverse: undo the recorded swap before the inverse field kernel. -/
def balancedInverseTranscriptBody (L : BalancedCircuit.Layout) (swap : Wire) : Program :=
  swapRegisters swap L.r L.y ++ [.X L.sign] ++ BalancedInverse.program L ++ [.X L.sign]

def balancedInverseTranscriptCell (L : BalancedCircuit.Layout) (b g swap effS : Wire)
    (inactiveG inactiveS : Bool) : Program :=
  transcriptSelectWindow b g L.sign inactiveG
    (transcriptSelectWindow b swap effS inactiveS (balancedInverseTranscriptBody L effS))

private theorem inverse_result_word (B : Bool) (X Y : Fp) :
    encodeWord 256 (BalancedInverse.result B (centerFp X) (centerFp Y)) =
      centerWord (2*X-(if B then -Y else Y)) := by
  unfold BalancedInverse.result BalancedField.signedY
  unfold centerWord
  congr 2
  cases B <;>
    simp [Int.cast_sub,Int.cast_mul,Int.cast_neg,centerFp_cast]

private theorem inverse_sign_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉L.r ∧ L.sign∉L.y := by
  have h := BalancedCircuit.flagAway L hn L.sign (by simp)
  exact ⟨fun hm => h (by simp [hm]),fun hm => h (by simp [hm])⟩

private theorem inverse_work_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r ∧ q∉L.y := by
  have nd := BalancedCircuit.allND L hn
  have h := List.nodup_iff_count.mp nd q
  have hw := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have hc := List.count_pos_iff.mpr hd
  all_goals
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h hw
    omega

private theorem inverse_sign_work (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉BalancedCircuit.work L := by
  have nd : (L.sign::BalancedCircuit.work L).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
      BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact (List.nodup_cons.mp nd).1

private theorem inverse_toggle_view (sign : Wire) (s : State) (m : List Bool) :
    let t := run [.X sign] m s
    t.phase=s.phase ∧ t.basis sign= !s.basis sign ∧
      ∀q,q≠sign → t.basis q=s.basis q := by
  simp only [run]
  refine ⟨True.intro,?_,?_⟩
  · simp only [writeBit,Function.update_self]
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]

/-- The sign-complement wrapper preserves the selected transcript exactly. -/
theorem balancedTranscriptDouble_frame (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (base : BasisState)
    (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      ([.X L.sign]++BalancedInverse.program L++[.X L.sign])
      (PairFrame L.r L.y base (centerWord (2*X+(if base L.sign then -Y else Y)))
        (centerWord Y)) := by
  intro s m h
  generalize eu : run [.X L.sign] m s=u
  have first := inverse_toggle_view L.sign s m
  rw [eu] at first
  have sa := inverse_sign_away L hn
  have uv (r : List Wire) (ha : L.sign∉r) : regValue r u.basis=regValue r s.basis :=
    regValue_congr r u.basis s.basis (fun q hq =>
      first.2.2 q (fun e => ha (e ▸ hq)))
  have us : u.basis L.sign= !base L.sign := by
    rw [first.2.1,h.2.2 L.sign sa.1 sa.2]
  have ur : signedRegValue L.r u.basis=centerFp X := by
    rw [signedRegValue,uv L.r sa.1,h.1,(BalancedCleanup.widths L.toLayout hw).2.1,centerWord_decode]
  have uy : signedRegValue L.y u.basis=centerFp Y := by
    rw [signedRegValue,uv L.y sa.2,h.2.1,(BalancedCleanup.widths L.toLayout hw).2.2.1,centerWord_decode]
  have uc : ∀q∈BalancedCircuit.work L,u.basis q=false := by
    intro q hq
    have away := inverse_work_away L hn q hq
    have ns : q≠L.sign := fun e => inverse_sign_work L hn (e ▸ hq)
    exact (first.2.2 q ns).trans ((h.2.2 q away.1 away.2).trans (hc q hq))
  generalize ev : run (BalancedInverse.program L) m u=v
  have hv := BalancedInverse.program_correct L hw hn (!base L.sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m us ur uy uc
  rw [ev] at hv
  have vv : regValue L.r v.basis=centerWord (2*X+(if base L.sign then -Y else Y)) := by
    rw [hv.2.1,inverse_result_word]
    cases base L.sign <;> simp only [Bool.not_false,Bool.not_true,if_true,if_false,Bool.false_eq_true,sub_eq_add_neg,neg_neg]
  let tail := m.drop (measurementCount (BalancedInverse.program L))
  generalize et : run [.X L.sign] tail v=t
  have last := inverse_toggle_view L.sign v tail
  rw [et] at last
  have actual : run ([.X L.sign]++BalancedInverse.program L++[.X L.sign]) m s=t := by
    simp only [List.append_assoc,run_append,run_take]
    simp only [show measurementCount [.X L.sign]=0 from rfl,List.drop_zero,Nat.zero_add,
      measurementCount_append]
    rw [eu,ev]
    exact et
  rw [actual]
  refine ⟨last.1.trans (hv.1.trans first.1),?_,?_,?_⟩
  · exact (regValue_congr _ _ _ (fun q hq =>
      last.2.2 q (fun e => sa.1 (e ▸ hq)))).trans vv
  · exact (regValue_congr _ _ _ (fun q hq => by
      have qr : q∉L.r := by
        have d := (List.nodup_append'.mp (List.nodup_append'.mp (BalancedCircuit.allND L hn)).2.1).1
        exact fun hr => List.disjoint_left.mp (List.nodup_append'.mp d).2.2 hr hq
      exact (last.2.2 q (fun e => sa.2 (e ▸ hq))).trans (hv.2.2.2 q qr))).trans
      ((uv L.y sa.2).trans h.2.1)
  · intro q qr qy
    by_cases qs : q=L.sign
    · subst q
      rw [last.2.1,hv.2.2.2 L.sign sa.1,us,Bool.not_not]
    · exact (last.2.2 q qs).trans ((hv.2.2.2 q qr).trans
        ((first.2.2 q qs).trans (h.2.2 q qr qy)))

private theorem inverseSwap_frame (r y : List Wire) (c : Wire)
    (hlen : r.length=y.length) (hn : (c::r++y).Nodup)
    (base : BasisState) (A B : Nat) :
    Triple (PairFrame r y base A B) (swapRegisters c r y)
      (PairFrame r y base (if base c then B else A) (if base c then A else B)) := by
  intro s m h
  have v := swapRegisters_correct c r y hlen hn s m
  have hc : c∉r ∧ c∉y := by
    have d := (List.nodup_cons.mp hn).1
    exact ⟨fun hm => d (List.mem_append_left _ hm),fun hm => d (List.mem_append_right _ hm)⟩
  have same := h.2.2 c hc.1 hc.2
  refine ⟨v.1,?_,?_,fun q qr qy => (v.2.1 q qr qy).trans (h.2.2 q qr qy)⟩
  · rw [v.2.2.1,same,h.1,h.2.1]
  · rw [v.2.2.2,same,h.1,h.2.1]

theorem balancedInverseTranscriptBody_frame (L : BalancedCircuit.Layout) (effS : Wire)
    (hw : L.Widths) (hn : L.wires.Nodup) (hs : (effS::L.r++L.y).Nodup)
    (base : BasisState) (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      (balancedInverseTranscriptBody L effS)
      (PairFrame L.r L.y base
        (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).2)) := by
  have len := BalancedCleanup.widths L.toLayout hw
  have sw := inverseSwap_frame L.r L.y effS (len.2.1.trans len.2.2.1.symm) hs
    base (centerWord X) (centerWord Y)
  let A := if base effS then Y else X
  let B := if base effS then X else Y
  have view : PairFrame L.r L.y base (centerWord A) (centerWord B) =
      PairFrame L.r L.y base (if base effS then centerWord Y else centerWord X)
        (if base effS then centerWord X else centerWord Y) := by
    cases e : base effS <;> simp only [A,B,e,Bool.false_eq_true,if_true,if_false]
  rw [←view] at sw
  have dbl := balancedTranscriptDouble_frame L hw hn base hc A B
  have out : PairFrame L.r L.y base
      (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).1)
      (centerWord (skywalkPayloadUncell (base L.sign) (base effS) (X,Y)).2) =
      PairFrame L.r L.y base (centerWord (2*A+(if base L.sign then -B else B)))
        (centerWord B) := by
    cases e : base effS <;> simp only [skywalkPayloadUncell,A,B,e,Bool.false_eq_true,if_true,if_false]
  rw [out]
  simpa only [balancedInverseTranscriptBody,List.append_assoc] using sw.seq dbl
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptDouble_frame
#print axioms ECDSAAdd.Arithmetic.balancedInverseTranscriptBody_frame
