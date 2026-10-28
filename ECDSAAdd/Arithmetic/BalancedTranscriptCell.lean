import ECDSAAdd.Arithmetic.BalancedFieldCircuitProof
import ECDSAAdd.Arithmetic.BalancedFieldSupport
import ECDSAAdd.Arithmetic.MixedTranscriptReplay
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic
open Secp256k1 BalancedField
attribute [local irreducible] centerWord

/-- Balanced words remain in this ABI throughout replay. -/
def balancedTranscriptBody (L : BalancedCircuit.Layout) (swap : Wire) : Program :=
  [.X L.sign] ++ BalancedCircuit.program L ++ [.X L.sign] ++
    swapRegisters swap L.r L.y

def balancedTranscriptCell (L : BalancedCircuit.Layout) (b g swap effS : Wire)
    (inactiveG inactiveS : Bool) : Program :=
  transcriptSelectWindow b g L.sign inactiveG
    (transcriptSelectWindow b swap effS inactiveS (balancedTranscriptBody L effS))

structure BalancedTranscriptLayout (L : BalancedCircuit.Layout)
    (b g swap effS : Wire) : Prop where
  widths : L.Widths
  kernel : L.wires.Nodup
  controls : [b,g,swap,L.sign,effS].Nodup
  outside : ∀q∈[b,g,swap,L.sign,effS],q∉L.r ∧ q∉L.y
  scratch : L.sign∉BalancedCircuit.work L ∧ effS∉BalancedCircuit.work L
  swapND : (effS::L.r++L.y).Nodup

private theorem balanced_sign_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉L.r ∧ L.sign∉L.y := by
  have h := BalancedCircuit.flagAway L hn L.sign (by simp)
  exact ⟨fun hm => h (by simp [hm]),fun hm => h (by simp [hm])⟩

private theorem balanced_work_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈BalancedCircuit.work L) : q∉L.r ∧ q∉L.y := by
  have nd := BalancedCircuit.allND L hn
  have h := List.nodup_iff_count.mp nd q
  have hw := List.count_pos_iff.mpr hq
  constructor <;> intro hd <;> have hc := List.count_pos_iff.mpr hd
  all_goals
    simp only [BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h hw
    omega

private theorem balanced_sign_work (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.sign∉BalancedCircuit.work L := by
  have nd : (L.sign::BalancedCircuit.work L).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
      BalancedCircuit.work,List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  exact (List.nodup_cons.mp nd).1

private theorem balanced_toggle_view (sign : Wire) (s : State) (m : List Bool) :
    let t := run [.X sign] m s
    t.phase=s.phase ∧ t.basis sign= !s.basis sign ∧
      ∀q,q≠sign → t.basis q=s.basis q := by
  simp only [run]
  refine ⟨True.intro,?_,?_⟩
  · simp only [writeBit,Function.update_self]
  · intro q hq
    simp only [writeBit,Function.update_of_ne hq]

/-- The sign-complement wrapper preserves the selected transcript exactly. -/
theorem balancedTranscriptHalf_frame (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (base : BasisState)
    (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      ([.X L.sign]++BalancedCircuit.program L++[.X L.sign])
      (PairFrame L.r L.y base (centerWord ((X+(if base L.sign then Y else -Y))/2))
        (centerWord Y)) := by
  intro s m h
  generalize eu : run [.X L.sign] m s=u
  have first := balanced_toggle_view L.sign s m
  rw [eu] at first
  have sa := balanced_sign_away L hn
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
    have away := balanced_work_away L hn q hq
    have ns : q≠L.sign := fun e => balanced_sign_work L hn (e ▸ hq)
    exact (first.2.2 q ns).trans ((h.2.2 q away.1 away.2).trans (hc q hq))
  generalize ev : run (BalancedCircuit.program L) m u=v
  have hv := BalancedCircuit.program_correct L hw hn (!base L.sign) (centerFp X) (centerFp Y)
    (centerFp_bounds X) (centerFp_bounds Y) u m us ur uy uc
  rw [ev] at hv
  have vv : regValue L.r v.basis=centerWord ((X+(if base L.sign then Y else -Y))/2) := by
    rw [hv.2.1,centeredFp_signedHalf]
    cases base L.sign <;> simp only [centerWord,Bool.not_false,Bool.not_true,if_true,if_false,Bool.false_eq_true]
  let tail := m.drop (measurementCount (BalancedCircuit.program L))
  generalize et : run [.X L.sign] tail v=t
  have last := balanced_toggle_view L.sign v tail
  rw [et] at last
  have actual : run ([.X L.sign]++BalancedCircuit.program L++[.X L.sign]) m s=t := by
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

private theorem balancedSwap_frame (r y : List Wire) (c : Wire)
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

theorem balancedTranscriptBody_frame (L : BalancedCircuit.Layout) (effS : Wire)
    (hw : L.Widths) (hn : L.wires.Nodup) (hs : (effS::L.r++L.y).Nodup)
    (base : BasisState) (hc : ∀q∈BalancedCircuit.work L,base q=false) (X Y : Fp) :
    Triple (PairFrame L.r L.y base (centerWord X) (centerWord Y))
      (balancedTranscriptBody L effS)
      (PairFrame L.r L.y base
        (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).1)
        (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).2)) := by
  have hh := balancedTranscriptHalf_frame L hw hn base hc X Y
  have len := BalancedCleanup.widths L.toLayout hw
  let T := (X+(if base L.sign then Y else -Y))/2
  have sw := balancedSwap_frame L.r L.y effS (len.2.1.trans len.2.2.1.symm) hs
    base (centerWord T) (centerWord Y)
  have view : PairFrame L.r L.y base
      (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).1)
      (centerWord (skywalkPayloadCell (base L.sign) (base effS) (X,Y)).2)=
      PairFrame L.r L.y base (if base effS then centerWord Y else centerWord T)
        (if base effS then centerWord T else centerWord Y) := by
    cases e : base effS <;>
      simp only [skywalkPayloadCell,e,Bool.false_eq_true,if_true,if_false,T]
  rw [←view] at sw
  simpa only [balancedTranscriptBody] using hh.seq sw
end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptHalf_frame
#print axioms ECDSAAdd.Arithmetic.balancedTranscriptBody_frame
