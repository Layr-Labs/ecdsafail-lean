import ECDSAAdd.Arithmetic.NativeFirstDirectNativeBridge
import ECDSAAdd.Arithmetic.NativeFirstDirectSeedInput
import ECDSAAdd.Arithmetic.NativeFirstDirectTickUnique
import ECDSAAdd.Arithmetic.NativeFirstDirectSupport

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 1024
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.NativeFirstDirect
attribute [local irreducible] run forward literalSkywalkSeed compactSkywalkTick wires

/-- The actual incumbent prefix, with its original seed and native tick. -/
def reference (w : Nat → Wire) : Program :=
  literalSkywalkSeed (literalSkywalkPoolSeed w) p++compactSkywalkTick w 0

private theorem a_inside (L : SkywalkIntegerLayout) : ∀q∈L.a,q∈L.wires := by
  intro q hq
  simp only [SkywalkIntegerLayout.a,List.mem_cons] at hq
  simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append]
  tauto
private theorem b_inside (L : SkywalkIntegerLayout) : ∀q∈L.b,q∈L.wires := by
  intro q hq
  simp only [SkywalkIntegerLayout.b,List.mem_cons] at hq
  simp only [SkywalkIntegerLayout.wires,List.mem_cons,List.mem_append]
  tauto
private theorem carry_inside (L : SkywalkIntegerLayout) : ∀q∈L.carry,q∈L.wires := by
  intro q hq
  simp [SkywalkIntegerLayout.wires,hq]

private theorem first_a (w : Nat → Wire) :
    (compactSkywalkTickLayout w 0).a=wireBlock w 0 258 := by
  simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_a w 0 (by omega)
private theorem first_b (w : Nat → Wire) :
    (compactSkywalkTickLayout w 0).b=wireBlock w 770 258 := by
  simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_b w 0 (by omega)
private theorem first_half (w : Nat → Wire) :
    (compactSkywalkTickLayout w 0).half=wireBlock w 1 258 := by
  simpa only [compactSkywalkTickPreWidth,narrowSkywalkRouteWidth] using compactSkywalkTick_half w 0 (by omega)

private theorem retained_full (r : List Wire) (h : r.length=258) :
    (compactSkywalkSignWord r 258).retained=r := by
  rw [compactSkywalkSignWord_retained r 258 (by omega) (by omega)]
  simpa only [h] using List.take_length (l := r)
private theorem a_retained (w : Nat → Wire) :
    (compactSkywalkTickARelease w 0).retained=(compactSkywalkTickLayout w 0).half := by
  unfold compactSkywalkTickARelease
  change (compactSkywalkSignWord _ 258).retained=_
  exact retained_full _ (by rw [first_half,wireBlock_length])
private theorem b_retained (w : Nat → Wire) :
    (compactSkywalkTickBRelease w 0).retained=(compactSkywalkTickLayout w 0).b := by
  unfold compactSkywalkTickBRelease
  change (compactSkywalkSignWord _ 258).retained=_
  exact retained_full _ (by rw [first_b,wireBlock_length])

private theorem sites_inside (w : Nat → Wire) :
    prefixSites w ⊆ (compactSkywalkTickLayout w 0).wires := by
  intro q hq
  simp only [prefixSites,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with ((hq|hq)|hq)|(hq|hq)
  · apply a_inside
    rw [first_a]
    exact block_subset w 0 257 258 (by omega) q hq
  · apply b_inside
    rw [first_b]
    exact hq
  · apply carry_inside
    exact block_subset w 1540 256 257 (by omega) q hq
  · subst q
    simp [SkywalkIntegerLayout.wires,compactSkywalkTickLayout,skywalkPoolPreviousId]
  · subst q
    simp [SkywalkIntegerLayout.wires,compactSkywalkTickLayout,skywalkPoolPreviousId]

private theorem output_unique (w : Nat → Wire) (x : Nat) (s t : State)
    (phase : s.phase=t.phase)
    (a : CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int)) (x : Int) false s.basis)
    (b : CompactSkywalkTickOutput w 0 ((x : Int)+(p : Int)) (x : Int) false t.basis)
    (outside : ∀q,q∉(compactSkywalkTickLayout w 0).wires → s.basis q=t.basis q) : s=t := by
  simp only [CompactSkywalkTickOutput,a_retained,b_retained] at a b
  exact native_output_state_unique _ s t phase (a.1.trans b.1.symm)
    (a.2.1.trans b.2.1.symm) (a.2.2.1.trans b.2.2.1.symm)
    (a.2.2.2.1.trans b.2.2.2.1.symm) (a.2.2.2.2.1.trans b.2.2.2.2.1.symm)
    (a.2.2.2.2.2.1.trans b.2.2.2.2.2.1.symm) outside

/-- Equality of complete states, with independent old and new measurement tapes. -/
theorem forward_reference_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx : x<p) (s : State) (mNew mOld : List Bool)
    (hin : LiteralSkywalkSeedValues (literalSkywalkPoolSeed w) 0 x s.basis)
    (ext : s.basis (w 258)=false) :
    run (forward w) mNew s=run (reference w) mOld s := by
  have hp : p<2^256 := by norm_num [p]
  have seed := literalSkywalkSeed_spec (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s mOld hin
  have input := seed_first_input w hn x hx s mOld hin ext
  generalize he : run (literalSkywalkSeed (literalSkywalkPoolSeed w) p) mOld s=u at seed input
  have oddp : (p : Int)%2=1 := by norm_num [p]
  have fitX : (x : Int)<(2^257 : Int) := by exact_mod_cast (show x<2^257 from by omega)
  have fitSum : (x : Int)+(p : Int)<(2^257 : Int) := by omega
  have range : 0≤(SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).1 ∧
      (SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).1<(2^257 : Int) ∧
      0≤(SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).2 ∧
      (SkywalkRails.route ((x : Int)+(p : Int)) (x : Int)).2<(2^257 : Int) := by
    unfold SkywalkRails.route
    split_ifs <;> omega
  have old := compactSkywalkTickOutput_spec w 0 (by omega) hn
    ((x : Int)+(p : Int)) (x : Int) false (by omega)
    (by change -(2^257 : Int)≤_; omega) (by change _<(2^257 : Int); omega)
    (by change -(2^257 : Int)≤_; omega) (by change _<(2^257 : Int); omega)
    u (mOld.drop 257) input
  generalize ho : run (compactSkywalkTick w 0) (mOld.drop 257) u=v at old
  have new := forward_native_output w hn x hx s mNew hin ext
  generalize hnw : run (forward w) mNew s=z at new ⊢
  have actual : run (reference w) mOld s=v := by
    rw [reference,run_append,run_take,(literalSkywalkPoolSeed_counts w p).2.1,he,ho]
  rw [actual]
  apply output_unique w x z v (new.1.trans (old.1.trans seed.1).symm) new.2 old.2
  intro q hq
  have ns : z.basis q=s.basis q := by
    have frame := run_preserves_outside (forward w) mNew s q (fun h =>
      hq (sites_inside w (List.mem_toFinset.mp ((prefix_support w).1 h))))
    rw [hnw] at frame
    exact frame
  have ts := compactSkywalkTickOutput_frame w 0 (by omega) hn u (mOld.drop 257) q hq
  rw [ho] at ts
  have qa : q∉(literalSkywalkPoolSeed w).a := by
    intro h
    apply hq
    apply a_inside
    rw [first_a]
    exact h
  have ss := literalSkywalkSeed_preserves_outsideA (literalSkywalkPoolSeed w) 258 p x
    (literalSkywalkPoolSeed_widths w) (literalSkywalkPoolSeed_valid w hn)
    (by omega) hp (hx.trans hp) s mOld hin q qa
  rw [he] at ss
  exact ns.trans (ts.trans ss).symm

end ECDSAAdd.Arithmetic.NativeFirstDirect
#print axioms ECDSAAdd.Arithmetic.NativeFirstDirect.forward_reference_eq
