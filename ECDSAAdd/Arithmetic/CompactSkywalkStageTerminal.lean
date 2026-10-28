import ECDSAAdd.Arithmetic.CompactSkywalkStageVirtual

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace ECDSAAdd.Arithmetic

/-- Clean physical tails and nonnegative retained rails make reconstruction
literally the original physical basis, for either terminal orientation. -/
theorem compactSkywalkStage_nonnegative_identity (w : Nat → Wire) (i : Nat) (hi : i ≤ 512)
    (hn : (skywalkPoolWires w).Nodup) (r : SkywalkRails.State) (s : BasisState)
    (hin : CompactSkywalkStage w r i s)
    (ha : 0 ≤ (SkywalkTrace.next^[i] r).a) (hb : 0 ≤ (SkywalkTrace.next^[i] r).b) :
    compactSkywalkStageVirtual w i s = s := by
  have values := compactSkywalkStage_virtual_values w i hi hn s
  have va := values.1.symm.trans hin.1.1
  have vb := values.2.symm.trans hin.1.2.1
  have sa := signedRegValue_sign (compactSkywalkSignPoolA w i).low
    (compactSkywalkSignPoolA w i).sign s
  have sb := signedRegValue_sign (compactSkywalkSignPoolB w i).low
    (compactSkywalkSignPoolB w i).sign s
  change s (compactSkywalkSignPoolA w i).sign =
    SkywalkRails.neg (signedRegValue (compactSkywalkSignPoolA w i).retained s) at sa
  change s (compactSkywalkSignPoolB w i).sign =
    SkywalkRails.neg (signedRegValue (compactSkywalkSignPoolB w i).retained s) at sb
  rw [va] at sa
  rw [vb] at sb
  have za : s (compactSkywalkSignPoolA w i).sign = false := by
    simpa only [SkywalkRails.neg,not_lt.mpr ha,decide_false] using sa
  have zb : s (compactSkywalkSignPoolB w i).sign = false := by
    simpa only [SkywalkRails.neg,not_lt.mpr hb,decide_false] using sb
  funext q
  by_cases qa : q ∈ (compactSkywalkSignPoolA w i).released
  · simp only [compactSkywalkStageVirtual,if_pos qa,za,hin.2.1 q qa]
  by_cases qb : q ∈ (compactSkywalkSignPoolB w i).released
  · simp only [compactSkywalkStageVirtual,if_neg qa,if_pos qb,zb,hin.2.2 q qb]
  · exact compactSkywalkStage_virtual_outside w i s q qa qb

/-- Exact termination has unsigned magnitudes (0,1); its orientation G is
arbitrary, hence the signed rails may be (1,0) or (0,1). Both are nonnegative. -/
theorem compactSkywalkStage_terminal_nonnegative (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) :
    0 ≤ (SkywalkTrace.next^[512] (SkywalkRails.encode false false (x:Int) (p:Int))).a ∧
    0 ≤ (SkywalkTrace.next^[512] (SkywalkRails.encode false false (x:Int) (p:Int))).b := by
  have ht := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpo hp (hx.trans hp) hc
  obtain ⟨G,S,he⟩ := SkywalkTrace.iter_encoded 512 false false (SkywalkNat.init x p) hp0 hpo
  norm_num only at ht
  simp only [SkywalkNat.init] at he ht
  rw [ht.1,ht.2] at he
  rw [he]
  cases G <;> cases S <;> norm_num [SkywalkRails.encode,SkywalkRails.signed]

/-- The unchanged old terminal caller may consume the physical compact state
at512 directly. No actual high-word expansion is needed. -/
theorem compactSkywalkStage_terminal (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (x p : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2 = 1) (hp : p < 2^256)
    (hx : x < p) (hc : x.Coprime p) (s : BasisState)
    (hin : CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s) :
    compactSkywalkStageVirtual w 512 s = s ∧
    SkywalkIntegerStage w (SkywalkRails.encode false false (x:Int) (p:Int)) 512 s := by
  have pos := compactSkywalkStage_terminal_nonnegative x p hp0 hx0 hpo hp hx hc
  have he := compactSkywalkStage_nonnegative_identity w 512 (by decide) hn _ s hin pos.1 pos.2
  exact ⟨he,by simpa only [he] using hin.1⟩

end ECDSAAdd.Arithmetic
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_terminal_nonnegative
#print axioms ECDSAAdd.Arithmetic.compactSkywalkStage_terminal
