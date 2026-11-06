import ECDSAAdd.Submission.Entrant.MainPart07

-- Adapted public peer module: TerminalFiveDomain
section

namespace ECDSAAdd.Entrant.TerminalFiveDomain
open ECDSAAdd Arithmetic MappedCompressed Secp256k1 History5
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

def pairs : List (Nat × Nat) := [(0, 1), (1, 1), (1, 3), (1, 5), (1, 7), (1, 9), (1, 11), (1, 13), (1, 15), (1, 17), (1, 19), (1, 21), (1, 23), (1, 25), (1, 27), (1, 29), (1, 31), (2, 1), (2, 3), (2, 5), (2, 7), (2, 9), (2, 11), (2, 13), (2, 15), (3, 1), (3, 5), (3, 7), (3, 11), (3, 13), (4, 1), (4, 3), (4, 5), (4, 7), (5, 1), (5, 3), (5, 7), (6, 1), (6, 5), (6, 7), (7, 1), (7, 3), (7, 5), (8, 1), (8, 3), (9, 1), (10, 1), (10, 3), (11, 1), (11, 3), (12, 1), (13, 1), (13, 3), (14, 1), (14, 3), (15, 1), (16, 1), (17, 1), (18, 1), (19, 1), (20, 1), (21, 1), (22, 1), (23, 1), (24, 1), (25, 1), (26, 1), (27, 1), (28, 1), (29, 1), (30, 1), (31, 1)]

theorem width506 (x : Nat) (hx0 : 0<x) (hx : x<p) :
    let z:=SkywalkNat.step^[506] (SkywalkNat.init x p)
    ∃ a b : Nat, a+b=6 ∧ z.u<2^a ∧ z.v<2^b := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  obtain ⟨a,b,h,ha,hb⟩:=MorningWidth.iter_budget 506 256 256 (SkywalkNat.init x p)
    hp0 hpo cop (hx.trans hp) hp (by omega)
  exact ⟨a,b,by omega,ha,hb⟩

theorem pairs_of (z : SkywalkNat.State) (hs : z.u+z.v≤32) (h0 : 0<z.v) (h1 : z.v%2=1)
    (hg : z.u.gcd z.v=1) (hw : ∃ a b : Nat,a+b=6 ∧ z.u<2^a ∧ z.v<2^b) :
    (z.u,z.v)∈pairs := by
  obtain ⟨u,v⟩ := z
  simp only at hs h0 h1 hg hw ⊢
  obtain ⟨a,b,he,ha,hb⟩:=hw
  have hw := Forward11Width.widthPair_of u v 6 a b he ha hb
  clear a b he ha hb
  have hv : v=1 ∨ v=3 ∨ v=5 ∨ v=7 ∨ v=9 ∨ v=11 ∨ v=13 ∨ v=15 ∨ v=17 ∨ v=19 ∨ v=21 ∨ v=23 ∨ v=25 ∨ v=27 ∨ v=29 ∨ v=31 := by omega
  have hu : u≤32-v := by omega
  clear hs h0 h1
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num at hu <;>
    interval_cases u <;> revert hg hw <;> decide +kernel

def sites : List Wire := [521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 1550, 1551, 1552, 1553, 1554, 1556, 1557, 1558, 1559, 1560]

def pre (g s : Bool) (u v : Nat) : BasisState := fun q =>
  if q=521 then g
  else if q=522 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).a / 1 % 2 = 1)
  else if q=523 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).a / 2 % 2 = 1)
  else if q=524 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).a / 4 % 2 = 1)
  else if q=525 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).a / 8 % 2 = 1)
  else if q=526 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).a / 16 % 2 = 1)
  else if q=527 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).a / 32 % 2 = 1)
  else if q=528 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).a < 0)
  else if q=786 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).b / 1 % 2 = 1)
  else if q=787 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).b / 2 % 2 = 1)
  else if q=788 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).b / 4 % 2 = 1)
  else if q=789 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).b / 8 % 2 = 1)
  else if q=790 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).b / 16 % 2 = 1)
  else if q=791 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).b / 32 % 2 = 1)
  else if q=792 then decide ((SkywalkRails.encode g s (u:Int) (v:Int)).b < 0)
  else false

theorem signed7_cases (a b c d e f g : Wire) (s : BasisState) (v : Int)
    (h : signedRegValue [a,b,c,d,e,f,g] s = v) :
    s a = decide (v % 2 = 1) ∧ s b = decide (v / 2 % 2 = 1) ∧
    s c = decide (v / 4 % 2 = 1) ∧ s d = decide (v / 8 % 2 = 1) ∧
    s e = decide (v / 16 % 2 = 1) ∧ s f = decide (v / 32 % 2 = 1) ∧ s g = decide (v < 0) := by
  unfold signedRegValue signedDecode at h
  simp only [regValue,List.length] at h
  cases ha : s a <;> cases hb : s b <;> cases hc : s c <;> cases hd : s d <;>
    cases he : s e <;> cases hf : s f <;> cases hg : s g <;>
    simp [ha,hb,hc,hd,he,hf,hg] at h <;> subst h <;> decide

theorem retainedA506 : (W.compactSkywalkSignPoolA base 506).retained =
    [522,523,524,525,526,527,528] := by decide +kernel

theorem retainedB506 : (W.compactSkywalkSignPoolB base 506).retained =
    [786,787,788,789,790,791,792] := by decide +kernel

attribute [local irreducible] run W.compactSkywalkStageVirtual SkywalkTrace.next Nat.iterate
  W.compactSkywalkTick History5.encodePrefix

theorem raw506 (x : Nat) (hx0 : 0<x) (hx : x<p) (raw : State)
    (hraw : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 506 raw.basis) :
    ∃ g s : Bool, ∃ uv∈pairs, ∀ q∈sites, raw.basis q = pre g s uv.1 uv.2 q := by
  have hp0 : 0<p := by norm_num [p]
  have hpo : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have cop := (StackOB5.prime_facts x hx0 hx).2.2.2
  have fields := (W.compactSkywalkStage_fields_iff base _ 506 (by omega) base_pool_nodup raw.basis).mp hraw
  obtain ⟨readA,readB,prev,-,future,carry,-,cleanA,cleanB⟩ := fields
  obtain ⟨G,S,encoded⟩ := SkywalkTrace.iter_encoded 506 false false (SkywalkNat.init x p) hp0 hpo
  have sum := W.iter_sum_width x p 506 hp0 hx0 hpo hp hx cop (by omega)
  have valid := SkywalkNat.iter_valid 506 (SkywalkNat.init x p) hp0 hpo
  have width := width506 x hx0 hx
  change (SkywalkNat.step^[506] (SkywalkNat.init x p)).u+
    (SkywalkNat.step^[506] (SkywalkNat.init x p)).v ≤ 32 at sum
  change SkywalkTrace.next^[506] (SkywalkRails.encode false false (x:Int) (p:Int)) =
    SkywalkRails.encode G S ((SkywalkNat.step^[506] (SkywalkNat.init x p)).u:Int)
      ((SkywalkNat.step^[506] (SkywalkNat.init x p)).v:Int) at encoded
  generalize SkywalkNat.step^[506] (SkywalkNat.init x p) = z at encoded sum valid width
  have mem := pairs_of z sum valid.1 valid.2.1 (valid.2.2.trans cop) width
  rw [encoded,retainedA506] at readA
  rw [encoded,retainedB506] at readB
  rw [encoded] at prev
  have bA := signed7_cases _ _ _ _ _ _ _ raw.basis _ readA
  have bB := signed7_cases _ _ _ _ _ _ _ raw.basis _ readB
  have prev' : raw.basis 521=G := by
    have h : skywalkPoolPreviousId 506=505 := rfl
    rw [h] at prev
    cases G <;> simpa [SkywalkRails.encode] using prev
  have c529 : raw.basis 529=false := cleanA _ (by decide +kernel)
  have c530 : raw.basis 530=false := cleanA _ (by decide +kernel)
  have c793 : raw.basis 793=false := cleanB _ (by decide +kernel)
  have c794 : raw.basis 794=false := cleanB _ (by decide +kernel)
  have c795 : raw.basis 795=false := cleanB _ (by decide +kernel)
  have c796 : raw.basis 796=false := cleanB _ (by decide +kernel)
  have c797 : raw.basis 797=false := cleanB _ (by decide +kernel)
  have c798 : raw.basis 798=false := cleanB _ (by decide +kernel)
  have c799 : raw.basis 799=false := cleanB _ (by decide +kernel)
  have c800 : raw.basis 800=false := cleanB _ (by decide +kernel)
  have c801 : raw.basis 801=false := cleanB _ (by decide +kernel)
  have c802 : raw.basis 802=false := cleanB _ (by decide +kernel)
  have c803 : raw.basis 803=false := cleanB _ (by decide +kernel)
  have c804 : raw.basis 804=false := cleanB _ (by decide +kernel)
  have c805 : raw.basis 805=false := cleanB _ (by decide +kernel)
  have c1550 := (future 506 (by omega) (by omega)).2
  have c1551 := (future 507 (by omega) (by omega)).2
  have c1552 := (future 508 (by omega) (by omega)).2
  have c1553 := (future 509 (by omega) (by omega)).2
  have c1554 := (future 510 (by omega) (by omega)).2
  have c1556 : raw.basis 1556=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have c1557 : raw.basis 1557=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have c1558 : raw.basis 1558=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have c1559 : raw.basis 1559=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  have c1560 : raw.basis 1560=false := (regValue_zero _ _).mp carry _ (by decide +kernel)
  refine ⟨G,S,_,mem,?_⟩
  intro q hq
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [pre] using prev'
  · simpa [pre] using bA.1
  · simpa [pre] using bA.2.1
  · simpa [pre] using bA.2.2.1
  · simpa [pre] using bA.2.2.2.1
  · simpa [pre] using bA.2.2.2.2.1
  · simpa [pre] using bA.2.2.2.2.2.1
  · simpa [pre] using bA.2.2.2.2.2.2
  · simpa [pre] using c529
  · simpa [pre] using c530
  · simpa [pre] using bB.1
  · simpa [pre] using bB.2.1
  · simpa [pre] using bB.2.2.1
  · simpa [pre] using bB.2.2.2.1
  · simpa [pre] using bB.2.2.2.2.1
  · simpa [pre] using bB.2.2.2.2.2.1
  · simpa [pre] using bB.2.2.2.2.2.2
  · simpa [pre] using c793
  · simpa [pre] using c794
  · simpa [pre] using c795
  · simpa [pre] using c796
  · simpa [pre] using c797
  · simpa [pre] using c798
  · simpa [pre] using c799
  · simpa [pre] using c800
  · simpa [pre] using c801
  · simpa [pre] using c802
  · simpa [pre] using c803
  · simpa [pre] using c804
  · simpa [pre] using c805
  · simpa [pre] using c1550
  · simpa [pre] using c1551
  · simpa [pre] using c1552
  · simpa [pre] using c1553
  · simpa [pre] using c1554
  · simpa [pre] using c1556
  · simpa [pre] using c1557
  · simpa [pre] using c1558
  · simpa [pre] using c1559
  · simpa [pre] using c1560

attribute [local irreducible] wires


theorem history_away (n : Nat) (hn : n≤505) (i : Fin 10) (q : Wire) (hq : q∈sites) :
    historyMap base (n-5) i ≠ q := by
  have hi : i.val/2≤4 := by omega
  change ((if i.val%2=0 then n-5+i.val/2 else 1028+(n-5)+i.val/2)+16 : Nat)≠(q : Nat)
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false] at hq
  split_ifs <;> rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega


theorem prefix_away_old (n : Nat) (hn : n≤506) :
    Disjoint (wires (History5.encodePrefix base n)) sites.toFinset := by
  induction n with
  | zero => simp [History5.encodePrefix,wires]
  | succ n ih =>
    have prior := ih (by omega)
    have current : Disjoint (wires (History5.packAfter base n)) sites.toFinset := by
      cases due : History5.packDue n
      · simp [History5.packAfter,due,wires]
      · apply Finset.disjoint_left.mpr
        intro q hq hs
        simp only [History5.packAfter,due,if_true] at hq
        obtain ⟨i,eq⟩ := History5.history_gate_mem base (n-5) _ (Or.inl rfl) q hq
        exact history_away n (by omega) i q (List.mem_toFinset.mp hs) eq.symm
    simpa only [History5.encodePrefix,wires_append,Finset.disjoint_union_left] using And.intro prior current


theorem prefix_away (isA : Bool) :
    Disjoint (wires (Rolling1588.Integer.encodePrefix base isA 506)) sites.toFinset := by
  rw [Rolling1588.Integer.prefix_support_eq]
  exact prefix_away_old 506 (by omega)


theorem stage506 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (a : State)
    (stage : Rolling1588.Integer.Stage base isA x p 506 a.basis) :
    ∃ g s : Bool, ∃ uv∈pairs, ∀ q∈sites, a.basis q = pre g s uv.1 uv.2 q := by
  obtain ⟨raw,hraw,hbits⟩ := stage
  obtain ⟨g,s,uv,mem,reads⟩ := raw506 x hx0 hx raw hraw
  refine ⟨g,s,uv,mem,?_⟩
  intro q hq
  rw [hbits]
  have kept : (run (Rolling1588.Integer.encodePrefix base isA 506) [] raw).basis q=raw.basis q := by
    apply run_preserves_outside
    intro used
    exact Finset.disjoint_left.mp (prefix_away isA) used (List.mem_toFinset.mpr hq)
  exact kept.trans (reads q hq)

end ECDSAAdd.Entrant.TerminalFiveDomain

end

-- Adapted public peer module: TerminalFivePermutation
section

namespace ECDSAAdd.Entrant.TerminalFivePermutation
open ECDSAAdd
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def port (q : Wire) : Wire :=
 if q<40 then TerminalFiveDomain.sites[q]!
 else if q=521 then 0
 else if q=522 then 1
 else if q=523 then 2
 else if q=524 then 3
 else if q=525 then 4
 else if q=526 then 5
 else if q=527 then 6
 else if q=528 then 7
 else if q=529 then 8
 else if q=530 then 9
 else if q=786 then 10
 else if q=787 then 11
 else if q=788 then 12
 else if q=789 then 13
 else if q=790 then 14
 else if q=791 then 15
 else if q=792 then 16
 else if q=793 then 17
 else if q=794 then 18
 else if q=795 then 19
 else if q=796 then 20
 else if q=797 then 21
 else if q=798 then 22
 else if q=799 then 23
 else if q=800 then 24
 else if q=801 then 25
 else if q=802 then 26
 else if q=803 then 27
 else if q=804 then 28
 else if q=805 then 29
 else if q=1550 then 30
 else if q=1551 then 31
 else if q=1552 then 32
 else if q=1553 then 33
 else if q=1554 then 34
 else if q=1556 then 35
 else if q=1557 then 36
 else if q=1558 then 37
 else if q=1559 then 38
 else if q=1560 then 39
 else q

theorem twice (q : Wire) : port (port q)=q := by
  by_cases low : q<40
  · change q<40 at low
    interval_cases q <;> decide +kernel
  by_cases e0 : q=521
  · subst q; decide +kernel
  by_cases e1 : q=522
  · subst q; decide +kernel
  by_cases e2 : q=523
  · subst q; decide +kernel
  by_cases e3 : q=524
  · subst q; decide +kernel
  by_cases e4 : q=525
  · subst q; decide +kernel
  by_cases e5 : q=526
  · subst q; decide +kernel
  by_cases e6 : q=527
  · subst q; decide +kernel
  by_cases e7 : q=528
  · subst q; decide +kernel
  by_cases e8 : q=529
  · subst q; decide +kernel
  by_cases e9 : q=530
  · subst q; decide +kernel
  by_cases e10 : q=786
  · subst q; decide +kernel
  by_cases e11 : q=787
  · subst q; decide +kernel
  by_cases e12 : q=788
  · subst q; decide +kernel
  by_cases e13 : q=789
  · subst q; decide +kernel
  by_cases e14 : q=790
  · subst q; decide +kernel
  by_cases e15 : q=791
  · subst q; decide +kernel
  by_cases e16 : q=792
  · subst q; decide +kernel
  by_cases e17 : q=793
  · subst q; decide +kernel
  by_cases e18 : q=794
  · subst q; decide +kernel
  by_cases e19 : q=795
  · subst q; decide +kernel
  by_cases e20 : q=796
  · subst q; decide +kernel
  by_cases e21 : q=797
  · subst q; decide +kernel
  by_cases e22 : q=798
  · subst q; decide +kernel
  by_cases e23 : q=799
  · subst q; decide +kernel
  by_cases e24 : q=800
  · subst q; decide +kernel
  by_cases e25 : q=801
  · subst q; decide +kernel
  by_cases e26 : q=802
  · subst q; decide +kernel
  by_cases e27 : q=803
  · subst q; decide +kernel
  by_cases e28 : q=804
  · subst q; decide +kernel
  by_cases e29 : q=805
  · subst q; decide +kernel
  by_cases e30 : q=1550
  · subst q; decide +kernel
  by_cases e31 : q=1551
  · subst q; decide +kernel
  by_cases e32 : q=1552
  · subst q; decide +kernel
  by_cases e33 : q=1553
  · subst q; decide +kernel
  by_cases e34 : q=1554
  · subst q; decide +kernel
  by_cases e35 : q=1556
  · subst q; decide +kernel
  by_cases e36 : q=1557
  · subst q; decide +kernel
  by_cases e37 : q=1558
  · subst q; decide +kernel
  by_cases e38 : q=1559
  · subst q; decide +kernel
  by_cases e39 : q=1560
  · subst q; decide +kernel
  simp only [port,low,if_false,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22,e23,e24,e25,e26,e27,e28,e29,e30,e31,e32,e33,e34,e35,e36,e37,e38,e39]

def perm : Equiv.Perm Wire := ⟨port,port,twice,twice⟩

end ECDSAAdd.Entrant.TerminalFivePermutation

end

-- Adapted public peer module: TerminalInverse23
section

namespace ECDSAAdd.Entrant.TerminalInverse23
open ECDSAAdd Arithmetic Challenge
open MeasuredCodec5 (safe bitRun)
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def program : Program := [
  .X 6,
  .CX 5 6,
  .CX 5 10,
  .CX 1 25,
  .CX 31 26,
  .CX 32 26,
  .CX 33 26,
  .CX 34 26,
  .CCX 25 26 6,
  .CX 34 26,
  .CX 33 26,
  .CX 32 26,
  .CX 31 26,
  .CX 1 25,
  .CX 3 25,
  .CX 4 25,
  .CX 32 26,
  .CX 33 26,
  .CX 34 26,
  .CCX 25 26 7,
  .CX 34 26,
  .CX 33 26,
  .CX 32 26,
  .CX 4 25,
  .CX 3 25,
  .CX 1 25,
  .CX 2 25,
  .CX 3 25,
  .CX 4 25,
  .CX 31 26,
  .CX 32 26,
  .CX 33 26,
  .CX 34 26,
  .CCX 25 26 8,
  .CX 34 26,
  .CX 33 26,
  .CX 32 26,
  .CX 31 26,
  .CX 4 25,
  .CX 3 25,
  .CX 2 25,
  .CX 1 25,
  .CX 4 25,
  .CX 3 26,
  .CX 31 26,
  .CX 32 26,
  .CX 7 26,
  .CCX 25 26 9,
  .CX 7 26,
  .CX 32 26,
  .CX 31 26,
  .CX 3 26,
  .CX 4 25,
  .CX 4 25,
  .CX 5 25,
  .CX 32 26,
  .CX 33 26,
  .CCX 25 26 10,
  .CX 33 26,
  .CX 32 26,
  .CX 5 25,
  .CX 4 25,
  .CX 2 25,
  .CX 3 25,
  .CX 2 26,
  .CX 4 26,
  .CX 31 26,
  .CX 32 26,
  .CX 33 26,
  .CX 6 26,
  .CX 8 26,
  .CX 9 26,
  .CX 10 26,
  .CCX 25 26 11,
  .CX 10 26,
  .CX 9 26,
  .CX 8 26,
  .CX 6 26,
  .CX 33 26,
  .CX 32 26,
  .CX 31 26,
  .CX 4 26,
  .CX 2 26,
  .CX 3 25,
  .CX 2 25,
  .CX 9 11,
  .CX 3 25,
  .CX 4 26,
  .CX 33 26,
  .CX 7 26,
  .CX 10 26,
  .CCX 25 26 9,
  .CX 10 26,
  .CX 7 26,
  .CX 33 26,
  .CX 4 26,
  .CX 3 25,
  .CX 1 25,
  .CX 2 25,
  .CX 1 26,
  .CX 33 26,
  .CX 34 26,
  .CX 6 26,
  .CX 8 26,
  .CX 9 26,
  .CCX 25 26 12,
  .CX 9 26,
  .CX 8 26,
  .CX 6 26,
  .CX 34 26,
  .CX 33 26,
  .CX 1 26,
  .CX 2 25,
  .CX 1 25,
  .CX 1 25,
  .CX 3 25,
  .CX 2 26,
  .CX 31 26,
  .CX 32 26,
  .CX 6 26,
  .CX 8 26,
  .CX 9 26,
  .CCX 25 26 13,
  .CX 9 26,
  .CX 8 26,
  .CX 6 26,
  .CX 32 26,
  .CX 31 26,
  .CX 2 26,
  .CX 3 25,
  .CX 1 25,
  .CX 1 25,
  .CX 2 25,
  .CX 1 26,
  .CX 3 26,
  .CX 31 26,
  .CX 32 26,
  .CX 34 26,
  .CX 7 26,
  .CX 8 26,
  .CX 10 26,
  .CX 13 26,
  .CCX 25 26 14,
  .CX 13 26,
  .CX 10 26,
  .CX 8 26,
  .CX 7 26,
  .CX 34 26,
  .CX 32 26,
  .CX 31 26,
  .CX 3 26,
  .CX 1 26,
  .CX 2 25,
  .CX 1 25,
  .CX 2 25,
  .CX 30 26,
  .CX 32 26,
  .CX 33 26,
  .CX 34 26,
  .CCX 25 26 15,
  .CX 34 26,
  .CX 33 26,
  .CX 32 26,
  .CX 30 26,
  .CX 2 25,
  .CX 3 25,
  .CX 30 26,
  .CCX 25 26 16,
  .CX 30 26,
  .CX 3 25,
  .CX 31 32,
  .CX 32 25,
  .CX 33 25,
  .CX 10 25,
  .CX 3 26,
  .CX 4 26,
  .CX 5 26,
  .CX 7 26,
  .CX 9 26,
  .CCX 25 26 31,
  .CX 9 26,
  .CX 7 26,
  .CX 5 26,
  .CX 4 26,
  .CX 3 26,
  .CX 10 25,
  .CX 33 25,
  .CX 32 25,
  .CX 3 31,
  .CX 3 12,
  .CX 3 16,
  .CX 1 25,
  .CX 2 25,
  .CX 4 26,
  .CX 30 26,
  .CX 31 26,
  .CX 6 26,
  .CX 8 26,
  .CX 11 26,
  .CCX 25 26 3,
  .CX 11 26,
  .CX 8 26,
  .CX 6 26,
  .CX 31 26,
  .CX 30 26,
  .CX 4 26,
  .CX 2 25,
  .CX 1 25,
  .CX 1 25,
  .CX 5 25,
  .CX 1 26,
  .CX 2 26,
  .CX 3 26,
  .CX 4 26,
  .CX 32 26,
  .CX 33 26,
  .CX 6 26,
  .CX 9 26,
  .CX 11 26,
  .CX 15 26,
  .CCX 25 26 17,
  .CX 15 26,
  .CX 11 26,
  .CX 9 26,
  .CX 6 26,
  .CX 33 26,
  .CX 32 26,
  .CX 4 26,
  .CX 3 26,
  .CX 2 26,
  .CX 1 26,
  .CX 5 25,
  .CX 1 25,
  .CX 4 25,
  .CX 14 25,
  .CX 16 25,
  .CX 1 26,
  .CX 2 26,
  .CX 30 26,
  .CX 32 26,
  .CX 33 26,
  .CX 6 26,
  .CX 7 26,
  .CX 9 26,
  .CX 10 26,
  .CX 12 26,
  .CX 13 26,
  .CCX 25 26 18,
  .CX 13 26,
  .CX 12 26,
  .CX 10 26,
  .CX 9 26,
  .CX 7 26,
  .CX 6 26,
  .CX 33 26,
  .CX 32 26,
  .CX 30 26,
  .CX 2 26,
  .CX 1 26,
  .CX 16 25,
  .CX 14 25,
  .CX 4 25,
  .CX 5 30,
  .CX 5 31,
  .CX 5 34,
  .CX 5 9,
  .CX 3 25,
  .CX 30 25,
  .CX 6 25,
  .CX 12 25,
  .CX 13 25,
  .CX 18 25,
  .CX 1 26,
  .CX 2 26,
  .CX 3 26,
  .CX 4 26,
  .CX 30 26,
  .CX 9 26,
  .CX 11 26,
  .CX 15 26,
  .CCX 25 26 5,
  .CX 15 26,
  .CX 11 26,
  .CX 9 26,
  .CX 30 26,
  .CX 4 26,
  .CX 3 26,
  .CX 2 26,
  .CX 1 26,
  .CX 18 25,
  .CX 13 25,
  .CX 12 25,
  .CX 6 25,
  .CX 30 25,
  .CX 3 25,
  .CX 0 25,
  .CX 1 25,
  .X 26,
  .CX 1 26,
  .CX 33 26,
  .CX 34 26,
  .CX 8 26,
  .CX 9 26,
  .CX 15 26,
  .CCX 25 26 19,
  .CX 15 26,
  .CX 9 26,
  .CX 8 26,
  .CX 34 26,
  .CX 33 26,
  .CX 1 26,
  .X 26,
  .CX 1 25,
  .CX 0 25,
  .CX 0 25,
  .CX 1 25,
  .X 26,
  .CX 2 26,
  .CX 34 26,
  .CX 6 26,
  .CX 7 26,
  .CX 9 26,
  .CX 10 26,
  .CX 12 26,
  .CX 16 26,
  .CCX 25 26 20,
  .CX 16 26,
  .CX 12 26,
  .CX 10 26,
  .CX 9 26,
  .CX 7 26,
  .CX 6 26,
  .CX 34 26,
  .CX 2 26,
  .X 26,
  .CX 1 25,
  .CX 0 25,
  .CX 0 25,
  .CX 1 25,
  .X 26,
  .CX 31 26,
  .CX 32 26,
  .CX 33 26,
  .CX 34 26,
  .CX 6 26,
  .CX 8 26,
  .CX 11 26,
  .CX 14 26,
  .CX 16 26,
  .CX 18 26,
  .CCX 25 26 21,
  .CX 18 26,
  .CX 16 26,
  .CX 14 26,
  .CX 11 26,
  .CX 8 26,
  .CX 6 26,
  .CX 34 26,
  .CX 33 26,
  .CX 32 26,
  .CX 31 26,
  .X 26,
  .CX 1 25,
  .CX 0 25,
  .CX 0 25,
  .CX 1 25,
  .X 26,
  .CX 2 26,
  .CX 4 26,
  .CX 5 26,
  .CX 30 26,
  .CX 31 26,
  .CX 34 26,
  .CX 6 26,
  .CX 8 26,
  .CX 11 26,
  .CX 12 26,
  .CX 13 26,
  .CX 16 26,
  .CX 17 26,
  .CX 18 26,
  .CCX 25 26 22,
  .CX 18 26,
  .CX 17 26,
  .CX 16 26,
  .CX 13 26,
  .CX 12 26,
  .CX 11 26,
  .CX 8 26,
  .CX 6 26,
  .CX 34 26,
  .CX 31 26,
  .CX 30 26,
  .CX 5 26,
  .CX 4 26,
  .CX 2 26,
  .X 26,
  .CX 1 25,
  .CX 0 25,
  .CX 0 25,
  .CX 1 25,
  .X 26,
  .CX 2 26,
  .CX 3 26,
  .CX 4 26,
  .CX 30 26,
  .CX 34 26,
  .CX 6 26,
  .CX 9 26,
  .CX 11 26,
  .CX 15 26,
  .CX 17 26,
  .CCX 25 26 23,
  .CX 17 26,
  .CX 15 26,
  .CX 11 26,
  .CX 9 26,
  .CX 6 26,
  .CX 34 26,
  .CX 30 26,
  .CX 4 26,
  .CX 3 26,
  .CX 2 26,
  .X 26,
  .CX 1 25,
  .CX 0 25,
  .CX 0 25,
  .CX 1 25,
  .CX 30 26,
  .CX 32 26,
  .CX 33 26,
  .CX 34 26,
  .CCX 25 26 24,
  .CX 34 26,
  .CX 33 26,
  .CX 32 26,
  .CX 30 26,
  .CX 1 25,
  .CX 0 25,
  .CX 24 23,
  .CX 24 13,
  .CX 24 10,
  .CX 24 8,
  .CX 24 6,
  .CX 24 33,
  .CX 24 32,
  .CX 24 4,
  .CX 23 16,
  .CX 23 15,
  .CX 23 9,
  .CX 23 32,
  .CX 23 30,
  .CX 23 24,
  .CX 24 23,
  .CX 23 24,
  .CX 22 21,
  .CX 22 20,
  .CX 22 19,
  .CX 22 9,
  .CX 22 8,
  .CX 22 32,
  .CX 22 30,
  .CX 22 5,
  .CX 22 3,
  .CX 22 2,
  .CX 22 24,
  .CX 24 22,
  .CX 22 24,
  .CX 21 24,
  .CX 21 20,
  .CX 21 19,
  .CX 21 16,
  .CX 21 8,
  .CX 21 33,
  .CX 21 32,
  .CX 21 5,
  .CX 21 3,
  .CX 21 2,
  .CX 20 24,
  .CX 20 19,
  .CX 20 17,
  .CX 20 9,
  .CX 20 8,
  .CX 20 32,
  .CX 20 30,
  .CX 20 5,
  .CX 20 4,
  .CX 20 3,
  .CX 20 2,
  .CX 20 21,
  .CX 21 20,
  .CX 20 21,
  .CX 19 24,
  .CX 19 17,
  .CX 19 13,
  .CX 19 12,
  .CX 19 10,
  .CX 19 9,
  .CX 19 8,
  .CX 19 32,
  .CX 19 30,
  .CX 19 5,
  .CX 19 4,
  .CX 19 3,
  .CX 19 2,
  .CX 19 22,
  .CX 22 19,
  .CX 19 22,
  .CX 18 16,
  .CX 18 15,
  .CX 18 9,
  .CX 18 19,
  .CX 19 18,
  .CX 18 19,
  .CX 17 18,
  .CX 17 16,
  .CX 17 10,
  .CX 17 32,
  .CX 16 19,
  .CX 16 15,
  .CX 16 11,
  .CX 16 10,
  .CX 16 33,
  .CX 16 32,
  .CX 16 17,
  .CX 17 16,
  .CX 16 17,
  .CX 15 19,
  .CX 15 10,
  .CX 15 9,
  .CX 15 18,
  .CX 18 15,
  .CX 15 18,
  .CX 14 16,
  .CX 14 15,
  .CX 14 13,
  .CX 14 11,
  .CX 14 10,
  .CX 14 9,
  .CX 14 8,
  .CX 14 31,
  .CX 14 30,
  .CX 14 5,
  .CX 13 16,
  .CX 13 15,
  .CX 13 14,
  .CX 13 10,
  .CX 13 9,
  .CX 13 8,
  .CX 13 31,
  .CX 13 30,
  .CX 13 5,
  .CX 13 4,
  .CX 12 16,
  .CX 12 15,
  .CX 12 14,
  .CX 12 13,
  .CX 12 10,
  .CX 12 9,
  .CX 12 8,
  .CX 12 31,
  .CX 12 30,
  .CX 12 5,
  .CX 12 4,
  .CX 11 19,
  .CX 11 17,
  .CX 11 16,
  .CX 11 15,
  .CX 11 10,
  .CX 11 9,
  .CX 11 33,
  .CX 11 32,
  .CX 11 30,
  .CX 11 13,
  .CX 13 11,
  .CX 11 13,
  .CX 10 12,
  .CX 12 10,
  .CX 10 12,
  .CX 9 18,
  .CX 9 17,
  .CX 9 16,
  .CX 9 15,
  .CX 9 12,
  .CX 9 11,
  .CX 9 33,
  .CX 9 32,
  .CX 9 30,
  .CX 9 5,
  .CX 9 3,
  .CX 9 10,
  .CX 10 9,
  .CX 9 10,
  .CX 8 19,
  .CX 8 18,
  .CX 8 14,
  .CX 8 13,
  .CX 8 12,
  .CX 8 7,
  .CX 8 33,
  .CX 8 32,
  .CX 8 5,
  .CX 8 11,
  .CX 11 8,
  .CX 8 11,
  .CX 7 19,
  .CX 7 17,
  .CX 7 16,
  .CX 7 15,
  .CX 7 13,
  .CX 7 12,
  .CX 7 11,
  .CX 7 31,
  .CX 7 30,
  .CX 7 9,
  .CX 9 7,
  .CX 7 9,
  .CX 6 23,
  .CX 6 18,
  .CX 6 17,
  .CX 6 14,
  .CX 6 13,
  .CX 6 12,
  .CX 6 10,
  .CX 6 32,
  .CX 6 31,
  .CX 6 3,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 34 19,
  .CX 34 18,
  .CX 34 13,
  .CX 34 12,
  .CX 34 33,
  .CX 34 32,
  .CX 34 30,
  .CX 34 8,
  .CX 8 34,
  .CX 34 8,
  .CX 33 32,
  .CX 33 11,
  .CX 11 33,
  .CX 33 11,
  .CX 32 16,
  .CX 32 15,
  .CX 32 13,
  .CX 32 6,
  .CX 6 32,
  .CX 32 6,
  .CX 31 19,
  .CX 31 17,
  .CX 31 16,
  .CX 31 15,
  .CX 31 13,
  .CX 31 33,
  .CX 31 30,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 30 19,
  .CX 30 18,
  .CX 30 16,
  .CX 30 15,
  .CX 30 14,
  .CX 14 30,
  .CX 30 14,
  .CX 5 19,
  .CX 5 17,
  .CX 5 14,
  .CX 5 9,
  .CX 5 34,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 19,
  .CX 4 18,
  .CX 4 14,
  .CX 4 13,
  .CX 4 10,
  .CX 4 9,
  .CX 4 31,
  .CX 4 3,
  .CX 3 19,
  .CX 3 18,
  .CX 3 14,
  .CX 3 10,
  .CX 3 9,
  .CX 3 6,
  .CX 3 31,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 13,
  .CX 2 11,
  .CX 2 10,
  .CX 2 6,
  .CX 2 33,
  .CX 2 32,
  .CX 2 31,
  .CX 2 30,
  .CX 2 5,
  .CX 2 4,
  .CX 2 3,
  .CX 1 23,
  .CX 1 19,
  .CX 1 17,
  .CX 1 14,
  .CX 1 13,
  .CX 1 34,
  .CX 1 31,
  .CX 1 5,
  .CX 1 4,
  .CX 1 2,
  .CX 0 1,
  .X 6,
  .X 8,
  .X 11,
  .X 12,
  .X 13,
  .X 14,
  .measureX 30 [] [.Z 0, .Z 1, .Z 3, .Z 4, .Z 5, .Z 13, .Z 15, .Z 16, .Z 31, .Z 32, .Z 33, .Z 34, .Z 8, .Z 9, .Z 21, .Z 23, .CZ 0 1, .CZ 0 4, .CZ 0 11, .CZ 0 33, .CZ 0 34, .CZ 0 8, .CZ 0 9, .CZ 0 10, .CZ 0 17, .CZ 0 20, .CZ 0 21, .CZ 0 24, .CZ 1 2, .CZ 1 4, .CZ 1 33, .CZ 1 34, .CZ 1 8, .CZ 1 9, .CZ 1 10, .CZ 1 17, .CZ 1 19, .CZ 2 5, .CZ 2 6, .CZ 2 12, .CZ 2 14, .CZ 2 15, .CZ 2 16, .CZ 2 32, .CZ 2 33, .CZ 2 34, .CZ 2 8, .CZ 2 9, .CZ 2 10, .CZ 2 20, .CZ 2 21, .CZ 2 22, .CZ 2 24, .CZ 3 5, .CZ 3 11, .CZ 3 12, .CZ 3 15, .CZ 3 32, .CZ 3 33, .CZ 3 34, .CZ 3 8, .CZ 3 17, .CZ 3 18, .CZ 3 21, .CZ 4 6, .CZ 4 12, .CZ 4 13, .CZ 4 14, .CZ 4 15, .CZ 4 31, .CZ 4 32, .CZ 4 9, .CZ 4 18, .CZ 4 20, .CZ 4 21, .CZ 4 23, .CZ 5 6, .CZ 5 15, .CZ 5 9, .CZ 5 17, .CZ 5 18, .CZ 5 19, .CZ 5 21, .CZ 5 24, .CZ 6 13, .CZ 6 31, .CZ 6 32, .CZ 6 9, .CZ 6 10, .CZ 6 17, .CZ 6 18, .CZ 6 21, .CZ 11 14, .CZ 11 15, .CZ 11 32, .CZ 11 33, .CZ 11 34, .CZ 11 8, .CZ 11 9, .CZ 11 10, .CZ 12 15, .CZ 12 32, .CZ 12 33, .CZ 12 34, .CZ 12 8, .CZ 12 17, .CZ 12 18, .CZ 12 20, .CZ 12 21, .CZ 12 23, .CZ 13 15, .CZ 13 31, .CZ 13 32, .CZ 13 9, .CZ 13 18, .CZ 14 31, .CZ 14 32, .CZ 14 10, .CZ 31 33, .CZ 31 17, .CZ 32 19],
  .measureX 31 [] [.Z 0, .Z 1, .Z 3, .Z 4, .Z 6, .Z 12, .Z 15, .Z 32, .Z 33, .Z 34, .Z 8, .Z 9, .Z 10, .Z 17, .Z 18, .Z 20, .Z 23, .CZ 0 3, .CZ 0 12, .CZ 0 13, .CZ 0 32, .CZ 0 33, .CZ 0 8, .CZ 0 9, .CZ 0 17, .CZ 0 20, .CZ 1 4, .CZ 1 32, .CZ 1 33, .CZ 1 8, .CZ 1 9, .CZ 1 17, .CZ 2 4, .CZ 2 5, .CZ 2 13, .CZ 2 14, .CZ 2 16, .CZ 2 10, .CZ 2 20, .CZ 2 22, .CZ 2 24, .CZ 3 5, .CZ 3 11, .CZ 3 12, .CZ 3 13, .CZ 3 14, .CZ 3 15, .CZ 3 32, .CZ 3 33, .CZ 3 9, .CZ 3 19, .CZ 3 20, .CZ 3 21, .CZ 3 23, .CZ 3 24, .CZ 4 5, .CZ 4 12, .CZ 4 13, .CZ 4 15, .CZ 4 10, .CZ 4 18, .CZ 4 19, .CZ 5 6, .CZ 5 12, .CZ 5 14, .CZ 5 15, .CZ 5 32, .CZ 5 8, .CZ 5 19, .CZ 5 20, .CZ 5 21, .CZ 5 22, .CZ 5 23, .CZ 5 24, .CZ 6 11, .CZ 6 13, .CZ 6 14, .CZ 6 33, .CZ 6 8, .CZ 6 9, .CZ 6 10, .CZ 6 18, .CZ 11 10, .CZ 11 20, .CZ 12 14, .CZ 12 15, .CZ 12 32, .CZ 12 33, .CZ 12 9, .CZ 12 19, .CZ 12 20, .CZ 12 21, .CZ 12 23, .CZ 13 14, .CZ 13 10, .CZ 13 18, .CZ 13 19, .CZ 14 32, .CZ 14 33, .CZ 14 8, .CZ 14 9, .CZ 14 10, .CZ 14 18, .CZ 14 19, .CZ 14 23, .CZ 15 8],
  .X 32,
  .measureX 32 [] [.Z 0, .Z 1, .Z 3, .Z 7, .Z 12, .Z 14, .Z 34, .Z 8, .Z 9, .Z 10, .Z 18, .Z 20, .Z 21, .Z 23, .Z 24, .CZ 0 2, .CZ 0 3, .CZ 0 5, .CZ 0 12, .CZ 0 13, .CZ 0 33, .CZ 0 34, .CZ 0 8, .CZ 0 9, .CZ 0 10, .CZ 0 18, .CZ 0 19, .CZ 0 21, .CZ 0 22, .CZ 1 2, .CZ 1 4, .CZ 1 5, .CZ 1 33, .CZ 1 34, .CZ 1 8, .CZ 1 9, .CZ 1 10, .CZ 1 18, .CZ 1 19, .CZ 2 5, .CZ 2 6, .CZ 2 12, .CZ 2 33, .CZ 2 10, .CZ 2 17, .CZ 2 20, .CZ 2 21, .CZ 2 22, .CZ 2 24, .CZ 3 4, .CZ 3 11, .CZ 3 12, .CZ 3 15, .CZ 3 33, .CZ 3 18, .CZ 3 23, .CZ 3 24, .CZ 4 15, .CZ 4 33, .CZ 4 34, .CZ 4 10, .CZ 4 17, .CZ 4 18, .CZ 4 19, .CZ 4 22, .CZ 5 11, .CZ 5 12, .CZ 5 13, .CZ 5 14, .CZ 5 15, .CZ 5 8, .CZ 5 10, .CZ 5 17, .CZ 5 20, .CZ 5 24, .CZ 6 16, .CZ 6 34, .CZ 6 8, .CZ 6 17, .CZ 6 21, .CZ 11 12, .CZ 11 13, .CZ 11 14, .CZ 11 15, .CZ 11 33, .CZ 11 10, .CZ 11 17, .CZ 11 21, .CZ 12 14, .CZ 12 18, .CZ 12 20, .CZ 12 23, .CZ 13 34, .CZ 13 10, .CZ 13 17, .CZ 13 18, .CZ 13 19, .CZ 14 33, .CZ 14 8, .CZ 14 10, .CZ 14 17, .CZ 15 34, .CZ 15 8, .CZ 15 17, .CZ 33 10, .CZ 33 17, .CZ 33 20, .CZ 33 22, .CZ 33 24],
  .X 33,
  .measureX 33 [] [.Z 2, .Z 3, .Z 4, .Z 7, .Z 11, .Z 12, .Z 10, .Z 17, .Z 21, .Z 22, .CZ 0 2, .CZ 0 4, .CZ 0 5, .CZ 0 11, .CZ 0 12, .CZ 0 13, .CZ 0 14, .CZ 0 17, .CZ 0 20, .CZ 1 3, .CZ 1 17, .CZ 2 3, .CZ 2 4, .CZ 2 11, .CZ 2 12, .CZ 2 13, .CZ 2 14, .CZ 2 16, .CZ 2 17, .CZ 2 22, .CZ 2 24, .CZ 3 6, .CZ 3 13, .CZ 3 17, .CZ 3 18, .CZ 3 21, .CZ 3 24, .CZ 4 6, .CZ 4 11, .CZ 4 8, .CZ 4 9, .CZ 4 18, .CZ 4 19, .CZ 4 23, .CZ 5 6, .CZ 5 11, .CZ 5 12, .CZ 5 13, .CZ 5 14, .CZ 5 15, .CZ 5 34, .CZ 5 8, .CZ 5 17, .CZ 5 18, .CZ 5 19, .CZ 5 20, .CZ 5 22, .CZ 5 24, .CZ 6 16, .CZ 6 34, .CZ 6 18, .CZ 7 11, .CZ 11 12, .CZ 11 13, .CZ 11 17, .CZ 12 13, .CZ 12 17, .CZ 12 18, .CZ 12 21, .CZ 12 23, .CZ 13 8, .CZ 13 9, .CZ 13 18, .CZ 13 19, .CZ 14 15, .CZ 14 34, .CZ 14 8, .CZ 14 17, .CZ 14 18, .CZ 14 19, .CZ 15 34, .CZ 15 18, .CZ 34 9, .CZ 34 10, .CZ 34 17, .CZ 8 10, .CZ 8 17],
  .measureX 34 [] [.Z 2, .Z 3, .Z 5, .Z 6, .Z 13, .Z 15, .Z 9, .Z 10, .Z 19, .Z 20, .Z 22, .CZ 0 2, .CZ 0 3, .CZ 0 4, .CZ 0 11, .CZ 0 12, .CZ 0 13, .CZ 0 9, .CZ 0 17, .CZ 0 18, .CZ 0 19, .CZ 1 9, .CZ 1 17, .CZ 1 18, .CZ 1 19, .CZ 2 3, .CZ 2 4, .CZ 2 6, .CZ 2 12, .CZ 2 14, .CZ 2 15, .CZ 2 16, .CZ 2 10, .CZ 2 17, .CZ 2 19, .CZ 2 21, .CZ 2 24, .CZ 3 5, .CZ 3 14, .CZ 3 15, .CZ 3 9, .CZ 3 10, .CZ 3 17, .CZ 3 18, .CZ 3 22, .CZ 3 23, .CZ 3 24, .CZ 4 11, .CZ 4 15, .CZ 4 19, .CZ 4 21, .CZ 4 22, .CZ 5 6, .CZ 5 11, .CZ 5 13, .CZ 5 14, .CZ 5 8, .CZ 5 9, .CZ 5 10, .CZ 5 18, .CZ 5 23, .CZ 6 11, .CZ 6 10, .CZ 6 17, .CZ 6 21, .CZ 7 11, .CZ 11 13, .CZ 11 15, .CZ 11 8, .CZ 11 9, .CZ 11 10, .CZ 11 17, .CZ 11 19, .CZ 11 22, .CZ 12 8, .CZ 12 9, .CZ 12 10, .CZ 12 17, .CZ 12 18, .CZ 12 20, .CZ 12 21, .CZ 12 23, .CZ 13 14, .CZ 13 19, .CZ 13 20, .CZ 14 15, .CZ 14 8, .CZ 14 9, .CZ 14 10, .CZ 14 18, .CZ 14 23, .CZ 15 10, .CZ 15 17, .CZ 8 9, .CZ 8 10, .CZ 8 18, .CZ 8 22, .CZ 9 17, .CZ 9 18, .CZ 9 24],
  .X 8,
  .measureX 8 [] [.Z 0, .Z 1, .Z 2, .Z 3, .Z 4, .Z 6, .Z 7, .Z 11, .Z 12, .Z 15, .Z 16, .Z 18, .Z 19, .Z 22, .CZ 0 2, .CZ 0 4, .CZ 0 5, .CZ 0 12, .CZ 0 13, .CZ 0 10, .CZ 0 17, .CZ 0 24, .CZ 1 2, .CZ 1 3, .CZ 1 5, .CZ 1 10, .CZ 1 17, .CZ 2 4, .CZ 2 5, .CZ 2 11, .CZ 2 13, .CZ 2 15, .CZ 2 16, .CZ 2 10, .CZ 2 20, .CZ 2 21, .CZ 2 22, .CZ 2 24, .CZ 3 12, .CZ 3 14, .CZ 3 9, .CZ 3 18, .CZ 3 19, .CZ 3 20, .CZ 3 24, .CZ 4 6, .CZ 4 11, .CZ 4 12, .CZ 4 13, .CZ 4 14, .CZ 4 15, .CZ 4 9, .CZ 4 10, .CZ 4 18, .CZ 4 19, .CZ 5 6, .CZ 5 11, .CZ 5 13, .CZ 5 14, .CZ 5 15, .CZ 5 9, .CZ 5 10, .CZ 5 18, .CZ 6 11, .CZ 6 12, .CZ 6 13, .CZ 6 17, .CZ 6 20, .CZ 6 21, .CZ 7 11, .CZ 11 12, .CZ 11 13, .CZ 11 10, .CZ 11 20, .CZ 11 21, .CZ 12 13, .CZ 12 14, .CZ 12 15, .CZ 12 10, .CZ 12 18, .CZ 12 19, .CZ 12 20, .CZ 12 23, .CZ 13 15, .CZ 13 9, .CZ 13 18, .CZ 13 19, .CZ 14 9, .CZ 14 10, .CZ 14 18, .CZ 14 23, .CZ 15 17, .CZ 9 17, .CZ 9 18, .CZ 9 22, .CZ 9 24, .CZ 10 21],
  .measureX 9 [] [.Z 0, .Z 1, .Z 3, .Z 4, .Z 5, .Z 6, .Z 11, .Z 12, .Z 15, .Z 10, .Z 17, .Z 19, .Z 21, .Z 22, .CZ 0 4, .CZ 0 11, .CZ 0 12, .CZ 0 19, .CZ 0 20, .CZ 0 21, .CZ 0 24, .CZ 1 2, .CZ 1 3, .CZ 1 4, .CZ 1 19, .CZ 2 4, .CZ 2 6, .CZ 2 11, .CZ 2 12, .CZ 2 14, .CZ 2 16, .CZ 2 10, .CZ 2 19, .CZ 2 22, .CZ 2 24, .CZ 3 5, .CZ 3 6, .CZ 3 12, .CZ 3 14, .CZ 3 15, .CZ 3 24, .CZ 4 5, .CZ 4 14, .CZ 4 10, .CZ 4 17, .CZ 4 18, .CZ 4 19, .CZ 4 20, .CZ 4 21, .CZ 4 23, .CZ 5 11, .CZ 5 13, .CZ 5 14, .CZ 5 15, .CZ 5 17, .CZ 5 23, .CZ 6 10, .CZ 6 18, .CZ 6 20, .CZ 6 21, .CZ 7 11, .CZ 11 13, .CZ 11 15, .CZ 11 19, .CZ 12 13, .CZ 12 15, .CZ 12 10, .CZ 12 20, .CZ 13 14, .CZ 13 15, .CZ 13 10, .CZ 13 17, .CZ 13 18, .CZ 13 19, .CZ 14 15, .CZ 14 17, .CZ 15 10, .CZ 15 18, .CZ 10 17, .CZ 10 18, .CZ 10 22],
  .X 10,
  .measureX 10 [] [.Z 3, .Z 4, .Z 5, .Z 6, .Z 7, .Z 13, .Z 14, .Z 15, .Z 16, .Z 19, .Z 21, .CZ 0 3, .CZ 0 4, .CZ 0 5, .CZ 0 12, .CZ 0 13, .CZ 0 14, .CZ 0 20, .CZ 0 21, .CZ 2 11, .CZ 2 12, .CZ 2 14, .CZ 2 15, .CZ 2 16, .CZ 2 17, .CZ 2 20, .CZ 2 21, .CZ 3 6, .CZ 3 20, .CZ 3 21, .CZ 3 22, .CZ 3 23, .CZ 4 14, .CZ 4 15, .CZ 4 17, .CZ 5 6, .CZ 5 12, .CZ 5 13, .CZ 5 22, .CZ 5 23, .CZ 6 11, .CZ 6 12, .CZ 6 13, .CZ 6 14, .CZ 6 20, .CZ 6 21, .CZ 7 11, .CZ 12 17, .CZ 13 17, .CZ 17 22, .CZ 17 23],
  .measureX 17 [] [.Z 6, .Z 14, .Z 15, .Z 18, .Z 19, .Z 20, .Z 24, .CZ 0 21, .CZ 2 4, .CZ 2 12, .CZ 2 15, .CZ 2 16, .CZ 2 22, .CZ 3 22, .CZ 4 14, .CZ 4 18, .CZ 4 19, .CZ 4 20, .CZ 4 21, .CZ 4 22, .CZ 4 23, .CZ 5 14, .CZ 5 21, .CZ 5 23, .CZ 6 11, .CZ 6 12, .CZ 6 13, .CZ 6 18, .CZ 6 21, .CZ 7 11, .CZ 11 21, .CZ 11 22, .CZ 12 14, .CZ 12 15, .CZ 12 18, .CZ 12 19, .CZ 12 20, .CZ 12 21, .CZ 12 23, .CZ 13 15, .CZ 14 23, .CZ 15 18, .CZ 18 21, .CZ 19 21],
  .X 18,
  .measureX 18 [] [.Z 2, .Z 5, .Z 7, .Z 11, .Z 13, .Z 14, .Z 20, .Z 21, .CZ 0 4, .CZ 0 5, .CZ 0 11, .CZ 0 13, .CZ 0 19, .CZ 0 20, .CZ 0 21, .CZ 0 24, .CZ 1 2, .CZ 1 5, .CZ 1 19, .CZ 2 15, .CZ 2 20, .CZ 2 22, .CZ 2 24, .CZ 3 4, .CZ 3 5, .CZ 3 6, .CZ 3 11, .CZ 3 13, .CZ 3 14, .CZ 3 15, .CZ 3 19, .CZ 3 20, .CZ 3 23, .CZ 3 24, .CZ 4 11, .CZ 5 6, .CZ 5 11, .CZ 5 14, .CZ 5 15, .CZ 5 20, .CZ 5 21, .CZ 5 22, .CZ 5 23, .CZ 5 24, .CZ 6 11, .CZ 6 14, .CZ 6 16, .CZ 6 20, .CZ 6 21, .CZ 11 13, .CZ 11 14, .CZ 11 19, .CZ 11 20, .CZ 12 20, .CZ 19 22],
  .X 19,
  .measureX 19 [] [.Z 4, .Z 5, .Z 6, .Z 7, .Z 13, .Z 14, .Z 15, .Z 16, .Z 23, .Z 24, .CZ 0 2, .CZ 0 11, .CZ 2 16, .CZ 2 23, .CZ 7 11, .CZ 11 23],
  .measureX 20 [] [.Z 21, .Z 22, .Z 24, .CZ 1 5, .CZ 1 14],
  .measureX 21 [] [.Z 22, .Z 24, .CZ 1 4, .CZ 1 13],
  .measureX 22 [] [.Z 24, .CZ 1 3, .CZ 1 12],
  .measureX 23 [] [.Z 0, .Z 1, .Z 7, .Z 15, .Z 16, .CZ 1 6, .CZ 1 15],
  .measureX 24 [] [.CZ 1 2, .CZ 1 11],
  .X 10,
  .CX 1 10
]

def reference : Program := [
  .X 6,
  .CX 5 6,
  .CX 5 10,
  .CX 34 33,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CCX 1 2 6,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 33,
  .CX 34 33,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 5,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 7,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 5,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 33,
  .CX 34 33,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 5,
  .CX 3 2,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 2 1,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 1 3,
  .CCX 1 2 8,
  .CX 1 3,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 2 1,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 2,
  .CX 3 5,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 33,
  .CX 7 32,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 31 3,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 10,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 3,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 7 32,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 4,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 31,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 11,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 31,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 5 4,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 11 10,
  .CX 10 11,
  .CX 10 8,
  .CX 8 10,
  .CX 8 6,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 6 33,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 31 4,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 2 4,
  .CX 2 3,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 12,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 3,
  .CX 2 4,
  .CX 4 2,
  .CX 4 3,
  .CX 4 5,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 4,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 6 33,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 6,
  .CX 8 10,
  .CX 10 8,
  .CX 10 11,
  .CX 11 10,
  .CX 11 7,
  .CX 10 12,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 11,
  .CX 11 8,
  .CX 8 11,
  .CX 7 10,
  .CX 7 33,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 8,
  .CX 8 6,
  .CX 6 8,
  .CX 34 7,
  .CX 7 34,
  .CX 34 7,
  .CX 33 6,
  .CX 33 4,
  .CX 32 34,
  .CX 34 32,
  .CX 32 34,
  .CX 31 33,
  .CX 33 31,
  .CX 31 33,
  .CX 5 32,
  .CX 32 5,
  .CX 5 32,
  .CX 4 31,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 5,
  .CX 5 2,
  .CX 2 5,
  .CX 1 4,
  .CX 4 1,
  .CX 1 4,
  .CCX 1 2 3,
  .CX 11 8,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 8 7,
  .CX 7 8,
  .CX 7 6,
  .CX 6 7,
  .CX 6 5,
  .CX 6 4,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 5 4,
  .CX 5 3,
  .CX 4 31,
  .CX 4 5,
  .CX 4 3,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 13,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 4 3,
  .CX 4 5,
  .CX 4 31,
  .CX 5 3,
  .CX 5 4,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 6 4,
  .CX 6 5,
  .CX 6 7,
  .CX 7 6,
  .CX 7 8,
  .CX 8 7,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 8,
  .CX 11 8,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 8 34,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 34 6,
  .CX 34 33,
  .CX 33 34,
  .CX 33 5,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 5 3,
  .CX 4 1,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CCX 1 2 14,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 4 1,
  .CX 5 3,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 5,
  .CX 33 34,
  .CX 34 33,
  .CX 34 6,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 34,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 8,
  .CX 14 11,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 12 13,
  .CX 13 12,
  .CX 12 13,
  .CX 11 12,
  .CX 11 7,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 7 6,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 33,
  .CX 33 34,
  .CX 33 31,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 31 5,
  .CX 31 4,
  .CX 4 31,
  .CX 4 5,
  .CX 4 2,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 4,
  .CX 2 1,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 1 3,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CCX 1 2 15,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 1 3,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 2 1,
  .CX 2 4,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 4 2,
  .CX 4 5,
  .CX 4 31,
  .CX 31 4,
  .CX 31 5,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 31,
  .CX 33 34,
  .CX 34 33,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 6,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 7,
  .CX 11 12,
  .CX 12 13,
  .CX 13 12,
  .CX 12 13,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 14 11,
  .CX 12 10,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 10 11,
  .CX 10 6,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 32,
  .CX 34 31,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 5,
  .CX 31 33,
  .CX 31 1,
  .CX 5 32,
  .CX 5 31,
  .CX 5 3,
  .CX 5 1,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 1 2,
  .CCX 1 2 35,
  .CX 1 2,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 5 1,
  .CX 5 3,
  .CX 5 31,
  .CX 5 32,
  .CX 31 1,
  .CX 31 33,
  .CX 32 5,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 31,
  .CX 34 32,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 6,
  .CX 10 11,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 12 10,
  .CX 35 12,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 12 13,
  .CX 12 10,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 10 11,
  .CX 10 6,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 32,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 32 5,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 5 3,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 36,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 5 3,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 5,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 32,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 6,
  .CX 10 11,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 12 10,
  .CX 12 13,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 35 12,
  .CX 10 34,
  .CX 10 32,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 34 33,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 6,
  .CX 33 34,
  .CX 33 32,
  .CX 33 31,
  .CX 32 34,
  .CX 32 3,
  .CX 31 33,
  .CX 31 32,
  .CX 31 3,
  .CX 31 2,
  .CX 5 32,
  .CX 32 5,
  .CX 5 32,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 3 5,
  .CX 3 1,
  .CX 2 4,
  .CX 1 3,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CCX 1 2 37,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 1 3,
  .CX 2 4,
  .CX 3 1,
  .CX 3 5,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 5 32,
  .CX 32 5,
  .CX 5 32,
  .CX 31 2,
  .CX 31 3,
  .CX 31 32,
  .CX 31 33,
  .CX 32 3,
  .CX 32 34,
  .CX 33 31,
  .CX 33 32,
  .CX 33 34,
  .CX 33 6,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 34 33,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 32,
  .CX 10 34,
  .CX 37 12,
  .CX 36 37,
  .CX 37 36,
  .CX 36 37,
  .CX 35 36,
  .CX 36 35,
  .CX 35 36,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 12 13,
  .CX 12 11,
  .CX 11 12,
  .CX 11 8,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 8 7,
  .CX 7 8,
  .CX 7 6,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 31,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 31 1,
  .CX 5 4,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 31,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CCX 1 2 9,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 4 31,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 5 4,
  .CX 31 1,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 31,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 6,
  .CX 7 8,
  .CX 8 7,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 8,
  .CX 11 12,
  .CX 12 11,
  .CX 12 13,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 35 36,
  .CX 36 35,
  .CX 35 36,
  .CX 36 37,
  .CX 37 36,
  .CX 36 37,
  .CX 37 12,
  .CX 9 37,
  .CX 9 35,
  .CX 9 12,
  .CX 37 35,
  .CX 37 34,
  .CX 37 33,
  .CX 37 9,
  .CX 9 37,
  .CX 37 9,
  .CX 36 35,
  .CX 36 15,
  .CX 36 14,
  .CX 36 11,
  .CX 36 7,
  .CX 36 37,
  .CX 37 36,
  .CX 36 37,
  .CX 35 9,
  .CX 35 12,
  .CX 35 6,
  .CX 35 33,
  .CX 35 3,
  .CX 35 37,
  .CX 37 35,
  .CX 35 37,
  .CX 15 9,
  .CX 15 14,
  .CX 15 11,
  .CX 15 7,
  .CX 15 33,
  .CX 14 9,
  .CX 14 37,
  .CX 14 6,
  .CX 14 33,
  .CX 14 31,
  .CX 14 3,
  .CX 14 35,
  .CX 35 14,
  .CX 14 35,
  .CX 13 9,
  .CX 13 37,
  .CX 13 36,
  .CX 13 6,
  .CX 13 33,
  .CX 13 3,
  .CX 13 1,
  .CX 13 35,
  .CX 35 13,
  .CX 13 35,
  .CX 12 9,
  .CX 12 37,
  .CX 12 10,
  .CX 12 6,
  .CX 12 33,
  .CX 12 3,
  .CX 12 36,
  .CX 36 12,
  .CX 12 36,
  .CX 11 9,
  .CX 11 7,
  .CX 11 33,
  .CX 11 2,
  .CX 11 15,
  .CX 15 11,
  .CX 11 15,
  .CX 10 36,
  .CX 10 7,
  .CX 10 6,
  .CX 10 35,
  .CX 35 10,
  .CX 10 35,
  .CX 8 35,
  .CX 8 6,
  .CX 8 14,
  .CX 14 8,
  .CX 8 14,
  .CX 7 9,
  .CX 7 35,
  .CX 7 6,
  .CX 7 34,
  .CX 7 33,
  .CX 7 14,
  .CX 14 7,
  .CX 7 14,
  .CX 6 37,
  .CX 6 34,
  .CX 6 32,
  .CX 6 3,
  .CX 6 14,
  .CX 14 6,
  .CX 6 14,
  .CX 34 9,
  .CX 34 37,
  .CX 34 35,
  .CX 34 15,
  .CX 34 14,
  .CX 34 10,
  .CX 34 33,
  .CX 34 32,
  .CX 34 5,
  .CX 34 3,
  .CX 34 2,
  .CX 34 1,
  .CX 33 9,
  .CX 33 11,
  .CX 33 8,
  .CX 33 7,
  .CX 7 33,
  .CX 33 7,
  .CX 32 37,
  .CX 32 35,
  .CX 32 15,
  .CX 32 14,
  .CX 32 3,
  .CX 32 2,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 13,
  .CX 31 12,
  .CX 31 10,
  .CX 31 7,
  .CX 31 33,
  .CX 31 5,
  .CX 31 4,
  .CX 31 1,
  .CX 5 10,
  .CX 5 6,
  .CX 5 34,
  .CX 5 33,
  .CX 5 1,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 37,
  .CX 4 35,
  .CX 4 15,
  .CX 4 12,
  .CX 4 7,
  .CX 4 34,
  .CX 4 33,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 3 37,
  .CX 3 35,
  .CX 3 15,
  .CX 3 12,
  .CX 3 6,
  .CX 3 33,
  .CX 3 31,
  .CX 3 2,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 15,
  .CX 2 11,
  .CX 2 34,
  .CX 34 2,
  .CX 2 34,
  .CX 1 10,
  .CX 1 33,
  .CX 1 5,
  .CX 1 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .X 31,
  .X 33,
  .X 34,
  .X 6,
  .measureX 9 [] [.Z 5, .Z 33, .Z 6, .Z 10, .Z 12, .Z 14, .Z 15, .CZ 1 10, .CZ 1 11, .CZ 1 37, .CZ 2 3, .CZ 2 4, .CZ 2 5, .CZ 2 34, .CZ 2 13, .CZ 2 14, .CZ 2 37, .CZ 3 10, .CZ 3 13, .CZ 33 7, .CZ 33 15, .CZ 33 37],
  .measureX 37 [] [.Z 5, .Z 31, .Z 32, .Z 33, .Z 34, .Z 6, .Z 8, .Z 12, .Z 14, .Z 15, .Z 35, .CZ 1 3, .CZ 1 33, .CZ 1 34, .CZ 1 15, .CZ 1 35, .CZ 2 34, .CZ 2 13, .CZ 2 35, .CZ 3 4, .CZ 3 33, .CZ 3 6, .CZ 3 7, .CZ 3 8, .CZ 3 10, .CZ 3 11, .CZ 3 13, .CZ 3 14, .CZ 3 15, .CZ 3 35, .CZ 3 36, .CZ 4 5, .CZ 4 31, .CZ 4 10, .CZ 4 12, .CZ 4 35, .CZ 5 7, .CZ 5 35, .CZ 31 33, .CZ 33 34, .CZ 33 7, .CZ 33 15, .CZ 33 35, .CZ 34 35],
  .X 36,
  .measureX 36 [] [.Z 1, .Z 2, .Z 4, .Z 31, .Z 32, .Z 10, .Z 12, .Z 13, .Z 14, .CZ 1 2, .CZ 1 3, .CZ 1 5, .CZ 1 34, .CZ 1 10, .CZ 1 12, .CZ 2 3, .CZ 2 5, .CZ 2 13, .CZ 2 14, .CZ 3 4, .CZ 3 5, .CZ 3 7, .CZ 3 8, .CZ 3 11, .CZ 3 13, .CZ 3 14, .CZ 4 5, .CZ 4 33, .CZ 4 34, .CZ 4 7, .CZ 4 10, .CZ 4 11, .CZ 4 12, .CZ 5 14, .CZ 31 33, .CZ 31 34, .CZ 31 12],
  .X 35,
  .measureX 35 [] [.Z 2, .Z 5, .Z 33, .Z 6, .Z 8, .Z 14, .CZ 1 2, .CZ 1 5, .CZ 1 33, .CZ 1 6, .CZ 1 10, .CZ 1 11, .CZ 1 13, .CZ 1 14, .CZ 2 4, .CZ 2 31, .CZ 2 34, .CZ 2 14, .CZ 3 33, .CZ 3 34, .CZ 3 8, .CZ 3 13, .CZ 3 14, .CZ 4 34, .CZ 4 6, .CZ 4 7, .CZ 4 14, .CZ 5 33, .CZ 5 6, .CZ 5 7, .CZ 5 10, .CZ 5 12, .CZ 5 14, .CZ 31 12, .CZ 33 6, .CZ 33 7, .CZ 33 12],
  .measureX 15 [] [.Z 1, .Z 3, .Z 4, .Z 5, .Z 33, .Z 34, .Z 10, .Z 13, .Z 14, .CZ 1 3, .CZ 1 33, .CZ 1 10, .CZ 1 11, .CZ 1 13, .CZ 2 3, .CZ 2 4, .CZ 2 5, .CZ 2 31, .CZ 2 13, .CZ 2 14, .CZ 3 7, .CZ 3 8, .CZ 3 10, .CZ 4 7, .CZ 4 13],
  .X 14,
  .measureX 14 [] [.Z 1, .Z 4, .Z 31, .Z 6, .Z 10, .Z 12, .CZ 1 3, .CZ 1 34, .CZ 1 12, .CZ 2 4, .CZ 2 5, .CZ 2 31, .CZ 3 34, .CZ 3 7, .CZ 3 10, .CZ 3 12, .CZ 4 31, .CZ 4 6, .CZ 4 7, .CZ 4 10, .CZ 4 11, .CZ 4 12, .CZ 5 33, .CZ 5 6, .CZ 5 10, .CZ 5 12, .CZ 31 33, .CZ 31 34, .CZ 31 10, .CZ 31 12, .CZ 33 34, .CZ 33 7, .CZ 34 7],
  .measureX 13 [] [.Z 3, .Z 4, .Z 33, .Z 10, .CZ 1 4, .CZ 1 34, .CZ 3 4, .CZ 3 31, .CZ 3 33, .CZ 3 11, .CZ 4 10, .CZ 33 34, .CZ 33 7, .CZ 33 11, .CZ 34 10],
  .measureX 12 [] [.Z 1, .Z 2, .Z 3, .Z 5, .CZ 2 3, .CZ 2 5, .CZ 2 33, .CZ 2 6],
  .X 11,
  .measureX 11 [] [.Z 34, .Z 7, .CZ 2 4, .CZ 2 31, .CZ 2 34, .CZ 2 7],
  .measureX 10 [] [.Z 1, .Z 2, .Z 3, .CZ 2 3, .CZ 2 33],
  .CX 31 6,
  .CX 6 31,
  .CX 31 6,
  .CX 32 7,
  .CX 7 32,
  .CX 32 7,
  .CX 33 11,
  .CX 11 33,
  .CX 33 11,
  .CX 34 12,
  .CX 12 34,
  .CX 34 12,
  .CX 31 13,
  .CX 13 31,
  .CX 31 13,
  .CX 32 14,
  .CX 14 32,
  .CX 32 14,
  .CX 8 15,
  .CX 15 8,
  .CX 8 15,
  .X 10,
  .CX 2 10,
  .measureX 9 [] [],
  .CX 15 16,
  .CX 7 8,
  .CX 0 1,
  .CX 30 16,
  .X 30,
  .CX 7 30,
  .CX 15 30,
  .X 10,
  .X 11,
  .X 12,
  .X 13,
  .X 14,
  .X 15,
  .CX 30 2,
  .CX 30 3,
  .CX 30 4,
  .CX 30 5,
  .CX 30 6,
  .CX 30 7,
  .CX 2 10,
  .CX 2 30,
  .CCX 10 30 35,
  .CX 2 35,
  .CX 2 30,
  .CX 2 10,
  .CX 3 11,
  .CX 3 35,
  .CCX 11 35 36,
  .CX 3 36,
  .CX 3 35,
  .CX 3 11,
  .CX 4 12,
  .CX 4 36,
  .CCX 12 36 37,
  .CX 4 37,
  .CX 4 36,
  .CX 4 12,
  .CX 5 13,
  .CX 5 37,
  .CCX 13 37 38,
  .CX 5 38,
  .CX 5 37,
  .CX 5 13,
  .measureX 15 [] [.CZ 6 14, .CZ 6 38, .CZ 14 38],
  .CX 7 15,
  .CX 6 14,
  .CX 38 14,
  .measureX 38 [] [.CZ 5 13, .CZ 5 37, .CZ 13 37],
  .CX 5 13,
  .CX 37 13,
  .measureX 37 [] [.CZ 4 12, .CZ 4 36, .CZ 12 36],
  .CX 4 12,
  .CX 36 12,
  .measureX 36 [] [.CZ 3 11, .CZ 3 35, .CZ 11 35],
  .CX 3 11,
  .CX 35 11,
  .measureX 35 [] [.CZ 2 10, .CZ 2 30, .CZ 10 30],
  .CX 2 10,
  .CX 30 10,
  .CX 30 2,
  .CX 30 3,
  .CX 30 4,
  .CX 30 5,
  .CX 30 6,
  .CX 30 7,
  .X 10,
  .X 11,
  .X 12,
  .X 13,
  .X 14,
  .X 15,
  .X 30,
  .CX 7 30,
  .CX 15 30,
  .CX 7 8,
  .CX 1 10,
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CX 16 7,
  .CCX 1 2 11,
  .CCX 1 3 12,
  .CCX 1 4 13,
  .CCX 1 5 14,
  .CCX 1 6 15,
  .CCX 1 7 16,
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CX 16 7
]

theorem counts : toffoliCount program=23 ∧ measurementCount program=16 ∧ gateSlots program=1633 := by decide +kernel

theorem physical : GatePhysical program :=
  CodecBitSliceVerify.physical_of_check program (by decide +kernel)

theorem support : wires program⊆Finset.range 40 :=
  CodecBitSliceVerify.support_of_check program 40 (by decide +kernel)

open CodecBitSliceVerify (Cols Rel eval target)
set_option linter.unnecessarySimpa false
attribute [local irreducible] program reference
def rowInputs : List Nat := [1086, 1087, 1084, 1073742908, 1085, 1073742909, 3221226552, 1073742904, 3221226553, 1073742905, 5368710196, 1073742900, 5368710197, 1073742901, 5368710192, 1073742896, 5368710193, 1073742897, 9663677484, 1073742892, 9663677485, 1073742893, 9663677480, 1073742888, 9663677481, 1073742889, 9663677476, 1073742884, 9663677477, 1073742885, 9663677472, 1073742880, 9663677473, 1073742881, 18253611100, 1073741916, 18253611101, 1073741917, 18253611096, 1073741912, 18253611097, 1073741913, 18253611092, 1073741908, 18253611093, 1073741909, 18253611088, 1073741904, 18253611089, 1073741905, 18253611084, 1073741900, 18253611085, 1073741901, 18253611080, 1073741896, 18253611081, 1073741897, 18253611076, 1073741892, 18253611077, 1073741893, 18253611072, 1073741888, 18253611073, 1073741889, 1082, 2147484730, 1083, 2147484731, 6442452018, 2147484722, 6442452019, 2147484723, 10737419306, 2147484714, 10737419307, 2147484715, 10737419298, 2147484706, 10737419299, 2147484707, 19327352922, 2147483738, 19327352923, 2147483739, 19327352914, 2147483730, 19327352915, 2147483731, 19327352906, 2147483722, 19327352907, 2147483723, 19327352898, 2147483714, 19327352899, 2147483715, 1080, 2147484728, 1081, 2147484729, 3221226544, 7516193840, 3221226545, 7516193841, 5368710180, 13958644772, 5368710181, 13958644773, 9663676492, 26843545676, 9663676493, 26843545677, 5368710176, 13958644768, 5368710177, 13958644769, 1078, 4294968374, 1079, 4294968375, 12884902950, 4294968358, 12884902951, 4294968359, 21474836566, 4294967382, 21474836567, 4294967383, 21474836550, 4294967366, 21474836551, 4294967367, 1076, 4294968372, 1077, 4294968373, 6442452016, 2147484720, 6442452017, 2147484721, 3221226536, 11811161128, 3221226537, 11811161129, 1074, 4294968370, 1075, 4294968371, 6442452002, 15032386594, 6442452003, 15032386595, 10737418314, 27917287498, 10737418315, 27917287499, 1072, 4294968368, 1073, 4294968369, 12884902948, 4294968356, 12884902949, 4294968357, 10737419304, 2147484712, 10737419305, 2147484713, 1070, 8589935662, 1071, 8589935663, 25769803854, 8589934670, 25769803855, 8589934671, 1068, 8589935660, 1069, 8589935661, 1066, 8589935658, 1067, 8589935659, 12884902946, 4294968354, 12884902947, 4294968355, 1064, 8589935656, 1065, 8589935657, 25769803852, 8589934668, 25769803853, 8589934669, 1062, 8589935654, 1063, 8589935655, 1060, 8589935652, 1061, 8589935653, 12884902944, 4294968352, 12884902945, 4294968353, 1058, 8589935650, 1059, 8589935651, 25769803850, 8589934666, 25769803851, 8589934667, 1056, 8589935648, 1057, 8589935649, 94, 17179869278, 95, 17179869279, 92, 17179869276, 93, 17179869277, 90, 17179869274, 91, 17179869275, 88, 17179869272, 89, 17179869273, 86, 17179869270, 87, 17179869271, 84, 17179869268, 85, 17179869269, 82, 17179869266, 83, 17179869267, 80, 17179869264, 81, 17179869265, 78, 17179869262, 79, 17179869263, 76, 17179869260, 77, 17179869261, 74, 17179869258, 75, 17179869259, 72, 17179869256, 73, 17179869257, 70, 17179869254, 71, 17179869255, 68, 17179869252, 69, 17179869253, 66, 17179869250, 67, 17179869251, 64, 17179869248, 65, 17179869249]
def inputColumns : Cols := [99464647281957328431076449629364168020091230159469543488092795378631899402506675106610, 7313577006026274149366996476163838831110099834557628619541616149067685538413989068803, 483777467324695177167828793134568020633829380303857492123620127396438216722112855103, 1897108642483584637900354440776668658749440131746523718715959141488542031904769023, 28948022302589062189105086308987197930954657990120560452497621796144378281983, 6345065196404107196363785427150149683075013179537663729244951281663, 124330809102446660532500496840301102828750252272186779677040981043752210523888392601600, 0, 0, 0, 6345065196404107196363785427150149683075013179537663729244951281663, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 83627794826791765124587072617753428742897640, 1403405608853838471720203957050097485798937313935680, 1542661993684441261928647815447584048602054862787530517569950720, 4624450713988395599348360893856719501858128957960173379948779929600, 82887206068297773688202024070072884301846691882006083737104965766559475826279642562560, 0, 0, 0, 0, 0]
def rowInput (r : Fin 286) : Nat := (rowInputs[r.val]?).getD 0

theorem input_length : inputColumns.length=40 := by decide +kernel

theorem columns_correct : ∀q : Fin 40,
    CodecBitSliceVerify.get inputColumns q.val=CodecBitSliceVerify.packBits (rowInputs.map (fun x=>x.testBit q.val)) := by
  decide +kernel

theorem finite_input_bits (r : Fin 286) (q : Fin 40) :
    (rowInput r).testBit q.val=(CodecBitSliceVerify.get inputColumns q.val).testBit r.val := by
  rw [columns_correct q,CodecBitSliceVerify.pack_rows]
  rfl

theorem input_bounds : ∀r : Fin 286,rowInput r<2^40 := by decide +kernel

theorem input_rel (r : Fin 286) : Rel inputColumns (rowInput r) r.val := by
  intro q
  by_cases hq:q<40
  · exact finite_input_bits r ⟨q,hq⟩
  · change ¬(q:Nat)<40 at hq
    have q40:40≤(q:Nat):=Nat.le_of_not_gt hq
    have qb:inputColumns.length≤q := by rw [input_length];exact q40
    have z:CodecBitSliceVerify.get inputColumns q=0 := by
      simp only [CodecBitSliceVerify.get,List.getElem?_eq_none qb,Option.getD_none]
    rw [z,Nat.zero_testBit]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (input_bounds r)
      (Nat.pow_le_pow_right (by decide) q40))

theorem mask_bits : ∀r : Fin 286,(2^286-1).testBit r.val=true := by decide +kernel

theorem program_targets : ∀i∈program,target i < inputColumns.length := by
  rw [input_length]
  decide +kernel

theorem reference_targets : ∀i∈reference,target i < inputColumns.length := by
  rw [input_length]
  decide +kernel

def resultP := eval (2^286-1) program inputColumns
def resultQ := eval (2^286-1) reference inputColumns

theorem vector_checked : resultP.1=true ∧ resultQ.1=true ∧ resultP.2=resultQ.2 := by
  decide +kernel

attribute [local irreducible] safe bitRun

theorem row_all (r : Fin 286) : safe program (rowInput r)=true ∧
    safe reference (rowInput r)=true ∧ bitRun program (rowInput r)=bitRun reference (rowInput r) := by
  have hp:=CodecBitSliceVerify.eval_sound (2^286-1) r.val (mask_bits r) program inputColumns
    (rowInput r) program_targets (input_rel r) vector_checked.1
  have hq:=CodecBitSliceVerify.eval_sound (2^286-1) r.val (mask_bits r) reference inputColumns
    (rowInput r) reference_targets (input_rel r) vector_checked.2.1
  refine ⟨hp.1,hq.1,?_⟩
  apply Nat.eq_of_testBit_eq
  intro q
  exact (hp.2 q).trans ((congrArg (fun s : Cols => (CodecBitSliceVerify.get s q).testBit r.val) vector_checked.2.2).trans
    (hq.2 q).symm)

theorem row0 : safe program 1086=true ∧ safe reference 1086=true ∧ bitRun program 1086=bitRun reference 1086 := row_all ⟨0,by decide⟩
theorem row1 : safe program 1087=true ∧ safe reference 1087=true ∧ bitRun program 1087=bitRun reference 1087 := row_all ⟨1,by decide⟩
theorem row2 : safe program 1084=true ∧ safe reference 1084=true ∧ bitRun program 1084=bitRun reference 1084 := row_all ⟨2,by decide⟩
theorem row3 : safe program 1073742908=true ∧ safe reference 1073742908=true ∧ bitRun program 1073742908=bitRun reference 1073742908 := row_all ⟨3,by decide⟩
theorem row4 : safe program 1085=true ∧ safe reference 1085=true ∧ bitRun program 1085=bitRun reference 1085 := row_all ⟨4,by decide⟩
theorem row5 : safe program 1073742909=true ∧ safe reference 1073742909=true ∧ bitRun program 1073742909=bitRun reference 1073742909 := row_all ⟨5,by decide⟩
theorem row6 : safe program 3221226552=true ∧ safe reference 3221226552=true ∧ bitRun program 3221226552=bitRun reference 3221226552 := row_all ⟨6,by decide⟩
theorem row7 : safe program 1073742904=true ∧ safe reference 1073742904=true ∧ bitRun program 1073742904=bitRun reference 1073742904 := row_all ⟨7,by decide⟩
theorem row8 : safe program 3221226553=true ∧ safe reference 3221226553=true ∧ bitRun program 3221226553=bitRun reference 3221226553 := row_all ⟨8,by decide⟩
theorem row9 : safe program 1073742905=true ∧ safe reference 1073742905=true ∧ bitRun program 1073742905=bitRun reference 1073742905 := row_all ⟨9,by decide⟩
theorem row10 : safe program 5368710196=true ∧ safe reference 5368710196=true ∧ bitRun program 5368710196=bitRun reference 5368710196 := row_all ⟨10,by decide⟩
theorem row11 : safe program 1073742900=true ∧ safe reference 1073742900=true ∧ bitRun program 1073742900=bitRun reference 1073742900 := row_all ⟨11,by decide⟩
theorem row12 : safe program 5368710197=true ∧ safe reference 5368710197=true ∧ bitRun program 5368710197=bitRun reference 5368710197 := row_all ⟨12,by decide⟩
theorem row13 : safe program 1073742901=true ∧ safe reference 1073742901=true ∧ bitRun program 1073742901=bitRun reference 1073742901 := row_all ⟨13,by decide⟩
theorem row14 : safe program 5368710192=true ∧ safe reference 5368710192=true ∧ bitRun program 5368710192=bitRun reference 5368710192 := row_all ⟨14,by decide⟩
theorem row15 : safe program 1073742896=true ∧ safe reference 1073742896=true ∧ bitRun program 1073742896=bitRun reference 1073742896 := row_all ⟨15,by decide⟩
theorem row16 : safe program 5368710193=true ∧ safe reference 5368710193=true ∧ bitRun program 5368710193=bitRun reference 5368710193 := row_all ⟨16,by decide⟩
theorem row17 : safe program 1073742897=true ∧ safe reference 1073742897=true ∧ bitRun program 1073742897=bitRun reference 1073742897 := row_all ⟨17,by decide⟩
theorem row18 : safe program 9663677484=true ∧ safe reference 9663677484=true ∧ bitRun program 9663677484=bitRun reference 9663677484 := row_all ⟨18,by decide⟩
theorem row19 : safe program 1073742892=true ∧ safe reference 1073742892=true ∧ bitRun program 1073742892=bitRun reference 1073742892 := row_all ⟨19,by decide⟩
theorem row20 : safe program 9663677485=true ∧ safe reference 9663677485=true ∧ bitRun program 9663677485=bitRun reference 9663677485 := row_all ⟨20,by decide⟩
theorem row21 : safe program 1073742893=true ∧ safe reference 1073742893=true ∧ bitRun program 1073742893=bitRun reference 1073742893 := row_all ⟨21,by decide⟩
theorem row22 : safe program 9663677480=true ∧ safe reference 9663677480=true ∧ bitRun program 9663677480=bitRun reference 9663677480 := row_all ⟨22,by decide⟩
theorem row23 : safe program 1073742888=true ∧ safe reference 1073742888=true ∧ bitRun program 1073742888=bitRun reference 1073742888 := row_all ⟨23,by decide⟩
theorem row24 : safe program 9663677481=true ∧ safe reference 9663677481=true ∧ bitRun program 9663677481=bitRun reference 9663677481 := row_all ⟨24,by decide⟩
theorem row25 : safe program 1073742889=true ∧ safe reference 1073742889=true ∧ bitRun program 1073742889=bitRun reference 1073742889 := row_all ⟨25,by decide⟩
theorem row26 : safe program 9663677476=true ∧ safe reference 9663677476=true ∧ bitRun program 9663677476=bitRun reference 9663677476 := row_all ⟨26,by decide⟩
theorem row27 : safe program 1073742884=true ∧ safe reference 1073742884=true ∧ bitRun program 1073742884=bitRun reference 1073742884 := row_all ⟨27,by decide⟩
theorem row28 : safe program 9663677477=true ∧ safe reference 9663677477=true ∧ bitRun program 9663677477=bitRun reference 9663677477 := row_all ⟨28,by decide⟩
theorem row29 : safe program 1073742885=true ∧ safe reference 1073742885=true ∧ bitRun program 1073742885=bitRun reference 1073742885 := row_all ⟨29,by decide⟩
theorem row30 : safe program 9663677472=true ∧ safe reference 9663677472=true ∧ bitRun program 9663677472=bitRun reference 9663677472 := row_all ⟨30,by decide⟩
theorem row31 : safe program 1073742880=true ∧ safe reference 1073742880=true ∧ bitRun program 1073742880=bitRun reference 1073742880 := row_all ⟨31,by decide⟩
theorem row32 : safe program 9663677473=true ∧ safe reference 9663677473=true ∧ bitRun program 9663677473=bitRun reference 9663677473 := row_all ⟨32,by decide⟩
theorem row33 : safe program 1073742881=true ∧ safe reference 1073742881=true ∧ bitRun program 1073742881=bitRun reference 1073742881 := row_all ⟨33,by decide⟩
theorem row34 : safe program 18253611100=true ∧ safe reference 18253611100=true ∧ bitRun program 18253611100=bitRun reference 18253611100 := row_all ⟨34,by decide⟩
theorem row35 : safe program 1073741916=true ∧ safe reference 1073741916=true ∧ bitRun program 1073741916=bitRun reference 1073741916 := row_all ⟨35,by decide⟩
theorem row36 : safe program 18253611101=true ∧ safe reference 18253611101=true ∧ bitRun program 18253611101=bitRun reference 18253611101 := row_all ⟨36,by decide⟩
theorem row37 : safe program 1073741917=true ∧ safe reference 1073741917=true ∧ bitRun program 1073741917=bitRun reference 1073741917 := row_all ⟨37,by decide⟩
theorem row38 : safe program 18253611096=true ∧ safe reference 18253611096=true ∧ bitRun program 18253611096=bitRun reference 18253611096 := row_all ⟨38,by decide⟩
theorem row39 : safe program 1073741912=true ∧ safe reference 1073741912=true ∧ bitRun program 1073741912=bitRun reference 1073741912 := row_all ⟨39,by decide⟩
theorem row40 : safe program 18253611097=true ∧ safe reference 18253611097=true ∧ bitRun program 18253611097=bitRun reference 18253611097 := row_all ⟨40,by decide⟩
theorem row41 : safe program 1073741913=true ∧ safe reference 1073741913=true ∧ bitRun program 1073741913=bitRun reference 1073741913 := row_all ⟨41,by decide⟩
theorem row42 : safe program 18253611092=true ∧ safe reference 18253611092=true ∧ bitRun program 18253611092=bitRun reference 18253611092 := row_all ⟨42,by decide⟩
theorem row43 : safe program 1073741908=true ∧ safe reference 1073741908=true ∧ bitRun program 1073741908=bitRun reference 1073741908 := row_all ⟨43,by decide⟩
theorem row44 : safe program 18253611093=true ∧ safe reference 18253611093=true ∧ bitRun program 18253611093=bitRun reference 18253611093 := row_all ⟨44,by decide⟩
theorem row45 : safe program 1073741909=true ∧ safe reference 1073741909=true ∧ bitRun program 1073741909=bitRun reference 1073741909 := row_all ⟨45,by decide⟩
theorem row46 : safe program 18253611088=true ∧ safe reference 18253611088=true ∧ bitRun program 18253611088=bitRun reference 18253611088 := row_all ⟨46,by decide⟩
theorem row47 : safe program 1073741904=true ∧ safe reference 1073741904=true ∧ bitRun program 1073741904=bitRun reference 1073741904 := row_all ⟨47,by decide⟩
theorem row48 : safe program 18253611089=true ∧ safe reference 18253611089=true ∧ bitRun program 18253611089=bitRun reference 18253611089 := row_all ⟨48,by decide⟩
theorem row49 : safe program 1073741905=true ∧ safe reference 1073741905=true ∧ bitRun program 1073741905=bitRun reference 1073741905 := row_all ⟨49,by decide⟩
theorem row50 : safe program 18253611084=true ∧ safe reference 18253611084=true ∧ bitRun program 18253611084=bitRun reference 18253611084 := row_all ⟨50,by decide⟩
theorem row51 : safe program 1073741900=true ∧ safe reference 1073741900=true ∧ bitRun program 1073741900=bitRun reference 1073741900 := row_all ⟨51,by decide⟩
theorem row52 : safe program 18253611085=true ∧ safe reference 18253611085=true ∧ bitRun program 18253611085=bitRun reference 18253611085 := row_all ⟨52,by decide⟩
theorem row53 : safe program 1073741901=true ∧ safe reference 1073741901=true ∧ bitRun program 1073741901=bitRun reference 1073741901 := row_all ⟨53,by decide⟩
theorem row54 : safe program 18253611080=true ∧ safe reference 18253611080=true ∧ bitRun program 18253611080=bitRun reference 18253611080 := row_all ⟨54,by decide⟩
theorem row55 : safe program 1073741896=true ∧ safe reference 1073741896=true ∧ bitRun program 1073741896=bitRun reference 1073741896 := row_all ⟨55,by decide⟩
theorem row56 : safe program 18253611081=true ∧ safe reference 18253611081=true ∧ bitRun program 18253611081=bitRun reference 18253611081 := row_all ⟨56,by decide⟩
theorem row57 : safe program 1073741897=true ∧ safe reference 1073741897=true ∧ bitRun program 1073741897=bitRun reference 1073741897 := row_all ⟨57,by decide⟩
theorem row58 : safe program 18253611076=true ∧ safe reference 18253611076=true ∧ bitRun program 18253611076=bitRun reference 18253611076 := row_all ⟨58,by decide⟩
theorem row59 : safe program 1073741892=true ∧ safe reference 1073741892=true ∧ bitRun program 1073741892=bitRun reference 1073741892 := row_all ⟨59,by decide⟩
theorem row60 : safe program 18253611077=true ∧ safe reference 18253611077=true ∧ bitRun program 18253611077=bitRun reference 18253611077 := row_all ⟨60,by decide⟩
theorem row61 : safe program 1073741893=true ∧ safe reference 1073741893=true ∧ bitRun program 1073741893=bitRun reference 1073741893 := row_all ⟨61,by decide⟩
theorem row62 : safe program 18253611072=true ∧ safe reference 18253611072=true ∧ bitRun program 18253611072=bitRun reference 18253611072 := row_all ⟨62,by decide⟩
theorem row63 : safe program 1073741888=true ∧ safe reference 1073741888=true ∧ bitRun program 1073741888=bitRun reference 1073741888 := row_all ⟨63,by decide⟩
theorem row64 : safe program 18253611073=true ∧ safe reference 18253611073=true ∧ bitRun program 18253611073=bitRun reference 18253611073 := row_all ⟨64,by decide⟩
theorem row65 : safe program 1073741889=true ∧ safe reference 1073741889=true ∧ bitRun program 1073741889=bitRun reference 1073741889 := row_all ⟨65,by decide⟩
theorem row66 : safe program 1082=true ∧ safe reference 1082=true ∧ bitRun program 1082=bitRun reference 1082 := row_all ⟨66,by decide⟩
theorem row67 : safe program 2147484730=true ∧ safe reference 2147484730=true ∧ bitRun program 2147484730=bitRun reference 2147484730 := row_all ⟨67,by decide⟩
theorem row68 : safe program 1083=true ∧ safe reference 1083=true ∧ bitRun program 1083=bitRun reference 1083 := row_all ⟨68,by decide⟩
theorem row69 : safe program 2147484731=true ∧ safe reference 2147484731=true ∧ bitRun program 2147484731=bitRun reference 2147484731 := row_all ⟨69,by decide⟩
theorem row70 : safe program 6442452018=true ∧ safe reference 6442452018=true ∧ bitRun program 6442452018=bitRun reference 6442452018 := row_all ⟨70,by decide⟩
theorem row71 : safe program 2147484722=true ∧ safe reference 2147484722=true ∧ bitRun program 2147484722=bitRun reference 2147484722 := row_all ⟨71,by decide⟩
theorem row72 : safe program 6442452019=true ∧ safe reference 6442452019=true ∧ bitRun program 6442452019=bitRun reference 6442452019 := row_all ⟨72,by decide⟩
theorem row73 : safe program 2147484723=true ∧ safe reference 2147484723=true ∧ bitRun program 2147484723=bitRun reference 2147484723 := row_all ⟨73,by decide⟩
theorem row74 : safe program 10737419306=true ∧ safe reference 10737419306=true ∧ bitRun program 10737419306=bitRun reference 10737419306 := row_all ⟨74,by decide⟩
theorem row75 : safe program 2147484714=true ∧ safe reference 2147484714=true ∧ bitRun program 2147484714=bitRun reference 2147484714 := row_all ⟨75,by decide⟩
theorem row76 : safe program 10737419307=true ∧ safe reference 10737419307=true ∧ bitRun program 10737419307=bitRun reference 10737419307 := row_all ⟨76,by decide⟩
theorem row77 : safe program 2147484715=true ∧ safe reference 2147484715=true ∧ bitRun program 2147484715=bitRun reference 2147484715 := row_all ⟨77,by decide⟩
theorem row78 : safe program 10737419298=true ∧ safe reference 10737419298=true ∧ bitRun program 10737419298=bitRun reference 10737419298 := row_all ⟨78,by decide⟩
theorem row79 : safe program 2147484706=true ∧ safe reference 2147484706=true ∧ bitRun program 2147484706=bitRun reference 2147484706 := row_all ⟨79,by decide⟩
theorem row80 : safe program 10737419299=true ∧ safe reference 10737419299=true ∧ bitRun program 10737419299=bitRun reference 10737419299 := row_all ⟨80,by decide⟩
theorem row81 : safe program 2147484707=true ∧ safe reference 2147484707=true ∧ bitRun program 2147484707=bitRun reference 2147484707 := row_all ⟨81,by decide⟩
theorem row82 : safe program 19327352922=true ∧ safe reference 19327352922=true ∧ bitRun program 19327352922=bitRun reference 19327352922 := row_all ⟨82,by decide⟩
theorem row83 : safe program 2147483738=true ∧ safe reference 2147483738=true ∧ bitRun program 2147483738=bitRun reference 2147483738 := row_all ⟨83,by decide⟩
theorem row84 : safe program 19327352923=true ∧ safe reference 19327352923=true ∧ bitRun program 19327352923=bitRun reference 19327352923 := row_all ⟨84,by decide⟩
theorem row85 : safe program 2147483739=true ∧ safe reference 2147483739=true ∧ bitRun program 2147483739=bitRun reference 2147483739 := row_all ⟨85,by decide⟩
theorem row86 : safe program 19327352914=true ∧ safe reference 19327352914=true ∧ bitRun program 19327352914=bitRun reference 19327352914 := row_all ⟨86,by decide⟩
theorem row87 : safe program 2147483730=true ∧ safe reference 2147483730=true ∧ bitRun program 2147483730=bitRun reference 2147483730 := row_all ⟨87,by decide⟩
theorem row88 : safe program 19327352915=true ∧ safe reference 19327352915=true ∧ bitRun program 19327352915=bitRun reference 19327352915 := row_all ⟨88,by decide⟩
theorem row89 : safe program 2147483731=true ∧ safe reference 2147483731=true ∧ bitRun program 2147483731=bitRun reference 2147483731 := row_all ⟨89,by decide⟩
theorem row90 : safe program 19327352906=true ∧ safe reference 19327352906=true ∧ bitRun program 19327352906=bitRun reference 19327352906 := row_all ⟨90,by decide⟩
theorem row91 : safe program 2147483722=true ∧ safe reference 2147483722=true ∧ bitRun program 2147483722=bitRun reference 2147483722 := row_all ⟨91,by decide⟩
theorem row92 : safe program 19327352907=true ∧ safe reference 19327352907=true ∧ bitRun program 19327352907=bitRun reference 19327352907 := row_all ⟨92,by decide⟩
theorem row93 : safe program 2147483723=true ∧ safe reference 2147483723=true ∧ bitRun program 2147483723=bitRun reference 2147483723 := row_all ⟨93,by decide⟩
theorem row94 : safe program 19327352898=true ∧ safe reference 19327352898=true ∧ bitRun program 19327352898=bitRun reference 19327352898 := row_all ⟨94,by decide⟩
theorem row95 : safe program 2147483714=true ∧ safe reference 2147483714=true ∧ bitRun program 2147483714=bitRun reference 2147483714 := row_all ⟨95,by decide⟩
theorem row96 : safe program 19327352899=true ∧ safe reference 19327352899=true ∧ bitRun program 19327352899=bitRun reference 19327352899 := row_all ⟨96,by decide⟩
theorem row97 : safe program 2147483715=true ∧ safe reference 2147483715=true ∧ bitRun program 2147483715=bitRun reference 2147483715 := row_all ⟨97,by decide⟩
theorem row98 : safe program 1080=true ∧ safe reference 1080=true ∧ bitRun program 1080=bitRun reference 1080 := row_all ⟨98,by decide⟩
theorem row99 : safe program 2147484728=true ∧ safe reference 2147484728=true ∧ bitRun program 2147484728=bitRun reference 2147484728 := row_all ⟨99,by decide⟩
theorem row100 : safe program 1081=true ∧ safe reference 1081=true ∧ bitRun program 1081=bitRun reference 1081 := row_all ⟨100,by decide⟩
theorem row101 : safe program 2147484729=true ∧ safe reference 2147484729=true ∧ bitRun program 2147484729=bitRun reference 2147484729 := row_all ⟨101,by decide⟩
theorem row102 : safe program 3221226544=true ∧ safe reference 3221226544=true ∧ bitRun program 3221226544=bitRun reference 3221226544 := row_all ⟨102,by decide⟩
theorem row103 : safe program 7516193840=true ∧ safe reference 7516193840=true ∧ bitRun program 7516193840=bitRun reference 7516193840 := row_all ⟨103,by decide⟩
theorem row104 : safe program 3221226545=true ∧ safe reference 3221226545=true ∧ bitRun program 3221226545=bitRun reference 3221226545 := row_all ⟨104,by decide⟩
theorem row105 : safe program 7516193841=true ∧ safe reference 7516193841=true ∧ bitRun program 7516193841=bitRun reference 7516193841 := row_all ⟨105,by decide⟩
theorem row106 : safe program 5368710180=true ∧ safe reference 5368710180=true ∧ bitRun program 5368710180=bitRun reference 5368710180 := row_all ⟨106,by decide⟩
theorem row107 : safe program 13958644772=true ∧ safe reference 13958644772=true ∧ bitRun program 13958644772=bitRun reference 13958644772 := row_all ⟨107,by decide⟩
theorem row108 : safe program 5368710181=true ∧ safe reference 5368710181=true ∧ bitRun program 5368710181=bitRun reference 5368710181 := row_all ⟨108,by decide⟩
theorem row109 : safe program 13958644773=true ∧ safe reference 13958644773=true ∧ bitRun program 13958644773=bitRun reference 13958644773 := row_all ⟨109,by decide⟩
theorem row110 : safe program 9663676492=true ∧ safe reference 9663676492=true ∧ bitRun program 9663676492=bitRun reference 9663676492 := row_all ⟨110,by decide⟩
theorem row111 : safe program 26843545676=true ∧ safe reference 26843545676=true ∧ bitRun program 26843545676=bitRun reference 26843545676 := row_all ⟨111,by decide⟩
theorem row112 : safe program 9663676493=true ∧ safe reference 9663676493=true ∧ bitRun program 9663676493=bitRun reference 9663676493 := row_all ⟨112,by decide⟩
theorem row113 : safe program 26843545677=true ∧ safe reference 26843545677=true ∧ bitRun program 26843545677=bitRun reference 26843545677 := row_all ⟨113,by decide⟩
theorem row114 : safe program 5368710176=true ∧ safe reference 5368710176=true ∧ bitRun program 5368710176=bitRun reference 5368710176 := row_all ⟨114,by decide⟩
theorem row115 : safe program 13958644768=true ∧ safe reference 13958644768=true ∧ bitRun program 13958644768=bitRun reference 13958644768 := row_all ⟨115,by decide⟩
theorem row116 : safe program 5368710177=true ∧ safe reference 5368710177=true ∧ bitRun program 5368710177=bitRun reference 5368710177 := row_all ⟨116,by decide⟩
theorem row117 : safe program 13958644769=true ∧ safe reference 13958644769=true ∧ bitRun program 13958644769=bitRun reference 13958644769 := row_all ⟨117,by decide⟩
theorem row118 : safe program 1078=true ∧ safe reference 1078=true ∧ bitRun program 1078=bitRun reference 1078 := row_all ⟨118,by decide⟩
theorem row119 : safe program 4294968374=true ∧ safe reference 4294968374=true ∧ bitRun program 4294968374=bitRun reference 4294968374 := row_all ⟨119,by decide⟩
theorem row120 : safe program 1079=true ∧ safe reference 1079=true ∧ bitRun program 1079=bitRun reference 1079 := row_all ⟨120,by decide⟩
theorem row121 : safe program 4294968375=true ∧ safe reference 4294968375=true ∧ bitRun program 4294968375=bitRun reference 4294968375 := row_all ⟨121,by decide⟩
theorem row122 : safe program 12884902950=true ∧ safe reference 12884902950=true ∧ bitRun program 12884902950=bitRun reference 12884902950 := row_all ⟨122,by decide⟩
theorem row123 : safe program 4294968358=true ∧ safe reference 4294968358=true ∧ bitRun program 4294968358=bitRun reference 4294968358 := row_all ⟨123,by decide⟩
theorem row124 : safe program 12884902951=true ∧ safe reference 12884902951=true ∧ bitRun program 12884902951=bitRun reference 12884902951 := row_all ⟨124,by decide⟩
theorem row125 : safe program 4294968359=true ∧ safe reference 4294968359=true ∧ bitRun program 4294968359=bitRun reference 4294968359 := row_all ⟨125,by decide⟩
theorem row126 : safe program 21474836566=true ∧ safe reference 21474836566=true ∧ bitRun program 21474836566=bitRun reference 21474836566 := row_all ⟨126,by decide⟩
theorem row127 : safe program 4294967382=true ∧ safe reference 4294967382=true ∧ bitRun program 4294967382=bitRun reference 4294967382 := row_all ⟨127,by decide⟩
theorem row128 : safe program 21474836567=true ∧ safe reference 21474836567=true ∧ bitRun program 21474836567=bitRun reference 21474836567 := row_all ⟨128,by decide⟩
theorem row129 : safe program 4294967383=true ∧ safe reference 4294967383=true ∧ bitRun program 4294967383=bitRun reference 4294967383 := row_all ⟨129,by decide⟩
theorem row130 : safe program 21474836550=true ∧ safe reference 21474836550=true ∧ bitRun program 21474836550=bitRun reference 21474836550 := row_all ⟨130,by decide⟩
theorem row131 : safe program 4294967366=true ∧ safe reference 4294967366=true ∧ bitRun program 4294967366=bitRun reference 4294967366 := row_all ⟨131,by decide⟩
theorem row132 : safe program 21474836551=true ∧ safe reference 21474836551=true ∧ bitRun program 21474836551=bitRun reference 21474836551 := row_all ⟨132,by decide⟩
theorem row133 : safe program 4294967367=true ∧ safe reference 4294967367=true ∧ bitRun program 4294967367=bitRun reference 4294967367 := row_all ⟨133,by decide⟩
theorem row134 : safe program 1076=true ∧ safe reference 1076=true ∧ bitRun program 1076=bitRun reference 1076 := row_all ⟨134,by decide⟩
theorem row135 : safe program 4294968372=true ∧ safe reference 4294968372=true ∧ bitRun program 4294968372=bitRun reference 4294968372 := row_all ⟨135,by decide⟩
theorem row136 : safe program 1077=true ∧ safe reference 1077=true ∧ bitRun program 1077=bitRun reference 1077 := row_all ⟨136,by decide⟩
theorem row137 : safe program 4294968373=true ∧ safe reference 4294968373=true ∧ bitRun program 4294968373=bitRun reference 4294968373 := row_all ⟨137,by decide⟩
theorem row138 : safe program 6442452016=true ∧ safe reference 6442452016=true ∧ bitRun program 6442452016=bitRun reference 6442452016 := row_all ⟨138,by decide⟩
theorem row139 : safe program 2147484720=true ∧ safe reference 2147484720=true ∧ bitRun program 2147484720=bitRun reference 2147484720 := row_all ⟨139,by decide⟩
theorem row140 : safe program 6442452017=true ∧ safe reference 6442452017=true ∧ bitRun program 6442452017=bitRun reference 6442452017 := row_all ⟨140,by decide⟩
theorem row141 : safe program 2147484721=true ∧ safe reference 2147484721=true ∧ bitRun program 2147484721=bitRun reference 2147484721 := row_all ⟨141,by decide⟩
theorem row142 : safe program 3221226536=true ∧ safe reference 3221226536=true ∧ bitRun program 3221226536=bitRun reference 3221226536 := row_all ⟨142,by decide⟩
theorem row143 : safe program 11811161128=true ∧ safe reference 11811161128=true ∧ bitRun program 11811161128=bitRun reference 11811161128 := row_all ⟨143,by decide⟩
theorem row144 : safe program 3221226537=true ∧ safe reference 3221226537=true ∧ bitRun program 3221226537=bitRun reference 3221226537 := row_all ⟨144,by decide⟩
theorem row145 : safe program 11811161129=true ∧ safe reference 11811161129=true ∧ bitRun program 11811161129=bitRun reference 11811161129 := row_all ⟨145,by decide⟩
theorem row146 : safe program 1074=true ∧ safe reference 1074=true ∧ bitRun program 1074=bitRun reference 1074 := row_all ⟨146,by decide⟩
theorem row147 : safe program 4294968370=true ∧ safe reference 4294968370=true ∧ bitRun program 4294968370=bitRun reference 4294968370 := row_all ⟨147,by decide⟩
theorem row148 : safe program 1075=true ∧ safe reference 1075=true ∧ bitRun program 1075=bitRun reference 1075 := row_all ⟨148,by decide⟩
theorem row149 : safe program 4294968371=true ∧ safe reference 4294968371=true ∧ bitRun program 4294968371=bitRun reference 4294968371 := row_all ⟨149,by decide⟩
theorem row150 : safe program 6442452002=true ∧ safe reference 6442452002=true ∧ bitRun program 6442452002=bitRun reference 6442452002 := row_all ⟨150,by decide⟩
theorem row151 : safe program 15032386594=true ∧ safe reference 15032386594=true ∧ bitRun program 15032386594=bitRun reference 15032386594 := row_all ⟨151,by decide⟩
theorem row152 : safe program 6442452003=true ∧ safe reference 6442452003=true ∧ bitRun program 6442452003=bitRun reference 6442452003 := row_all ⟨152,by decide⟩
theorem row153 : safe program 15032386595=true ∧ safe reference 15032386595=true ∧ bitRun program 15032386595=bitRun reference 15032386595 := row_all ⟨153,by decide⟩
theorem row154 : safe program 10737418314=true ∧ safe reference 10737418314=true ∧ bitRun program 10737418314=bitRun reference 10737418314 := row_all ⟨154,by decide⟩
theorem row155 : safe program 27917287498=true ∧ safe reference 27917287498=true ∧ bitRun program 27917287498=bitRun reference 27917287498 := row_all ⟨155,by decide⟩
theorem row156 : safe program 10737418315=true ∧ safe reference 10737418315=true ∧ bitRun program 10737418315=bitRun reference 10737418315 := row_all ⟨156,by decide⟩
theorem row157 : safe program 27917287499=true ∧ safe reference 27917287499=true ∧ bitRun program 27917287499=bitRun reference 27917287499 := row_all ⟨157,by decide⟩
theorem row158 : safe program 1072=true ∧ safe reference 1072=true ∧ bitRun program 1072=bitRun reference 1072 := row_all ⟨158,by decide⟩
theorem row159 : safe program 4294968368=true ∧ safe reference 4294968368=true ∧ bitRun program 4294968368=bitRun reference 4294968368 := row_all ⟨159,by decide⟩
theorem row160 : safe program 1073=true ∧ safe reference 1073=true ∧ bitRun program 1073=bitRun reference 1073 := row_all ⟨160,by decide⟩
theorem row161 : safe program 4294968369=true ∧ safe reference 4294968369=true ∧ bitRun program 4294968369=bitRun reference 4294968369 := row_all ⟨161,by decide⟩
theorem row162 : safe program 12884902948=true ∧ safe reference 12884902948=true ∧ bitRun program 12884902948=bitRun reference 12884902948 := row_all ⟨162,by decide⟩
theorem row163 : safe program 4294968356=true ∧ safe reference 4294968356=true ∧ bitRun program 4294968356=bitRun reference 4294968356 := row_all ⟨163,by decide⟩
theorem row164 : safe program 12884902949=true ∧ safe reference 12884902949=true ∧ bitRun program 12884902949=bitRun reference 12884902949 := row_all ⟨164,by decide⟩
theorem row165 : safe program 4294968357=true ∧ safe reference 4294968357=true ∧ bitRun program 4294968357=bitRun reference 4294968357 := row_all ⟨165,by decide⟩
theorem row166 : safe program 10737419304=true ∧ safe reference 10737419304=true ∧ bitRun program 10737419304=bitRun reference 10737419304 := row_all ⟨166,by decide⟩
theorem row167 : safe program 2147484712=true ∧ safe reference 2147484712=true ∧ bitRun program 2147484712=bitRun reference 2147484712 := row_all ⟨167,by decide⟩
theorem row168 : safe program 10737419305=true ∧ safe reference 10737419305=true ∧ bitRun program 10737419305=bitRun reference 10737419305 := row_all ⟨168,by decide⟩
theorem row169 : safe program 2147484713=true ∧ safe reference 2147484713=true ∧ bitRun program 2147484713=bitRun reference 2147484713 := row_all ⟨169,by decide⟩
theorem row170 : safe program 1070=true ∧ safe reference 1070=true ∧ bitRun program 1070=bitRun reference 1070 := row_all ⟨170,by decide⟩
theorem row171 : safe program 8589935662=true ∧ safe reference 8589935662=true ∧ bitRun program 8589935662=bitRun reference 8589935662 := row_all ⟨171,by decide⟩
theorem row172 : safe program 1071=true ∧ safe reference 1071=true ∧ bitRun program 1071=bitRun reference 1071 := row_all ⟨172,by decide⟩
theorem row173 : safe program 8589935663=true ∧ safe reference 8589935663=true ∧ bitRun program 8589935663=bitRun reference 8589935663 := row_all ⟨173,by decide⟩
theorem row174 : safe program 25769803854=true ∧ safe reference 25769803854=true ∧ bitRun program 25769803854=bitRun reference 25769803854 := row_all ⟨174,by decide⟩
theorem row175 : safe program 8589934670=true ∧ safe reference 8589934670=true ∧ bitRun program 8589934670=bitRun reference 8589934670 := row_all ⟨175,by decide⟩
theorem row176 : safe program 25769803855=true ∧ safe reference 25769803855=true ∧ bitRun program 25769803855=bitRun reference 25769803855 := row_all ⟨176,by decide⟩
theorem row177 : safe program 8589934671=true ∧ safe reference 8589934671=true ∧ bitRun program 8589934671=bitRun reference 8589934671 := row_all ⟨177,by decide⟩
theorem row178 : safe program 1068=true ∧ safe reference 1068=true ∧ bitRun program 1068=bitRun reference 1068 := row_all ⟨178,by decide⟩
theorem row179 : safe program 8589935660=true ∧ safe reference 8589935660=true ∧ bitRun program 8589935660=bitRun reference 8589935660 := row_all ⟨179,by decide⟩
theorem row180 : safe program 1069=true ∧ safe reference 1069=true ∧ bitRun program 1069=bitRun reference 1069 := row_all ⟨180,by decide⟩
theorem row181 : safe program 8589935661=true ∧ safe reference 8589935661=true ∧ bitRun program 8589935661=bitRun reference 8589935661 := row_all ⟨181,by decide⟩
theorem row182 : safe program 1066=true ∧ safe reference 1066=true ∧ bitRun program 1066=bitRun reference 1066 := row_all ⟨182,by decide⟩
theorem row183 : safe program 8589935658=true ∧ safe reference 8589935658=true ∧ bitRun program 8589935658=bitRun reference 8589935658 := row_all ⟨183,by decide⟩
theorem row184 : safe program 1067=true ∧ safe reference 1067=true ∧ bitRun program 1067=bitRun reference 1067 := row_all ⟨184,by decide⟩
theorem row185 : safe program 8589935659=true ∧ safe reference 8589935659=true ∧ bitRun program 8589935659=bitRun reference 8589935659 := row_all ⟨185,by decide⟩
theorem row186 : safe program 12884902946=true ∧ safe reference 12884902946=true ∧ bitRun program 12884902946=bitRun reference 12884902946 := row_all ⟨186,by decide⟩
theorem row187 : safe program 4294968354=true ∧ safe reference 4294968354=true ∧ bitRun program 4294968354=bitRun reference 4294968354 := row_all ⟨187,by decide⟩
theorem row188 : safe program 12884902947=true ∧ safe reference 12884902947=true ∧ bitRun program 12884902947=bitRun reference 12884902947 := row_all ⟨188,by decide⟩
theorem row189 : safe program 4294968355=true ∧ safe reference 4294968355=true ∧ bitRun program 4294968355=bitRun reference 4294968355 := row_all ⟨189,by decide⟩
theorem row190 : safe program 1064=true ∧ safe reference 1064=true ∧ bitRun program 1064=bitRun reference 1064 := row_all ⟨190,by decide⟩
theorem row191 : safe program 8589935656=true ∧ safe reference 8589935656=true ∧ bitRun program 8589935656=bitRun reference 8589935656 := row_all ⟨191,by decide⟩
theorem row192 : safe program 1065=true ∧ safe reference 1065=true ∧ bitRun program 1065=bitRun reference 1065 := row_all ⟨192,by decide⟩
theorem row193 : safe program 8589935657=true ∧ safe reference 8589935657=true ∧ bitRun program 8589935657=bitRun reference 8589935657 := row_all ⟨193,by decide⟩
theorem row194 : safe program 25769803852=true ∧ safe reference 25769803852=true ∧ bitRun program 25769803852=bitRun reference 25769803852 := row_all ⟨194,by decide⟩
theorem row195 : safe program 8589934668=true ∧ safe reference 8589934668=true ∧ bitRun program 8589934668=bitRun reference 8589934668 := row_all ⟨195,by decide⟩
theorem row196 : safe program 25769803853=true ∧ safe reference 25769803853=true ∧ bitRun program 25769803853=bitRun reference 25769803853 := row_all ⟨196,by decide⟩
theorem row197 : safe program 8589934669=true ∧ safe reference 8589934669=true ∧ bitRun program 8589934669=bitRun reference 8589934669 := row_all ⟨197,by decide⟩
theorem row198 : safe program 1062=true ∧ safe reference 1062=true ∧ bitRun program 1062=bitRun reference 1062 := row_all ⟨198,by decide⟩
theorem row199 : safe program 8589935654=true ∧ safe reference 8589935654=true ∧ bitRun program 8589935654=bitRun reference 8589935654 := row_all ⟨199,by decide⟩
theorem row200 : safe program 1063=true ∧ safe reference 1063=true ∧ bitRun program 1063=bitRun reference 1063 := row_all ⟨200,by decide⟩
theorem row201 : safe program 8589935655=true ∧ safe reference 8589935655=true ∧ bitRun program 8589935655=bitRun reference 8589935655 := row_all ⟨201,by decide⟩
theorem row202 : safe program 1060=true ∧ safe reference 1060=true ∧ bitRun program 1060=bitRun reference 1060 := row_all ⟨202,by decide⟩
theorem row203 : safe program 8589935652=true ∧ safe reference 8589935652=true ∧ bitRun program 8589935652=bitRun reference 8589935652 := row_all ⟨203,by decide⟩
theorem row204 : safe program 1061=true ∧ safe reference 1061=true ∧ bitRun program 1061=bitRun reference 1061 := row_all ⟨204,by decide⟩
theorem row205 : safe program 8589935653=true ∧ safe reference 8589935653=true ∧ bitRun program 8589935653=bitRun reference 8589935653 := row_all ⟨205,by decide⟩
theorem row206 : safe program 12884902944=true ∧ safe reference 12884902944=true ∧ bitRun program 12884902944=bitRun reference 12884902944 := row_all ⟨206,by decide⟩
theorem row207 : safe program 4294968352=true ∧ safe reference 4294968352=true ∧ bitRun program 4294968352=bitRun reference 4294968352 := row_all ⟨207,by decide⟩
theorem row208 : safe program 12884902945=true ∧ safe reference 12884902945=true ∧ bitRun program 12884902945=bitRun reference 12884902945 := row_all ⟨208,by decide⟩
theorem row209 : safe program 4294968353=true ∧ safe reference 4294968353=true ∧ bitRun program 4294968353=bitRun reference 4294968353 := row_all ⟨209,by decide⟩
theorem row210 : safe program 1058=true ∧ safe reference 1058=true ∧ bitRun program 1058=bitRun reference 1058 := row_all ⟨210,by decide⟩
theorem row211 : safe program 8589935650=true ∧ safe reference 8589935650=true ∧ bitRun program 8589935650=bitRun reference 8589935650 := row_all ⟨211,by decide⟩
theorem row212 : safe program 1059=true ∧ safe reference 1059=true ∧ bitRun program 1059=bitRun reference 1059 := row_all ⟨212,by decide⟩
theorem row213 : safe program 8589935651=true ∧ safe reference 8589935651=true ∧ bitRun program 8589935651=bitRun reference 8589935651 := row_all ⟨213,by decide⟩
theorem row214 : safe program 25769803850=true ∧ safe reference 25769803850=true ∧ bitRun program 25769803850=bitRun reference 25769803850 := row_all ⟨214,by decide⟩
theorem row215 : safe program 8589934666=true ∧ safe reference 8589934666=true ∧ bitRun program 8589934666=bitRun reference 8589934666 := row_all ⟨215,by decide⟩
theorem row216 : safe program 25769803851=true ∧ safe reference 25769803851=true ∧ bitRun program 25769803851=bitRun reference 25769803851 := row_all ⟨216,by decide⟩
theorem row217 : safe program 8589934667=true ∧ safe reference 8589934667=true ∧ bitRun program 8589934667=bitRun reference 8589934667 := row_all ⟨217,by decide⟩
theorem row218 : safe program 1056=true ∧ safe reference 1056=true ∧ bitRun program 1056=bitRun reference 1056 := row_all ⟨218,by decide⟩
theorem row219 : safe program 8589935648=true ∧ safe reference 8589935648=true ∧ bitRun program 8589935648=bitRun reference 8589935648 := row_all ⟨219,by decide⟩
theorem row220 : safe program 1057=true ∧ safe reference 1057=true ∧ bitRun program 1057=bitRun reference 1057 := row_all ⟨220,by decide⟩
theorem row221 : safe program 8589935649=true ∧ safe reference 8589935649=true ∧ bitRun program 8589935649=bitRun reference 8589935649 := row_all ⟨221,by decide⟩
theorem row222 : safe program 94=true ∧ safe reference 94=true ∧ bitRun program 94=bitRun reference 94 := row_all ⟨222,by decide⟩
theorem row223 : safe program 17179869278=true ∧ safe reference 17179869278=true ∧ bitRun program 17179869278=bitRun reference 17179869278 := row_all ⟨223,by decide⟩
theorem row224 : safe program 95=true ∧ safe reference 95=true ∧ bitRun program 95=bitRun reference 95 := row_all ⟨224,by decide⟩
theorem row225 : safe program 17179869279=true ∧ safe reference 17179869279=true ∧ bitRun program 17179869279=bitRun reference 17179869279 := row_all ⟨225,by decide⟩
theorem row226 : safe program 92=true ∧ safe reference 92=true ∧ bitRun program 92=bitRun reference 92 := row_all ⟨226,by decide⟩
theorem row227 : safe program 17179869276=true ∧ safe reference 17179869276=true ∧ bitRun program 17179869276=bitRun reference 17179869276 := row_all ⟨227,by decide⟩
theorem row228 : safe program 93=true ∧ safe reference 93=true ∧ bitRun program 93=bitRun reference 93 := row_all ⟨228,by decide⟩
theorem row229 : safe program 17179869277=true ∧ safe reference 17179869277=true ∧ bitRun program 17179869277=bitRun reference 17179869277 := row_all ⟨229,by decide⟩
theorem row230 : safe program 90=true ∧ safe reference 90=true ∧ bitRun program 90=bitRun reference 90 := row_all ⟨230,by decide⟩
theorem row231 : safe program 17179869274=true ∧ safe reference 17179869274=true ∧ bitRun program 17179869274=bitRun reference 17179869274 := row_all ⟨231,by decide⟩
theorem row232 : safe program 91=true ∧ safe reference 91=true ∧ bitRun program 91=bitRun reference 91 := row_all ⟨232,by decide⟩
theorem row233 : safe program 17179869275=true ∧ safe reference 17179869275=true ∧ bitRun program 17179869275=bitRun reference 17179869275 := row_all ⟨233,by decide⟩
theorem row234 : safe program 88=true ∧ safe reference 88=true ∧ bitRun program 88=bitRun reference 88 := row_all ⟨234,by decide⟩
theorem row235 : safe program 17179869272=true ∧ safe reference 17179869272=true ∧ bitRun program 17179869272=bitRun reference 17179869272 := row_all ⟨235,by decide⟩
theorem row236 : safe program 89=true ∧ safe reference 89=true ∧ bitRun program 89=bitRun reference 89 := row_all ⟨236,by decide⟩
theorem row237 : safe program 17179869273=true ∧ safe reference 17179869273=true ∧ bitRun program 17179869273=bitRun reference 17179869273 := row_all ⟨237,by decide⟩
theorem row238 : safe program 86=true ∧ safe reference 86=true ∧ bitRun program 86=bitRun reference 86 := row_all ⟨238,by decide⟩
theorem row239 : safe program 17179869270=true ∧ safe reference 17179869270=true ∧ bitRun program 17179869270=bitRun reference 17179869270 := row_all ⟨239,by decide⟩
theorem row240 : safe program 87=true ∧ safe reference 87=true ∧ bitRun program 87=bitRun reference 87 := row_all ⟨240,by decide⟩
theorem row241 : safe program 17179869271=true ∧ safe reference 17179869271=true ∧ bitRun program 17179869271=bitRun reference 17179869271 := row_all ⟨241,by decide⟩
theorem row242 : safe program 84=true ∧ safe reference 84=true ∧ bitRun program 84=bitRun reference 84 := row_all ⟨242,by decide⟩
theorem row243 : safe program 17179869268=true ∧ safe reference 17179869268=true ∧ bitRun program 17179869268=bitRun reference 17179869268 := row_all ⟨243,by decide⟩
theorem row244 : safe program 85=true ∧ safe reference 85=true ∧ bitRun program 85=bitRun reference 85 := row_all ⟨244,by decide⟩
theorem row245 : safe program 17179869269=true ∧ safe reference 17179869269=true ∧ bitRun program 17179869269=bitRun reference 17179869269 := row_all ⟨245,by decide⟩
theorem row246 : safe program 82=true ∧ safe reference 82=true ∧ bitRun program 82=bitRun reference 82 := row_all ⟨246,by decide⟩
theorem row247 : safe program 17179869266=true ∧ safe reference 17179869266=true ∧ bitRun program 17179869266=bitRun reference 17179869266 := row_all ⟨247,by decide⟩
theorem row248 : safe program 83=true ∧ safe reference 83=true ∧ bitRun program 83=bitRun reference 83 := row_all ⟨248,by decide⟩
theorem row249 : safe program 17179869267=true ∧ safe reference 17179869267=true ∧ bitRun program 17179869267=bitRun reference 17179869267 := row_all ⟨249,by decide⟩
theorem row250 : safe program 80=true ∧ safe reference 80=true ∧ bitRun program 80=bitRun reference 80 := row_all ⟨250,by decide⟩
theorem row251 : safe program 17179869264=true ∧ safe reference 17179869264=true ∧ bitRun program 17179869264=bitRun reference 17179869264 := row_all ⟨251,by decide⟩
theorem row252 : safe program 81=true ∧ safe reference 81=true ∧ bitRun program 81=bitRun reference 81 := row_all ⟨252,by decide⟩
theorem row253 : safe program 17179869265=true ∧ safe reference 17179869265=true ∧ bitRun program 17179869265=bitRun reference 17179869265 := row_all ⟨253,by decide⟩
theorem row254 : safe program 78=true ∧ safe reference 78=true ∧ bitRun program 78=bitRun reference 78 := row_all ⟨254,by decide⟩
theorem row255 : safe program 17179869262=true ∧ safe reference 17179869262=true ∧ bitRun program 17179869262=bitRun reference 17179869262 := row_all ⟨255,by decide⟩
theorem row256 : safe program 79=true ∧ safe reference 79=true ∧ bitRun program 79=bitRun reference 79 := row_all ⟨256,by decide⟩
theorem row257 : safe program 17179869263=true ∧ safe reference 17179869263=true ∧ bitRun program 17179869263=bitRun reference 17179869263 := row_all ⟨257,by decide⟩
theorem row258 : safe program 76=true ∧ safe reference 76=true ∧ bitRun program 76=bitRun reference 76 := row_all ⟨258,by decide⟩
theorem row259 : safe program 17179869260=true ∧ safe reference 17179869260=true ∧ bitRun program 17179869260=bitRun reference 17179869260 := row_all ⟨259,by decide⟩
theorem row260 : safe program 77=true ∧ safe reference 77=true ∧ bitRun program 77=bitRun reference 77 := row_all ⟨260,by decide⟩
theorem row261 : safe program 17179869261=true ∧ safe reference 17179869261=true ∧ bitRun program 17179869261=bitRun reference 17179869261 := row_all ⟨261,by decide⟩
theorem row262 : safe program 74=true ∧ safe reference 74=true ∧ bitRun program 74=bitRun reference 74 := row_all ⟨262,by decide⟩
theorem row263 : safe program 17179869258=true ∧ safe reference 17179869258=true ∧ bitRun program 17179869258=bitRun reference 17179869258 := row_all ⟨263,by decide⟩
theorem row264 : safe program 75=true ∧ safe reference 75=true ∧ bitRun program 75=bitRun reference 75 := row_all ⟨264,by decide⟩
theorem row265 : safe program 17179869259=true ∧ safe reference 17179869259=true ∧ bitRun program 17179869259=bitRun reference 17179869259 := row_all ⟨265,by decide⟩
theorem row266 : safe program 72=true ∧ safe reference 72=true ∧ bitRun program 72=bitRun reference 72 := row_all ⟨266,by decide⟩
theorem row267 : safe program 17179869256=true ∧ safe reference 17179869256=true ∧ bitRun program 17179869256=bitRun reference 17179869256 := row_all ⟨267,by decide⟩
theorem row268 : safe program 73=true ∧ safe reference 73=true ∧ bitRun program 73=bitRun reference 73 := row_all ⟨268,by decide⟩
theorem row269 : safe program 17179869257=true ∧ safe reference 17179869257=true ∧ bitRun program 17179869257=bitRun reference 17179869257 := row_all ⟨269,by decide⟩
theorem row270 : safe program 70=true ∧ safe reference 70=true ∧ bitRun program 70=bitRun reference 70 := row_all ⟨270,by decide⟩
theorem row271 : safe program 17179869254=true ∧ safe reference 17179869254=true ∧ bitRun program 17179869254=bitRun reference 17179869254 := row_all ⟨271,by decide⟩
theorem row272 : safe program 71=true ∧ safe reference 71=true ∧ bitRun program 71=bitRun reference 71 := row_all ⟨272,by decide⟩
theorem row273 : safe program 17179869255=true ∧ safe reference 17179869255=true ∧ bitRun program 17179869255=bitRun reference 17179869255 := row_all ⟨273,by decide⟩
theorem row274 : safe program 68=true ∧ safe reference 68=true ∧ bitRun program 68=bitRun reference 68 := row_all ⟨274,by decide⟩
theorem row275 : safe program 17179869252=true ∧ safe reference 17179869252=true ∧ bitRun program 17179869252=bitRun reference 17179869252 := row_all ⟨275,by decide⟩
theorem row276 : safe program 69=true ∧ safe reference 69=true ∧ bitRun program 69=bitRun reference 69 := row_all ⟨276,by decide⟩
theorem row277 : safe program 17179869253=true ∧ safe reference 17179869253=true ∧ bitRun program 17179869253=bitRun reference 17179869253 := row_all ⟨277,by decide⟩
theorem row278 : safe program 66=true ∧ safe reference 66=true ∧ bitRun program 66=bitRun reference 66 := row_all ⟨278,by decide⟩
theorem row279 : safe program 17179869250=true ∧ safe reference 17179869250=true ∧ bitRun program 17179869250=bitRun reference 17179869250 := row_all ⟨279,by decide⟩
theorem row280 : safe program 67=true ∧ safe reference 67=true ∧ bitRun program 67=bitRun reference 67 := row_all ⟨280,by decide⟩
theorem row281 : safe program 17179869251=true ∧ safe reference 17179869251=true ∧ bitRun program 17179869251=bitRun reference 17179869251 := row_all ⟨281,by decide⟩
theorem row282 : safe program 64=true ∧ safe reference 64=true ∧ bitRun program 64=bitRun reference 64 := row_all ⟨282,by decide⟩
theorem row283 : safe program 17179869248=true ∧ safe reference 17179869248=true ∧ bitRun program 17179869248=bitRun reference 17179869248 := row_all ⟨283,by decide⟩
theorem row284 : safe program 65=true ∧ safe reference 65=true ∧ bitRun program 65=bitRun reference 65 := row_all ⟨284,by decide⟩
theorem row285 : safe program 17179869249=true ∧ safe reference 17179869249=true ∧ bitRun program 17179869249=bitRun reference 17179869249 := row_all ⟨285,by decide⟩

end ECDSAAdd.Entrant.TerminalInverse23

end

-- Adapted public peer module: TerminalSafeEq
section

namespace ECDSAAdd.Entrant.TerminalSafeEq
open ECDSAAdd Arithmetic MeasuredCodec5
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run

theorem of_law (P Q : Program) (v : Nat)
    (law : safe P v=true ∧ safe Q v=true ∧ bitRun P v=bitRun Q v) (m n : List Bool) :
    run P m ⟨false,bitsOf v⟩=run Q n ⟨false,bitsOf v⟩ := by
  rw [run_sim,run_sim,sim_safe _ _ law.1,sim_safe _ _ law.2.1,law.2.2]

end ECDSAAdd.Entrant.TerminalSafeEq

end

-- Adapted public peer module: TerminalFiveRows
section

namespace ECDSAAdd.Entrant.TerminalFiveRows
open ECDSAAdd Arithmetic MeasuredCodec5
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run safe bitRun TerminalInverse23.program TerminalInverse23.reference

def rowInputs : List Nat := [1086, 1087, 1084, 1073742908, 1085, 1073742909, 3221226552, 1073742904, 3221226553, 1073742905, 5368710196, 1073742900, 5368710197, 1073742901, 5368710192, 1073742896, 5368710193, 1073742897, 9663677484, 1073742892, 9663677485, 1073742893, 9663677480, 1073742888, 9663677481, 1073742889, 9663677476, 1073742884, 9663677477, 1073742885, 9663677472, 1073742880, 9663677473, 1073742881, 18253611100, 1073741916, 18253611101, 1073741917, 18253611096, 1073741912, 18253611097, 1073741913, 18253611092, 1073741908, 18253611093, 1073741909, 18253611088, 1073741904, 18253611089, 1073741905, 18253611084, 1073741900, 18253611085, 1073741901, 18253611080, 1073741896, 18253611081, 1073741897, 18253611076, 1073741892, 18253611077, 1073741893, 18253611072, 1073741888, 18253611073, 1073741889, 1082, 2147484730, 1083, 2147484731, 6442452018, 2147484722, 6442452019, 2147484723, 10737419306, 2147484714, 10737419307, 2147484715, 10737419298, 2147484706, 10737419299, 2147484707, 19327352922, 2147483738, 19327352923, 2147483739, 19327352914, 2147483730, 19327352915, 2147483731, 19327352906, 2147483722, 19327352907, 2147483723, 19327352898, 2147483714, 19327352899, 2147483715, 1080, 2147484728, 1081, 2147484729, 3221226544, 7516193840, 3221226545, 7516193841, 5368710180, 13958644772, 5368710181, 13958644773, 9663676492, 26843545676, 9663676493, 26843545677, 5368710176, 13958644768, 5368710177, 13958644769, 1078, 4294968374, 1079, 4294968375, 12884902950, 4294968358, 12884902951, 4294968359, 21474836566, 4294967382, 21474836567, 4294967383, 21474836550, 4294967366, 21474836551, 4294967367, 1076, 4294968372, 1077, 4294968373, 6442452016, 2147484720, 6442452017, 2147484721, 3221226536, 11811161128, 3221226537, 11811161129, 1074, 4294968370, 1075, 4294968371, 6442452002, 15032386594, 6442452003, 15032386595, 10737418314, 27917287498, 10737418315, 27917287499, 1072, 4294968368, 1073, 4294968369, 12884902948, 4294968356, 12884902949, 4294968357, 10737419304, 2147484712, 10737419305, 2147484713, 1070, 8589935662, 1071, 8589935663, 25769803854, 8589934670, 25769803855, 8589934671, 1068, 8589935660, 1069, 8589935661, 1066, 8589935658, 1067, 8589935659, 12884902946, 4294968354, 12884902947, 4294968355, 1064, 8589935656, 1065, 8589935657, 25769803852, 8589934668, 25769803853, 8589934669, 1062, 8589935654, 1063, 8589935655, 1060, 8589935652, 1061, 8589935653, 12884902944, 4294968352, 12884902945, 4294968353, 1058, 8589935650, 1059, 8589935651, 25769803850, 8589934666, 25769803851, 8589934667, 1056, 8589935648, 1057, 8589935649, 94, 17179869278, 95, 17179869279, 92, 17179869276, 93, 17179869277, 90, 17179869274, 91, 17179869275, 88, 17179869272, 89, 17179869273, 86, 17179869270, 87, 17179869271, 84, 17179869268, 85, 17179869269, 82, 17179869266, 83, 17179869267, 80, 17179869264, 81, 17179869265, 78, 17179869262, 79, 17179869263, 76, 17179869260, 77, 17179869261, 74, 17179869258, 75, 17179869259, 72, 17179869256, 73, 17179869257, 70, 17179869254, 71, 17179869255, 68, 17179869252, 69, 17179869253, 66, 17179869250, 67, 17179869251, 64, 17179869248, 65, 17179869249]


theorem laws : ∀v∈rowInputs,
    safe TerminalInverse23.program v=true ∧ safe TerminalInverse23.reference v=true ∧
      bitRun TerminalInverse23.program v=bitRun TerminalInverse23.reference v := by
  simp (config := {maxSteps:=4000000}) only [rowInputs,List.forall_mem_cons]
  exact ⟨TerminalInverse23.row0,⟨TerminalInverse23.row1,⟨TerminalInverse23.row2,⟨TerminalInverse23.row3,⟨TerminalInverse23.row4,⟨TerminalInverse23.row5,⟨TerminalInverse23.row6,⟨TerminalInverse23.row7,⟨TerminalInverse23.row8,⟨TerminalInverse23.row9,⟨TerminalInverse23.row10,⟨TerminalInverse23.row11,⟨TerminalInverse23.row12,⟨TerminalInverse23.row13,⟨TerminalInverse23.row14,⟨TerminalInverse23.row15,⟨TerminalInverse23.row16,⟨TerminalInverse23.row17,⟨TerminalInverse23.row18,⟨TerminalInverse23.row19,⟨TerminalInverse23.row20,⟨TerminalInverse23.row21,⟨TerminalInverse23.row22,⟨TerminalInverse23.row23,⟨TerminalInverse23.row24,⟨TerminalInverse23.row25,⟨TerminalInverse23.row26,⟨TerminalInverse23.row27,⟨TerminalInverse23.row28,⟨TerminalInverse23.row29,⟨TerminalInverse23.row30,⟨TerminalInverse23.row31,⟨TerminalInverse23.row32,⟨TerminalInverse23.row33,⟨TerminalInverse23.row34,⟨TerminalInverse23.row35,⟨TerminalInverse23.row36,⟨TerminalInverse23.row37,⟨TerminalInverse23.row38,⟨TerminalInverse23.row39,⟨TerminalInverse23.row40,⟨TerminalInverse23.row41,⟨TerminalInverse23.row42,⟨TerminalInverse23.row43,⟨TerminalInverse23.row44,⟨TerminalInverse23.row45,⟨TerminalInverse23.row46,⟨TerminalInverse23.row47,⟨TerminalInverse23.row48,⟨TerminalInverse23.row49,⟨TerminalInverse23.row50,⟨TerminalInverse23.row51,⟨TerminalInverse23.row52,⟨TerminalInverse23.row53,⟨TerminalInverse23.row54,⟨TerminalInverse23.row55,⟨TerminalInverse23.row56,⟨TerminalInverse23.row57,⟨TerminalInverse23.row58,⟨TerminalInverse23.row59,⟨TerminalInverse23.row60,⟨TerminalInverse23.row61,⟨TerminalInverse23.row62,⟨TerminalInverse23.row63,⟨TerminalInverse23.row64,⟨TerminalInverse23.row65,⟨TerminalInverse23.row66,⟨TerminalInverse23.row67,⟨TerminalInverse23.row68,⟨TerminalInverse23.row69,⟨TerminalInverse23.row70,⟨TerminalInverse23.row71,⟨TerminalInverse23.row72,⟨TerminalInverse23.row73,⟨TerminalInverse23.row74,⟨TerminalInverse23.row75,⟨TerminalInverse23.row76,⟨TerminalInverse23.row77,⟨TerminalInverse23.row78,⟨TerminalInverse23.row79,⟨TerminalInverse23.row80,⟨TerminalInverse23.row81,⟨TerminalInverse23.row82,⟨TerminalInverse23.row83,⟨TerminalInverse23.row84,⟨TerminalInverse23.row85,⟨TerminalInverse23.row86,⟨TerminalInverse23.row87,⟨TerminalInverse23.row88,⟨TerminalInverse23.row89,⟨TerminalInverse23.row90,⟨TerminalInverse23.row91,⟨TerminalInverse23.row92,⟨TerminalInverse23.row93,⟨TerminalInverse23.row94,⟨TerminalInverse23.row95,⟨TerminalInverse23.row96,⟨TerminalInverse23.row97,⟨TerminalInverse23.row98,⟨TerminalInverse23.row99,⟨TerminalInverse23.row100,⟨TerminalInverse23.row101,⟨TerminalInverse23.row102,⟨TerminalInverse23.row103,⟨TerminalInverse23.row104,⟨TerminalInverse23.row105,⟨TerminalInverse23.row106,⟨TerminalInverse23.row107,⟨TerminalInverse23.row108,⟨TerminalInverse23.row109,⟨TerminalInverse23.row110,⟨TerminalInverse23.row111,⟨TerminalInverse23.row112,⟨TerminalInverse23.row113,⟨TerminalInverse23.row114,⟨TerminalInverse23.row115,⟨TerminalInverse23.row116,⟨TerminalInverse23.row117,⟨TerminalInverse23.row118,⟨TerminalInverse23.row119,⟨TerminalInverse23.row120,⟨TerminalInverse23.row121,⟨TerminalInverse23.row122,⟨TerminalInverse23.row123,⟨TerminalInverse23.row124,⟨TerminalInverse23.row125,⟨TerminalInverse23.row126,⟨TerminalInverse23.row127,⟨TerminalInverse23.row128,⟨TerminalInverse23.row129,⟨TerminalInverse23.row130,⟨TerminalInverse23.row131,⟨TerminalInverse23.row132,⟨TerminalInverse23.row133,⟨TerminalInverse23.row134,⟨TerminalInverse23.row135,⟨TerminalInverse23.row136,⟨TerminalInverse23.row137,⟨TerminalInverse23.row138,⟨TerminalInverse23.row139,⟨TerminalInverse23.row140,⟨TerminalInverse23.row141,⟨TerminalInverse23.row142,⟨TerminalInverse23.row143,⟨TerminalInverse23.row144,⟨TerminalInverse23.row145,⟨TerminalInverse23.row146,⟨TerminalInverse23.row147,⟨TerminalInverse23.row148,⟨TerminalInverse23.row149,⟨TerminalInverse23.row150,⟨TerminalInverse23.row151,⟨TerminalInverse23.row152,⟨TerminalInverse23.row153,⟨TerminalInverse23.row154,⟨TerminalInverse23.row155,⟨TerminalInverse23.row156,⟨TerminalInverse23.row157,⟨TerminalInverse23.row158,⟨TerminalInverse23.row159,⟨TerminalInverse23.row160,⟨TerminalInverse23.row161,⟨TerminalInverse23.row162,⟨TerminalInverse23.row163,⟨TerminalInverse23.row164,⟨TerminalInverse23.row165,⟨TerminalInverse23.row166,⟨TerminalInverse23.row167,⟨TerminalInverse23.row168,⟨TerminalInverse23.row169,⟨TerminalInverse23.row170,⟨TerminalInverse23.row171,⟨TerminalInverse23.row172,⟨TerminalInverse23.row173,⟨TerminalInverse23.row174,⟨TerminalInverse23.row175,⟨TerminalInverse23.row176,⟨TerminalInverse23.row177,⟨TerminalInverse23.row178,⟨TerminalInverse23.row179,⟨TerminalInverse23.row180,⟨TerminalInverse23.row181,⟨TerminalInverse23.row182,⟨TerminalInverse23.row183,⟨TerminalInverse23.row184,⟨TerminalInverse23.row185,⟨TerminalInverse23.row186,⟨TerminalInverse23.row187,⟨TerminalInverse23.row188,⟨TerminalInverse23.row189,⟨TerminalInverse23.row190,⟨TerminalInverse23.row191,⟨TerminalInverse23.row192,⟨TerminalInverse23.row193,⟨TerminalInverse23.row194,⟨TerminalInverse23.row195,⟨TerminalInverse23.row196,⟨TerminalInverse23.row197,⟨TerminalInverse23.row198,⟨TerminalInverse23.row199,⟨TerminalInverse23.row200,⟨TerminalInverse23.row201,⟨TerminalInverse23.row202,⟨TerminalInverse23.row203,⟨TerminalInverse23.row204,⟨TerminalInverse23.row205,⟨TerminalInverse23.row206,⟨TerminalInverse23.row207,⟨TerminalInverse23.row208,⟨TerminalInverse23.row209,⟨TerminalInverse23.row210,⟨TerminalInverse23.row211,⟨TerminalInverse23.row212,⟨TerminalInverse23.row213,⟨TerminalInverse23.row214,⟨TerminalInverse23.row215,⟨TerminalInverse23.row216,⟨TerminalInverse23.row217,⟨TerminalInverse23.row218,⟨TerminalInverse23.row219,⟨TerminalInverse23.row220,⟨TerminalInverse23.row221,⟨TerminalInverse23.row222,⟨TerminalInverse23.row223,⟨TerminalInverse23.row224,⟨TerminalInverse23.row225,⟨TerminalInverse23.row226,⟨TerminalInverse23.row227,⟨TerminalInverse23.row228,⟨TerminalInverse23.row229,⟨TerminalInverse23.row230,⟨TerminalInverse23.row231,⟨TerminalInverse23.row232,⟨TerminalInverse23.row233,⟨TerminalInverse23.row234,⟨TerminalInverse23.row235,⟨TerminalInverse23.row236,⟨TerminalInverse23.row237,⟨TerminalInverse23.row238,⟨TerminalInverse23.row239,⟨TerminalInverse23.row240,⟨TerminalInverse23.row241,⟨TerminalInverse23.row242,⟨TerminalInverse23.row243,⟨TerminalInverse23.row244,⟨TerminalInverse23.row245,⟨TerminalInverse23.row246,⟨TerminalInverse23.row247,⟨TerminalInverse23.row248,⟨TerminalInverse23.row249,⟨TerminalInverse23.row250,⟨TerminalInverse23.row251,⟨TerminalInverse23.row252,⟨TerminalInverse23.row253,⟨TerminalInverse23.row254,⟨TerminalInverse23.row255,⟨TerminalInverse23.row256,⟨TerminalInverse23.row257,⟨TerminalInverse23.row258,⟨TerminalInverse23.row259,⟨TerminalInverse23.row260,⟨TerminalInverse23.row261,⟨TerminalInverse23.row262,⟨TerminalInverse23.row263,⟨TerminalInverse23.row264,⟨TerminalInverse23.row265,⟨TerminalInverse23.row266,⟨TerminalInverse23.row267,⟨TerminalInverse23.row268,⟨TerminalInverse23.row269,⟨TerminalInverse23.row270,⟨TerminalInverse23.row271,⟨TerminalInverse23.row272,⟨TerminalInverse23.row273,⟨TerminalInverse23.row274,⟨TerminalInverse23.row275,⟨TerminalInverse23.row276,⟨TerminalInverse23.row277,⟨TerminalInverse23.row278,⟨TerminalInverse23.row279,⟨TerminalInverse23.row280,⟨TerminalInverse23.row281,⟨TerminalInverse23.row282,⟨TerminalInverse23.row283,⟨TerminalInverse23.row284,⟨TerminalInverse23.row285,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem allRows (v : Nat) (member : v∈rowInputs) (m n : List Bool) :
    run TerminalInverse23.program m ⟨false,bitsOf v⟩=run TerminalInverse23.reference n ⟨false,bitsOf v⟩ :=
  TerminalSafeEq.of_law _ _ v (laws v member) m n

end ECDSAAdd.Entrant.TerminalFiveRows

end

-- Adapted public peer module: TerminalFiveBridge
section

namespace ECDSAAdd.Entrant.TerminalFiveBridge
open ECDSAAdd Arithmetic MappedCompressed Challenge History5
open MeasuredCodec5 (safe bitRun bitsOf run_sim sim_safe)
set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def perm : Equiv.Perm Wire := TerminalFivePermutation.perm

attribute [local irreducible] run wires

def physical : Program := renameProgram perm TerminalInverse23.program
def old : Program := Inverse14Width.candidate ++ W.ReverseCarry.compactReceiverTick base 506
theorem reference_placement : renameProgram perm TerminalInverse23.reference=old := by decide +kernel


def forwardDense : Program := [
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CCX 1 2 11,
  .CCX 1 3 12,
  .CCX 1 4 13,
  .CCX 1 5 14,
  .CCX 1 6 15,
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CX 7 16,
  .measureX 7 [] [.CZ 0 16],
  .CX 16 7,
  .CX 7 16,
  .CX 15 16,
  .CX 15 7,
  .CX 1 10,
  .CX 7 8,
  .X 30,
  .CX 7 30,
  .CX 15 30,
  .CX 30 2,
  .CX 30 3,
  .CX 30 4,
  .CX 30 5,
  .CX 30 6,
  .CX 30 7,
  .CX 2 10,
  .CX 2 30,
  .CCX 10 30 35,
  .CX 2 35,
  .CX 2 30,
  .CX 2 10,
  .CX 3 11,
  .CX 3 35,
  .CCX 11 35 36,
  .CX 3 36,
  .CX 3 35,
  .CX 3 11,
  .CX 4 12,
  .CX 4 36,
  .CCX 12 36 37,
  .CX 4 37,
  .CX 4 36,
  .CX 4 12,
  .CX 5 13,
  .CX 5 37,
  .CCX 13 37 38,
  .CX 5 38,
  .CX 5 37,
  .CX 5 13,
  .CX 6 14,
  .CX 6 38,
  .CCX 14 38 39,
  .CX 6 39,
  .CX 6 38,
  .CX 6 14,
  .CX 7 15,
  .CX 39 15,
  .measureX 39 [] [.CZ 6 14, .CZ 6 38, .CZ 14 38],
  .CX 6 14,
  .CX 38 14,
  .measureX 38 [] [.CZ 5 13, .CZ 5 37, .CZ 13 37],
  .CX 5 13,
  .CX 37 13,
  .measureX 37 [] [.CZ 4 12, .CZ 4 36, .CZ 12 36],
  .CX 4 12,
  .CX 36 12,
  .measureX 36 [] [.CZ 3 11, .CZ 3 35, .CZ 11 35],
  .CX 3 11,
  .CX 35 11,
  .measureX 35 [] [.CZ 2 10, .CZ 2 30, .CZ 10 30],
  .CX 2 10,
  .CX 30 10,
  .CX 30 2,
  .CX 30 3,
  .CX 30 4,
  .CX 30 5,
  .CX 30 6,
  .CX 30 7,
  .X 30,
  .CX 7 30,
  .CX 15 30,
  .CX 30 16,
  .CX 0 1,
  .CX 7 8,
  .CX 15 16,
  .CX 11 3,
  .CX 12 4,
  .CX 13 5,
  .CX 14 6,
  .CCX 2 3 11,
  .CCX 2 4 12,
  .CCX 2 5 13,
  .CCX 2 6 14,
  .CX 11 3,
  .CX 12 4,
  .CX 13 5,
  .CX 14 6,
  .CX 7 15,
  .measureX 7 [] [.CZ 1 15],
  .CX 15 7,
  .CX 7 15,
  .CX 14 15,
  .CX 14 7,
  .CX 2 10,
  .CX 7 8,
  .X 31,
  .CX 7 31,
  .CX 14 31,
  .CX 31 3,
  .CX 31 4,
  .CX 31 5,
  .CX 31 6,
  .CX 31 7,
  .CX 3 10,
  .CX 3 31,
  .CCX 10 31 35,
  .CX 3 35,
  .CX 3 31,
  .CX 3 10,
  .CX 4 11,
  .CX 4 35,
  .CCX 11 35 36,
  .CX 4 36,
  .CX 4 35,
  .CX 4 11,
  .CX 5 12,
  .CX 5 36,
  .CCX 12 36 37,
  .CX 5 37,
  .CX 5 36,
  .CX 5 12,
  .CX 6 13,
  .CX 6 37,
  .CCX 13 37 38,
  .CX 6 38,
  .CX 6 37,
  .CX 6 13,
  .CX 7 14,
  .CX 38 14,
  .measureX 38 [] [.CZ 6 13, .CZ 6 37, .CZ 13 37],
  .CX 6 13,
  .CX 37 13,
  .measureX 37 [] [.CZ 5 12, .CZ 5 36, .CZ 12 36],
  .CX 5 12,
  .CX 36 12,
  .measureX 36 [] [.CZ 4 11, .CZ 4 35, .CZ 11 35],
  .CX 4 11,
  .CX 35 11,
  .measureX 35 [] [.CZ 3 10, .CZ 3 31, .CZ 10 31],
  .CX 3 10,
  .CX 31 10,
  .CX 31 3,
  .CX 31 4,
  .CX 31 5,
  .CX 31 6,
  .CX 31 7,
  .X 31,
  .CX 7 31,
  .CX 14 31,
  .CX 31 15,
  .CX 1 2,
  .CX 7 8,
  .CX 14 15,
  .CX 11 4,
  .CX 12 5,
  .CX 13 6,
  .CCX 3 4 11,
  .CCX 3 5 12,
  .CCX 3 6 13,
  .CX 11 4,
  .CX 12 5,
  .CX 13 6,
  .CX 7 14,
  .measureX 7 [] [.CZ 2 14],
  .CX 14 7,
  .CX 7 14,
  .CX 13 14,
  .CX 13 7,
  .CX 3 10,
  .CX 7 8,
  .X 32,
  .CX 7 32,
  .CX 13 32,
  .CX 32 4,
  .CX 32 5,
  .CX 32 6,
  .CX 32 7,
  .CX 4 10,
  .CX 4 32,
  .CCX 10 32 35,
  .CX 4 35,
  .CX 4 32,
  .CX 4 10,
  .CX 5 11,
  .CX 5 35,
  .CCX 11 35 36,
  .CX 5 36,
  .CX 5 35,
  .CX 5 11,
  .CX 6 12,
  .CX 6 36,
  .CCX 12 36 37,
  .CX 6 37,
  .CX 6 36,
  .CX 6 12,
  .CX 7 13,
  .CX 37 13,
  .measureX 37 [] [.CZ 6 12, .CZ 6 36, .CZ 12 36],
  .CX 6 12,
  .CX 36 12,
  .measureX 36 [] [.CZ 5 11, .CZ 5 35, .CZ 11 35],
  .CX 5 11,
  .CX 35 11,
  .measureX 35 [] [.CZ 4 10, .CZ 4 32, .CZ 10 32],
  .CX 4 10,
  .CX 32 10,
  .CX 32 4,
  .CX 32 5,
  .CX 32 6,
  .CX 32 7,
  .X 32,
  .CX 7 32,
  .CX 13 32,
  .CX 32 14,
  .CX 2 3,
  .CX 7 8,
  .CX 13 14,
  .CX 11 5,
  .CX 12 6,
  .CCX 4 5 11,
  .CCX 4 6 12,
  .CX 11 5,
  .CX 12 6,
  .CX 7 13,
  .measureX 7 [] [.CZ 3 13],
  .CX 13 7,
  .CX 7 13,
  .CX 12 13,
  .CX 12 7,
  .CX 4 10,
  .CX 7 8,
  .X 33,
  .CX 7 33,
  .CX 12 33,
  .CX 33 5,
  .CX 33 6,
  .CX 33 7,
  .CX 5 10,
  .CX 5 33,
  .CCX 10 33 35,
  .CX 5 35,
  .CX 5 33,
  .CX 5 10,
  .CX 6 11,
  .CX 6 35,
  .CCX 11 35 36,
  .CX 6 36,
  .CX 6 35,
  .CX 6 11,
  .CX 7 12,
  .CX 36 12,
  .measureX 36 [] [.CZ 6 11, .CZ 6 35, .CZ 11 35],
  .CX 6 11,
  .CX 35 11,
  .measureX 35 [] [.CZ 5 10, .CZ 5 33, .CZ 10 33],
  .CX 5 10,
  .CX 33 10,
  .CX 33 5,
  .CX 33 6,
  .CX 33 7,
  .X 33,
  .CX 7 33,
  .CX 12 33,
  .CX 33 13,
  .CX 3 4,
  .CX 7 8,
  .CX 12 13,
  .CX 11 6,
  .CX 12 7,
  .CCX 5 6 11,
  .CCX 5 7 12,
  .CX 11 6,
  .CX 12 7,
  .CX 5 10,
  .CX 7 8,
  .X 34,
  .CX 8 34,
  .CX 12 34,
  .CX 34 6,
  .CX 34 7,
  .CX 34 8,
  .CX 6 10,
  .CX 6 34,
  .CCX 10 34 35,
  .CX 6 35,
  .CX 6 34,
  .CX 6 10,
  .CX 7 11,
  .CX 7 35,
  .CCX 11 35 36,
  .CX 7 36,
  .CX 7 35,
  .CX 7 11,
  .CX 8 12,
  .CX 36 12,
  .measureX 36 [] [.CZ 7 11, .CZ 7 35, .CZ 11 35],
  .CX 7 11,
  .CX 35 11,
  .measureX 35 [] [.CZ 6 10, .CZ 6 34, .CZ 10 34],
  .CX 6 10,
  .CX 34 10,
  .CX 34 6,
  .CX 34 7,
  .CX 34 8,
  .X 34,
  .CX 8 34,
  .CX 12 34,
  .CX 4 5
]

def forward : Program := W.repairedTick base 506 ++ (MorningFour.tick507 ++ tripF)
theorem forward_placement : renameProgram perm forwardDense=forward := by decide +kernel


def rowInputs : List Nat := TerminalFiveRows.rowInputs

theorem allRows (v : Nat) (member : v∈rowInputs) (m n : List Bool) :
    run TerminalInverse23.program m ⟨false,bitsOf v⟩=
      run TerminalInverse23.reference n ⟨false,bitsOf v⟩ :=
  TerminalFiveRows.allRows v member m n

def preDense (g s : Bool) (uv : Nat×Nat) : Nat :=
  encN_t8 (fun q=>TerminalFiveDomain.pre g s uv.1 uv.2 (perm q)) (List.range 40)

def postDense (g s : Bool) (uv : Nat×Nat) : Nat := bitRun forwardDense (preDense g s uv)

def checkInput (uv : Nat×Nat) : Bool :=
  [false,true].all fun g=>[false,true].all fun s=>decide (postDense g s uv∈rowInputs)

theorem inputTable : TerminalFiveDomain.pairs.all checkInput=true := by decide +kernel

end ECDSAAdd.Entrant.TerminalFiveBridge

end

-- Adapted public peer module: WireWitness
section

namespace ECDSAAdd.Entrant.WireWitness
open ECDSAAdd Arithmetic
attribute [local irreducible] wires

def atWire (P : Program) (q k : Nat) : Bool :=
  match P[k]? with
  | none => false
  | some instruction => decide (q∈instruction.wires)

theorem of_member (P : Program) (q : Wire) (instruction : Instr) (member : instruction∈P)
    (used : q∈instruction.wires) : q∈wires P := by
  induction P with
  | nil => simp at member
  | cons head tail ih =>
    rw [wires]
    rcases List.mem_cons.mp member with equal|member
    · subst head; exact Finset.mem_union_left _ used
    · exact Finset.mem_union_right _ (ih member)

theorem atWire_sound (P : Program) (q k : Nat) (checked : atWire P q k=true) : q∈wires P := by
  cases found : P[k]? with
  | none => simp only [atWire,found,Bool.false_eq_true] at checked
  | some instruction =>
    have used : q∈instruction.wires := by simpa only [atWire,found,decide_eq_true_eq] using checked
    exact of_member P q instruction (List.mem_of_getElem? found) used

end ECDSAAdd.Entrant.WireWitness

end

-- Adapted public peer module: TerminalFiveShifted
section

namespace ECDSAAdd.Entrant.TerminalFiveShifted
open ECDSAAdd Arithmetic Challenge
open MeasuredCodec5 (safe bitRun)
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def reference : Program := [
  .X 6,
  .CX 5 6,
  .CX 5 10,
  .CX 34 33,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CCX 1 2 6,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 33,
  .CX 34 33,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 5,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 7,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 5,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 33,
  .CX 34 33,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 3,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 5,
  .CX 3 2,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 2 1,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 1 3,
  .CCX 1 2 8,
  .CX 1 3,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 2 1,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 2,
  .CX 3 5,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 3,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 33,
  .CX 7 32,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 31 3,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 10,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 3,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 7 32,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 4,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 31,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 11,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 4 31,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 5 4,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 11 10,
  .CX 10 11,
  .CX 10 8,
  .CX 8 10,
  .CX 8 6,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 6 33,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 34,
  .CX 33 32,
  .CX 32 33,
  .CX 32 31,
  .CX 31 32,
  .CX 31 4,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 2 4,
  .CX 2 3,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 12,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 3,
  .CX 2 4,
  .CX 4 2,
  .CX 4 3,
  .CX 4 5,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 31 4,
  .CX 31 32,
  .CX 32 31,
  .CX 32 33,
  .CX 33 32,
  .CX 33 34,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 6 33,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 6,
  .CX 8 10,
  .CX 10 8,
  .CX 10 11,
  .CX 11 10,
  .CX 11 7,
  .CX 10 12,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 11,
  .CX 11 8,
  .CX 8 11,
  .CX 7 10,
  .CX 7 33,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 8,
  .CX 8 6,
  .CX 6 8,
  .CX 34 7,
  .CX 7 34,
  .CX 34 7,
  .CX 33 6,
  .CX 33 4,
  .CX 32 34,
  .CX 34 32,
  .CX 32 34,
  .CX 31 33,
  .CX 33 31,
  .CX 31 33,
  .CX 5 32,
  .CX 32 5,
  .CX 5 32,
  .CX 4 31,
  .CX 4 5,
  .CX 5 4,
  .CX 4 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 5,
  .CX 5 2,
  .CX 2 5,
  .CX 1 4,
  .CX 4 1,
  .CX 1 4,
  .CCX 1 2 3,
  .CX 11 8,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 8 7,
  .CX 7 8,
  .CX 7 6,
  .CX 6 7,
  .CX 6 5,
  .CX 6 4,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 5 4,
  .CX 5 3,
  .CX 4 31,
  .CX 4 5,
  .CX 4 3,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 13,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 4 3,
  .CX 4 5,
  .CX 4 31,
  .CX 5 3,
  .CX 5 4,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 6 4,
  .CX 6 5,
  .CX 6 7,
  .CX 7 6,
  .CX 7 8,
  .CX 8 7,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 8,
  .CX 11 8,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 8 34,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 34 6,
  .CX 34 33,
  .CX 33 34,
  .CX 33 5,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 5 3,
  .CX 4 1,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CCX 1 2 14,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 4 1,
  .CX 5 3,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 5,
  .CX 33 34,
  .CX 34 33,
  .CX 34 6,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 34,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 8,
  .CX 14 11,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 12 13,
  .CX 13 12,
  .CX 12 13,
  .CX 11 12,
  .CX 11 7,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 7 6,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 33,
  .CX 33 34,
  .CX 33 31,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 31 5,
  .CX 31 4,
  .CX 4 31,
  .CX 4 5,
  .CX 4 2,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 4,
  .CX 2 1,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 1 3,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CCX 1 2 15,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 1 3,
  .CX 2 3,
  .CX 3 2,
  .CX 2 3,
  .CX 2 1,
  .CX 2 4,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 4 2,
  .CX 4 5,
  .CX 4 31,
  .CX 31 4,
  .CX 31 5,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 31,
  .CX 33 34,
  .CX 34 33,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 6,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 7,
  .CX 11 12,
  .CX 12 13,
  .CX 13 12,
  .CX 12 13,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 14 11,
  .CX 12 10,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 10 11,
  .CX 10 6,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 32,
  .CX 34 31,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 5,
  .CX 31 33,
  .CX 31 1,
  .CX 5 32,
  .CX 5 31,
  .CX 5 3,
  .CX 5 1,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 1 2,
  .CCX 1 2 35,
  .CX 1 2,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 5 1,
  .CX 5 3,
  .CX 5 31,
  .CX 5 32,
  .CX 31 1,
  .CX 31 33,
  .CX 32 5,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 31,
  .CX 34 32,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 6,
  .CX 10 11,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 12 10,
  .CX 35 12,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 12 13,
  .CX 12 10,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 10 11,
  .CX 10 6,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 32,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 32 5,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 5 31,
  .CX 5 3,
  .CX 3 5,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CCX 1 2 36,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 4,
  .CX 4 3,
  .CX 3 4,
  .CX 3 5,
  .CX 5 3,
  .CX 5 31,
  .CX 31 32,
  .CX 32 31,
  .CX 31 32,
  .CX 32 5,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 32,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 6,
  .CX 10 11,
  .CX 11 12,
  .CX 12 11,
  .CX 11 12,
  .CX 12 10,
  .CX 12 13,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 35 12,
  .CX 10 34,
  .CX 10 32,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 34 33,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 33 6,
  .CX 33 34,
  .CX 33 32,
  .CX 33 31,
  .CX 32 34,
  .CX 32 3,
  .CX 31 33,
  .CX 31 32,
  .CX 31 3,
  .CX 31 2,
  .CX 5 32,
  .CX 32 5,
  .CX 5 32,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 3 5,
  .CX 3 1,
  .CX 2 4,
  .CX 1 3,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CCX 1 2 37,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 1 3,
  .CX 2 4,
  .CX 3 1,
  .CX 3 5,
  .CX 4 31,
  .CX 31 4,
  .CX 4 31,
  .CX 5 32,
  .CX 32 5,
  .CX 5 32,
  .CX 31 2,
  .CX 31 3,
  .CX 31 32,
  .CX 31 33,
  .CX 32 3,
  .CX 32 34,
  .CX 33 31,
  .CX 33 32,
  .CX 33 34,
  .CX 33 6,
  .CX 34 6,
  .CX 6 34,
  .CX 34 6,
  .CX 34 33,
  .CX 6 7,
  .CX 7 6,
  .CX 6 7,
  .CX 7 8,
  .CX 8 7,
  .CX 7 8,
  .CX 8 10,
  .CX 10 8,
  .CX 8 10,
  .CX 10 32,
  .CX 10 34,
  .CX 37 12,
  .CX 36 37,
  .CX 37 36,
  .CX 36 37,
  .CX 35 36,
  .CX 36 35,
  .CX 35 36,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 12 13,
  .CX 12 11,
  .CX 11 12,
  .CX 11 8,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 8 10,
  .CX 8 7,
  .CX 7 8,
  .CX 7 6,
  .CX 6 7,
  .CX 6 34,
  .CX 34 6,
  .CX 34 31,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 32,
  .CX 31 1,
  .CX 5 4,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 31,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 1 3,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CCX 1 2 9,
  .CX 1 2,
  .CX 2 1,
  .CX 1 2,
  .CX 1 3,
  .CX 2 4,
  .CX 4 2,
  .CX 2 4,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 4 31,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 5 4,
  .CX 31 1,
  .CX 31 32,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 33 34,
  .CX 34 33,
  .CX 33 34,
  .CX 34 31,
  .CX 34 6,
  .CX 6 34,
  .CX 6 7,
  .CX 7 6,
  .CX 7 8,
  .CX 8 7,
  .CX 8 10,
  .CX 10 11,
  .CX 11 10,
  .CX 10 11,
  .CX 11 8,
  .CX 11 12,
  .CX 12 11,
  .CX 12 13,
  .CX 13 14,
  .CX 14 13,
  .CX 13 14,
  .CX 14 15,
  .CX 15 14,
  .CX 14 15,
  .CX 15 35,
  .CX 35 15,
  .CX 15 35,
  .CX 35 36,
  .CX 36 35,
  .CX 35 36,
  .CX 36 37,
  .CX 37 36,
  .CX 36 37,
  .CX 37 12,
  .CX 9 37,
  .CX 9 35,
  .CX 9 12,
  .CX 37 35,
  .CX 37 34,
  .CX 37 33,
  .CX 37 9,
  .CX 9 37,
  .CX 37 9,
  .CX 36 35,
  .CX 36 15,
  .CX 36 14,
  .CX 36 11,
  .CX 36 7,
  .CX 36 37,
  .CX 37 36,
  .CX 36 37,
  .CX 35 9,
  .CX 35 12,
  .CX 35 6,
  .CX 35 33,
  .CX 35 3,
  .CX 35 37,
  .CX 37 35,
  .CX 35 37,
  .CX 15 9,
  .CX 15 14,
  .CX 15 11,
  .CX 15 7,
  .CX 15 33,
  .CX 14 9,
  .CX 14 37,
  .CX 14 6,
  .CX 14 33,
  .CX 14 31,
  .CX 14 3,
  .CX 14 35,
  .CX 35 14,
  .CX 14 35,
  .CX 13 9,
  .CX 13 37,
  .CX 13 36,
  .CX 13 6,
  .CX 13 33,
  .CX 13 3,
  .CX 13 1,
  .CX 13 35,
  .CX 35 13,
  .CX 13 35,
  .CX 12 9,
  .CX 12 37,
  .CX 12 10,
  .CX 12 6,
  .CX 12 33,
  .CX 12 3,
  .CX 12 36,
  .CX 36 12,
  .CX 12 36,
  .CX 11 9,
  .CX 11 7,
  .CX 11 33,
  .CX 11 2,
  .CX 11 15,
  .CX 15 11,
  .CX 11 15,
  .CX 10 36,
  .CX 10 7,
  .CX 10 6,
  .CX 10 35,
  .CX 35 10,
  .CX 10 35,
  .CX 8 35,
  .CX 8 6,
  .CX 8 14,
  .CX 14 8,
  .CX 8 14,
  .CX 7 9,
  .CX 7 35,
  .CX 7 6,
  .CX 7 34,
  .CX 7 33,
  .CX 7 14,
  .CX 14 7,
  .CX 7 14,
  .CX 6 37,
  .CX 6 34,
  .CX 6 32,
  .CX 6 3,
  .CX 6 14,
  .CX 14 6,
  .CX 6 14,
  .CX 34 9,
  .CX 34 37,
  .CX 34 35,
  .CX 34 15,
  .CX 34 14,
  .CX 34 10,
  .CX 34 33,
  .CX 34 32,
  .CX 34 5,
  .CX 34 3,
  .CX 34 2,
  .CX 34 1,
  .CX 33 9,
  .CX 33 11,
  .CX 33 8,
  .CX 33 7,
  .CX 7 33,
  .CX 33 7,
  .CX 32 37,
  .CX 32 35,
  .CX 32 15,
  .CX 32 14,
  .CX 32 3,
  .CX 32 2,
  .CX 32 33,
  .CX 33 32,
  .CX 32 33,
  .CX 31 13,
  .CX 31 12,
  .CX 31 10,
  .CX 31 7,
  .CX 31 33,
  .CX 31 5,
  .CX 31 4,
  .CX 31 1,
  .CX 5 10,
  .CX 5 6,
  .CX 5 34,
  .CX 5 33,
  .CX 5 1,
  .CX 5 31,
  .CX 31 5,
  .CX 5 31,
  .CX 4 37,
  .CX 4 35,
  .CX 4 15,
  .CX 4 12,
  .CX 4 7,
  .CX 4 34,
  .CX 4 33,
  .CX 4 5,
  .CX 4 3,
  .CX 4 2,
  .CX 3 37,
  .CX 3 35,
  .CX 3 15,
  .CX 3 12,
  .CX 3 6,
  .CX 3 33,
  .CX 3 31,
  .CX 3 2,
  .CX 3 5,
  .CX 5 3,
  .CX 3 5,
  .CX 2 15,
  .CX 2 11,
  .CX 2 34,
  .CX 34 2,
  .CX 2 34,
  .CX 1 10,
  .CX 1 33,
  .CX 1 5,
  .CX 1 4,
  .CX 1 3,
  .CX 3 1,
  .CX 1 3,
  .X 31,
  .X 33,
  .X 34,
  .X 6,
  .measureX 9 [] [.Z 5, .Z 33, .Z 6, .Z 10, .Z 12, .Z 14, .Z 15, .CZ 1 10, .CZ 1 11, .CZ 1 37, .CZ 2 3, .CZ 2 4, .CZ 2 5, .CZ 2 34, .CZ 2 13, .CZ 2 14, .CZ 2 37, .CZ 3 10, .CZ 3 13, .CZ 33 7, .CZ 33 15, .CZ 33 37],
  .measureX 37 [] [.Z 5, .Z 31, .Z 32, .Z 33, .Z 34, .Z 6, .Z 8, .Z 12, .Z 14, .Z 15, .Z 35, .CZ 1 3, .CZ 1 33, .CZ 1 34, .CZ 1 15, .CZ 1 35, .CZ 2 34, .CZ 2 13, .CZ 2 35, .CZ 3 4, .CZ 3 33, .CZ 3 6, .CZ 3 7, .CZ 3 8, .CZ 3 10, .CZ 3 11, .CZ 3 13, .CZ 3 14, .CZ 3 15, .CZ 3 35, .CZ 3 36, .CZ 4 5, .CZ 4 31, .CZ 4 10, .CZ 4 12, .CZ 4 35, .CZ 5 7, .CZ 5 35, .CZ 31 33, .CZ 33 34, .CZ 33 7, .CZ 33 15, .CZ 33 35, .CZ 34 35],
  .X 36,
  .measureX 36 [] [.Z 1, .Z 2, .Z 4, .Z 31, .Z 32, .Z 10, .Z 12, .Z 13, .Z 14, .CZ 1 2, .CZ 1 3, .CZ 1 5, .CZ 1 34, .CZ 1 10, .CZ 1 12, .CZ 2 3, .CZ 2 5, .CZ 2 13, .CZ 2 14, .CZ 3 4, .CZ 3 5, .CZ 3 7, .CZ 3 8, .CZ 3 11, .CZ 3 13, .CZ 3 14, .CZ 4 5, .CZ 4 33, .CZ 4 34, .CZ 4 7, .CZ 4 10, .CZ 4 11, .CZ 4 12, .CZ 5 14, .CZ 31 33, .CZ 31 34, .CZ 31 12],
  .X 35,
  .measureX 35 [] [.Z 2, .Z 5, .Z 33, .Z 6, .Z 8, .Z 14, .CZ 1 2, .CZ 1 5, .CZ 1 33, .CZ 1 6, .CZ 1 10, .CZ 1 11, .CZ 1 13, .CZ 1 14, .CZ 2 4, .CZ 2 31, .CZ 2 34, .CZ 2 14, .CZ 3 33, .CZ 3 34, .CZ 3 8, .CZ 3 13, .CZ 3 14, .CZ 4 34, .CZ 4 6, .CZ 4 7, .CZ 4 14, .CZ 5 33, .CZ 5 6, .CZ 5 7, .CZ 5 10, .CZ 5 12, .CZ 5 14, .CZ 31 12, .CZ 33 6, .CZ 33 7, .CZ 33 12],
  .measureX 15 [] [.Z 1, .Z 3, .Z 4, .Z 5, .Z 33, .Z 34, .Z 10, .Z 13, .Z 14, .CZ 1 3, .CZ 1 33, .CZ 1 10, .CZ 1 11, .CZ 1 13, .CZ 2 3, .CZ 2 4, .CZ 2 5, .CZ 2 31, .CZ 2 13, .CZ 2 14, .CZ 3 7, .CZ 3 8, .CZ 3 10, .CZ 4 7, .CZ 4 13],
  .X 14,
  .measureX 14 [] [.Z 1, .Z 4, .Z 31, .Z 6, .Z 10, .Z 12, .CZ 1 3, .CZ 1 34, .CZ 1 12, .CZ 2 4, .CZ 2 5, .CZ 2 31, .CZ 3 34, .CZ 3 7, .CZ 3 10, .CZ 3 12, .CZ 4 31, .CZ 4 6, .CZ 4 7, .CZ 4 10, .CZ 4 11, .CZ 4 12, .CZ 5 33, .CZ 5 6, .CZ 5 10, .CZ 5 12, .CZ 31 33, .CZ 31 34, .CZ 31 10, .CZ 31 12, .CZ 33 34, .CZ 33 7, .CZ 34 7],
  .measureX 13 [] [.Z 3, .Z 4, .Z 33, .Z 10, .CZ 1 4, .CZ 1 34, .CZ 3 4, .CZ 3 31, .CZ 3 33, .CZ 3 11, .CZ 4 10, .CZ 33 34, .CZ 33 7, .CZ 33 11, .CZ 34 10],
  .measureX 12 [] [.Z 1, .Z 2, .Z 3, .Z 5, .CZ 2 3, .CZ 2 5, .CZ 2 33, .CZ 2 6],
  .X 11,
  .measureX 11 [] [.Z 34, .Z 7, .CZ 2 4, .CZ 2 31, .CZ 2 34, .CZ 2 7],
  .measureX 10 [] [.Z 1, .Z 2, .Z 3, .CZ 2 3, .CZ 2 33],
  .CX 31 6,
  .CX 6 31,
  .CX 31 6,
  .CX 32 7,
  .CX 7 32,
  .CX 32 7,
  .CX 33 11,
  .CX 11 33,
  .CX 33 11,
  .CX 34 12,
  .CX 12 34,
  .CX 34 12,
  .CX 31 13,
  .CX 13 31,
  .CX 31 13,
  .CX 32 14,
  .CX 14 32,
  .CX 32 14,
  .CX 8 15,
  .CX 15 8,
  .CX 8 15,
  .X 10,
  .CX 2 10,
  .measureX 9 [] [],
  .CX 15 16,
  .CX 7 8,
  .CX 0 1,
  .CX 30 16,
  .X 30,
  .CX 7 30,
  .CX 15 30,
  .X 10,
  .X 11,
  .X 12,
  .X 13,
  .X 14,
  .X 15,
  .CX 30 2,
  .CX 30 3,
  .CX 30 4,
  .CX 30 5,
  .CX 30 6,
  .CX 30 7,
  .CX 2 10,
  .CX 2 30,
  .CCX 10 30 35,
  .CX 2 35,
  .CX 2 30,
  .CX 2 10,
  .CX 3 11,
  .CX 3 35,
  .CCX 11 35 36,
  .CX 3 36,
  .CX 3 35,
  .CX 3 11,
  .CX 4 12,
  .CX 4 36,
  .CCX 12 36 37,
  .CX 4 37,
  .CX 4 36,
  .CX 4 12,
  .CX 5 13,
  .CX 5 37,
  .CCX 13 37 34,
  .CX 5 34,
  .CX 5 37,
  .CX 5 13,
  .measureX 15 [] [.CZ 6 14, .CZ 6 34, .CZ 14 34],
  .CX 7 15,
  .CX 6 14,
  .CX 34 14,
  .measureX 34 [] [.CZ 5 13, .CZ 5 37, .CZ 13 37],
  .CX 5 13,
  .CX 37 13,
  .measureX 37 [] [.CZ 4 12, .CZ 4 36, .CZ 12 36],
  .CX 4 12,
  .CX 36 12,
  .measureX 36 [] [.CZ 3 11, .CZ 3 35, .CZ 11 35],
  .CX 3 11,
  .CX 35 11,
  .measureX 35 [] [.CZ 2 10, .CZ 2 30, .CZ 10 30],
  .CX 2 10,
  .CX 30 10,
  .CX 30 2,
  .CX 30 3,
  .CX 30 4,
  .CX 30 5,
  .CX 30 6,
  .CX 30 7,
  .X 10,
  .X 11,
  .X 12,
  .X 13,
  .X 14,
  .X 15,
  .X 30,
  .CX 7 30,
  .CX 15 30,
  .CX 7 8,
  .CX 1 10,
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CX 16 7,
  .CCX 1 2 11,
  .CCX 1 3 12,
  .CCX 1 4 13,
  .CCX 1 5 14,
  .CCX 1 6 15,
  .CCX 1 7 16,
  .CX 11 2,
  .CX 12 3,
  .CX 13 4,
  .CX 14 5,
  .CX 15 6,
  .CX 16 7
]

attribute [local irreducible] reference safe bitRun
open CodecBitSliceVerify (Cols target)

theorem targets : ∀i∈reference,target i < TerminalInverse23.inputColumns.length := by
  rw [TerminalInverse23.input_length]
  decide +kernel

def resultS := CodecBitSliceVerify.eval (2^286-1) reference TerminalInverse23.inputColumns

theorem checked : resultS.1=true ∧ resultS.2=TerminalInverse23.resultQ.2 := by
  decide +kernel

theorem row_all (r : Fin 286) : safe reference (TerminalInverse23.rowInput r)=true ∧
    bitRun reference (TerminalInverse23.rowInput r)=
      bitRun TerminalInverse23.reference (TerminalInverse23.rowInput r) := by
  have hs:=CodecBitSliceVerify.eval_sound (2^286-1) r.val (TerminalInverse23.mask_bits r)
    reference TerminalInverse23.inputColumns (TerminalInverse23.rowInput r)
    targets (TerminalInverse23.input_rel r) checked.1
  have hq:=CodecBitSliceVerify.eval_sound (2^286-1) r.val (TerminalInverse23.mask_bits r)
    TerminalInverse23.reference TerminalInverse23.inputColumns
    (TerminalInverse23.rowInput r) TerminalInverse23.reference_targets
    (TerminalInverse23.input_rel r) TerminalInverse23.vector_checked.2.1
  refine ⟨hs.1,?_⟩
  apply Nat.eq_of_testBit_eq
  intro q
  exact (hs.2 q).trans ((congrArg (fun s : Cols => (CodecBitSliceVerify.get s q).testBit r.val)
    checked.2).trans (hq.2 q).symm)

theorem row0 : safe reference 1086=true ∧ bitRun reference 1086=bitRun TerminalInverse23.reference 1086 := row_all ⟨0,by decide⟩
theorem row1 : safe reference 1087=true ∧ bitRun reference 1087=bitRun TerminalInverse23.reference 1087 := row_all ⟨1,by decide⟩
theorem row2 : safe reference 1084=true ∧ bitRun reference 1084=bitRun TerminalInverse23.reference 1084 := row_all ⟨2,by decide⟩
theorem row3 : safe reference 1073742908=true ∧ bitRun reference 1073742908=bitRun TerminalInverse23.reference 1073742908 := row_all ⟨3,by decide⟩
theorem row4 : safe reference 1085=true ∧ bitRun reference 1085=bitRun TerminalInverse23.reference 1085 := row_all ⟨4,by decide⟩
theorem row5 : safe reference 1073742909=true ∧ bitRun reference 1073742909=bitRun TerminalInverse23.reference 1073742909 := row_all ⟨5,by decide⟩
theorem row6 : safe reference 3221226552=true ∧ bitRun reference 3221226552=bitRun TerminalInverse23.reference 3221226552 := row_all ⟨6,by decide⟩
theorem row7 : safe reference 1073742904=true ∧ bitRun reference 1073742904=bitRun TerminalInverse23.reference 1073742904 := row_all ⟨7,by decide⟩
theorem row8 : safe reference 3221226553=true ∧ bitRun reference 3221226553=bitRun TerminalInverse23.reference 3221226553 := row_all ⟨8,by decide⟩
theorem row9 : safe reference 1073742905=true ∧ bitRun reference 1073742905=bitRun TerminalInverse23.reference 1073742905 := row_all ⟨9,by decide⟩
theorem row10 : safe reference 5368710196=true ∧ bitRun reference 5368710196=bitRun TerminalInverse23.reference 5368710196 := row_all ⟨10,by decide⟩
theorem row11 : safe reference 1073742900=true ∧ bitRun reference 1073742900=bitRun TerminalInverse23.reference 1073742900 := row_all ⟨11,by decide⟩
theorem row12 : safe reference 5368710197=true ∧ bitRun reference 5368710197=bitRun TerminalInverse23.reference 5368710197 := row_all ⟨12,by decide⟩
theorem row13 : safe reference 1073742901=true ∧ bitRun reference 1073742901=bitRun TerminalInverse23.reference 1073742901 := row_all ⟨13,by decide⟩
theorem row14 : safe reference 5368710192=true ∧ bitRun reference 5368710192=bitRun TerminalInverse23.reference 5368710192 := row_all ⟨14,by decide⟩
theorem row15 : safe reference 1073742896=true ∧ bitRun reference 1073742896=bitRun TerminalInverse23.reference 1073742896 := row_all ⟨15,by decide⟩
theorem row16 : safe reference 5368710193=true ∧ bitRun reference 5368710193=bitRun TerminalInverse23.reference 5368710193 := row_all ⟨16,by decide⟩
theorem row17 : safe reference 1073742897=true ∧ bitRun reference 1073742897=bitRun TerminalInverse23.reference 1073742897 := row_all ⟨17,by decide⟩
theorem row18 : safe reference 9663677484=true ∧ bitRun reference 9663677484=bitRun TerminalInverse23.reference 9663677484 := row_all ⟨18,by decide⟩
theorem row19 : safe reference 1073742892=true ∧ bitRun reference 1073742892=bitRun TerminalInverse23.reference 1073742892 := row_all ⟨19,by decide⟩
theorem row20 : safe reference 9663677485=true ∧ bitRun reference 9663677485=bitRun TerminalInverse23.reference 9663677485 := row_all ⟨20,by decide⟩
theorem row21 : safe reference 1073742893=true ∧ bitRun reference 1073742893=bitRun TerminalInverse23.reference 1073742893 := row_all ⟨21,by decide⟩
theorem row22 : safe reference 9663677480=true ∧ bitRun reference 9663677480=bitRun TerminalInverse23.reference 9663677480 := row_all ⟨22,by decide⟩
theorem row23 : safe reference 1073742888=true ∧ bitRun reference 1073742888=bitRun TerminalInverse23.reference 1073742888 := row_all ⟨23,by decide⟩
theorem row24 : safe reference 9663677481=true ∧ bitRun reference 9663677481=bitRun TerminalInverse23.reference 9663677481 := row_all ⟨24,by decide⟩
theorem row25 : safe reference 1073742889=true ∧ bitRun reference 1073742889=bitRun TerminalInverse23.reference 1073742889 := row_all ⟨25,by decide⟩
theorem row26 : safe reference 9663677476=true ∧ bitRun reference 9663677476=bitRun TerminalInverse23.reference 9663677476 := row_all ⟨26,by decide⟩
theorem row27 : safe reference 1073742884=true ∧ bitRun reference 1073742884=bitRun TerminalInverse23.reference 1073742884 := row_all ⟨27,by decide⟩
theorem row28 : safe reference 9663677477=true ∧ bitRun reference 9663677477=bitRun TerminalInverse23.reference 9663677477 := row_all ⟨28,by decide⟩
theorem row29 : safe reference 1073742885=true ∧ bitRun reference 1073742885=bitRun TerminalInverse23.reference 1073742885 := row_all ⟨29,by decide⟩
theorem row30 : safe reference 9663677472=true ∧ bitRun reference 9663677472=bitRun TerminalInverse23.reference 9663677472 := row_all ⟨30,by decide⟩
theorem row31 : safe reference 1073742880=true ∧ bitRun reference 1073742880=bitRun TerminalInverse23.reference 1073742880 := row_all ⟨31,by decide⟩
theorem row32 : safe reference 9663677473=true ∧ bitRun reference 9663677473=bitRun TerminalInverse23.reference 9663677473 := row_all ⟨32,by decide⟩
theorem row33 : safe reference 1073742881=true ∧ bitRun reference 1073742881=bitRun TerminalInverse23.reference 1073742881 := row_all ⟨33,by decide⟩
theorem row34 : safe reference 18253611100=true ∧ bitRun reference 18253611100=bitRun TerminalInverse23.reference 18253611100 := row_all ⟨34,by decide⟩
theorem row35 : safe reference 1073741916=true ∧ bitRun reference 1073741916=bitRun TerminalInverse23.reference 1073741916 := row_all ⟨35,by decide⟩
theorem row36 : safe reference 18253611101=true ∧ bitRun reference 18253611101=bitRun TerminalInverse23.reference 18253611101 := row_all ⟨36,by decide⟩
theorem row37 : safe reference 1073741917=true ∧ bitRun reference 1073741917=bitRun TerminalInverse23.reference 1073741917 := row_all ⟨37,by decide⟩
theorem row38 : safe reference 18253611096=true ∧ bitRun reference 18253611096=bitRun TerminalInverse23.reference 18253611096 := row_all ⟨38,by decide⟩
theorem row39 : safe reference 1073741912=true ∧ bitRun reference 1073741912=bitRun TerminalInverse23.reference 1073741912 := row_all ⟨39,by decide⟩
theorem row40 : safe reference 18253611097=true ∧ bitRun reference 18253611097=bitRun TerminalInverse23.reference 18253611097 := row_all ⟨40,by decide⟩
theorem row41 : safe reference 1073741913=true ∧ bitRun reference 1073741913=bitRun TerminalInverse23.reference 1073741913 := row_all ⟨41,by decide⟩
theorem row42 : safe reference 18253611092=true ∧ bitRun reference 18253611092=bitRun TerminalInverse23.reference 18253611092 := row_all ⟨42,by decide⟩
theorem row43 : safe reference 1073741908=true ∧ bitRun reference 1073741908=bitRun TerminalInverse23.reference 1073741908 := row_all ⟨43,by decide⟩
theorem row44 : safe reference 18253611093=true ∧ bitRun reference 18253611093=bitRun TerminalInverse23.reference 18253611093 := row_all ⟨44,by decide⟩
theorem row45 : safe reference 1073741909=true ∧ bitRun reference 1073741909=bitRun TerminalInverse23.reference 1073741909 := row_all ⟨45,by decide⟩
theorem row46 : safe reference 18253611088=true ∧ bitRun reference 18253611088=bitRun TerminalInverse23.reference 18253611088 := row_all ⟨46,by decide⟩
theorem row47 : safe reference 1073741904=true ∧ bitRun reference 1073741904=bitRun TerminalInverse23.reference 1073741904 := row_all ⟨47,by decide⟩
theorem row48 : safe reference 18253611089=true ∧ bitRun reference 18253611089=bitRun TerminalInverse23.reference 18253611089 := row_all ⟨48,by decide⟩
theorem row49 : safe reference 1073741905=true ∧ bitRun reference 1073741905=bitRun TerminalInverse23.reference 1073741905 := row_all ⟨49,by decide⟩
theorem row50 : safe reference 18253611084=true ∧ bitRun reference 18253611084=bitRun TerminalInverse23.reference 18253611084 := row_all ⟨50,by decide⟩
theorem row51 : safe reference 1073741900=true ∧ bitRun reference 1073741900=bitRun TerminalInverse23.reference 1073741900 := row_all ⟨51,by decide⟩
theorem row52 : safe reference 18253611085=true ∧ bitRun reference 18253611085=bitRun TerminalInverse23.reference 18253611085 := row_all ⟨52,by decide⟩
theorem row53 : safe reference 1073741901=true ∧ bitRun reference 1073741901=bitRun TerminalInverse23.reference 1073741901 := row_all ⟨53,by decide⟩
theorem row54 : safe reference 18253611080=true ∧ bitRun reference 18253611080=bitRun TerminalInverse23.reference 18253611080 := row_all ⟨54,by decide⟩
theorem row55 : safe reference 1073741896=true ∧ bitRun reference 1073741896=bitRun TerminalInverse23.reference 1073741896 := row_all ⟨55,by decide⟩
theorem row56 : safe reference 18253611081=true ∧ bitRun reference 18253611081=bitRun TerminalInverse23.reference 18253611081 := row_all ⟨56,by decide⟩
theorem row57 : safe reference 1073741897=true ∧ bitRun reference 1073741897=bitRun TerminalInverse23.reference 1073741897 := row_all ⟨57,by decide⟩
theorem row58 : safe reference 18253611076=true ∧ bitRun reference 18253611076=bitRun TerminalInverse23.reference 18253611076 := row_all ⟨58,by decide⟩
theorem row59 : safe reference 1073741892=true ∧ bitRun reference 1073741892=bitRun TerminalInverse23.reference 1073741892 := row_all ⟨59,by decide⟩
theorem row60 : safe reference 18253611077=true ∧ bitRun reference 18253611077=bitRun TerminalInverse23.reference 18253611077 := row_all ⟨60,by decide⟩
theorem row61 : safe reference 1073741893=true ∧ bitRun reference 1073741893=bitRun TerminalInverse23.reference 1073741893 := row_all ⟨61,by decide⟩
theorem row62 : safe reference 18253611072=true ∧ bitRun reference 18253611072=bitRun TerminalInverse23.reference 18253611072 := row_all ⟨62,by decide⟩
theorem row63 : safe reference 1073741888=true ∧ bitRun reference 1073741888=bitRun TerminalInverse23.reference 1073741888 := row_all ⟨63,by decide⟩
theorem row64 : safe reference 18253611073=true ∧ bitRun reference 18253611073=bitRun TerminalInverse23.reference 18253611073 := row_all ⟨64,by decide⟩
theorem row65 : safe reference 1073741889=true ∧ bitRun reference 1073741889=bitRun TerminalInverse23.reference 1073741889 := row_all ⟨65,by decide⟩
theorem row66 : safe reference 1082=true ∧ bitRun reference 1082=bitRun TerminalInverse23.reference 1082 := row_all ⟨66,by decide⟩
theorem row67 : safe reference 2147484730=true ∧ bitRun reference 2147484730=bitRun TerminalInverse23.reference 2147484730 := row_all ⟨67,by decide⟩
theorem row68 : safe reference 1083=true ∧ bitRun reference 1083=bitRun TerminalInverse23.reference 1083 := row_all ⟨68,by decide⟩
theorem row69 : safe reference 2147484731=true ∧ bitRun reference 2147484731=bitRun TerminalInverse23.reference 2147484731 := row_all ⟨69,by decide⟩
theorem row70 : safe reference 6442452018=true ∧ bitRun reference 6442452018=bitRun TerminalInverse23.reference 6442452018 := row_all ⟨70,by decide⟩
theorem row71 : safe reference 2147484722=true ∧ bitRun reference 2147484722=bitRun TerminalInverse23.reference 2147484722 := row_all ⟨71,by decide⟩
theorem row72 : safe reference 6442452019=true ∧ bitRun reference 6442452019=bitRun TerminalInverse23.reference 6442452019 := row_all ⟨72,by decide⟩
theorem row73 : safe reference 2147484723=true ∧ bitRun reference 2147484723=bitRun TerminalInverse23.reference 2147484723 := row_all ⟨73,by decide⟩
theorem row74 : safe reference 10737419306=true ∧ bitRun reference 10737419306=bitRun TerminalInverse23.reference 10737419306 := row_all ⟨74,by decide⟩
theorem row75 : safe reference 2147484714=true ∧ bitRun reference 2147484714=bitRun TerminalInverse23.reference 2147484714 := row_all ⟨75,by decide⟩
theorem row76 : safe reference 10737419307=true ∧ bitRun reference 10737419307=bitRun TerminalInverse23.reference 10737419307 := row_all ⟨76,by decide⟩
theorem row77 : safe reference 2147484715=true ∧ bitRun reference 2147484715=bitRun TerminalInverse23.reference 2147484715 := row_all ⟨77,by decide⟩
theorem row78 : safe reference 10737419298=true ∧ bitRun reference 10737419298=bitRun TerminalInverse23.reference 10737419298 := row_all ⟨78,by decide⟩
theorem row79 : safe reference 2147484706=true ∧ bitRun reference 2147484706=bitRun TerminalInverse23.reference 2147484706 := row_all ⟨79,by decide⟩
theorem row80 : safe reference 10737419299=true ∧ bitRun reference 10737419299=bitRun TerminalInverse23.reference 10737419299 := row_all ⟨80,by decide⟩
theorem row81 : safe reference 2147484707=true ∧ bitRun reference 2147484707=bitRun TerminalInverse23.reference 2147484707 := row_all ⟨81,by decide⟩
theorem row82 : safe reference 19327352922=true ∧ bitRun reference 19327352922=bitRun TerminalInverse23.reference 19327352922 := row_all ⟨82,by decide⟩
theorem row83 : safe reference 2147483738=true ∧ bitRun reference 2147483738=bitRun TerminalInverse23.reference 2147483738 := row_all ⟨83,by decide⟩
theorem row84 : safe reference 19327352923=true ∧ bitRun reference 19327352923=bitRun TerminalInverse23.reference 19327352923 := row_all ⟨84,by decide⟩
theorem row85 : safe reference 2147483739=true ∧ bitRun reference 2147483739=bitRun TerminalInverse23.reference 2147483739 := row_all ⟨85,by decide⟩
theorem row86 : safe reference 19327352914=true ∧ bitRun reference 19327352914=bitRun TerminalInverse23.reference 19327352914 := row_all ⟨86,by decide⟩
theorem row87 : safe reference 2147483730=true ∧ bitRun reference 2147483730=bitRun TerminalInverse23.reference 2147483730 := row_all ⟨87,by decide⟩
theorem row88 : safe reference 19327352915=true ∧ bitRun reference 19327352915=bitRun TerminalInverse23.reference 19327352915 := row_all ⟨88,by decide⟩
theorem row89 : safe reference 2147483731=true ∧ bitRun reference 2147483731=bitRun TerminalInverse23.reference 2147483731 := row_all ⟨89,by decide⟩
theorem row90 : safe reference 19327352906=true ∧ bitRun reference 19327352906=bitRun TerminalInverse23.reference 19327352906 := row_all ⟨90,by decide⟩
theorem row91 : safe reference 2147483722=true ∧ bitRun reference 2147483722=bitRun TerminalInverse23.reference 2147483722 := row_all ⟨91,by decide⟩
theorem row92 : safe reference 19327352907=true ∧ bitRun reference 19327352907=bitRun TerminalInverse23.reference 19327352907 := row_all ⟨92,by decide⟩
theorem row93 : safe reference 2147483723=true ∧ bitRun reference 2147483723=bitRun TerminalInverse23.reference 2147483723 := row_all ⟨93,by decide⟩
theorem row94 : safe reference 19327352898=true ∧ bitRun reference 19327352898=bitRun TerminalInverse23.reference 19327352898 := row_all ⟨94,by decide⟩
theorem row95 : safe reference 2147483714=true ∧ bitRun reference 2147483714=bitRun TerminalInverse23.reference 2147483714 := row_all ⟨95,by decide⟩
theorem row96 : safe reference 19327352899=true ∧ bitRun reference 19327352899=bitRun TerminalInverse23.reference 19327352899 := row_all ⟨96,by decide⟩
theorem row97 : safe reference 2147483715=true ∧ bitRun reference 2147483715=bitRun TerminalInverse23.reference 2147483715 := row_all ⟨97,by decide⟩
theorem row98 : safe reference 1080=true ∧ bitRun reference 1080=bitRun TerminalInverse23.reference 1080 := row_all ⟨98,by decide⟩
theorem row99 : safe reference 2147484728=true ∧ bitRun reference 2147484728=bitRun TerminalInverse23.reference 2147484728 := row_all ⟨99,by decide⟩
theorem row100 : safe reference 1081=true ∧ bitRun reference 1081=bitRun TerminalInverse23.reference 1081 := row_all ⟨100,by decide⟩
theorem row101 : safe reference 2147484729=true ∧ bitRun reference 2147484729=bitRun TerminalInverse23.reference 2147484729 := row_all ⟨101,by decide⟩
theorem row102 : safe reference 3221226544=true ∧ bitRun reference 3221226544=bitRun TerminalInverse23.reference 3221226544 := row_all ⟨102,by decide⟩
theorem row103 : safe reference 7516193840=true ∧ bitRun reference 7516193840=bitRun TerminalInverse23.reference 7516193840 := row_all ⟨103,by decide⟩
theorem row104 : safe reference 3221226545=true ∧ bitRun reference 3221226545=bitRun TerminalInverse23.reference 3221226545 := row_all ⟨104,by decide⟩
theorem row105 : safe reference 7516193841=true ∧ bitRun reference 7516193841=bitRun TerminalInverse23.reference 7516193841 := row_all ⟨105,by decide⟩
theorem row106 : safe reference 5368710180=true ∧ bitRun reference 5368710180=bitRun TerminalInverse23.reference 5368710180 := row_all ⟨106,by decide⟩
theorem row107 : safe reference 13958644772=true ∧ bitRun reference 13958644772=bitRun TerminalInverse23.reference 13958644772 := row_all ⟨107,by decide⟩
theorem row108 : safe reference 5368710181=true ∧ bitRun reference 5368710181=bitRun TerminalInverse23.reference 5368710181 := row_all ⟨108,by decide⟩
theorem row109 : safe reference 13958644773=true ∧ bitRun reference 13958644773=bitRun TerminalInverse23.reference 13958644773 := row_all ⟨109,by decide⟩
theorem row110 : safe reference 9663676492=true ∧ bitRun reference 9663676492=bitRun TerminalInverse23.reference 9663676492 := row_all ⟨110,by decide⟩
theorem row111 : safe reference 26843545676=true ∧ bitRun reference 26843545676=bitRun TerminalInverse23.reference 26843545676 := row_all ⟨111,by decide⟩
theorem row112 : safe reference 9663676493=true ∧ bitRun reference 9663676493=bitRun TerminalInverse23.reference 9663676493 := row_all ⟨112,by decide⟩
theorem row113 : safe reference 26843545677=true ∧ bitRun reference 26843545677=bitRun TerminalInverse23.reference 26843545677 := row_all ⟨113,by decide⟩
theorem row114 : safe reference 5368710176=true ∧ bitRun reference 5368710176=bitRun TerminalInverse23.reference 5368710176 := row_all ⟨114,by decide⟩
theorem row115 : safe reference 13958644768=true ∧ bitRun reference 13958644768=bitRun TerminalInverse23.reference 13958644768 := row_all ⟨115,by decide⟩
theorem row116 : safe reference 5368710177=true ∧ bitRun reference 5368710177=bitRun TerminalInverse23.reference 5368710177 := row_all ⟨116,by decide⟩
theorem row117 : safe reference 13958644769=true ∧ bitRun reference 13958644769=bitRun TerminalInverse23.reference 13958644769 := row_all ⟨117,by decide⟩
theorem row118 : safe reference 1078=true ∧ bitRun reference 1078=bitRun TerminalInverse23.reference 1078 := row_all ⟨118,by decide⟩
theorem row119 : safe reference 4294968374=true ∧ bitRun reference 4294968374=bitRun TerminalInverse23.reference 4294968374 := row_all ⟨119,by decide⟩
theorem row120 : safe reference 1079=true ∧ bitRun reference 1079=bitRun TerminalInverse23.reference 1079 := row_all ⟨120,by decide⟩
theorem row121 : safe reference 4294968375=true ∧ bitRun reference 4294968375=bitRun TerminalInverse23.reference 4294968375 := row_all ⟨121,by decide⟩
theorem row122 : safe reference 12884902950=true ∧ bitRun reference 12884902950=bitRun TerminalInverse23.reference 12884902950 := row_all ⟨122,by decide⟩
theorem row123 : safe reference 4294968358=true ∧ bitRun reference 4294968358=bitRun TerminalInverse23.reference 4294968358 := row_all ⟨123,by decide⟩
theorem row124 : safe reference 12884902951=true ∧ bitRun reference 12884902951=bitRun TerminalInverse23.reference 12884902951 := row_all ⟨124,by decide⟩
theorem row125 : safe reference 4294968359=true ∧ bitRun reference 4294968359=bitRun TerminalInverse23.reference 4294968359 := row_all ⟨125,by decide⟩
theorem row126 : safe reference 21474836566=true ∧ bitRun reference 21474836566=bitRun TerminalInverse23.reference 21474836566 := row_all ⟨126,by decide⟩
theorem row127 : safe reference 4294967382=true ∧ bitRun reference 4294967382=bitRun TerminalInverse23.reference 4294967382 := row_all ⟨127,by decide⟩
theorem row128 : safe reference 21474836567=true ∧ bitRun reference 21474836567=bitRun TerminalInverse23.reference 21474836567 := row_all ⟨128,by decide⟩
theorem row129 : safe reference 4294967383=true ∧ bitRun reference 4294967383=bitRun TerminalInverse23.reference 4294967383 := row_all ⟨129,by decide⟩
theorem row130 : safe reference 21474836550=true ∧ bitRun reference 21474836550=bitRun TerminalInverse23.reference 21474836550 := row_all ⟨130,by decide⟩
theorem row131 : safe reference 4294967366=true ∧ bitRun reference 4294967366=bitRun TerminalInverse23.reference 4294967366 := row_all ⟨131,by decide⟩
theorem row132 : safe reference 21474836551=true ∧ bitRun reference 21474836551=bitRun TerminalInverse23.reference 21474836551 := row_all ⟨132,by decide⟩
theorem row133 : safe reference 4294967367=true ∧ bitRun reference 4294967367=bitRun TerminalInverse23.reference 4294967367 := row_all ⟨133,by decide⟩
theorem row134 : safe reference 1076=true ∧ bitRun reference 1076=bitRun TerminalInverse23.reference 1076 := row_all ⟨134,by decide⟩
theorem row135 : safe reference 4294968372=true ∧ bitRun reference 4294968372=bitRun TerminalInverse23.reference 4294968372 := row_all ⟨135,by decide⟩
theorem row136 : safe reference 1077=true ∧ bitRun reference 1077=bitRun TerminalInverse23.reference 1077 := row_all ⟨136,by decide⟩
theorem row137 : safe reference 4294968373=true ∧ bitRun reference 4294968373=bitRun TerminalInverse23.reference 4294968373 := row_all ⟨137,by decide⟩
theorem row138 : safe reference 6442452016=true ∧ bitRun reference 6442452016=bitRun TerminalInverse23.reference 6442452016 := row_all ⟨138,by decide⟩
theorem row139 : safe reference 2147484720=true ∧ bitRun reference 2147484720=bitRun TerminalInverse23.reference 2147484720 := row_all ⟨139,by decide⟩
theorem row140 : safe reference 6442452017=true ∧ bitRun reference 6442452017=bitRun TerminalInverse23.reference 6442452017 := row_all ⟨140,by decide⟩
theorem row141 : safe reference 2147484721=true ∧ bitRun reference 2147484721=bitRun TerminalInverse23.reference 2147484721 := row_all ⟨141,by decide⟩
theorem row142 : safe reference 3221226536=true ∧ bitRun reference 3221226536=bitRun TerminalInverse23.reference 3221226536 := row_all ⟨142,by decide⟩
theorem row143 : safe reference 11811161128=true ∧ bitRun reference 11811161128=bitRun TerminalInverse23.reference 11811161128 := row_all ⟨143,by decide⟩
theorem row144 : safe reference 3221226537=true ∧ bitRun reference 3221226537=bitRun TerminalInverse23.reference 3221226537 := row_all ⟨144,by decide⟩
theorem row145 : safe reference 11811161129=true ∧ bitRun reference 11811161129=bitRun TerminalInverse23.reference 11811161129 := row_all ⟨145,by decide⟩
theorem row146 : safe reference 1074=true ∧ bitRun reference 1074=bitRun TerminalInverse23.reference 1074 := row_all ⟨146,by decide⟩
theorem row147 : safe reference 4294968370=true ∧ bitRun reference 4294968370=bitRun TerminalInverse23.reference 4294968370 := row_all ⟨147,by decide⟩
theorem row148 : safe reference 1075=true ∧ bitRun reference 1075=bitRun TerminalInverse23.reference 1075 := row_all ⟨148,by decide⟩
theorem row149 : safe reference 4294968371=true ∧ bitRun reference 4294968371=bitRun TerminalInverse23.reference 4294968371 := row_all ⟨149,by decide⟩
theorem row150 : safe reference 6442452002=true ∧ bitRun reference 6442452002=bitRun TerminalInverse23.reference 6442452002 := row_all ⟨150,by decide⟩
theorem row151 : safe reference 15032386594=true ∧ bitRun reference 15032386594=bitRun TerminalInverse23.reference 15032386594 := row_all ⟨151,by decide⟩
theorem row152 : safe reference 6442452003=true ∧ bitRun reference 6442452003=bitRun TerminalInverse23.reference 6442452003 := row_all ⟨152,by decide⟩
theorem row153 : safe reference 15032386595=true ∧ bitRun reference 15032386595=bitRun TerminalInverse23.reference 15032386595 := row_all ⟨153,by decide⟩
theorem row154 : safe reference 10737418314=true ∧ bitRun reference 10737418314=bitRun TerminalInverse23.reference 10737418314 := row_all ⟨154,by decide⟩
theorem row155 : safe reference 27917287498=true ∧ bitRun reference 27917287498=bitRun TerminalInverse23.reference 27917287498 := row_all ⟨155,by decide⟩
theorem row156 : safe reference 10737418315=true ∧ bitRun reference 10737418315=bitRun TerminalInverse23.reference 10737418315 := row_all ⟨156,by decide⟩
theorem row157 : safe reference 27917287499=true ∧ bitRun reference 27917287499=bitRun TerminalInverse23.reference 27917287499 := row_all ⟨157,by decide⟩
theorem row158 : safe reference 1072=true ∧ bitRun reference 1072=bitRun TerminalInverse23.reference 1072 := row_all ⟨158,by decide⟩
theorem row159 : safe reference 4294968368=true ∧ bitRun reference 4294968368=bitRun TerminalInverse23.reference 4294968368 := row_all ⟨159,by decide⟩
theorem row160 : safe reference 1073=true ∧ bitRun reference 1073=bitRun TerminalInverse23.reference 1073 := row_all ⟨160,by decide⟩
theorem row161 : safe reference 4294968369=true ∧ bitRun reference 4294968369=bitRun TerminalInverse23.reference 4294968369 := row_all ⟨161,by decide⟩
theorem row162 : safe reference 12884902948=true ∧ bitRun reference 12884902948=bitRun TerminalInverse23.reference 12884902948 := row_all ⟨162,by decide⟩
theorem row163 : safe reference 4294968356=true ∧ bitRun reference 4294968356=bitRun TerminalInverse23.reference 4294968356 := row_all ⟨163,by decide⟩
theorem row164 : safe reference 12884902949=true ∧ bitRun reference 12884902949=bitRun TerminalInverse23.reference 12884902949 := row_all ⟨164,by decide⟩
theorem row165 : safe reference 4294968357=true ∧ bitRun reference 4294968357=bitRun TerminalInverse23.reference 4294968357 := row_all ⟨165,by decide⟩
theorem row166 : safe reference 10737419304=true ∧ bitRun reference 10737419304=bitRun TerminalInverse23.reference 10737419304 := row_all ⟨166,by decide⟩
theorem row167 : safe reference 2147484712=true ∧ bitRun reference 2147484712=bitRun TerminalInverse23.reference 2147484712 := row_all ⟨167,by decide⟩
theorem row168 : safe reference 10737419305=true ∧ bitRun reference 10737419305=bitRun TerminalInverse23.reference 10737419305 := row_all ⟨168,by decide⟩
theorem row169 : safe reference 2147484713=true ∧ bitRun reference 2147484713=bitRun TerminalInverse23.reference 2147484713 := row_all ⟨169,by decide⟩
theorem row170 : safe reference 1070=true ∧ bitRun reference 1070=bitRun TerminalInverse23.reference 1070 := row_all ⟨170,by decide⟩
theorem row171 : safe reference 8589935662=true ∧ bitRun reference 8589935662=bitRun TerminalInverse23.reference 8589935662 := row_all ⟨171,by decide⟩
theorem row172 : safe reference 1071=true ∧ bitRun reference 1071=bitRun TerminalInverse23.reference 1071 := row_all ⟨172,by decide⟩
theorem row173 : safe reference 8589935663=true ∧ bitRun reference 8589935663=bitRun TerminalInverse23.reference 8589935663 := row_all ⟨173,by decide⟩
theorem row174 : safe reference 25769803854=true ∧ bitRun reference 25769803854=bitRun TerminalInverse23.reference 25769803854 := row_all ⟨174,by decide⟩
theorem row175 : safe reference 8589934670=true ∧ bitRun reference 8589934670=bitRun TerminalInverse23.reference 8589934670 := row_all ⟨175,by decide⟩
theorem row176 : safe reference 25769803855=true ∧ bitRun reference 25769803855=bitRun TerminalInverse23.reference 25769803855 := row_all ⟨176,by decide⟩
theorem row177 : safe reference 8589934671=true ∧ bitRun reference 8589934671=bitRun TerminalInverse23.reference 8589934671 := row_all ⟨177,by decide⟩
theorem row178 : safe reference 1068=true ∧ bitRun reference 1068=bitRun TerminalInverse23.reference 1068 := row_all ⟨178,by decide⟩
theorem row179 : safe reference 8589935660=true ∧ bitRun reference 8589935660=bitRun TerminalInverse23.reference 8589935660 := row_all ⟨179,by decide⟩
theorem row180 : safe reference 1069=true ∧ bitRun reference 1069=bitRun TerminalInverse23.reference 1069 := row_all ⟨180,by decide⟩
theorem row181 : safe reference 8589935661=true ∧ bitRun reference 8589935661=bitRun TerminalInverse23.reference 8589935661 := row_all ⟨181,by decide⟩
theorem row182 : safe reference 1066=true ∧ bitRun reference 1066=bitRun TerminalInverse23.reference 1066 := row_all ⟨182,by decide⟩
theorem row183 : safe reference 8589935658=true ∧ bitRun reference 8589935658=bitRun TerminalInverse23.reference 8589935658 := row_all ⟨183,by decide⟩
theorem row184 : safe reference 1067=true ∧ bitRun reference 1067=bitRun TerminalInverse23.reference 1067 := row_all ⟨184,by decide⟩
theorem row185 : safe reference 8589935659=true ∧ bitRun reference 8589935659=bitRun TerminalInverse23.reference 8589935659 := row_all ⟨185,by decide⟩
theorem row186 : safe reference 12884902946=true ∧ bitRun reference 12884902946=bitRun TerminalInverse23.reference 12884902946 := row_all ⟨186,by decide⟩
theorem row187 : safe reference 4294968354=true ∧ bitRun reference 4294968354=bitRun TerminalInverse23.reference 4294968354 := row_all ⟨187,by decide⟩
theorem row188 : safe reference 12884902947=true ∧ bitRun reference 12884902947=bitRun TerminalInverse23.reference 12884902947 := row_all ⟨188,by decide⟩
theorem row189 : safe reference 4294968355=true ∧ bitRun reference 4294968355=bitRun TerminalInverse23.reference 4294968355 := row_all ⟨189,by decide⟩
theorem row190 : safe reference 1064=true ∧ bitRun reference 1064=bitRun TerminalInverse23.reference 1064 := row_all ⟨190,by decide⟩
theorem row191 : safe reference 8589935656=true ∧ bitRun reference 8589935656=bitRun TerminalInverse23.reference 8589935656 := row_all ⟨191,by decide⟩
theorem row192 : safe reference 1065=true ∧ bitRun reference 1065=bitRun TerminalInverse23.reference 1065 := row_all ⟨192,by decide⟩
theorem row193 : safe reference 8589935657=true ∧ bitRun reference 8589935657=bitRun TerminalInverse23.reference 8589935657 := row_all ⟨193,by decide⟩
theorem row194 : safe reference 25769803852=true ∧ bitRun reference 25769803852=bitRun TerminalInverse23.reference 25769803852 := row_all ⟨194,by decide⟩
theorem row195 : safe reference 8589934668=true ∧ bitRun reference 8589934668=bitRun TerminalInverse23.reference 8589934668 := row_all ⟨195,by decide⟩
theorem row196 : safe reference 25769803853=true ∧ bitRun reference 25769803853=bitRun TerminalInverse23.reference 25769803853 := row_all ⟨196,by decide⟩
theorem row197 : safe reference 8589934669=true ∧ bitRun reference 8589934669=bitRun TerminalInverse23.reference 8589934669 := row_all ⟨197,by decide⟩
theorem row198 : safe reference 1062=true ∧ bitRun reference 1062=bitRun TerminalInverse23.reference 1062 := row_all ⟨198,by decide⟩
theorem row199 : safe reference 8589935654=true ∧ bitRun reference 8589935654=bitRun TerminalInverse23.reference 8589935654 := row_all ⟨199,by decide⟩
theorem row200 : safe reference 1063=true ∧ bitRun reference 1063=bitRun TerminalInverse23.reference 1063 := row_all ⟨200,by decide⟩
theorem row201 : safe reference 8589935655=true ∧ bitRun reference 8589935655=bitRun TerminalInverse23.reference 8589935655 := row_all ⟨201,by decide⟩
theorem row202 : safe reference 1060=true ∧ bitRun reference 1060=bitRun TerminalInverse23.reference 1060 := row_all ⟨202,by decide⟩
theorem row203 : safe reference 8589935652=true ∧ bitRun reference 8589935652=bitRun TerminalInverse23.reference 8589935652 := row_all ⟨203,by decide⟩
theorem row204 : safe reference 1061=true ∧ bitRun reference 1061=bitRun TerminalInverse23.reference 1061 := row_all ⟨204,by decide⟩
theorem row205 : safe reference 8589935653=true ∧ bitRun reference 8589935653=bitRun TerminalInverse23.reference 8589935653 := row_all ⟨205,by decide⟩
theorem row206 : safe reference 12884902944=true ∧ bitRun reference 12884902944=bitRun TerminalInverse23.reference 12884902944 := row_all ⟨206,by decide⟩
theorem row207 : safe reference 4294968352=true ∧ bitRun reference 4294968352=bitRun TerminalInverse23.reference 4294968352 := row_all ⟨207,by decide⟩
theorem row208 : safe reference 12884902945=true ∧ bitRun reference 12884902945=bitRun TerminalInverse23.reference 12884902945 := row_all ⟨208,by decide⟩
theorem row209 : safe reference 4294968353=true ∧ bitRun reference 4294968353=bitRun TerminalInverse23.reference 4294968353 := row_all ⟨209,by decide⟩
theorem row210 : safe reference 1058=true ∧ bitRun reference 1058=bitRun TerminalInverse23.reference 1058 := row_all ⟨210,by decide⟩
theorem row211 : safe reference 8589935650=true ∧ bitRun reference 8589935650=bitRun TerminalInverse23.reference 8589935650 := row_all ⟨211,by decide⟩
theorem row212 : safe reference 1059=true ∧ bitRun reference 1059=bitRun TerminalInverse23.reference 1059 := row_all ⟨212,by decide⟩
theorem row213 : safe reference 8589935651=true ∧ bitRun reference 8589935651=bitRun TerminalInverse23.reference 8589935651 := row_all ⟨213,by decide⟩
theorem row214 : safe reference 25769803850=true ∧ bitRun reference 25769803850=bitRun TerminalInverse23.reference 25769803850 := row_all ⟨214,by decide⟩
theorem row215 : safe reference 8589934666=true ∧ bitRun reference 8589934666=bitRun TerminalInverse23.reference 8589934666 := row_all ⟨215,by decide⟩
theorem row216 : safe reference 25769803851=true ∧ bitRun reference 25769803851=bitRun TerminalInverse23.reference 25769803851 := row_all ⟨216,by decide⟩
theorem row217 : safe reference 8589934667=true ∧ bitRun reference 8589934667=bitRun TerminalInverse23.reference 8589934667 := row_all ⟨217,by decide⟩
theorem row218 : safe reference 1056=true ∧ bitRun reference 1056=bitRun TerminalInverse23.reference 1056 := row_all ⟨218,by decide⟩
theorem row219 : safe reference 8589935648=true ∧ bitRun reference 8589935648=bitRun TerminalInverse23.reference 8589935648 := row_all ⟨219,by decide⟩
theorem row220 : safe reference 1057=true ∧ bitRun reference 1057=bitRun TerminalInverse23.reference 1057 := row_all ⟨220,by decide⟩
theorem row221 : safe reference 8589935649=true ∧ bitRun reference 8589935649=bitRun TerminalInverse23.reference 8589935649 := row_all ⟨221,by decide⟩
theorem row222 : safe reference 94=true ∧ bitRun reference 94=bitRun TerminalInverse23.reference 94 := row_all ⟨222,by decide⟩
theorem row223 : safe reference 17179869278=true ∧ bitRun reference 17179869278=bitRun TerminalInverse23.reference 17179869278 := row_all ⟨223,by decide⟩
theorem row224 : safe reference 95=true ∧ bitRun reference 95=bitRun TerminalInverse23.reference 95 := row_all ⟨224,by decide⟩
theorem row225 : safe reference 17179869279=true ∧ bitRun reference 17179869279=bitRun TerminalInverse23.reference 17179869279 := row_all ⟨225,by decide⟩
theorem row226 : safe reference 92=true ∧ bitRun reference 92=bitRun TerminalInverse23.reference 92 := row_all ⟨226,by decide⟩
theorem row227 : safe reference 17179869276=true ∧ bitRun reference 17179869276=bitRun TerminalInverse23.reference 17179869276 := row_all ⟨227,by decide⟩
theorem row228 : safe reference 93=true ∧ bitRun reference 93=bitRun TerminalInverse23.reference 93 := row_all ⟨228,by decide⟩
theorem row229 : safe reference 17179869277=true ∧ bitRun reference 17179869277=bitRun TerminalInverse23.reference 17179869277 := row_all ⟨229,by decide⟩
theorem row230 : safe reference 90=true ∧ bitRun reference 90=bitRun TerminalInverse23.reference 90 := row_all ⟨230,by decide⟩
theorem row231 : safe reference 17179869274=true ∧ bitRun reference 17179869274=bitRun TerminalInverse23.reference 17179869274 := row_all ⟨231,by decide⟩
theorem row232 : safe reference 91=true ∧ bitRun reference 91=bitRun TerminalInverse23.reference 91 := row_all ⟨232,by decide⟩
theorem row233 : safe reference 17179869275=true ∧ bitRun reference 17179869275=bitRun TerminalInverse23.reference 17179869275 := row_all ⟨233,by decide⟩
theorem row234 : safe reference 88=true ∧ bitRun reference 88=bitRun TerminalInverse23.reference 88 := row_all ⟨234,by decide⟩
theorem row235 : safe reference 17179869272=true ∧ bitRun reference 17179869272=bitRun TerminalInverse23.reference 17179869272 := row_all ⟨235,by decide⟩
theorem row236 : safe reference 89=true ∧ bitRun reference 89=bitRun TerminalInverse23.reference 89 := row_all ⟨236,by decide⟩
theorem row237 : safe reference 17179869273=true ∧ bitRun reference 17179869273=bitRun TerminalInverse23.reference 17179869273 := row_all ⟨237,by decide⟩
theorem row238 : safe reference 86=true ∧ bitRun reference 86=bitRun TerminalInverse23.reference 86 := row_all ⟨238,by decide⟩
theorem row239 : safe reference 17179869270=true ∧ bitRun reference 17179869270=bitRun TerminalInverse23.reference 17179869270 := row_all ⟨239,by decide⟩
theorem row240 : safe reference 87=true ∧ bitRun reference 87=bitRun TerminalInverse23.reference 87 := row_all ⟨240,by decide⟩
theorem row241 : safe reference 17179869271=true ∧ bitRun reference 17179869271=bitRun TerminalInverse23.reference 17179869271 := row_all ⟨241,by decide⟩
theorem row242 : safe reference 84=true ∧ bitRun reference 84=bitRun TerminalInverse23.reference 84 := row_all ⟨242,by decide⟩
theorem row243 : safe reference 17179869268=true ∧ bitRun reference 17179869268=bitRun TerminalInverse23.reference 17179869268 := row_all ⟨243,by decide⟩
theorem row244 : safe reference 85=true ∧ bitRun reference 85=bitRun TerminalInverse23.reference 85 := row_all ⟨244,by decide⟩
theorem row245 : safe reference 17179869269=true ∧ bitRun reference 17179869269=bitRun TerminalInverse23.reference 17179869269 := row_all ⟨245,by decide⟩
theorem row246 : safe reference 82=true ∧ bitRun reference 82=bitRun TerminalInverse23.reference 82 := row_all ⟨246,by decide⟩
theorem row247 : safe reference 17179869266=true ∧ bitRun reference 17179869266=bitRun TerminalInverse23.reference 17179869266 := row_all ⟨247,by decide⟩
theorem row248 : safe reference 83=true ∧ bitRun reference 83=bitRun TerminalInverse23.reference 83 := row_all ⟨248,by decide⟩
theorem row249 : safe reference 17179869267=true ∧ bitRun reference 17179869267=bitRun TerminalInverse23.reference 17179869267 := row_all ⟨249,by decide⟩
theorem row250 : safe reference 80=true ∧ bitRun reference 80=bitRun TerminalInverse23.reference 80 := row_all ⟨250,by decide⟩
theorem row251 : safe reference 17179869264=true ∧ bitRun reference 17179869264=bitRun TerminalInverse23.reference 17179869264 := row_all ⟨251,by decide⟩
theorem row252 : safe reference 81=true ∧ bitRun reference 81=bitRun TerminalInverse23.reference 81 := row_all ⟨252,by decide⟩
theorem row253 : safe reference 17179869265=true ∧ bitRun reference 17179869265=bitRun TerminalInverse23.reference 17179869265 := row_all ⟨253,by decide⟩
theorem row254 : safe reference 78=true ∧ bitRun reference 78=bitRun TerminalInverse23.reference 78 := row_all ⟨254,by decide⟩
theorem row255 : safe reference 17179869262=true ∧ bitRun reference 17179869262=bitRun TerminalInverse23.reference 17179869262 := row_all ⟨255,by decide⟩
theorem row256 : safe reference 79=true ∧ bitRun reference 79=bitRun TerminalInverse23.reference 79 := row_all ⟨256,by decide⟩
theorem row257 : safe reference 17179869263=true ∧ bitRun reference 17179869263=bitRun TerminalInverse23.reference 17179869263 := row_all ⟨257,by decide⟩
theorem row258 : safe reference 76=true ∧ bitRun reference 76=bitRun TerminalInverse23.reference 76 := row_all ⟨258,by decide⟩
theorem row259 : safe reference 17179869260=true ∧ bitRun reference 17179869260=bitRun TerminalInverse23.reference 17179869260 := row_all ⟨259,by decide⟩
theorem row260 : safe reference 77=true ∧ bitRun reference 77=bitRun TerminalInverse23.reference 77 := row_all ⟨260,by decide⟩
theorem row261 : safe reference 17179869261=true ∧ bitRun reference 17179869261=bitRun TerminalInverse23.reference 17179869261 := row_all ⟨261,by decide⟩
theorem row262 : safe reference 74=true ∧ bitRun reference 74=bitRun TerminalInverse23.reference 74 := row_all ⟨262,by decide⟩
theorem row263 : safe reference 17179869258=true ∧ bitRun reference 17179869258=bitRun TerminalInverse23.reference 17179869258 := row_all ⟨263,by decide⟩
theorem row264 : safe reference 75=true ∧ bitRun reference 75=bitRun TerminalInverse23.reference 75 := row_all ⟨264,by decide⟩
theorem row265 : safe reference 17179869259=true ∧ bitRun reference 17179869259=bitRun TerminalInverse23.reference 17179869259 := row_all ⟨265,by decide⟩
theorem row266 : safe reference 72=true ∧ bitRun reference 72=bitRun TerminalInverse23.reference 72 := row_all ⟨266,by decide⟩
theorem row267 : safe reference 17179869256=true ∧ bitRun reference 17179869256=bitRun TerminalInverse23.reference 17179869256 := row_all ⟨267,by decide⟩
theorem row268 : safe reference 73=true ∧ bitRun reference 73=bitRun TerminalInverse23.reference 73 := row_all ⟨268,by decide⟩
theorem row269 : safe reference 17179869257=true ∧ bitRun reference 17179869257=bitRun TerminalInverse23.reference 17179869257 := row_all ⟨269,by decide⟩
theorem row270 : safe reference 70=true ∧ bitRun reference 70=bitRun TerminalInverse23.reference 70 := row_all ⟨270,by decide⟩
theorem row271 : safe reference 17179869254=true ∧ bitRun reference 17179869254=bitRun TerminalInverse23.reference 17179869254 := row_all ⟨271,by decide⟩
theorem row272 : safe reference 71=true ∧ bitRun reference 71=bitRun TerminalInverse23.reference 71 := row_all ⟨272,by decide⟩
theorem row273 : safe reference 17179869255=true ∧ bitRun reference 17179869255=bitRun TerminalInverse23.reference 17179869255 := row_all ⟨273,by decide⟩
theorem row274 : safe reference 68=true ∧ bitRun reference 68=bitRun TerminalInverse23.reference 68 := row_all ⟨274,by decide⟩
theorem row275 : safe reference 17179869252=true ∧ bitRun reference 17179869252=bitRun TerminalInverse23.reference 17179869252 := row_all ⟨275,by decide⟩
theorem row276 : safe reference 69=true ∧ bitRun reference 69=bitRun TerminalInverse23.reference 69 := row_all ⟨276,by decide⟩
theorem row277 : safe reference 17179869253=true ∧ bitRun reference 17179869253=bitRun TerminalInverse23.reference 17179869253 := row_all ⟨277,by decide⟩
theorem row278 : safe reference 66=true ∧ bitRun reference 66=bitRun TerminalInverse23.reference 66 := row_all ⟨278,by decide⟩
theorem row279 : safe reference 17179869250=true ∧ bitRun reference 17179869250=bitRun TerminalInverse23.reference 17179869250 := row_all ⟨279,by decide⟩
theorem row280 : safe reference 67=true ∧ bitRun reference 67=bitRun TerminalInverse23.reference 67 := row_all ⟨280,by decide⟩
theorem row281 : safe reference 17179869251=true ∧ bitRun reference 17179869251=bitRun TerminalInverse23.reference 17179869251 := row_all ⟨281,by decide⟩
theorem row282 : safe reference 64=true ∧ bitRun reference 64=bitRun TerminalInverse23.reference 64 := row_all ⟨282,by decide⟩
theorem row283 : safe reference 17179869248=true ∧ bitRun reference 17179869248=bitRun TerminalInverse23.reference 17179869248 := row_all ⟨283,by decide⟩
theorem row284 : safe reference 65=true ∧ bitRun reference 65=bitRun TerminalInverse23.reference 65 := row_all ⟨284,by decide⟩
theorem row285 : safe reference 17179869249=true ∧ bitRun reference 17179869249=bitRun TerminalInverse23.reference 17179869249 := row_all ⟨285,by decide⟩

end ECDSAAdd.Entrant.TerminalFiveShifted

end

-- Adapted public peer module: TerminalFivePreTransport
section

namespace ECDSAAdd.Entrant.TerminalFivePreTransport
open ECDSAAdd Arithmetic MappedCompressed CompactCertificates
open TerminalFiveDomain
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

def perm := TerminalFivePermutation.perm

theorem pre_supp (g s : Bool) (uv : Nat×Nat) (q : Wire) (hq : q∉sites) :
    pre g s uv.1 uv.2 q=false := by
  simp only [sites,List.mem_cons,List.not_mem_nil,or_false,not_or] at hq
  simp_all [pre]

theorem sitesTable : sites.all (fun q=>decide (perm.symm q<40))=true := by decide +kernel

def preDense (g s : Bool) (uv : Nat×Nat) : Nat :=
  encN_t8 (fun q=>pre g s uv.1 uv.2 (perm q)) (List.range 40)

theorem pre_pull (g s : Bool) (uv : Nat×Nat) :
    pullState perm ⟨false,pre g s uv.1 uv.2⟩ = ⟨false,MeasuredCodec5.bitsOf (preDense g s uv)⟩ := by
  have supp : ∀q : Wire,pre g s uv.1 uv.2 (perm q)=true → q∈List.range 40 := by
    intro q yes
    have member : perm q∈sites := by
      by_contra no
      rw [pre_supp g s uv (perm q) no] at yes
      contradiction
    have table := sitesTable
    simp only [List.all_eq_true,decide_eq_true_eq] at table
    have small := table (perm q) member
    simpa only [List.mem_range,Equiv.symm_apply_apply] using small
  have enc := tb_enc_t8 (fun q=>pre g s uv.1 uv.2 (perm q)) (List.range 40) supp
  apply State.extensionality
  · rfl
  · change (fun q=>pre g s uv.1 uv.2 (perm q))=tbN_t8 (preDense g s uv)
    exact enc

end ECDSAAdd.Entrant.TerminalFivePreTransport

end

-- Adapted public peer module: TerminalFiveShiftedRows
section

namespace ECDSAAdd.Entrant.TerminalFiveShiftedRows
open ECDSAAdd Arithmetic MeasuredCodec5
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run safe bitRun TerminalInverse23.program TerminalInverse23.reference TerminalFiveShifted.reference

def rowInputs : List Nat := [1086, 1087, 1084, 1073742908, 1085, 1073742909, 3221226552, 1073742904, 3221226553, 1073742905, 5368710196, 1073742900, 5368710197, 1073742901, 5368710192, 1073742896, 5368710193, 1073742897, 9663677484, 1073742892, 9663677485, 1073742893, 9663677480, 1073742888, 9663677481, 1073742889, 9663677476, 1073742884, 9663677477, 1073742885, 9663677472, 1073742880, 9663677473, 1073742881, 18253611100, 1073741916, 18253611101, 1073741917, 18253611096, 1073741912, 18253611097, 1073741913, 18253611092, 1073741908, 18253611093, 1073741909, 18253611088, 1073741904, 18253611089, 1073741905, 18253611084, 1073741900, 18253611085, 1073741901, 18253611080, 1073741896, 18253611081, 1073741897, 18253611076, 1073741892, 18253611077, 1073741893, 18253611072, 1073741888, 18253611073, 1073741889, 1082, 2147484730, 1083, 2147484731, 6442452018, 2147484722, 6442452019, 2147484723, 10737419306, 2147484714, 10737419307, 2147484715, 10737419298, 2147484706, 10737419299, 2147484707, 19327352922, 2147483738, 19327352923, 2147483739, 19327352914, 2147483730, 19327352915, 2147483731, 19327352906, 2147483722, 19327352907, 2147483723, 19327352898, 2147483714, 19327352899, 2147483715, 1080, 2147484728, 1081, 2147484729, 3221226544, 7516193840, 3221226545, 7516193841, 5368710180, 13958644772, 5368710181, 13958644773, 9663676492, 26843545676, 9663676493, 26843545677, 5368710176, 13958644768, 5368710177, 13958644769, 1078, 4294968374, 1079, 4294968375, 12884902950, 4294968358, 12884902951, 4294968359, 21474836566, 4294967382, 21474836567, 4294967383, 21474836550, 4294967366, 21474836551, 4294967367, 1076, 4294968372, 1077, 4294968373, 6442452016, 2147484720, 6442452017, 2147484721, 3221226536, 11811161128, 3221226537, 11811161129, 1074, 4294968370, 1075, 4294968371, 6442452002, 15032386594, 6442452003, 15032386595, 10737418314, 27917287498, 10737418315, 27917287499, 1072, 4294968368, 1073, 4294968369, 12884902948, 4294968356, 12884902949, 4294968357, 10737419304, 2147484712, 10737419305, 2147484713, 1070, 8589935662, 1071, 8589935663, 25769803854, 8589934670, 25769803855, 8589934671, 1068, 8589935660, 1069, 8589935661, 1066, 8589935658, 1067, 8589935659, 12884902946, 4294968354, 12884902947, 4294968355, 1064, 8589935656, 1065, 8589935657, 25769803852, 8589934668, 25769803853, 8589934669, 1062, 8589935654, 1063, 8589935655, 1060, 8589935652, 1061, 8589935653, 12884902944, 4294968352, 12884902945, 4294968353, 1058, 8589935650, 1059, 8589935651, 25769803850, 8589934666, 25769803851, 8589934667, 1056, 8589935648, 1057, 8589935649, 94, 17179869278, 95, 17179869279, 92, 17179869276, 93, 17179869277, 90, 17179869274, 91, 17179869275, 88, 17179869272, 89, 17179869273, 86, 17179869270, 87, 17179869271, 84, 17179869268, 85, 17179869269, 82, 17179869266, 83, 17179869267, 80, 17179869264, 81, 17179869265, 78, 17179869262, 79, 17179869263, 76, 17179869260, 77, 17179869261, 74, 17179869258, 75, 17179869259, 72, 17179869256, 73, 17179869257, 70, 17179869254, 71, 17179869255, 68, 17179869252, 69, 17179869253, 66, 17179869250, 67, 17179869251, 64, 17179869248, 65, 17179869249]



theorem laws : ∀v∈rowInputs, safe TerminalFiveShifted.reference v=true ∧
    bitRun TerminalFiveShifted.reference v=bitRun TerminalInverse23.reference v := by
  simp (config := {maxSteps:=4000000}) only [rowInputs,List.forall_mem_cons]
  exact ⟨TerminalFiveShifted.row0,⟨TerminalFiveShifted.row1,⟨TerminalFiveShifted.row2,⟨TerminalFiveShifted.row3,⟨TerminalFiveShifted.row4,⟨TerminalFiveShifted.row5,⟨TerminalFiveShifted.row6,⟨TerminalFiveShifted.row7,⟨TerminalFiveShifted.row8,⟨TerminalFiveShifted.row9,⟨TerminalFiveShifted.row10,⟨TerminalFiveShifted.row11,⟨TerminalFiveShifted.row12,⟨TerminalFiveShifted.row13,⟨TerminalFiveShifted.row14,⟨TerminalFiveShifted.row15,⟨TerminalFiveShifted.row16,⟨TerminalFiveShifted.row17,⟨TerminalFiveShifted.row18,⟨TerminalFiveShifted.row19,⟨TerminalFiveShifted.row20,⟨TerminalFiveShifted.row21,⟨TerminalFiveShifted.row22,⟨TerminalFiveShifted.row23,⟨TerminalFiveShifted.row24,⟨TerminalFiveShifted.row25,⟨TerminalFiveShifted.row26,⟨TerminalFiveShifted.row27,⟨TerminalFiveShifted.row28,⟨TerminalFiveShifted.row29,⟨TerminalFiveShifted.row30,⟨TerminalFiveShifted.row31,⟨TerminalFiveShifted.row32,⟨TerminalFiveShifted.row33,⟨TerminalFiveShifted.row34,⟨TerminalFiveShifted.row35,⟨TerminalFiveShifted.row36,⟨TerminalFiveShifted.row37,⟨TerminalFiveShifted.row38,⟨TerminalFiveShifted.row39,⟨TerminalFiveShifted.row40,⟨TerminalFiveShifted.row41,⟨TerminalFiveShifted.row42,⟨TerminalFiveShifted.row43,⟨TerminalFiveShifted.row44,⟨TerminalFiveShifted.row45,⟨TerminalFiveShifted.row46,⟨TerminalFiveShifted.row47,⟨TerminalFiveShifted.row48,⟨TerminalFiveShifted.row49,⟨TerminalFiveShifted.row50,⟨TerminalFiveShifted.row51,⟨TerminalFiveShifted.row52,⟨TerminalFiveShifted.row53,⟨TerminalFiveShifted.row54,⟨TerminalFiveShifted.row55,⟨TerminalFiveShifted.row56,⟨TerminalFiveShifted.row57,⟨TerminalFiveShifted.row58,⟨TerminalFiveShifted.row59,⟨TerminalFiveShifted.row60,⟨TerminalFiveShifted.row61,⟨TerminalFiveShifted.row62,⟨TerminalFiveShifted.row63,⟨TerminalFiveShifted.row64,⟨TerminalFiveShifted.row65,⟨TerminalFiveShifted.row66,⟨TerminalFiveShifted.row67,⟨TerminalFiveShifted.row68,⟨TerminalFiveShifted.row69,⟨TerminalFiveShifted.row70,⟨TerminalFiveShifted.row71,⟨TerminalFiveShifted.row72,⟨TerminalFiveShifted.row73,⟨TerminalFiveShifted.row74,⟨TerminalFiveShifted.row75,⟨TerminalFiveShifted.row76,⟨TerminalFiveShifted.row77,⟨TerminalFiveShifted.row78,⟨TerminalFiveShifted.row79,⟨TerminalFiveShifted.row80,⟨TerminalFiveShifted.row81,⟨TerminalFiveShifted.row82,⟨TerminalFiveShifted.row83,⟨TerminalFiveShifted.row84,⟨TerminalFiveShifted.row85,⟨TerminalFiveShifted.row86,⟨TerminalFiveShifted.row87,⟨TerminalFiveShifted.row88,⟨TerminalFiveShifted.row89,⟨TerminalFiveShifted.row90,⟨TerminalFiveShifted.row91,⟨TerminalFiveShifted.row92,⟨TerminalFiveShifted.row93,⟨TerminalFiveShifted.row94,⟨TerminalFiveShifted.row95,⟨TerminalFiveShifted.row96,⟨TerminalFiveShifted.row97,⟨TerminalFiveShifted.row98,⟨TerminalFiveShifted.row99,⟨TerminalFiveShifted.row100,⟨TerminalFiveShifted.row101,⟨TerminalFiveShifted.row102,⟨TerminalFiveShifted.row103,⟨TerminalFiveShifted.row104,⟨TerminalFiveShifted.row105,⟨TerminalFiveShifted.row106,⟨TerminalFiveShifted.row107,⟨TerminalFiveShifted.row108,⟨TerminalFiveShifted.row109,⟨TerminalFiveShifted.row110,⟨TerminalFiveShifted.row111,⟨TerminalFiveShifted.row112,⟨TerminalFiveShifted.row113,⟨TerminalFiveShifted.row114,⟨TerminalFiveShifted.row115,⟨TerminalFiveShifted.row116,⟨TerminalFiveShifted.row117,⟨TerminalFiveShifted.row118,⟨TerminalFiveShifted.row119,⟨TerminalFiveShifted.row120,⟨TerminalFiveShifted.row121,⟨TerminalFiveShifted.row122,⟨TerminalFiveShifted.row123,⟨TerminalFiveShifted.row124,⟨TerminalFiveShifted.row125,⟨TerminalFiveShifted.row126,⟨TerminalFiveShifted.row127,⟨TerminalFiveShifted.row128,⟨TerminalFiveShifted.row129,⟨TerminalFiveShifted.row130,⟨TerminalFiveShifted.row131,⟨TerminalFiveShifted.row132,⟨TerminalFiveShifted.row133,⟨TerminalFiveShifted.row134,⟨TerminalFiveShifted.row135,⟨TerminalFiveShifted.row136,⟨TerminalFiveShifted.row137,⟨TerminalFiveShifted.row138,⟨TerminalFiveShifted.row139,⟨TerminalFiveShifted.row140,⟨TerminalFiveShifted.row141,⟨TerminalFiveShifted.row142,⟨TerminalFiveShifted.row143,⟨TerminalFiveShifted.row144,⟨TerminalFiveShifted.row145,⟨TerminalFiveShifted.row146,⟨TerminalFiveShifted.row147,⟨TerminalFiveShifted.row148,⟨TerminalFiveShifted.row149,⟨TerminalFiveShifted.row150,⟨TerminalFiveShifted.row151,⟨TerminalFiveShifted.row152,⟨TerminalFiveShifted.row153,⟨TerminalFiveShifted.row154,⟨TerminalFiveShifted.row155,⟨TerminalFiveShifted.row156,⟨TerminalFiveShifted.row157,⟨TerminalFiveShifted.row158,⟨TerminalFiveShifted.row159,⟨TerminalFiveShifted.row160,⟨TerminalFiveShifted.row161,⟨TerminalFiveShifted.row162,⟨TerminalFiveShifted.row163,⟨TerminalFiveShifted.row164,⟨TerminalFiveShifted.row165,⟨TerminalFiveShifted.row166,⟨TerminalFiveShifted.row167,⟨TerminalFiveShifted.row168,⟨TerminalFiveShifted.row169,⟨TerminalFiveShifted.row170,⟨TerminalFiveShifted.row171,⟨TerminalFiveShifted.row172,⟨TerminalFiveShifted.row173,⟨TerminalFiveShifted.row174,⟨TerminalFiveShifted.row175,⟨TerminalFiveShifted.row176,⟨TerminalFiveShifted.row177,⟨TerminalFiveShifted.row178,⟨TerminalFiveShifted.row179,⟨TerminalFiveShifted.row180,⟨TerminalFiveShifted.row181,⟨TerminalFiveShifted.row182,⟨TerminalFiveShifted.row183,⟨TerminalFiveShifted.row184,⟨TerminalFiveShifted.row185,⟨TerminalFiveShifted.row186,⟨TerminalFiveShifted.row187,⟨TerminalFiveShifted.row188,⟨TerminalFiveShifted.row189,⟨TerminalFiveShifted.row190,⟨TerminalFiveShifted.row191,⟨TerminalFiveShifted.row192,⟨TerminalFiveShifted.row193,⟨TerminalFiveShifted.row194,⟨TerminalFiveShifted.row195,⟨TerminalFiveShifted.row196,⟨TerminalFiveShifted.row197,⟨TerminalFiveShifted.row198,⟨TerminalFiveShifted.row199,⟨TerminalFiveShifted.row200,⟨TerminalFiveShifted.row201,⟨TerminalFiveShifted.row202,⟨TerminalFiveShifted.row203,⟨TerminalFiveShifted.row204,⟨TerminalFiveShifted.row205,⟨TerminalFiveShifted.row206,⟨TerminalFiveShifted.row207,⟨TerminalFiveShifted.row208,⟨TerminalFiveShifted.row209,⟨TerminalFiveShifted.row210,⟨TerminalFiveShifted.row211,⟨TerminalFiveShifted.row212,⟨TerminalFiveShifted.row213,⟨TerminalFiveShifted.row214,⟨TerminalFiveShifted.row215,⟨TerminalFiveShifted.row216,⟨TerminalFiveShifted.row217,⟨TerminalFiveShifted.row218,⟨TerminalFiveShifted.row219,⟨TerminalFiveShifted.row220,⟨TerminalFiveShifted.row221,⟨TerminalFiveShifted.row222,⟨TerminalFiveShifted.row223,⟨TerminalFiveShifted.row224,⟨TerminalFiveShifted.row225,⟨TerminalFiveShifted.row226,⟨TerminalFiveShifted.row227,⟨TerminalFiveShifted.row228,⟨TerminalFiveShifted.row229,⟨TerminalFiveShifted.row230,⟨TerminalFiveShifted.row231,⟨TerminalFiveShifted.row232,⟨TerminalFiveShifted.row233,⟨TerminalFiveShifted.row234,⟨TerminalFiveShifted.row235,⟨TerminalFiveShifted.row236,⟨TerminalFiveShifted.row237,⟨TerminalFiveShifted.row238,⟨TerminalFiveShifted.row239,⟨TerminalFiveShifted.row240,⟨TerminalFiveShifted.row241,⟨TerminalFiveShifted.row242,⟨TerminalFiveShifted.row243,⟨TerminalFiveShifted.row244,⟨TerminalFiveShifted.row245,⟨TerminalFiveShifted.row246,⟨TerminalFiveShifted.row247,⟨TerminalFiveShifted.row248,⟨TerminalFiveShifted.row249,⟨TerminalFiveShifted.row250,⟨TerminalFiveShifted.row251,⟨TerminalFiveShifted.row252,⟨TerminalFiveShifted.row253,⟨TerminalFiveShifted.row254,⟨TerminalFiveShifted.row255,⟨TerminalFiveShifted.row256,⟨TerminalFiveShifted.row257,⟨TerminalFiveShifted.row258,⟨TerminalFiveShifted.row259,⟨TerminalFiveShifted.row260,⟨TerminalFiveShifted.row261,⟨TerminalFiveShifted.row262,⟨TerminalFiveShifted.row263,⟨TerminalFiveShifted.row264,⟨TerminalFiveShifted.row265,⟨TerminalFiveShifted.row266,⟨TerminalFiveShifted.row267,⟨TerminalFiveShifted.row268,⟨TerminalFiveShifted.row269,⟨TerminalFiveShifted.row270,⟨TerminalFiveShifted.row271,⟨TerminalFiveShifted.row272,⟨TerminalFiveShifted.row273,⟨TerminalFiveShifted.row274,⟨TerminalFiveShifted.row275,⟨TerminalFiveShifted.row276,⟨TerminalFiveShifted.row277,⟨TerminalFiveShifted.row278,⟨TerminalFiveShifted.row279,⟨TerminalFiveShifted.row280,⟨TerminalFiveShifted.row281,⟨TerminalFiveShifted.row282,⟨TerminalFiveShifted.row283,⟨TerminalFiveShifted.row284,⟨TerminalFiveShifted.row285,by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem allRows (v : Nat) (member : v∈rowInputs) (m n : List Bool) :
    run TerminalInverse23.program m ⟨false,bitsOf v⟩=run TerminalFiveShifted.reference n ⟨false,bitsOf v⟩ := by
  have a := TerminalFiveRows.laws v member
  have b := laws v member
  exact TerminalSafeEq.of_law _ _ v ⟨a.1,b.1,a.2.2.trans b.2.symm⟩ m n

end ECDSAAdd.Entrant.TerminalFiveShiftedRows

end

-- Adapted public peer module: TerminalFivePlacement
section

namespace ECDSAAdd.Entrant.TerminalFivePlacement
open ECDSAAdd Arithmetic MappedCompressed Challenge History5 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires Rolling1588.reverse Rolling1588.Integer.reverse

def shiftedReceiver : Program := renameProgram (fun q=>sig 510 (sig 506 q))
  (W.ReverseCarry.compactReceiverTick base 506)

def old : Program := Inverse14Width.candidate ++ shiftedReceiver

theorem shifted_placed : renameProgram (sig 510) shiftedReceiver=
    renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506) := by
  rw [shiftedReceiver,renameProgram_comp]
  have same : (sig 510 ∘ fun q=>sig 510 (sig 506 q))=sig 506 := by
    funext q
    exact sig_invol 510 (by omega) (sig 506 q)
  rw [same]

theorem old_placed : renameProgram (sig 510) old=
    renameProgram (sig 510) Inverse14Width.candidate ++
      renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506) := by
  simp only [old,renameProgram,List.map_append]
  exact congrArg (fun tail=>renameProgram (sig 510) Inverse14Width.candidate ++ tail) shifted_placed

theorem unpack506 (isA : Bool) : unpackFirst base isA 506=[] := by
  simp only [unpackFirst,show ¬(506:Nat)=5 from by decide,if_false,Rolling1588.Integer.decodeBefore,
    show History5.packDue 506=false from by decide,Bool.false_eq_true,if_false]

theorem reverse_shape (isA : Bool) :
    InverseFour15.stackReverse15 isA = renameProgram (sig 511) tickR ++
      (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ old) ++
        Rolling1588.reverse isA 1 505) := by
  have shape := reverse_snoc isA 1 505
  rw [show (1:Nat)+505=506 by rfl,unpack506,List.nil_append] at shape
  rw [reverse_eq_packets,reverse_eq_packets] at shape
  rw [InverseFour15.stackReverse15,InverseFour15.reverseTail15,shape]
  have ren (P Q : Program) : renameProgram (sig 510) (P++Q)=
      renameProgram (sig 510) P ++ renameProgram (sig 510) Q := by
    simp only [renameProgram,List.map_append]
  simp only [ren,old_placed,InverseFour15.candidate15,List.append_assoc]

end ECDSAAdd.Entrant.TerminalFivePlacement

end

-- Adapted public peer module: TerminalFiveSampleCore
section

namespace ECDSAAdd.Entrant.TerminalFiveSample
open ECDSAAdd Arithmetic MappedCompressed Challenge CompactCertificates
open TerminalFiveBridge
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

def model (g s : Bool) (uv : Nat×Nat) : State :=
  ⟨false,(run forward [] ⟨false,TerminalFiveDomain.pre g s uv.1 uv.2⟩).basis⟩

theorem model_pull (g s : Bool) (uv : Nat×Nat) :
    pullState perm (model g s uv)=⟨false,MeasuredCodec5.bitsOf (postDense g s uv)⟩ := by
  have start : pullState perm ⟨false,TerminalFiveDomain.pre g s uv.1 uv.2⟩=
      ⟨false,MeasuredCodec5.bitsOf (preDense g s uv)⟩ := TerminalFivePreTransport.pre_pull g s uv
  have eq := ECDSAAdd.run_rename perm perm.injective forwardDense []
    ⟨false,TerminalFiveDomain.pre g s uv.1 uv.2⟩
  rw [forward_placement,start,MeasuredCodec5.run_sim] at eq
  apply State.extensionality
  · rfl
  · have basis := congrArg State.basis eq
    simpa only [model,pullState,Rolling1588.Replay.sim_basis,postDense] using basis

theorem shifted_placement : renameProgram perm TerminalFiveShifted.reference=TerminalFivePlacement.old := by
  decide +kernel

theorem sample_run (g s : Bool) (uv : Nat×Nat) (member : uv∈TerminalFiveDomain.pairs)
    (m n : List Bool) : run physical m (model g s uv)=run TerminalFivePlacement.old n (model g s uv) := by
  have table := inputTable
  simp only [List.all_eq_true] at table
  have row := table uv member
  simp only [checkInput,List.all_eq_true] at row
  have mem := row g (by cases g <;> simp) s (by cases s <;> simp)
  simp only [decide_eq_true_eq] at mem
  have same := TerminalFiveShiftedRows.allRows (postDense g s uv) mem m n
  rw [←shifted_placement]
  unfold physical
  apply pull_injective perm
  rw [ECDSAAdd.run_rename perm perm.injective,ECDSAAdd.run_rename perm perm.injective,model_pull]
  exact same


end ECDSAAdd.Entrant.TerminalFiveSample

end

-- Adapted public peer module: TerminalFiveSupport
section

namespace ECDSAAdd.Entrant.TerminalFiveSample
open ECDSAAdd Arithmetic MappedCompressed Challenge CompactCertificates
open TerminalFiveBridge
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

theorem physical_support : wires physical ⊆ TerminalFiveDomain.sites.toFinset := by
  have table : ∀i∈Finset.range 40,perm i∈TerminalFiveDomain.sites := by decide +kernel
  intro q hq
  rw [physical,renameProgram_support] at hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  exact List.mem_toFinset.mpr (table i (TerminalInverse23.support hi))

theorem old_support : wires TerminalFivePlacement.old ⊆ TerminalFiveDomain.sites.toFinset := by
  have contain : Inverse14Width.sites.toFinset ⊆ TerminalFiveDomain.sites.toFinset := by decide +kernel
  rw [TerminalFivePlacement.old,wires_append,Finset.union_subset_iff]
  exact ⟨Inverse14Width.support.trans contain,by decide +kernel⟩

theorem forward_support : wires forward ⊆ TerminalFiveDomain.sites.toFinset := by
  have contain : InverseFour15.sites15.toFinset ⊆ TerminalFiveDomain.sites.toFinset := by decide +kernel
  rw [forward,wires_append,Finset.union_subset_iff]
  exact ⟨by decide +kernel,InverseFour15.forward_support.trans contain⟩


end ECDSAAdd.Entrant.TerminalFiveSample

end

-- Adapted public peer module: LocalWindowReplace
section

namespace ECDSAAdd.Entrant.LocalWindowReplace
open ECDSAAdd Arithmetic
set_option maxRecDepth 30000
set_option maxHeartbeats 0
attribute [local irreducible] run wires

theorem after_forward (P Q F : Program) (sites : List Wire)
    (hp : wires P⊆sites.toFinset) (hq : wires Q⊆sites.toFinset) (hf : wires F⊆sites.toFinset)
    (a state : State) (pre : BasisState)
    (reads : ∀q∈sites,a.basis q=pre q)
    (agree : ∀q∈sites,state.basis q=(run F [] a).basis q)
    (m n : List Bool)
    (law : run P m ⟨false,(run F [] ⟨false,pre⟩).basis⟩=
      run Q n ⟨false,(run F [] ⟨false,pre⟩).basis⟩) : run P m state=run Q n state := by
  apply Stack5.local_replace P Q sites.toFinset hp hq state
    ⟨false,(run F [] ⟨false,pre⟩).basis⟩ m n
  · intro q hmem
    have member := List.mem_toFinset.mp hmem
    exact (agree q member).trans (site_run F sites hf a ⟨false,pre⟩ reads [] q member)
  · exact law

end ECDSAAdd.Entrant.LocalWindowReplace

end

-- Adapted public peer module: TerminalFiveSample
section

namespace ECDSAAdd.Entrant.TerminalFiveSample
open ECDSAAdd Arithmetic MappedCompressed Challenge CompactCertificates
open TerminalFiveBridge
set_option maxRecDepth 30000
set_option maxHeartbeats 400000
set_option diagnostics true
attribute [local irreducible] run wires

theorem stage_replace (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p)
    (a state : State) (stage : Rolling1588.Integer.Stage base isA x ECDSAAdd.p 506 a.basis)
    (m n : List Bool)
    (agree : ∀q∈TerminalFiveDomain.sites,state.basis q=(run forward [] a).basis q) :
    run physical m state=run TerminalFivePlacement.old n state := by
  obtain ⟨g,s,uv,member,reads⟩ := TerminalFiveDomain.stage506 isA x hx0 hx a stage
  exact LocalWindowReplace.after_forward physical TerminalFivePlacement.old forward TerminalFiveDomain.sites
    physical_support old_support forward_support a state (TerminalFiveDomain.pre g s uv.1 uv.2)
    reads agree m n (sample_run g s uv member m n)

end ECDSAAdd.Entrant.TerminalFiveSample

end

-- Adapted public peer module: TerminalBorrowB
section

namespace ECDSAAdd.Entrant.TerminalBorrowB
open ECDSAAdd Arithmetic MappedCompressed History5 OB5
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires Rolling1588.reverse Rolling1588.Integer.reverse

def sites : List Wire := List.range' 793 13

theorem first_prefix : sites.toFinset ⊆ wires ((W.ReverseCarry.compactReceiverTick base 1).take 24) := by
  decide +kernel

theorem take_subset (P : Program) (n : Nat) : wires (P.take n)⊆wires P := by
  have sub : wires (P.take n)⊆wires (P.take n++P.drop n) := by
    rw [wires_append]
    exact Finset.subset_union_left
  simpa only [List.take_append_drop] using sub

theorem first_sites : sites.toFinset ⊆ wires (W.ReverseCarry.compactReceiverTick base 1) :=
  first_prefix.trans (take_subset _ 24)

theorem sig_fixed : ∀q∈sites, sig 1 q=q := by decide +kernel

theorem unpack1 (isA : Bool) : Rolling1588.Integer.unpackFirst base isA 1=[] := by
  simp only [Rolling1588.Integer.unpackFirst,show ¬(1:Nat)=5 from by decide,if_false,
    Rolling1588.Integer.decodeBefore,show History5.packDue 1=false from by decide,
    Bool.false_eq_true,if_false]

theorem reverse_sites (isA : Bool) : sites.toFinset ⊆ wires (Rolling1588.reverse isA 1 505) := by
  intro q hq
  have member : q∈wires (renameProgram (sig 1) (W.ReverseCarry.compactReceiverTick base 1)) := by
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨q,first_sites hq,sig_fixed q (List.mem_toFinset.mp hq)⟩
  rw [←Rolling1588.Integer.reverse_eq_packets,Rolling1588.Integer.reverse,wires_append]
  apply Finset.mem_union_right
  simpa only [unpack1,List.nil_append] using member

end ECDSAAdd.Entrant.TerminalBorrowB

end

-- Adapted public peer module: TerminalFiveLiveSupport
section

namespace ECDSAAdd.Entrant.TerminalFiveLiveSupport
open ECDSAAdd Arithmetic MappedCompressed Challenge OB5
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
attribute [local irreducible] run wires

def liveCheck (i : Instr) : Bool :=
  decide (i.wires ⊆ ((Finset.range 40).erase 38).erase 39)

theorem program_live : wires TerminalInverse23.program ⊆ ((Finset.range 40).erase 38).erase 39 := by
  apply CodecBitSliceVerify.wires_of_instructions
  intro i hi
  have checked : TerminalInverse23.program.all liveCheck = true := by decide +kernel
  exact of_decide_eq_true ((List.all_eq_true.mp checked) i hi)

def leftIndices : List Nat := [0, 21, 18, 15, 12, 1, 0, 61, 107, 877, 2, 209, 262, 376, 449, 527, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 5, 3, 3, 611, 698, 784, 0, 0]
def rightIndices : List Nat := [2, 2, 13, 14, 15, 16, 17, 1, 1, 0, 7, 8, 9, 10, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 39, 21, 27, 33, 0, 0]

def checkSite (i : Nat) : Bool :=
  if i=38 ∨ i=39 then true else
    let q:=sig 510 (TerminalFiveBridge.perm i)
    WireWitness.atWire (renameProgram (sig 510) Inverse14Width.candidate) q leftIndices[i]! ||
    WireWitness.atWire (renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)) q rightIndices[i]! ||
    decide (q∈TerminalBorrowB.sites)

theorem sites_checked : (List.range 40).all checkSite=true := by decide +kernel

theorem placed_local : wires (renameProgram (sig 510) TerminalFiveBridge.physical) ⊆
    wires (renameProgram (sig 510) Inverse14Width.candidate) ∪
    wires (renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)) ∪
    TerminalBorrowB.sites.toFinset := by
  intro q hq
  rw [TerminalFiveBridge.physical,renameProgram_comp,renameProgram_support] at hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  have live:=program_live hi
  have no39 : i≠39 := (Finset.mem_erase.mp live).1
  have next:=(Finset.mem_erase.mp live).2
  have no38 : i≠38 := (Finset.mem_erase.mp next).1
  have small:=Finset.mem_range.mp (Finset.mem_erase.mp next).2
  have table:=List.all_eq_true.mp sites_checked
  have checked:=table i (List.mem_range.mpr small)
  simp only [checkSite,if_neg (not_or.mpr ⟨no38,no39⟩),Bool.or_eq_true,decide_eq_true_eq] at checked
  rcases checked with (h|h)|h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (WireWitness.atWire_sound _ _ _ h))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (WireWitness.atWire_sound _ _ _ h))
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr h)

end ECDSAAdd.Entrant.TerminalFiveLiveSupport

end

-- Adapted public peer module: InverseFive23
section

namespace ECDSAAdd.Entrant.InverseFive23
open ECDSAAdd Arithmetic MappedCompressed Challenge History5 OB5
open Rolling1588.Integer
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward regularForward

def candidate15 : Program := TerminalFiveBridge.physical

def reverseTail15 (isA : Bool) : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510 ++ candidate15) ++
    Rolling1588.reverse isA 1 505

def stackReverse15 (isA : Bool) : Program := renameProgram (sig 511) tickR ++ reverseTail15 isA

theorem resources : toffoliCount candidate15=23 ∧ measurementCount candidate15=16 ∧
    Challenge.gateSlots candidate15=1633 := by
  have h:=TerminalInverse23.counts
  simpa only [candidate15,TerminalFiveBridge.physical,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots] using h

theorem old_resources : toffoliCount TerminalFivePlacement.old=24 ∧
    measurementCount TerminalFivePlacement.old=16 ∧ Challenge.gateSlots TerminalFivePlacement.old=1482 := by
  have a:=Inverse14Width.resources
  have b : toffoliCount (W.ReverseCarry.compactReceiverTick base 506)=10 ∧
      measurementCount (W.ReverseCarry.compactReceiverTick base 506)=5 ∧
      Challenge.gateSlots (W.ReverseCarry.compactReceiverTick base 506)=109 := by decide +kernel
  simp only [TerminalFivePlacement.old,TerminalFivePlacement.shiftedReceiver,toffoliCount_append,
    measurementCount_append,Challenge.gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,Baselines.rename_gateSlots]
  omega

theorem candidate_physical : GatePhysical candidate15 :=
  gatePhysical_rename TerminalFiveBridge.perm TerminalFiveBridge.perm.injective _ TerminalInverse23.physical

theorem pack506 (isA : Bool) : Rolling1588.Integer.packAfter base isA 506=[] := by
  simp only [Rolling1588.Integer.packAfter,show History5.packDue 506=false from by decide,Bool.false_eq_true,if_false]

theorem pack_inverse15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510) mD
      (run (Rolling1588.Integer.packAfter base isA 510) mE (run TerminalFiveBridge.forward [] a))=
        run TerminalFiveBridge.forward [] a := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  let b:=run (W.repairedTick base 506) [] a
  have stage507 : Stage base isA x p 507 b.basis := by
    have h := (step_spec base isA base_pool_nodup StackOB5.historyAbove x p 506
      hp0 hx0 hpo hp gap hx cop (by omega) a [] stage).2
    simpa only [pack506,List.append_nil,b] using h
  have same : run TerminalFiveBridge.forward [] a=run (MorningFour.tick507++tripF) [] b := by
    rw [TerminalFiveBridge.forward,run_append]
    simp only [List.take_nil,List.drop_nil,b]
  rw [same]
  exact InverseFour15.pack_inverse15 isA x hx0 hx b stage507 mE mD

theorem decoded_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool) :
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ candidate15) mD
      (run (Rolling1588.Integer.packAfter base isA 510) mE (run TerminalFiveBridge.forward [] a))=
    run (Rolling1588.Integer.decodeBefore base isA 510 ++ TerminalFivePlacement.old) mD
      (run (Rolling1588.Integer.packAfter base isA 510) mE (run TerminalFiveBridge.forward [] a)) := by
  rw [run_append (Rolling1588.Integer.decodeBefore base isA 510) candidate15,
    run_append (Rolling1588.Integer.decodeBefore base isA 510) TerminalFivePlacement.old,
    pack_inverse15 isA x hx0 hx a stage mE]
  exact TerminalFiveSample.stage_replace isA x hx0 hx a _ stage _ _ (fun _ _=>rfl)

theorem sites_pool15 : TerminalFiveDomain.sites.toFinset ⊆ (skywalkPoolWires base).toFinset := by
  let indices : List Nat := [505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 1534, 1535, 1536, 1537, 1538, 1540, 1541, 1542, 1543, 1544]
  have layout : TerminalFiveDomain.sites=indices.map base := by decide +kernel
  have bounds : indices.all (fun i=>Nat.blt i 1798)=true := by decide +kernel
  intro q hq
  have member := List.mem_toFinset.mp hq
  rw [layout] at member
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
  have small:=List.all_eq_true.mp bounds i hi
  exact List.mem_toFinset.mpr (OB5.base_pool i (Nat.blt_eq.mp small))

theorem decoded_replace_pool15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool)
    (agree : ∀q∈skywalkPoolWires base,
      u.basis q=(run (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) mE a).basis q) :
    run (Rolling1588.Integer.decodeBefore base isA 510++candidate15) mD u=
      run (Rolling1588.Integer.decodeBefore base isA 510++TerminalFivePlacement.old) mD u := by
  let f:=TerminalFiveBridge.forward
  let codec:=Rolling1588.Integer.decodeBefore base isA 510
  let ref:=run (Rolling1588.Integer.packAfter base isA 510) mE (run f [] a)
  have dec : wires codec⊆(skywalkPoolWires base).toFinset := by
    have h:=(History5.pack_support5 base 510 (by omega)).2.trans (History5.integerSites5_pool base)
    rw [←decodeBefore_support_eq base isA 510] at h
    exact h
  have sc : wires (codec++candidate15)⊆(skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,TerminalFiveSample.physical_support.trans sites_pool15⟩
  have so : wires (codec++TerminalFivePlacement.old)⊆(skywalkPoolWires base).toFinset := by
    rw [wires_append,Finset.union_subset_iff]
    exact ⟨dec,TerminalFiveSample.old_support.trans sites_pool15⟩
  apply Stack5.local_replace _ _ _ sc so u ref mD mD
  · intro q hq
    have e1:=congrFun (run_basis_records (f++Rolling1588.Integer.packAfter base isA 510) a a mE [] rfl) q
    have e2:=congrFun (run_basis_records (Rolling1588.Integer.packAfter base isA 510) (run f [] a) (run f [] a) [] mE rfl) q
    have e3 : (run (f++Rolling1588.Integer.packAfter base isA 510) [] a).basis q=
        (run (Rolling1588.Integer.packAfter base isA 510) [] (run f [] a)).basis q := by
      rw [run_append]; simp only [List.take_nil,List.drop_nil]
    exact (agree q (List.mem_toFinset.mp hq)).trans (e1.trans (e3.trans e2))
  · exact decoded_replace15 isA x hx0 hx a stage mE mD

theorem tail_replace15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (a u : State) (stage : Stage base isA x p 506 a.basis) (mE mD : List Bool)
    (agree : ∀q∈skywalkPoolWires base,
      u.basis q=(run (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) mE a).basis q) :
    run (reverseTail15 isA) mD (pullState (sig 510) u)=
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old)++
      Rolling1588.reverse isA 1 505) mD (pullState (sig 510) u) := by
  have count : measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++candidate15))=
      measurementCount (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,
      measurementCount_append,measurementCount_append,resources.2.1,old_resources.2.1]
  rw [reverseTail15,
    run_append (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++candidate15))
      (Rolling1588.reverse isA 1 505),
    run_append (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old))
      (Rolling1588.reverse isA 1 505),count]
  rw [InverseFour15.unpack51015,OB5.run_rename 510 (by omega),OB5.run_rename 510 (by omega),
    decoded_replace_pool15 isA x hx0 hx a u stage mE _ agree]

theorem tail_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p)
    (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (u : State) (hu : ∀q∈skywalkPoolWires base,
      u.basis q=(run (regularForward base isA 1 510) mE s1).basis q) (mD : List Bool) :
    run (reverseTail15 isA) mD (pullState (sig 510) u)=
    run (renameProgram (sig 510) (Rolling1588.unpackAtTick isA 510++TerminalFivePlacement.old)++
      Rolling1588.reverse isA 1 505) mD (pullState (sig 510) u) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have gap : p+2^32≤2^256 := by norm_num [p]
  let k:=measurementCount (regularForward base isA 1 505)
  have stage0 : Stage base isA x p 506
      (run (regularForward base isA 1 505)
        (mE.take (measurementCount (regularForward base isA 1 505))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 505
      hp0 hx0 hpo hp gap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  change Stage base isA x p 506 (run (regularForward base isA 1 505) (mE.take k) s1).basis at stage0
  obtain ⟨a,ha⟩ : ∃a : State,run (regularForward base isA 1 505) (mE.take k) s1=a := ⟨_,rfl⟩
  rw [ha] at stage0
  have fwdP : regularForward base isA 1 510=regularForward base isA 1 505 ++
      (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) := by
    rw [regularForward_snoc base isA 1 509,show (1:Nat)+509=510 by rfl,
      regularForward_snoc base isA 1 508,show (1:Nat)+508=509 by rfl,
      regularForward_snoc base isA 1 507,show (1:Nat)+507=508 by rfl,
      regularForward_snoc base isA 1 506,show (1:Nat)+506=507 by rfl,
      regularForward_snoc base isA 1 505,show (1:Nat)+505=506 by rfl,
      pack506,MorningPlacement.pack507,pack508,pack509,
      MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
    simp only [TerminalFiveBridge.forward,tripF,List.append_assoc,List.append_nil]
  have agree : ∀q∈skywalkPoolWires base,
      u.basis q=(run (TerminalFiveBridge.forward++Rolling1588.Integer.packAfter base isA 510) (mE.drop k) a).basis q := by
    intro q hq
    rw [hu q hq,fwdP,run_append,←show measurementCount (regularForward base isA 1 505)=k from rfl,ha]
  exact tail_replace15 isA x hx0 hx a u stage0 (mE.drop k) mD agree


theorem reverse_actual15 (isA : Bool) (x : Nat) (hx0 : 0<x) (hx : x<p) (s1 : State) (mE : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (t5 : State) (agree : ∀q∈skywalkPoolWires base,
      t5.basis q=(run (regularForward base isA 1 511) mE s1).basis q) (mD : List Bool) :
    run (stackReverse15 isA) mD (pullState (sig 511) t5)=
      run (InverseFour15.stackReverse15 isA) mD (pullState (sig 511) t5) := by
  obtain ⟨hp0,hpo,hp,cop⟩ := StackOB5.prime_facts x hx0 hx
  have hgap : p+2^32  ≤  2^256 := by norm_num [p]
  have aStage : Stage base isA x p 511
      (run (regularForward base isA 1 510)
        (mE.take (measurementCount (regularForward base isA 1 510))) s1).basis :=
    ((regularForward_spec base isA base_pool_nodup StackOB5.historyAbove x p 1 510
      hp0 hx0 hpo hp hgap hx cop (by omega)) s1 _ (stage_one base isA x p s1 first)).2
  have whole : run (regularForward base isA 1 510)
      (mE.take (measurementCount (regularForward base isA 1 510))) s1=
        run (regularForward base isA 1 510) mE s1 := run_take _ mE s1
  have last : run (regularForward base isA 1 511) mE s1=
      run (W.repairedTick base 511) (mE.drop (measurementCount (regularForward base isA 1 510)))
        (run (regularForward base isA 1 510)
          (mE.take (measurementCount (regularForward base isA 1 510))) s1) := by
    rw [regularForward_snoc base isA 1 510,show (1:Nat)+510=511 by rfl,regular_pack511,List.append_nil,run_append]
  rw [last] at agree
  generalize run (regularForward base isA 1 510)
    (mE.take (measurementCount (regularForward base isA 1 510))) s1=a at aStage whole agree
  obtain ⟨G,bits⟩ := stage511_bits isA x hx0 hx a aStage
  rw [repaired511_forced G a bits] at agree
  have post : ∀q∈tickSites,t5.basis q=postBits G q := by
    intro q hq
    rw [agree q (tickSites_pool q hq)]
    exact tickF_post G a bits q hq
  have uAgree : ∀q∈skywalkPoolWires base,(run tickR [] t5).basis q=a.basis q := by
    intro q hq
    by_cases ht : q∈tickSites
    · rw [site_run tickR tickSites tickR_wires t5 ⟨false,postBits G⟩ post [] q ht,tickR_pre G q ht]
      exact (bits q ht).symm
    · have hr : q∉wires tickR := fun h => ht (List.mem_toFinset.mp (tickR_wires h))
      have hf : q∉wires tickF := fun h => ht (List.mem_toFinset.mp (tickF_wires h))
      rw [run_preserves_outside tickR [] t5 q hr,agree q hq,run_preserves_outside tickF [] a q hf]
  have z := stage_zero isA x 511 (by omega) a.basis aStage
  have move : pullState (sig 511) (run tickR [] t5)=pullState (sig 510) (run tickR [] t5) :=
    (OB5.pull_step 511 (by omega) _
      ((uAgree _ (StackOB5Base.base_pool _ (by omega))).trans z.1)
      (fun big => (uAgree _ (StackOB5Base.base_pool _ (by omega))).trans (z.2 big))).symm
  have cn : measurementCount (renameProgram (sig 511) tickR)=0 :=
    (renameProgram_counts (sig 511) tickR).2.trans tickR_counts.2
  rw [stackReverse15,TerminalFivePlacement.reverse_shape,run_append,run_append,cn]
  simp only [List.take_zero,List.drop_zero]
  rw [OB5.run_rename 511 (by omega),tickR_run,move]
  exact tail_actual15 isA x hx0 hx s1 mE first _
    (fun q hq => (uAgree q hq).trans (congrArg (fun st : State => st.basis q) whole)) mD

theorem stack_roundtrip15 (isA : Bool)
    (hn : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (x : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (mE mD : List Bool)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s.basis) :
    run (stackReverse15 isA) mD (run (Rolling1588TickGap.stackForward isA) mE s)=s := by
  have fwd : run (Rolling1588TickGap.stackForward isA) mE s =
      pullState (sig 511) (run (regularForward base isA 1 511) mE s) := by
    rw [Rolling1588TickGap.stackForward_run_eq isA x hx0 hx s mE first,
      ←Rolling1588.Integer.stackForward_eq_packets,Rolling1588.Integer.stackForwardT_run isA hn hlo x hx0 hx s mE first,
      Rolling1588.Integer.forward_run isA x hx0 hx s mE first]
  rw [fwd, reverse_actual15 isA x hx0 hx s mE first _ (fun _ _ => rfl) mD,←fwd]
  exact InverseFour15.stack_roundtrip15 isA hn hlo x hx0 hx s mE mD first


attribute [local irreducible] candidate15 TerminalFivePlacement.old stackReverse15 reverseTail15
  InverseFour15.stackReverse15

theorem stack_delta (isA : Bool) :
    toffoliCount (stackReverse15 isA)+1=toffoliCount (InverseFour15.stackReverse15 isA) ∧
    measurementCount (stackReverse15 isA)=measurementCount (InverseFour15.stackReverse15 isA) ∧
    Challenge.gateSlots (stackReverse15 isA)=Challenge.gateSlots (InverseFour15.stackReverse15 isA)+151 := by
  have fresh:=resources
  have old:=old_resources
  rw [TerminalFivePlacement.reverse_shape]
  simp only [stackReverse15,reverseTail15,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots]
  omega

theorem stack_subset (isA : Bool) : wires (stackReverse15 isA)⊆wires (InverseFour15.stackReverse15 isA) := by
  have ren (P Q : Program) : renameProgram (sig 510) (P++Q)=
      renameProgram (sig 510) P++renameProgram (sig 510) Q := by
    simp only [renameProgram,List.map_append]
  have oldPlace : wires (renameProgram (sig 510) TerminalFivePlacement.old)=
      wires (renameProgram (sig 510) Inverse14Width.candidate) ∪
        wires (renameProgram (sig 506) (W.ReverseCarry.compactReceiverTick base 506)) := by
    rw [TerminalFivePlacement.old_placed,wires_append]
  have block : wires (renameProgram (sig 510) candidate15)⊆
      wires (renameProgram (sig 510) TerminalFivePlacement.old) ∪
        wires (Rolling1588.reverse isA 1 505) := by
    have sub:=TerminalFiveLiveSupport.placed_local
    rw [←oldPlace] at sub
    intro q hq
    have used:=sub (by simpa only [candidate15] using hq)
    rcases Finset.mem_union.mp used with oldsite | borrowed
    · exact Finset.mem_union_left _ oldsite
    · exact Finset.mem_union_right _ (TerminalBorrowB.reverse_sites isA borrowed)
  intro q hq
  have move : q∈wires (renameProgram (sig 510) candidate15) →
      q∈wires (renameProgram (sig 510) TerminalFivePlacement.old) ∨
        q∈wires (Rolling1588.reverse isA 1 505) := fun used=>Finset.mem_union.mp (block used)
  rw [stackReverse15,reverseTail15] at hq
  rw [TerminalFivePlacement.reverse_shape]
  simp only [ren,wires_append,Finset.mem_union] at hq ⊢
  tauto

open Arithmetic.DirectSkywalk

def lastPhase15 (isA : Bool) : Program :=
  skywalkArithmeticClear base ++ stackReverse15 isA ++ FrontierEntry1591NativeH.inverse base

theorem last_subset (isA : Bool) : wires (lastPhase15 isA)⊆wires (InverseFour15.lastPhase15 isA) := by
  intro q hq
  have sub:=stack_subset isA
  simp only [lastPhase15,InverseFour15.lastPhase15,wires_append,Finset.mem_union] at hq ⊢
  have move : q∈wires (stackReverse15 isA) → q∈wires (InverseFour15.stackReverse15 isA) := fun used=>sub used
  tauto

theorem last_pool15 (isA : Bool) : wires (lastPhase15 isA)⊆(skywalkPoolWires base).toFinset :=
  (last_subset isA).trans (InverseFour15.last_pool15 isA)

theorem last_hosts_free15 (isA : Bool) (q : Wire) (hq : q∈Rolling1588Lifetime.phaseHosts) : q∉wires (lastPhase15 isA) :=
  fun used=>InverseFour15.last_hosts_free15 isA q hq (last_subset isA used)

theorem last_extra15 (isA : Bool) : wires (lastPhase15 isA)⊆wires (Rolling1588.lastPhase isA)∪{530} :=
  (last_subset isA).trans (InverseFour15.last_extra15 isA)

theorem stack_physical (isA : Bool) : GatePhysical (stackReverse15 isA) := by
  have old:=InverseFour15.last_physical15 isA
  simp only [InverseFour15.lastPhase15,gatePhysical_append] at old
  have stack : GatePhysical (InverseFour15.stackReverse15 isA) := by tauto
  rw [TerminalFivePlacement.reverse_shape] at stack
  have ren (P Q : Program) : renameProgram (sig 510) (P++Q)=
      renameProgram (sig 510) P++renameProgram (sig 510) Q := by
    simp only [renameProgram,List.map_append]
  have inj : Function.Injective (sig 510) := by
    intro a b equal
    have e:=congrArg (sig 510) equal
    simpa only [sig_invol 510 (by omega)] using e
  have fresh:=gatePhysical_rename (sig 510) inj candidate15 candidate_physical
  simp only [ren,gatePhysical_append] at stack
  simp only [stackReverse15,reverseTail15,ren,gatePhysical_append]
  tauto

theorem last_physical15 (isA : Bool) : GatePhysical (lastPhase15 isA) := by
  have old:=InverseFour15.last_physical15 isA
  have stack:=stack_physical isA
  simp only [InverseFour15.lastPhase15,gatePhysical_append] at old
  simp only [lastPhase15,gatePhysical_append]
  tauto

theorem reverse_metrics_new (isA : Bool) :
    toffoliCount (stackReverse15 isA)+3=toffoliCount (Rolling1588.stackReverse isA) ∧
    measurementCount (stackReverse15 isA)=measurementCount (Rolling1588.stackReverse isA) ∧
    Challenge.gateSlots (stackReverse15 isA)=Challenge.gateSlots (Rolling1588.stackReverse isA)+1235 := by
  have fresh:=stack_delta isA
  have old:=InverseFour15.reverse_metrics_new isA
  omega

end ECDSAAdd.Entrant.InverseFive23

end

-- Adapted public peer module: InverseFiveEntry23
section

namespace ECDSAAdd.Entrant.InverseFiveEntry23
open ECDSAAdd Arithmetic MappedCompressed Challenge History5 OB5
open Rolling1588.Integer FrontierEntry1591Callers DirectSkywalk
open InverseFive23
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots
  InverseFive23.stackReverse15 InverseFive23.lastPhase15 Rolling1588.reverse

private theorem compose_roundtrip15 (N F C R I : Program) (s : State) (mp mr : List Bool)
    (clearM : measurementCount C=0)
    (twice : ∀ (t : State) mc,run C [] (run C mc t)=t)
    (stack : ∀mn mf md,run R md (run F mf (run N mn s))=run N mn s)
    (native : ∀mn mi,run I mi (run N mn s)=s) :
    run (C++(R++I)) mr (run (N++(F++C)) mp s)=s := by
  simp only [run_append,clearM,List.take_zero,List.drop_zero]
  rw [twice,stack]
  exact native _ _

theorem phases_roundtrip15 (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (mp mr : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (lastPhase15 isA) mr (run (Rolling1588TickGap.firstPhase isA) mp s)=s := by
  have clearM : measurementCount (skywalkArithmeticClear base)=0 := by
    simp [skywalkArithmeticClear,skywalkTerminalClear,measurementCount]
  have twice (t : State) (mc : List Bool) : run (skywalkArithmeticClear base) []
      (run (skywalkArithmeticClear base) mc t)=t := by
    simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
      (base 511) (base 512) (base 770) (arith_clear_gates base hn) t mc []
  have stack (mn mf md : List Bool) :
      run (stackReverse15 isA) md (run (Rolling1588TickGap.stackForward isA) mf
        (run (FrontierEntry1591Native.forward base) mn s))=
      run (FrontierEntry1591Native.forward base) mn s :=
    stack_roundtrip15 isA hn hlo x hx0 hx _ mf md
      (FrontierEntry1591Native.caller_first_stageW base hn x y hx0 hx s mn input)
  simpa only [Rolling1588TickGap.firstPhase,Rolling1588TickGap.tailPhase,lastPhase15,List.append_assoc] using
    compose_roundtrip15 (FrontierEntry1591Native.forward base) (Rolling1588TickGap.stackForward isA)
      (skywalkArithmeticClear base) (stackReverse15 isA)
      (FrontierEntry1591NativeH.inverse base) s mp mr clearM twice stack
      (fun mn mi=>FrontierEntry1591NativeH.inverse_roundtrip base hn x y hx s mn mi input)

open ECDSAAdd.Entrant.Rolling1588Lifetime
private theorem phase_sites_split :
    phaseSites=FrontierEntry1591Native.workSites∪phaseHosts := by
  ext q
  simp only [phaseSites,phaseHosts,FrontierEntry1591Native.workSites,Finset.mem_union,
    List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

private theorem phase_kernel_rebind (P F Q : Program) (s : State) (m : List Bool)
    (input : ∀q∈phaseSites,s.basis q=false)
    (firstFree : ∀q∈phaseHosts,q∉wires P)
    (firstClean : ∀records,∀q∈FrontierEntry1591Native.workSites,
      (run P records s).basis q=false)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (lastFree : ∀q∈phaseHosts,q∉wires Q)
    (output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel P F Q) m s).basis q=false) :
    run (renameProgram phaseHost P++(F++renameProgram phaseHost Q)) m s=
      run (FrontierEntry1591Native.kernel P F Q) m s := by
  let mp := m.take (measurementCount P)
  let rest := m.drop (measurementCount P)
  let mf := rest.take (measurementCount F)
  let mr := rest.drop (measurementCount F)
  let before := run P mp s
  let after := run F mf before
  have finalClean : ∀q∈phaseSites,(run Q mr after).basis q=false := by
    simpa only [FrontierEntry1591Native.kernel,run_append] using output
  have lastInput : ∀q∈phaseSites,after.basis q=false := by
    intro q hq
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact (run_preserves_outside F mf before q (fieldFree q work)).trans (firstClean mp q work)
    · exact (run_preserves_outside Q mr after q (lastFree q host)).symm.trans
        (finalClean q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have firstOutput : ∀q∈phaseSites,(run P mp s).basis q=false := by
    intro q hq
    rw [phase_sites_split] at hq
    rcases Finset.mem_union.mp hq with work|host
    · exact firstClean mp q work
    · exact (run_preserves_outside P mp s q (firstFree q host)).trans
        (input q (by rw [phase_sites_split];exact Finset.mem_union_right _ host))
  have first := phase_run_eq P s mp input firstOutput
  have last := phase_run_eq Q after mr lastInput finalClean
  simp only [FrontierEntry1591Native.kernel,run_append,(renameProgram_counts _ _).2]
  rw [first]
  exact last


private theorem phase_numerator_away (q : Wire) (hq : q∈phaseSites) :
    q∉wireBlock base 2056 256 := by
  simp only [phaseSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact OwnPlusHost.not_block _ 2056 256 (by omega)

/-- The field changes A into B. Its output is compared with a B encoding
of the same raw integer history before the B inverse is applied. -/
theorem raw_result_of_roundtrip (a b : Bool) (F : Program) (s : State) (m : List Bool)
    (value : Nat)
    (roundtrip : ∀mp mr,run (lastPhase15 b) mr (run (firstPhase b) mp s)=s)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have firstPool : wires (firstPhase b)⊆(skywalkPoolWires base).toFinset := by
    rw [first_support_eq]
    exact FrontierEntry1591Kernel.first_pool
  have lastPool : wires (lastPhase15 b)⊆(skywalkPoolWires base).toFinset :=
    last_pool15 b
  have all := run_three_states (firstPhase a) F (lastPhase15 b)
    (fun initial out=>initial=s → out.phase=s.phase ∧
      regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q) (by
      intro initial beforeA after out mp mf mr h1 h2 h3 eq
      subst initial
      have result := fieldResult mp mf
      dsimp only at result
      rw [h1,h2] at result
      exact FrontierEntry1591Kernel.sandwich_states (firstPhase b) (lastPhase15 b) firstPool lastPool s
        (run (firstPhase b) mp s) after out mp mr value rfl h3 (roundtrip mp mr) result) s m
  simpa only [FrontierEntry1591Native.kernel,List.append_assoc] using all rfl



theorem kernel_result15 (a b : Bool) (F : Program) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0<x) (hx : x<p) (s : State) (m : List Bool) (value : Nat)
    (input : SkywalkArithmeticInput base x y s.basis)
    (fieldFree : ∀q∈FrontierEntry1591Native.workSites,q∉wires F)
    (fieldResult : ∀mp mf,
      let beforeA := run (firstPhase a) mp s
      let beforeB := run (firstPhase b) mp s
      let after := run F mf beforeA
      after.phase=beforeB.phase ∧ regValue (wireBlock base 2056 256) after.basis=value ∧
        ∀q,q∉wireBlock base 2056 256 → after.basis q=beforeB.basis q) :
    let out := run (renameProgram phaseHost (firstPhase a)++
      (F++renameProgram phaseHost (lastPhase15 b))) m s
    out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=value ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q := by
  have rt (mp mr : List Bool) : run (lastPhase15 b) mr (run (firstPhase b) mp s)=s := by
    rw [←Rolling1588TickGap.first_run_eq b hn x y hx0 hx s mp input]
    exact phases_roundtrip15 b hn hlo x y hx0 hx s mp mr input
  have raw := raw_result_of_roundtrip a b F s m value rt fieldResult
  have clean := caller_phase_clean x y s input
  have output : ∀q∈phaseSites,
      (run (FrontierEntry1591Native.kernel (firstPhase a) F (lastPhase15 b)) m s).basis q=false := by
    intro q hq
    exact (raw.2.2 q (phase_numerator_away q hq)).trans (clean q hq)
  have same := phase_kernel_rebind (firstPhase a) F (lastPhase15 b) s m clean
    (first_hosts_free a) (fun records => Rolling1588Lifetime.first_clean a hn hlo x y hx0 hx s records input)
    fieldFree (last_hosts_free15 b) output
  dsimp only
  rw [same]
  exact raw

open ECDSAAdd.Entrant.Rolling1588 ECDSAAdd.Entrant.FrontierEntry1591Callers ECDSAAdd.Arithmetic.BalancedField
def oldKernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def kernel15 (a b : Bool) (F : Program) : Program :=
  renameProgram phaseHost (Rolling1588TickGap.firstPhase a) ++
    (F ++ renameProgram phaseHost (lastPhase15 b))
def entryKernel15 : Program := kernel15 true false entryFieldHosted
def exitKernel15 : Program := kernel15 false true exitFieldHosted

theorem old_entry_correct15 : EntryCorrect (oldKernel15 true false entryFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  obtain ⟨out,outEq⟩ : ∃out : State,run (oldKernel15 true false entryFieldHosted) m t=out := ⟨_,rfl⟩
  have actualInput := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  have result := kernel_result15 true false entryFieldHosted hn hlo
    x _ hx0 hx t m (Y/(x:Fp)).val actualInput entryFieldHosted_work_free
    (fun mp mf=>entry_boundary hn hlo ho hf x Y hx0 hx s t mp mf input hg hs phase same half)
  change (run (oldKernel15 true false entryFieldHosted) m t).phase=t.phase ∧
    regValue (wireBlock base 2056 256) (run (oldKernel15 true false entryFieldHosted) m t).basis=(Y/(x:Fp)).val ∧
    ∀q,q∉wireBlock base 2056 256 → (run (oldKernel15 true false entryFieldHosted) m t).basis q=t.basis q at result
  rw [outEq] at result
  have conclusion : out.phase=s.phase ∧ regValue (wireBlock base 2056 256) out.basis=(Y/(x:Fp)).val ∧
      ∀q,q∉wireBlock base 2056 256 → out.basis q=s.basis q :=
    ⟨result.1.trans phase,result.2.1,fun q hq=>(result.2.2 q hq).trans (same q hq)⟩
  dsimp only
  rw [outEq]
  simpa only [skywalkArithmeticResult,if_true] using conclusion

theorem old_exit_correct15 : ExitCorrect (oldKernel15 false true exitFieldHosted) := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  have result := kernel_result15 false true exitFieldHosted hn hlo
    x Y.val hx0 hx s m (centerWord (Y*(x:Fp)/2)) input exitFieldHosted_work_free
    (fun mp mf=>exit_boundary hn hlo ho hf x Y hx0 hx s mp mf input hg hs)
  simpa only [oldKernel15,skywalkArithmeticNumerator] using result

theorem kernel_first_eq15 (a b : Bool) (F : Program)
    (hn : (skywalkSharedWires base).Nodup) (x y : Nat) (hx0 : 0<x) (hx : x<p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (kernel15 a b F) m s = run (oldKernel15 a b F) m s := by
  have records : measurementCount (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)) =
      measurementCount (renameProgram phaseHost (Rolling1588.firstPhase a)) := by
    rw [(renameProgram_counts _ _).2,(renameProgram_counts _ _).2,(Rolling1588TickGap.first_metrics a).2.1]
  rw [kernel15,oldKernel15,
    run_append (renameProgram phaseHost (Rolling1588TickGap.firstPhase a)),
    run_append (renameProgram phaseHost (Rolling1588.firstPhase a)),records,
    Rolling1588TickGap.first_hosted_run_eq a hn x y hx0 hx s _ input]

theorem entry_correct15 : EntryCorrect entryKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half
  have actual := FrontierEntry1591Kernel.paired_input x Y.val s t input same
  rw [entryKernel15,kernel_first_eq15 true false entryFieldHosted hn x _ hx0 hx t m actual]
  exact old_entry_correct15 hn hlo ho hf x Y hx0 hx s t m input hg hs phase same half

theorem exit_correct15 : ExitCorrect exitKernel15 := by
  intro hn hlo ho hf x Y hx0 hx s m input hg hs
  rw [exitKernel15,kernel_first_eq15 false true exitFieldHosted hn x _ hx0 hx s m input]
  exact old_exit_correct15 hn hlo ho hf x Y hx0 hx s m input hg hs

theorem kernel_physical15 (a b : Bool) (F : Program) (field : GatePhysical F) :
    GatePhysical (kernel15 a b F) := by
  simpa only [kernel15,gatePhysical_append] using
    And.intro (Rolling1588Lifetime.phase_physical _ (Rolling1588TickGap.first_physical a))
      (And.intro field (Rolling1588Lifetime.phase_physical _ (last_physical15 b)))

theorem entry_physical15 : GatePhysical entryKernel15 := by
  simpa only [entryKernel15] using
    kernel_physical15 true false Rolling1588.entryFieldHosted Rolling1588.entryFieldHosted_physical

theorem exit_physical15 : GatePhysical exitKernel15 := by
  simpa only [exitKernel15] using
    kernel_physical15 false true Rolling1588.exitFieldHosted Rolling1588.exitFieldHosted_physical

theorem hosted_extra530 (b : Bool) :
    wires (renameProgram phaseHost (lastPhase15 b)) ⊆
      wires (renameProgram phaseHost (Rolling1588.lastPhase b)) ∪ {530} := by
  intro q hq
  rw [renameProgram_support] at hq
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_union.mp (last_extra15 b hv) with old | extra
  · apply Finset.mem_union_left
    rw [renameProgram_support]
    exact Finset.mem_image.mpr ⟨v,old,rfl⟩
  · simp only [Finset.mem_singleton] at extra
    subst v
    apply Finset.mem_union_right
    simp only [Finset.mem_singleton]
    decide +kernel

theorem kernel_extra530 (a b : Bool) (F : Program) :
    wires (kernel15 a b F) ⊆ wires (Rolling1588TickGap.kernel a b F) ∪ {530} := by
  have hsub := hosted_extra530 b
  intro q h
  simp only [kernel15,wires_append,Finset.mem_union] at h
  simp only [Rolling1588TickGap.kernel,wires_append,Finset.mem_union,Finset.mem_singleton]
  rcases h with hfirst | hfield | hlast
  · exact Or.inl (Or.inl hfirst)
  · exact Or.inl (Or.inr (Or.inl hfield))
  · rcases Finset.mem_union.mp (hsub hlast) with hold | hextra
    · exact Or.inl (Or.inr (Or.inr hold))
    · exact Or.inr (Finset.mem_singleton.mp hextra)

theorem extra_logical530 : (530:Wire) ∈ OB5Support.logicalSites := by
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨514,?_,by decide +kernel⟩
  simp [OB5Support.logicalIndices]

theorem entry_support530 : wires entryKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 true false Rolling1588.entryFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.entryKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530

theorem exit_support530 : wires exitKernel15 ⊆ OB5Support.logicalSites := by
  intro q hq
  have h := kernel_extra530 false true Rolling1588.exitFieldHosted hq
  rcases Finset.mem_union.mp h with old | extra
  · exact Rolling1588TickGap.exitKernel_support old
  · simp only [Finset.mem_singleton] at extra
    subst q
    exact extra_logical530


end ECDSAAdd.Entrant.InverseFiveEntry23

end
