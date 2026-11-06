import ECDSAAdd.Submission.Entrant.MainPart07

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
