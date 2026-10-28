import ECDSAAdd.Arithmetic.Paper935.Arena
import ECDSAAdd.Arithmetic.Constant

set_option maxRecDepth 4096

namespace ECDSAAdd.Arithmetic.Paper935

/-- Concrete row-only seed: g rides the input word, f rides the clean second
word, the third word is preserved, and two coefficient bits spill beyond
those three words. Four independent sign wires occupy 768..771. -/
def seedG : List Wire := List.range 256
def seedF : List Wire := List.range' 256 256
def seedWord : List Wire := seedF++[773]

def seedBefore : Arena := ⟨xHost∪aHost,by
  intro q hq
  simp only [xHost,aHost,Finset.mem_union,Finset.mem_Ico,arenaWires,Finset.mem_range] at *
  simp only [Wire] at *
  omega⟩

def seedArena : Arena := ⟨Finset.range 774,by
  intro q hq
  simp only [Finset.mem_range,arenaWires] at *
  omega⟩

def seedBorrowed : Finset Wire := yHost∪Finset.Ico 768 774

/-- One constant-X circuit seeds f=p and gv=1. The concatenated constant
word is a proof convenience; only X gates are emitted. -/
def seedRows (p : Nat) : Program := xorConstant seedWord (p+2^256)

theorem seed_reserve : seedBefore.reserve seedBorrowed=some seedArena := by
  have hb : seedBorrowed⊆arenaWires := by
    intro q hq
    simp only [seedBorrowed,yHost,Finset.mem_union,Finset.mem_Ico,arenaWires,Finset.mem_range] at *
    simp only [Wire] at *
    omega
  have hd : Disjoint seedBefore.live seedBorrowed := by
    apply Finset.disjoint_left.mpr
    intro q hq ht
    simp only [seedBefore,xHost,aHost,seedBorrowed,yHost,Finset.mem_union,Finset.mem_Ico] at *
    simp only [Wire] at *
    omega
  have he : seedBefore.live∪seedBorrowed=seedArena.live := by
    ext q
    simp only [seedBefore,xHost,aHost,seedBorrowed,yHost,seedArena,Finset.mem_union,Finset.mem_Ico,Finset.mem_range]
    simp only [Wire] at *
    omega
  unfold Arena.reserve
  rw [dif_pos ⟨hb,hd⟩]
  apply congrArg some
  change Arena.mk _ _ = Arena.mk _ _
  apply (show ∀ A B : Arena,A.live=B.live → A=B from by
    intro A B h; cases A; cases B; cases h; rfl)
  exact he

theorem seedWord_distinct : seedWord.Nodup := by
  rw [seedWord,List.nodup_append]
  refine ⟨List.nodup_range' _,by simp,?_⟩
  intro a ha b hb he
  simp only [List.mem_singleton] at hb
  subst b
  subst a
  simp [seedF,List.mem_range'_1] at ha

theorem seed_support (p : Nat) : wires (seedRows p)⊆seedBorrowed := by
  intro q hq
  have hm := List.mem_toFinset.mp (xorConstant_wires_subset seedWord (p+2^256) hq)
  simp only [seedWord,seedF,List.mem_append,List.mem_range'_1,List.mem_singleton] at hm
  simp only [seedBorrowed,yHost,Finset.mem_union,Finset.mem_Ico]
  simp only [Wire] at *
  omega

private theorem seed_bound (p : Nat) (hp : p<2^256) : p+2^256<2^seedWord.length := by
  simp only [seedWord,seedF,List.length_append,List.length_range',List.length_singleton]
  norm_num at *
  omega

private theorem seed_zero (s : State) (hr : seedBefore.Ready s.basis) :
    regValue seedWord s.basis=0 := by
  apply (regValue_zero _ _).mpr
  intro q hq
  have hc := (seedBefore.reserve_ready seedArena seedBorrowed s.basis hr seed_reserve).2
  apply hc q
  simp only [seedWord,seedF,List.mem_append,List.mem_range'_1,List.mem_singleton] at hq
  simp only [seedBorrowed,yHost,Finset.mem_union,Finset.mem_Ico]
  simp only [Wire] at *
  omega

private theorem split_seed_value (f : List Wire) (gv p : Nat) (t : BasisState)
    (hv : regValue (f++[gv]) t=p+2^f.length) :
    regValue f t=p ∧ t gv=true := by
  have hf := regValue_lt f t
  rw [regValue_append] at hv
  change regValue f t + 2^f.length * (if t gv then 1 else 0)=p+2^f.length at hv
  cases ht : t gv with
  | false =>
    simp only [ht,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero] at hv
    omega
  | true =>
    simp only [ht,ite_true,Nat.mul_one] at hv
    exact ⟨by omega,rfl⟩

/-- The actual seed sets the modulus and unit coefficient, preserves phase
and every non-seed wire, and leaves every unowned arena site clean. -/
theorem seed_run (p : Nat) (hp : p<2^256) (s : State) (m : List Bool)
    (hr : seedBefore.Ready s.basis) :
    let t := run (seedRows p) m s
    t.phase=s.phase ∧ (∀ q,q∉seedWord → t.basis q=s.basis q) ∧
      regValue seedF t.basis=p ∧ t.basis 773=true ∧ seedArena.Ready t.basis := by
  have hc := xorConstant_correct seedWord seedWord_distinct (p+2^256) (seed_bound p hp) s m
  change (run (seedRows p) m s).phase=s.phase ∧
    (∀ q,q∉seedWord → (run (seedRows p) m s).basis q=s.basis q) ∧
    regValue seedWord (run (seedRows p) m s).basis=regValue seedWord s.basis ^^^ (p+2^256) at hc
  generalize ht : run (seedRows p) m s = t at *
  have hv := hc.2.2
  rw [seed_zero s hr,Nat.zero_xor] at hv
  have hl : seedF.length=256 := by simp [seedF]
  have hout : regValue seedF t.basis=p ∧ t.basis 773=true :=
    split_seed_value seedF 773 p t.basis
      (by simpa only [seedWord,hl] using hv)
  refine ⟨hc.1,hc.2.1,hout.1,hout.2,?_⟩
  intro q hq hn
  have hnot : q∉seedWord := by
    intro hm
    have hb : q∈seedArena.live := by
      simp only [seedArena,Finset.mem_range]
      simp only [seedWord,seedF,List.mem_append,List.mem_range'_1,List.mem_singleton,Wire] at hm
      simp only [Wire] at *
      omega
    exact hn hb
  rw [hc.2.1 q hnot]
  exact (seedBefore.reserve_ready seedArena seedBorrowed s.basis hr seed_reserve).1 q hq hn

private theorem signed_positive (lo : List Wire) (sign : Wire) (s : BasisState)
    (hz : s sign=false) : signedRegValue (lo++[sign]) s=(regValue lo s:Int) := by
  rw [signedRegValue_msb,regValue_append]
  simp [regValue,hz]

/-- Four signed rows at the real seed point: (f,g,fv,gv)=(p,input,0,1).
The coefficient payloads use two extra sites, rather than overlapping a
full 256-bit host. -/
private theorem seed_rows_state (p : Nat) (s t : State)
    (hr : seedBefore.Ready s.basis)
    (hframe : ∀ q,q∉seedWord → t.basis q=s.basis q)
    (hvalue : regValue seedF t.basis=p) (hunit : t.basis 773=true) :
    signedRegValue (seedF++[768]) t.basis=(p:Int) ∧
    signedRegValue (seedG++[769]) t.basis=(regValue seedG s.basis:Int) ∧
    signedRegValue [772,770] t.basis=0 ∧ signedRegValue [773,771] t.basis=1 := by
  have hz : ∀ q,768≤q → q≤772 → t.basis q=false := by
    intro q hlo hhi
    rw [hframe q (by simp only [seedWord,seedF,List.mem_append,List.mem_range'_1,List.mem_singleton]; simp only [Wire] at *; omega)]
    apply hr q
    · simp only [arenaWires,Finset.mem_range]; simp only [Wire] at *; omega
    · simp only [seedBefore,xHost,aHost,Finset.mem_union,Finset.mem_Ico]; simp only [Wire] at *; omega
  have hg : regValue seedG t.basis=regValue seedG s.basis := by
    apply regValue_congr
    intro q hq
    apply hframe q
    simp only [seedG,List.mem_range] at hq
    simp only [seedWord,seedF,List.mem_append,List.mem_range'_1,List.mem_singleton,Wire] at *
    omega
  refine ⟨?_,?_,?_,?_⟩
  · exact (signed_positive seedF 768 t.basis (hz 768 (by decide) (by decide))).trans
      (congrArg Int.ofNat hvalue)
  · exact (signed_positive seedG 769 t.basis (hz 769 (by decide) (by decide))).trans
      (congrArg Int.ofNat hg)
  · change signedRegValue ([772]++[770]) _=0
    rw [signed_positive _ _ _ (hz 770 (by decide) (by decide))]
    simp [regValue,hz 772 (by decide) (by decide)]
  · change signedRegValue ([773]++[771]) _=1
    rw [signed_positive _ _ _ (hz 771 (by decide) (by decide))]
    simp [regValue,hunit]


theorem seed_rows (p : Nat) (hp : p<2^256) (s : State) (m : List Bool)
    (hr : seedBefore.Ready s.basis) :
    let t := run (seedRows p) m s
    signedRegValue (seedF++[768]) t.basis=(p:Int) ∧
    signedRegValue (seedG++[769]) t.basis=(regValue seedG s.basis:Int) ∧
    signedRegValue [772,770] t.basis=0 ∧ signedRegValue [773,771] t.basis=1 := by
  have hc := seed_run p hp s m hr
  exact seed_rows_state p s _ hr hc.2.1 hc.2.2.1 hc.2.2.2.1

private theorem xor_constant_roundtrip (r : List Wire) (k : Nat) (hn : r.Nodup)
    (hk : k<2^r.length) (s : State) (m n : List Bool) :
    run (xorConstant r k) n (run (xorConstant r k) m s)=s := by
  have h1 := xorConstant_correct r hn k hk s m
  have h2 := xorConstant_correct r hn k hk (run (xorConstant r k) m s) n
  apply congrArg₂ State.mk
  · exact h2.1.trans h1.1
  · funext q
    by_cases hq : q∈r
    · apply (regValue_eq_iff r _ _).mp _ q hq
      rw [h2.2.2,h1.2.2]
      simp
    · exact (h2.2.1 q hq).trans (h1.2.1 q hq)

theorem seed_roundtrip (p : Nat) (hp : p<2^256) (s : State) (m n : List Bool) :
    run (seedRows p) n (run (seedRows p) m s)=s :=
  xor_constant_roundtrip seedWord (p+2^256) seedWord_distinct (seed_bound p hp) s m n

theorem seed_release (s : State) (hr : seedBefore.Ready s.basis) :
    seedArena.release seedBorrowed s.basis=some seedBefore := by
  have hc := (seedBefore.reserve_ready seedArena seedBorrowed s.basis hr seed_reserve).2
  have hb : seedBorrowed⊆seedArena.live := by
    intro q hq
    simp only [seedBorrowed,yHost,seedArena,Finset.mem_union,Finset.mem_Ico,Finset.mem_range,Wire] at *
    omega
  have he : seedArena.live\seedBorrowed=seedBefore.live := by
    ext q
    simp only [seedArena,seedBorrowed,yHost,seedBefore,xHost,aHost,Finset.mem_sdiff,
      Finset.mem_range,Finset.mem_union,Finset.mem_Ico,Wire]
    omega
  unfold Arena.release
  rw [if_pos ⟨hb,hc⟩]
  apply congrArg some
  apply (show ∀ A B : Arena,A.live=B.live → A=B from by
    intro A B h; cases A; cases B; cases h; rfl)
  exact he

/-- Applying the emitted inverse before release restores every input bit,
phase, and the original allocator, including the untouched third word. -/
theorem seed_uninit (p : Nat) (hp : p<2^256) (s : State) (m n : List Bool)
    (hr : seedBefore.Ready s.basis) :
    let t := run (seedRows p) n (run (seedRows p) m s)
    t=s ∧ seedArena.release seedBorrowed t.basis=some seedBefore := by
  dsimp only
  rw [seed_roundtrip p hp s m n]
  exact ⟨rfl,seed_release s hr⟩

theorem seed_counts (p : Nat) : toffoliCount (seedRows p)=0 ∧ measurementCount (seedRows p)=0 :=
  xorConstant_counts _ _

theorem seed_qubits (p : Nat) : qubitCount (seedRows p)≤257 := by
  have h := Finset.card_le_card (xorConstant_wires_subset seedWord (p+2^256))
  rw [List.toFinset_card_of_nodup seedWord_distinct] at h
  simpa only [seedRows,qubitCount,seedWord,seedF,List.length_append,
    List.length_range',List.length_singleton] using h

theorem seed_live_count : seedBefore.live.card=512 ∧ seedArena.live.card=774 ∧
    (arenaWires\seedArena.live).card=161 := by
  constructor
  · rw [show seedBefore.live=Finset.range 256∪Finset.Ico 512 768 by rfl]
    rw [Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro q hq ht
      simp only [Finset.mem_range,Finset.mem_Ico] at *
      omega)]
    simp
  · constructor
    · simp [seedArena]
    · rw [Finset.card_sdiff_of_subset seedArena.bounded]
      simp [arenaWires,seedArena]

end ECDSAAdd.Arithmetic.Paper935
