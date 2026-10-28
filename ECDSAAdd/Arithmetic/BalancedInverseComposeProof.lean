import ECDSAAdd.Arithmetic.BalancedInverseComposePackets
import ECDSAAdd.Arithmetic.BalancedCoreComposeViews

set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic.BalancedInverse
open BalancedCircuit BalancedField BalancedFold

private theorem initialWork (L : Layout) (a : Wire)
    (ha : a∈[L.parity,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorWork (L : Layout) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem frameWork (L : Layout) (a : Wire)
    (ha : a∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a∈work L := by
  simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at ha ⊢
  tauto

private theorem selectorAway (L : Layout) (hn : L.wires.Nodup) (a : Wire)
    (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) :
    a≠L.sourceGuard ∧ a≠L.parity := by
  have nd : ([L.sourceGuard,L.parity]++([L.cout,L.minus,L.plus,L.lower,L.one]++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (allND L hn) q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have sep := List.disjoint_left.mp (List.nodup_append'.mp nd).2.2
  exact ⟨fun e => sep (by simp [←e]) ha,fun e => sep (by simp [←e]) ha⟩

/-- Complete independently emitted inverse field kernel, including phase,
all measurement records, complete workspace cleanup, and outside-R frame. -/
theorem program_correct (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (hc : ∀q∈work L,s.basis q=false) :
    let t := run (program L) m s
    t.phase=s.phase ∧ regValue L.r t.basis=encodeWord 256 (result B R Y) ∧
    (∀q∈work L,t.basis q=false) ∧ (∀q,q∉L.r → t.basis q=s.basis q) := by
  let X := result B R Y
  let T := rawSum B X Y
  let P := originalParity T
  let m₁ := m.drop (measurementCount (recoverParity L))
  let m₂ := m₁.drop (measurementCount (undoFold L))
  let m₃ := m₂.drop (measurementCount (undoPreparation L))
  let m₄ := m₃.drop (measurementCount (rawSubtract L))
  generalize e₀ : run [.CX L.ymsb L.sourceGuard] m s=u₀
  generalize e₁ : run (recoverParity L) m u₀=u₁
  generalize e₂ : run (recoverSelectors L) m₁ u₁=u₂
  generalize e₃ : run (rotateLeft (rawTarget L)) m₁ u₂=u₃
  generalize e₄ : run (undoFold L) m₁ u₃=u₄
  generalize e₅ : run (undoPreparation L) m₂ u₄=u₅
  generalize e₆ : run (rawSubtract L) m₃ u₅=u₆
  generalize e₇ : run (seedViews L).reverse m₄ u₆=t
  have hx : Centered X := result_bounds B R Y
  have ht : -(2*q)≤T ∧ T≤2*q := rawSum_bounds B X Y hx hy
  have half : halfResult T=R := result_half B R Y hr hy
  have rawRange : -((2^(257-1) : Nat) : Int)≤T ∧ T<((2^(257-1) : Nat) : Int) := by
    have c := BalancedField.constants
    norm_num at ⊢
    omega
  have w := BalancedCircuit.widths L hw
  have rlen := (BalancedCleanup.widths L.toLayout hw).2.1
  have ylen := (BalancedCleanup.widths L.toLayout hw).2.2.1
  have cnd : L.toLayout.wires.Nodup :=
    (List.nodup_append'.mp (show ([L.sourceGuard,L.cout,L.minus,L.plus]++L.toLayout.wires).Nodup from hn)).2.1
  have ndR := List.nodup_reverse.mpr (scalarND L hn)
  simp only [List.reverse_cons,List.reverse_nil,List.cons_append,List.nil_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at ndR
  have nd := scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  rcases nd with ⟨⟨h0_1,h0_2,h0_3,h0_4,h0_5,h0_6,h0_7,h0_8,h0_9,h0_10⟩,⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7,h1_8,h1_9,h1_10⟩,⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8,h2_9,h2_10⟩,⟨h3_4,h3_5,h3_6,h3_7,h3_8,h3_9,h3_10⟩,⟨h4_5,h4_6,h4_7,h4_8,h4_9,h4_10⟩,⟨h5_6,h5_7,h5_8,h5_9,h5_10⟩,⟨h6_7,h6_8,h6_9,h6_10⟩,⟨h7_8,h7_9,h7_10⟩,⟨h8_9,h8_10⟩,h9_10⟩
  rcases ndR with ⟨⟨r0_1,r0_2,r0_3,r0_4,r0_5,r0_6,r0_7,r0_8,r0_9,r0_10⟩,⟨r1_2,r1_3,r1_4,r1_5,r1_6,r1_7,r1_8,r1_9,r1_10⟩,⟨r2_3,r2_4,r2_5,r2_6,r2_7,r2_8,r2_9,r2_10⟩,⟨r3_4,r3_5,r3_6,r3_7,r3_8,r3_9,r3_10⟩,⟨r4_5,r4_6,r4_7,r4_8,r4_9,r4_10⟩,⟨r5_6,r5_7,r5_8,r5_9,r5_10⟩,⟨r6_7,r6_8,r6_9,r6_10⟩,⟨r7_8,r7_9,r7_10⟩,⟨r8_9,r8_10⟩,r9_10⟩
  have away (q : Wire)
      (hq : q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower]++L.y++L.carry) :
      q∉rawTarget L := compose_raw_away L hn q hq
  have zero (q : Wire) (hq : q∈work L) : s.basis q=false := hc q hq
  have f₀ (a : Wire) (ha : a≠L.sourceGuard) : u₀.basis a=s.basis a := by
    rw [←e₀]; simp only [run,writeBit,Function.update_of_ne ha]
  have guard₀ : u₀.basis L.sourceGuard=s.basis L.ymsb := by
    rw [←e₀]
    simp only [run,writeBit,Function.update_self]
    rw [hc L.sourceGuard (by simp [work])]
    simp only [Bool.false_xor]
  have R₀ : regValue L.r u₀.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have Y₀ : regValue L.y u₀.basis=encodeWord 256 Y := by
    apply Eq.trans _ (word_encoding L.y 256 ylen s.basis Y hY)
    apply regValue_congr
    intro a ha
    exact f₀ a (fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha]))
  have z₀ (a : Wire) (ha : a∈[L.parity,L.lower,L.one]++L.carry) : u₀.basis a=false := by
    have ne : a≠L.sourceGuard := by
      rcases List.mem_append.mp ha with ha|ha
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl|rfl|rfl <;> assumption
      · exact fun e => flagAway L hn L.sourceGuard (by simp) (by simp [e ▸ ha])
    exact (f₀ a ne).trans (hc a (initialWork L a ha))
  have oneOracle := recoverParity_correct L hw cnd R Y B hr hy u₀ m R₀ Y₀
    ((f₀ _ (by assumption)).trans hs) (z₀ _ (by simp)) (z₀ _ (by simp))
    (fun a ha => z₀ a (by simp [ha])) (z₀ _ (by simp))
  have parity : decide (q < |2*R-signedY B Y|)=P := result_parity B R Y hr hy
  rw [parity,e₁] at oneOracle
  have p₁ : u₁.basis L.parity=P := by rw [oneOracle]; simp only [writeBit,Function.update_self]
  have f₁ (a : Wire) (hg : a≠L.sourceGuard) (hp : a≠L.parity) : u₁.basis a=s.basis a := by
    rw [oneOracle]; simp only [writeBit,Function.update_of_ne hp]; exact f₀ a hg
  have g₁ : u₁.basis L.sourceGuard=s.basis L.ymsb := by
    rw [oneOracle]; simpa only [writeBit,Function.update_of_ne (show L.sourceGuard≠L.parity by assumption)] using guard₀
  have z₁ (a : Wire) (ha : a∈[L.cout,L.minus,L.plus,L.lower,L.one]++L.carry) : u₁.basis a=false := by
    have ne := selectorAway L hn a ha
    exact (f₁ a ne.1 ne.2).trans (hc a (selectorWork L a ha))
  have R₁ : regValue L.r u₁.basis=encodeWord 256 R := by
    apply Eq.trans _ (word_encoding L.r 256 rlen s.basis R hR)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₁ a (neq _ (by simp)) (neq _ (by simp))
  have sign₁ : u₁.basis L.rmsb=decide (halfResult T<0) := by
    rw [half]
    exact BalancedCleanup.result_msb L.toLayout hw R hr u₁.basis R₁
  have packet₂ := recoverSelectors_packet L hn T ht u₁ m₁ p₁ sign₁
    (z₁ _ (by simp)) (z₁ _ (by simp)) (z₁ _ (by simp))
  rw [e₂] at packet₂
  have f₂ (a : Wire) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) : u₂.basis a=u₁.basis a :=
    packet₂.2.2.2.2 a hl hm hu
  have R₂ : regValue L.r u₂.basis=encodeWord 256 R := by
    apply Eq.trans _ R₁
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  have one₂ : u₂.basis L.one=false :=
    (f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp))
  have packet₃ := rotate_unfold L hw hn R u₂ m₁ one₂ R₂
  rw [e₃] at packet₃
  have f₃ (a : Wire) (ha : a∉rawTarget L) : u₃.basis a=u₂.basis a := packet₃.2.2.2 a ha
  have p₃ : u₃.basis L.parity=P := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans p₁)
  have c₃ : u₃.basis L.cout=false := (f₃ _ (away _ (by simp))).trans
    ((f₂ _ (by assumption) (by assumption) (by assumption)).trans (z₁ _ (by simp)))
  have carry₃ : regValue L.carry u₃.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₃ a (away a (by simp [ha]))).trans
      ((f₂ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans (z₁ a (by simp [ha])))
  have upper₃ : regValue (foldTarget L) u₃.basis=encodeWord 256 (halfResult T) := by
    rw [half]; exact packet₃.2.2.1
  have packet₄ := undoFold_correct L hw hn T ht u₃ m₁ p₃
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)
    ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1) c₃ carry₃ upper₃
  rw [e₄] at packet₄
  have f₄ (a : Wire) (ha : a∉rawTarget L) : u₄.basis a=u₃.basis a :=
    packet₄.2.2.2 a (compose_fold_subset L a ha)
  have zero₄ : u₄.basis L.r0=false :=
    (packet₄.2.2.2 _ (compose_not_fold_r0 L hn)).trans packet₃.2.1
  have packet₅ := undoPreparation_packet L hw hn T ht u₄ m₂
    ((f₄ _ (away _ (by simp))).trans p₃) zero₄
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.1))
    ((f₄ _ (away _ (by simp))).trans ((f₃ _ (away _ (by simp))).trans packet₂.2.2.2.1)) packet₄.2.1
  rw [e₅] at packet₅
  have f₅ (a : Wire) (ha : a∉rawTarget L) (hl : a≠L.lower) (hm : a≠L.minus) (hu : a≠L.plus) :
      u₅.basis a=u₁.basis a := (packet₅.2.2.2.2.2 a ha hl hm hu).trans
    ((f₄ a ha).trans ((f₃ a ha).trans (f₂ a hl hm hu)))
  have raw₅ : signedRegValue (rawTarget L) u₅.basis=T := by
    unfold signedRegValue
    rw [w.2.1,packet₅.2.1]
    exact decode_encodeWord 257 (by norm_num) T rawRange
  have Y₅ : signedRegValue L.y u₅.basis=Y := by
    apply Eq.trans _ hY
    unfold signedRegValue
    congr 1
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (f₅ a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans (f₁ a (neq _ (by simp)) (neq _ (by simp)))
  have g₅ : u₅.basis L.sourceGuard=u₅.basis L.ymsb := by
    have left := (f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans g₁
    have right := (f₅ L.ymsb (away L.ymsb (by simp [BalancedCleanup.Layout.y]))
      (by assumption) (by assumption) (by assumption)).trans (f₁ L.ymsb (by assumption) (by assumption))
    exact left.trans right.symm
  have src₅ : signedRegValue (rawSource L) u₅.basis=Y := by
    exact (signed_extension L.ylow L.ymsb L.sourceGuard u₅.basis g₅).trans Y₅
  have carry₅ : regValue L.carry u₅.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact (packet₅.2.2.2.2.2 a (away a (by simp [ha])) (neq _ (by simp))
      (neq _ (by simp)) (neq _ (by simp))).trans
      ((regValue_zero _ _).mp carry₃ a ha |> fun h => (f₄ a (away a (by simp [ha]))).trans h)
  have sign₅ : u₅.basis L.sign=B := (f₅ _ (away _ (by simp))
    (by assumption) (by assumption) (by assumption)).trans ((f₁ _ (by assumption) (by assumption)).trans hs)
  have packet₆ := rawSubtract_signed L hw hn B X Y hx u₅ m₃ sign₅ src₅ raw₅ carry₅
  rw [e₆] at packet₆
  have f₆ (a : Wire) (ha : a∉rawTarget L) : u₆.basis a=u₅.basis a := packet₆.2.2 a ha
  have Y₆ : signedRegValue L.y u₆.basis=Y := by
    apply Eq.trans _ Y₅
    unfold signedRegValue
    congr 1
    exact regValue_congr _ _ _ (fun a ha => f₆ a (away a (by simp [ha])))
  have g₆ : u₆.basis L.sourceGuard=u₆.basis L.ymsb := by
    exact (f₆ _ (away _ (by simp))).trans (g₅.trans
      (f₆ _ (away _ (by simp [BalancedCleanup.Layout.y]))).symm)
  have p₆ : u₆.basis L.parity=P := (f₆ _ (away _ (by simp))).trans
    ((f₅ _ (away _ (by simp)) (by assumption) (by assumption) (by assumption)).trans p₁)
  have packet₇ := unseed_packet L hw hn B X Y hx u₆ m₄ packet₆.2.1 Y₆ g₆ p₆
  rw [e₇] at packet₇
  have f₇ (a : Wire) (hg : a≠L.sourceGuard) (ho : a≠L.one) (hp : a≠L.parity) :
      t.basis a=u₆.basis a := packet₇.2.2.2.2 a hg ho hp
  have actual : run (program L) m s=t := by
    simp only [program,List.append_assoc]
    rw [run_append,run_take]
    simp only [show measurementCount [.CX L.ymsb L.sourceGuard]=0 from rfl,List.drop_zero]
    rw [e₀,run_append,run_take,e₁,run_append,run_take]
    simp only [show measurementCount (recoverSelectors L)=0 from rfl,List.drop_zero]
    rw [e₂,run_append,run_take,(rotate_counts (rawTarget L)).2.2.2,List.drop_zero,
      e₃,run_append,run_take,e₄,run_append,run_take,e₅,run_append,run_take,e₆,e₇]

  have clean : ∀a∈work L,t.basis a=false := by
    intro a ha
    simp only [work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|ha
    · exact packet₇.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans ((packet₅.2.2.2.2.2 _ (away _ (by simp))
          (by assumption) (by assumption) (by assumption)).trans packet₄.2.2.1))
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.1)
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.2.2.1)
    · exact packet₇.2.2.2.1
    · exact (f₇ _ (by assumption) (by assumption) (by assumption)).trans
        ((f₆ _ (away _ (by simp))).trans packet₅.2.2.1)
    · exact packet₇.2.2.1
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
        fun e => flagAway L hn f hf (by simp [e ▸ ha])
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a (away a (by simp [ha]))).trans ((regValue_zero _ _).mp carry₅ a ha))
  have frame : ∀a,a∉L.r → t.basis a=s.basis a := by
    intro a ha
    by_cases workA : a∈work L
    · exact (clean a workA).trans (hc a workA).symm
    · have neq (f : Wire) (hf : f∈[L.sourceGuard,L.one,L.parity,L.lower,L.minus,L.plus]) : a≠f :=
        fun e => workA (e.symm ▸ frameWork L f hf)
      have ar : a∉rawTarget L := by
        simp only [rawTarget,List.mem_append,List.mem_singleton,not_or]
        exact ⟨ha,neq _ (by simp)⟩
      exact (f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
        ((f₆ a ar).trans ((f₅ a ar (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))).trans
          (f₁ a (neq _ (by simp)) (neq _ (by simp)))))
  have out : regValue L.r t.basis=encodeWord 256 X := by
    have corr := unseed_correlations L hw B X Y hx u₆ packet₆.2.1 Y₆ g₆ p₆
    have narrow : signedRegValue L.r u₆.basis=X :=
      (signed_extension (L.r0::L.rtail) L.rmsb L.one u₆.basis corr.1).symm.trans packet₆.2.1
    apply Eq.trans _ (word_encoding L.r 256 rlen u₆.basis X narrow)
    apply regValue_congr
    intro a ha
    have neq (f : Wire) (hf : f∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one]) : a≠f :=
      fun e => flagAway L hn f hf (by simp [e ▸ ha])
    exact f₇ a (neq _ (by simp)) (neq _ (by simp)) (neq _ (by simp))
  rw [actual]
  exact ⟨packet₇.1.trans (packet₆.1.trans (packet₅.1.trans (packet₄.1.trans
    (packet₃.1.trans (packet₂.1.trans (by rw [oneOracle,←e₀]; rfl)))))),out,clean,frame⟩

end ECDSAAdd.Arithmetic.BalancedInverse

#print axioms ECDSAAdd.Arithmetic.BalancedInverse.program_correct
