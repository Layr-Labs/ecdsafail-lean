import ECDSAAdd.Arithmetic.RoundLayout
import ECDSAAdd.Arithmetic.MeasuredMaskedAdder

namespace ECDSAAdd.Arithmetic

/-- 组合轮内操作时同时保留整个布局外部的状态，而非只列出少数控制位。 -/
def RoundFrame (L : RoundDataLayout) (v : RoundField → Nat) (base : BasisState)
    (st : BasisState) : Prop := RoundValues L v st ∧ ∀ w, w∉L.wires → st w=base w

/-- 复用原地受控加减，y和低位进位链清零，out不再被触及。 -/
def inplaceArithmetic (L : RoundDataLayout) (f g : RoundField) (c : Wire) (negative : Bool) : Program :=
  if negative then
    measuredMaskedSubInPlace c (L.reg g) (L.reg .y) (L.reg f) ((L.reg .carry).take (L.width-1)) L.cin
  else
    measuredMaskedAddInPlace c (L.reg g) (L.reg .y) (L.reg f) ((L.reg .carry).take (L.width-1)) L.cin

namespace RoundFrame

private theorem lift_one (L : RoundDataLayout) (hnd : L.wires.Nodup) (v : RoundField → Nat)
    (base : BasisState) (f : RoundField) (X : Nat) (p : Program)
    (hp : Triple (RoundFrame L v base) p (fun st => regValue (L.reg f) st=X))
    (he : ∀ (s : State) (m : List Bool), ∀ w, w∉L.reg f → (run p m s).basis w=s.basis w) :
    Triple (RoundFrame L v base) p (RoundFrame L (Function.update v f X) base) := by
  intro s m hv
  obtain ⟨hphase,hx⟩ := hp s m hv
  refine ⟨hphase, RoundValues.update L hnd v f X s.basis _ hv.1 (he s m) hx, ?_⟩
  intro w hw
  exact (he s m w (fun h => hw (L.reg_mem f h))).trans (hv.2 w hw)

theorem shift_right (L : RoundDataLayout) (c : Wire) (hnd : (c::L.wires).Nodup)
    (v : RoundField → Nat) (base : BasisState) (f : RoundField)
    (heven : base c=true → v f%2=0) :
    Triple (RoundFrame L v base) (shiftRight c (L.reg f))
      (RoundFrame L (Function.update v f (if base c then v f/2 else v f)) base) := by
  have hh := List.nodup_cons.mp hnd
  have hr : (c::L.reg f).Nodup := List.nodup_cons.mpr
    ⟨fun hm => hh.1 (L.reg_mem f hm),L.reg_nodup hh.2 f⟩
  apply lift_one L hh.2 v base f _ _
  · intro s m hv
    obtain ⟨hp,h⟩ := shiftRight_spec c (L.reg f) hr (base c) (v f) heven s m
      ⟨hv.2 c hh.1,hv.1.1 f⟩
    exact ⟨hp,h.2⟩
  · intro s m
    exact (shift_frame c (L.reg f) s m).2.1

theorem shift_left (L : RoundDataLayout) (c : Wire) (hnd : (c::L.wires).Nodup)
    (v : RoundField → Nat) (base : BasisState) (f : RoundField)
    (hfit : base c=true → 2*v f<2^L.width) :
    Triple (RoundFrame L v base) (shiftLeft c (L.reg f))
      (RoundFrame L (Function.update v f (if base c then 2*v f else v f)) base) := by
  have hh := List.nodup_cons.mp hnd
  have hr : (c::L.reg f).Nodup := List.nodup_cons.mpr
    ⟨fun hm => hh.1 (L.reg_mem f hm),L.reg_nodup hh.2 f⟩
  apply lift_one L hh.2 v base f _ _
  · intro s m hv
    obtain ⟨hp,h⟩ := shiftLeft_spec c (L.reg f) hr (base c) (v f)
      (by simpa only [L.reg_length] using hfit) s m ⟨hv.2 c hh.1,hv.1.1 f⟩
    exact ⟨hp,h.2⟩
  · intro s m
    exact (shift_frame c (L.reg f) s m).2.2.2

private theorem lift_two (L : RoundDataLayout) (hnd : L.wires.Nodup) (v : RoundField → Nat)
    (base : BasisState) (f g : RoundField) (X Y : Nat) (p : Program)
    (hp : Triple (RoundFrame L v base) p (fun st => regValue (L.reg f) st=X ∧ regValue (L.reg g) st=Y))
    (he : ∀ (s : State) (m : List Bool), RoundFrame L v base s.basis →
      ∀ w, w∉L.reg f → w∉L.reg g → (run p m s).basis w=s.basis w) :
    Triple (RoundFrame L v base) p
      (RoundFrame L (Function.update (Function.update v f X) g Y) base) := by
  intro s m hv
  obtain ⟨hphase,hx,hy⟩ := hp s m hv
  refine ⟨hphase, RoundValues.update_two L hnd v f g X Y s.basis _ hv.1 (he s m hv) hx hy, ?_⟩
  intro w hw
  exact (he s m hv w (fun h => hw (L.reg_mem f h)) (fun h => hw (L.reg_mem g h))).trans (hv.2 w hw)

theorem swap (L : RoundDataLayout) (c : Wire) (hnd : (c::L.wires).Nodup)
    (v : RoundField → Nat) (base : BasisState) (f g : RoundField) (hne : f≠g) :
    Triple (RoundFrame L v base) (swapRegisters c (L.reg f) (L.reg g))
      (RoundFrame L (Function.update (Function.update v f (if base c then v g else v f))
        g (if base c then v f else v g)) base) := by
  have hh := List.nodup_cons.mp hnd
  have hr : (c::(L.reg f++L.reg g)).Nodup := List.nodup_cons.mpr
    ⟨by intro hm; simp only [List.mem_append] at hm; rcases hm with hm | hm
        exact hh.1 (L.reg_mem f hm)
        exact hh.1 (L.reg_mem g hm),
      List.nodup_append'.mpr ⟨L.reg_nodup hh.2 f,L.reg_nodup hh.2 g,L.reg_disjoint hh.2 f g hne⟩⟩
  have hlen : (L.reg f).length=(L.reg g).length := by rw [L.reg_length,L.reg_length]
  apply lift_two L hh.2 v base f g _ _ _
  · intro s m hv
    obtain ⟨hp,_,hf,hg⟩ := swapRegisters_correct c (L.reg f) (L.reg g) hlen hr s m
    exact ⟨hp,by simpa only [hv.2 c hh.1,hv.1.1 f,hv.1.1 g] using hf,
      by simpa only [hv.2 c hh.1,hv.1.1 f,hv.1.1 g] using hg⟩
  · intro s m _
    exact (swapRegisters_correct c (L.reg f) (L.reg g) hlen hr s m).2.1

theorem inplace (L : RoundDataLayout) (c : Wire) (hnd : (c::L.wires).Nodup)
    (hpos : 0<L.width) (v : RoundField → Nat) (base : BasisState)
    (f g : RoundField) (hf : RoundDataLayout.DataField f) (hg : RoundDataLayout.DataField g) (hne : f≠g)
    (hy : v .y=0) (hcarry : v .carry=0) (negative : Bool) :
    let R := if negative then (v f+2^L.width-(if base c then v g else 0))%2^L.width
      else (v f+(if base c then v g else 0))%2^L.width
    Triple (RoundFrame L v base) (inplaceArithmetic L f g c negative)
      (RoundFrame L (Function.update v f R) base) := by
  dsimp only
  let chain := (L.reg .carry).take (L.width-1)
  let p := inplaceArithmetic L f g c negative
  have hh := List.nodup_cons.mp hnd
  have hs : (L.reg g).length=(L.reg .y).length := by simp [L.reg_length]
  have ht : (L.reg .y).length=(L.reg f).length := by simp [L.reg_length]
  have hc : chain.length+1=(L.reg f).length := by simp [chain,L.reg_length]; omega
  have hn : (c::L.cin::(L.reg g++L.reg .y++L.reg f++chain)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h1 := L.source_adder_count f g hf hg hne w
    have h2 := (L.adder f).interface_perm.count_eq w
    have h3 := List.nodup_iff_count.mp hnd w
    have h4 := (List.take_sublist (L.width-1) (L.reg .carry)).count_le w
    simp only [List.count_append,List.count_cons,
      (L.adder_fields f).1,(L.adder_fields f).2.1,(L.adder_fields f).2.2.1,
      (L.adder_fields f).2.2.2.1,(L.adder_fields f).2.2.2.2.1] at h1 h2 h3 ⊢
    dsimp only [chain] at *
    omega
  have hwEq := measuredMaskedInPlace_wires c (L.reg g) (L.reg .y) (L.reg f) chain L.cin hs ht hc
  intro s m hv
  have hz : regValue chain s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro w hm
    exact (regValue_zero _ _).mp ((hv.1.1 .carry).trans hcarry) w (List.mem_of_mem_take hm)
  have hpost :
      (run p m s).phase=s.phase ∧
      (run p m s).basis c=base c ∧
      regValue (L.reg g) (run p m s).basis=v g ∧
      regValue (L.reg .y) (run p m s).basis=0 ∧
      regValue (L.reg f) (run p m s).basis=
        (if negative then (v f+2^L.width-(if base c then v g else 0))%2^L.width
        else (v f+(if base c then v g else 0))%2^L.width) ∧
      (run p m s).basis L.cin=false ∧ regValue chain (run p m s).basis=0 := by
    have hp : ((((s.basis c=base c ∧ regValue (L.reg g) s.basis=v g) ∧
        regValue (L.reg .y) s.basis=0) ∧ regValue (L.reg f) s.basis=v f) ∧
        s.basis L.cin=false) ∧ regValue chain s.basis=0 := ⟨⟨⟨⟨⟨hv.2 c hh.1,hv.1.1 g⟩,(hv.1.1 .y).trans hy⟩,hv.1.1 f⟩,hv.1.2⟩,hz⟩
    cases negative
    · obtain ⟨ha,hb⟩ := measuredMaskedAddInPlace_spec c L.cin (L.reg g) (L.reg .y) (L.reg f) chain
        hn hs ht hc (base c) (v g) (v f) s m hp
      simp only [Holds.holds,L.reg_length] at hb
      simpa only [p,inplaceArithmetic,Bool.false_eq_true,if_false,L.reg_length] using
        ⟨ha,hb.1.1.1.1.1,hb.1.1.1.1.2,hb.1.1.1.2,hb.1.1.2,hb.1.2,hb.2⟩
    · obtain ⟨ha,hb⟩ := measuredMaskedSubInPlace_spec c L.cin (L.reg g) (L.reg .y) (L.reg f) chain
        hn hs ht hc (base c) (v g) (v f) s m hp
      simp only [Holds.holds,L.reg_length] at hb
      simpa only [p,inplaceArithmetic,if_true,L.reg_length] using
        ⟨ha,hb.1.1.1.1.1,hb.1.1.1.1.2,hb.1.1.1.2,hb.1.1.2,hb.1.2,hb.2⟩
  obtain ⟨hp,hc',hg',hy',hf',hcin',hchain'⟩ := hpost
  have he (w : Wire) (hf : w∉L.reg f) : (run p m s).basis w=s.basis w := by
    by_cases hm : w∈(c::L.cin::(L.reg g++L.reg .y++L.reg f++chain))
    · simp only [List.mem_cons,List.mem_append] at hm
      rcases hm with rfl | rfl | ((hm | hm) | hm) | hm
      · exact hc'.trans (hv.2 w hh.1).symm
      · exact hcin'.trans hv.1.2.symm
      · exact (regValue_eq_iff _ _ _).mp (hg'.trans (hv.1.1 g).symm) w hm
      · exact (regValue_eq_iff _ _ _).mp (hy'.trans ((hv.1.1 .y).trans hy).symm) w hm
      · exact False.elim (hf hm)
      · exact (regValue_eq_iff _ _ _).mp (hchain'.trans hz.symm) w hm
    · apply run_preserves_outside
      intro hw'
      have hsub : wires p ⊆ (c::L.cin::(L.reg g++L.reg .y++L.reg f++chain)).toFinset := by
        cases negative
        · simpa only [p,inplaceArithmetic,Bool.false_eq_true,if_false,chain] using hwEq.1.le
        · simpa only [p,inplaceArithmetic,if_true,chain] using hwEq.2.le
      exact hm (List.mem_toFinset.mp (hsub hw'))
  exact ⟨hp,RoundValues.update L hh.2 v f _ s.basis _ hv.1 he hf',
    fun w hw => (he w (fun hm => hw (L.reg_mem f hm))).trans (hv.2 w hw)⟩

theorem copy (L : RoundDataLayout) (hnd : L.wires.Nodup) (v : RoundField → Nat)
    (base : BasisState) (f g : RoundField) (hne : f≠g) :
    Triple (RoundFrame L v base) (copyRegister none (L.reg f) (L.reg g))
      (RoundFrame L (Function.update v g (v g ^^^ v f)) base) := by
  have hn : (L.reg f++L.reg g).Nodup := List.nodup_append'.mpr
    ⟨L.reg_nodup hnd f,L.reg_nodup hnd g,L.reg_disjoint hnd f g hne⟩
  have hlen : (L.reg f).length=(L.reg g).length := by rw [L.reg_length,L.reg_length]
  apply lift_one L hnd v base g _ _
  · intro s m hv
    obtain ⟨hp,_,ho⟩ := copyRegister_correct none (L.reg f) (L.reg g) hlen hn (by simp) s m
    exact ⟨hp,by simpa only [copyValue,hv.1.1 f,hv.1.1 g] using ho⟩
  · intro s m
    exact (copyRegister_correct none (L.reg f) (L.reg g) hlen hn (by simp) s m).2.1

theorem subtract (L : RoundDataLayout) (hnd : L.wires.Nodup) (v : RoundField → Nat)
    (base : BasisState) (f : RoundField) (hf : RoundDataLayout.DataField f) (hcarry : v .carry=0) :
    Triple (RoundFrame L v base) (sub (L.adder f))
      (RoundFrame L (Function.update v .out (v .out ^^^ ((v f+2^L.width-v .y)%2^L.width))) base) := by
  let A := L.adder f
  obtain ⟨ax,ay,ao,ac,ai,aw⟩ := L.adder_fields f
  change A.x=L.reg f at ax
  change A.y=L.reg .y at ay
  change A.out=L.reg .out at ao
  change A.carry=L.reg .carry at ac
  change A.cin=L.cin at ai
  change A.width=L.width at aw
  have hn := L.adder_nodup hnd f hf
  have hp : Triple (RoundFrame L v base) (sub A)
      (fun st => regValue (L.reg .out) st=v .out ^^^ ((v f+2^L.width-v .y)%2^L.width)) := by
    intro s m hv
    have hs := sub_spec A hn (v f) (v .y) (v .out)
    simp only [ax,ay,ao,ac,ai,aw] at hs
    obtain ⟨hp,h⟩ := hs s m ⟨⟨⟨⟨hv.1.1 f,hv.1.1 .y⟩,hv.1.2⟩,hv.1.1 .out⟩,
      (hv.1.1 .carry).trans hcarry⟩
    exact ⟨hp,h.1.2⟩
  intro s m hv
  obtain ⟨hphase,hout⟩ := hp s m hv
  have hc : s.basis A.cin=false := by simpa only [ai] using hv.1.2
  have hz : ∀ b∈A.bits, s.basis b.carry=false := by
    intro b hb
    have hh : regValue A.carry s.basis=0 := by simpa only [ac] using (hv.1.1 .carry).trans hcarry
    exact (regValue_zero _ _).mp hh b.carry (List.mem_map.mpr ⟨b,hb,rfl⟩)
  have he : ∀ w, w∉L.reg .out → (run (sub A) m s).basis w=s.basis w := by
    have hh := (rippleSubtractor_xor_correct A.bits A.cin hn s m hc hz).2.1
    simpa only [← ao] using hh
  refine ⟨hphase,RoundValues.update L hnd v .out _ s.basis _ hv.1 he hout,?_⟩
  intro w hw
  exact (he w (fun h => hw (L.reg_mem .out h))).trans (hv.2 w hw)

end RoundFrame
end ECDSAAdd.Arithmetic
