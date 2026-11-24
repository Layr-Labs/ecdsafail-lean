import ECDSAAdd.Submission.Entrant.MainP1


section

/-!
H3 only on accepted d9ade54c: the original CRTBarrel providers, digit tail,
portal providers and leaves are retained. Positive inverse ticks use the H3
receiver; tick zero is unchanged. Native forward admission is inherited.
This source preparation has not been compiled on the d9 base.
-/
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Core
open ECDSAAdd Arithmetic IntegerPacket
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem ready_range (p : IntegerPacket.Shape) (i : Nat) (z : SkywalkRails.State)
    (s : BasisState) (h : IntegerPacket.ready p i z s) :
    (-((2^(p.mid+1):Nat):Int) ≤ z.a ∧ z.a < ((2^(p.mid+1):Nat):Int)) ∧
    (-((2^(p.mid+1):Nat):Int) ≤ z.b ∧ z.b < ((2^(p.mid+1):Nat):Int)) := by
  have la : (IntegerPacket.ports p i).a.length=p.mid+2 := by
    simp [IntegerPacket.ports,SkywalkIntegerLayout.a,SkywalkIntegerLayout.ah,Nat.add_assoc,Nat.add_comm]
    omega
  have lb : (IntegerPacket.ports p i).b.length=p.mid+2 := by
    simp [IntegerPacket.ports,SkywalkIntegerLayout.b,SkywalkIntegerLayout.bh,Nat.add_assoc,Nat.add_comm]
    omega
  have a := signedDecode_range (IntegerPacket.ports p i).a.length
    (regValue (IntegerPacket.ports p i).a s) (by rw [la]; omega) (regValue_lt _ _)
  have b := signedDecode_range (IntegerPacket.ports p i).b.length
    (regValue (IntegerPacket.ports p i).b s) (by rw [lb]; omega) (regValue_lt _ _)
  change -((2^((IntegerPacket.ports p i).a.length-1):Nat):Int) ≤
    signedRegValue (IntegerPacket.ports p i).a s ∧
    signedRegValue (IntegerPacket.ports p i).a s <
      ((2^((IntegerPacket.ports p i).a.length-1):Nat):Int) at a
  change -((2^((IntegerPacket.ports p i).b.length-1):Nat):Int) ≤
    signedRegValue (IntegerPacket.ports p i).b s ∧
    signedRegValue (IntegerPacket.ports p i).b s <
      ((2^((IntegerPacket.ports p i).b.length-1):Nat):Int) at b
  simp only [h.1,la] at a
  simp only [h.2.1,lb] at b
  simpa only [show p.mid+2-1=p.mid+1 by omega] using And.intro a b

theorem next_a_range (n : Nat) (z : SkywalkRails.State)
    (ha : -((2^(n+1):Nat):Int) ≤ z.a ∧ z.a < ((2^(n+1):Nat):Int))
    (hb : -((2^(n+1):Nat):Int) ≤ z.b ∧ z.b < ((2^(n+1):Nat):Int)) :
    -((2^n:Nat):Int) ≤ (SkywalkTrace.next z).a ∧
      (SkywalkTrace.next z).a < ((2^n:Nat):Int) := by
  have power : ((2^(n+1):Nat):Int)=2*((2^n:Nat):Int) := by
    rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    ring
  rw [power] at ha hb
  simp only [SkywalkTrace.next,SkywalkRails.railsOf,SkywalkRails.step]
  unfold SkywalkRails.route
  split <;> dsimp only <;> omega

theorem ports_a_shape (p : IntegerPacket.Shape) (i : Nat) :
    (IntegerPacket.ports p i).a =
      List.range' (p.start+i+16) p.mid ++ [p.start+i+16+p.mid,p.start+i+16+p.mid+1] := by
  let b := p.start+i+16
  have slide : List.range' b p.mid ++ [b+p.mid] = b::List.range' (b+1) p.mid := by
    calc
      _ = List.range' b (p.mid+1) := List.range'_append_1
      _ = _ := List.range'_succ
  calc
    _ = (b::List.range' (b+1) p.mid) ++ [b+p.mid+1] := by
      simp [IntegerPacket.ports,SkywalkIntegerLayout.a,SkywalkIntegerLayout.ah,b,Nat.add_assoc]
    _ = (List.range' b p.mid ++ [b+p.mid]) ++ [b+p.mid+1] := by rw [slide]
    _ = _ := by simp [b,List.append_assoc]

/-- Every old forward tick leaves equal top two cells in its next A rail.
This derives the extra invariant from retained ready/one and signed bounds. -/
theorem one_top_pair (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1)
    (s : State) (m : List Bool) (ready : IntegerPacket.ready p i z s.basis) :
    (run (skywalkIntegerTick (IntegerPacket.ports p i)) m s).basis
        (p.start+i+17+p.mid+1) =
      (run (skywalkIntegerTick (IntegerPacket.ports p i)) m s).basis
        (p.start+i+17+p.mid) := by
  let out := run (skywalkIntegerTick (IntegerPacket.ports p i)) m s
  have post := (IntegerPacket.one p hi z odd s m ready).2
  have range := ready_range p i z s.basis ready
  have bounds := next_a_range p.mid z range.1 range.2
  have value : signedRegValue (IntegerPacket.ports p (i+1)).a out.basis = (SkywalkTrace.next z).a := post.1
  rw [ports_a_shape] at value
  have same := ECDSAAdd.Entrant.W.top_pair_eq
    (List.range' (p.start+(i+1)+16) p.mid)
    (p.start+(i+1)+16+p.mid) (p.start+(i+1)+16+p.mid+1)
    out.basis (SkywalkTrace.next z).a value
    (by simpa only [List.length_range'] using bounds.1)
    (by simpa only [List.length_range'] using bounds.2)
  simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using same

end ECDSAAdd.Entrant.StairPacket.TickCut.Core

end

section


namespace ECDSAAdd.Entrant.StairPacket.TickCut.Core
open ECDSAAdd Arithmetic
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-- At the second CCX site, x already holds the first CCX's output. -/
def affineErase (k p q x y : Wire) : Program :=
  [.CX p y,.CX q y,.CX x y,.measureX y [] [.CZ k q],.CX p y,.CX q y,.CX x y]

/-- Both measurement branches reproduce the old CCX under the affine AND relation. -/
theorem affineErase_same (k p q x y : Wire) (hky : k≠y) (hpy : p≠y)
    (hqy : q≠y) (hxy : x≠y) (s : State) (m : List Bool)
    (known : (((s.basis y ^^ s.basis p) ^^ s.basis q) ^^ s.basis x) =
      (s.basis k && s.basis q)) :
    run (affineErase k p q x y) m s = run [.CCX k q y] [] s := by
  apply State.extensionality
  · cases hm : m.headD false <;>
      cases hk : s.basis k <;> cases hp : s.basis p <;>
      cases hq : s.basis q <;> cases hx : s.basis x <;> cases hy : s.basis y <;>
      simp_all [affineErase,run,measureAndCorrect,correct,writeBit,Function.update_apply]
  · funext w
    by_cases hw : w=y
    · subst w
      cases hm : m.headD false <;>
        cases hk : s.basis k <;> cases hp : s.basis p <;>
        cases hq : s.basis q <;> cases hx : s.basis x <;> cases hy : s.basis y <;>
        simp_all [affineErase,run,measureAndCorrect,correct,writeBit,Function.update_apply]
    · cases hm : m.headD false <;>
        simp [affineErase,run,measureAndCorrect,correct,writeBit,Function.update_apply,
          hw,hky,hpy,hqy,hxy,hm]


/-- Split a copy tape at equal-length register prefixes. -/
theorem copy_append (control : Option Wire) (a b a' b' : List Wire)
    (hlen : a.length=b.length) :
    copyRegister control (a++a') (b++b') =
      copyRegister control a b ++ copyRegister control a' b' := by
  induction a generalizing b with
  | nil =>
    have hb : b=[] := List.eq_nil_of_length_eq_zero hlen.symm
    subst b
    rfl
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have htail : xs.length=ys.length := by simpa using hlen
      simpa only [List.cons_append,copyRegister,List.append_assoc] using
        congrArg (fun P : Program => [copyGate control x y]++P) (ih ys htail)

/-- Keep all low controlled copies and the first of the high pair. -/
def swapHigh (k : Wire) (a b : List Wire) (p q x y : Wire) : Program :=
  copyRegister none (b++[x,y]) (a++[p,q]) ++
    copyRegister (some k) a b ++ [.CCX k p x] ++ affineErase k p q x y ++
    copyRegister none (b++[x,y]) (a++[p,q])

/-- The old inverse swap has precisely the adjacent CCX pair selected by H3. -/
theorem swap_tail (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    swapRegisters k (a++[p,q]) (b++[x,y]) =
      copyRegister none (b++[x,y]) (a++[p,q]) ++
        copyRegister (some k) a b ++ [.CCX k p x,.CCX k q y] ++
        copyRegister none (b++[x,y]) (a++[p,q]) := by
  unfold swapRegisters
  rw [copy_append (some k) a b [p,q] [x,y] hlen]
  simp only [copyRegister,copyGate,List.append_assoc,List.cons_append,List.nil_append,List.append_nil]

/-- Exact syntax deltas; no admissibility or semantic hypothesis is hidden here. -/
theorem swapHigh_counts (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    toffoliCount (swapHigh k a b p q x y)+1 =
        toffoliCount (swapRegisters k (a++[p,q]) (b++[x,y])) ∧
    measurementCount (swapHigh k a b p q x y) =
        measurementCount (swapRegisters k (a++[p,q]) (b++[x,y]))+1 ∧
    Challenge.gateSlots (swapHigh k a b p q x y) =
        Challenge.gateSlots (swapRegisters k (a++[p,q]) (b++[x,y]))+7 := by
  have hf := copyRegister_counts none (b++[x,y]) (a++[p,q]) (by simp [hlen])
  have hl := copyRegister_counts (some k) a b hlen
  have ho := copyRegister_counts (some k) (a++[p,q]) (b++[x,y]) (by simp [hlen])
  change toffoliCount (copyRegister none (b++[x,y]) (a++[p,q]))=0 ∧
    measurementCount (copyRegister none (b++[x,y]) (a++[p,q]))=0 at hf
  change toffoliCount (copyRegister (some k) a b)=a.length ∧
    measurementCount (copyRegister (some k) a b)=0 at hl
  change toffoliCount (copyRegister (some k) (a++[p,q]) (b++[x,y]))=(a++[p,q]).length ∧
    measurementCount (copyRegister (some k) (a++[p,q]) (b++[x,y]))=0 at ho
  constructor
  · simp only [swapHigh,swapRegisters,toffoliCount_append,hf.1,hl.1,ho.1,
      affineErase,toffoliCount,List.length_append,List.length_cons,List.length_nil]
    omega
  constructor
  · simp only [swapHigh,swapRegisters,measurementCount_append,hf.2,hl.2,ho.2,
      affineErase,measurementCount]
  · have affineSlots : Challenge.gateSlots (affineErase k p q x y)=8 := rfl
    have oneSlot : Challenge.gateSlots [.CCX k p x]=1 := rfl
    simp only [swapHigh,swapRegisters,Challenge.gateSlots_append,affineSlots,oneSlot,
      Baselines.copyRegister_gateSlots,List.length_append,List.length_cons,List.length_nil,
      hlen,Nat.min_self]
    omega


/-- A measurement-free suffix is independent of its supplied tape. -/
theorem no_measure (P : Program) (h : measurementCount P=0) (s : State) (m : List Bool) :
    run P m s=run P [] s := by
  have same := run_take P m s
  simpa only [h,List.take_zero] using same.symm

theorem append_no_measure (P Q : Program) (hQ : measurementCount Q=0)
    (s : State) (m : List Bool) :
    run (P++Q) m s=run Q [] (run P m s) := by
  rw [run_append,run_take]
  exact no_measure Q hQ _ _

def suffixOld (k p q x y : Wire) (P : Program) : Program :=
  [.CCX k q y] ++ P ++ [.CX x p,.CX y q]

def suffixNew (k p q x y : Wire) (P : Program) : Program :=
  affineErase k p q x y ++ P ++ [.CX x p,.CX y q]

/-- The output top-pair invariant gives the affine relation at the last CCX.
P is the final swap's low CX layer; it leaves these four high wires alone. -/
theorem suffix_same (k p q x y : Wire) (P : Program)
    (distinct : [k,p,q,x,y].Nodup) (noP : measurementCount P=0)
    (frame : ∀(t : State)(m : List Bool)(w : Wire),w∈[p,q,x,y] →
      (run P m t).basis w=t.basis w)
    (s : State) (m : List Bool)
    (top : (run (suffixOld k p q x y P) [] s).basis p =
      (run (suffixOld k p q x y P) [] s).basis q) :
    run (suffixNew k p q x y P) m s=run (suffixOld k p q x y P) [] s := by
  simp only [List.nodup_cons,List.nodup_nil,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at distinct
  have hky : k≠y := by tauto
  have hpy : p≠y := by tauto
  have hqy : q≠y := by tauto
  have hxy : x≠y := by tauto
  have hpq : p≠q := by tauto
  have hxp : x≠p := by tauto
  have hxq : x≠q := by tauto
  have hqp : q≠p := Ne.symm hpq
  let t := run [.CCX k q y] [] s
  let u := run P [] t
  have up : u.basis p=s.basis p := by
    rw [frame t [] p (by simp)]
    simp [t,run,writeBit,Function.update_apply,hpy]
  have uq : u.basis q=s.basis q := by
    rw [frame t [] q (by simp)]
    simp [t,run,writeBit,Function.update_apply,hqy]
  have ux : u.basis x=s.basis x := by
    rw [frame t [] x (by simp)]
    simp [t,run,writeBit,Function.update_apply,hxy]
  have uy : u.basis y=(s.basis y ^^ (s.basis k && s.basis q)) := by
    rw [frame t [] y (by simp)]
    simp [t,run,writeBit,Function.update_apply]
  have out : run (suffixOld k p q x y P) [] s=run [.CX x p,.CX y q] [] u := by
    simp only [suffixOld,run_append,List.take_nil,List.drop_nil]
    rfl
  rw [out] at top
  have bits : (s.basis p ^^ s.basis x)=
      (s.basis q ^^ (s.basis y ^^ (s.basis k && s.basis q))) := by
    simpa only [run,writeBit,Function.update_apply,hpq,hqp,hxp,hxq,
      hpy,hqy,Ne.symm hpy,Ne.symm hqy,if_false,if_true,up,uq,ux,uy] using top
  have known : (((s.basis y ^^ s.basis p) ^^ s.basis q) ^^ s.basis x)=
      (s.basis k && s.basis q) := by
    cases hk : s.basis k <;> cases hp : s.basis p <;> cases hq : s.basis q <;>
      cases hx : s.basis x <;> cases hy : s.basis y <;> simp_all
  have localSame := affineErase_same k p q x y hky hpy hqy hxy s m known
  have noTail : measurementCount (P++[.CX x p,.CX y q])=0 := by
    simp [noP,measurementCount]
  change run (affineErase k p q x y ++ (P++[.CX x p,.CX y q])) m s = _
  rw [append_no_measure _ _ noTail,localSame]
  symm
  exact append_no_measure [.CCX k q y] (P++[.CX x p,.CX y q]) noTail s []


/-- Common prefix ending with the retained first high CCX. -/
def swapFront (k : Wire) (a b : List Wire) (p q x y : Wire) : Program :=
  copyRegister none (b++[x,y]) (a++[p,q]) ++
    copyRegister (some k) a b ++ [.CCX k p x]

theorem swap_old_shape (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    swapRegisters k (a++[p,q]) (b++[x,y]) =
      swapFront k a b p q x y ++ suffixOld k p q x y (copyRegister none b a) := by
  rw [swap_tail k a b p q x y hlen]
  simp only [swapFront,suffixOld,copy_append none b a [x,y] [p,q] hlen.symm,
    copyRegister,copyGate,List.append_assoc,
    List.cons_append,List.nil_append,List.append_nil]

theorem swap_new_shape (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length) :
    swapHigh k a b p q x y =
      swapFront k a b p q x y ++ suffixNew k p q x y (copyRegister none b a) := by
  unfold swapHigh
  simp only [swapFront,suffixNew,copy_append none b a [x,y] [p,q] hlen.symm,
    copyRegister,copyGate,List.append_assoc,
    List.cons_append,List.nil_append,List.append_nil]

/-- Generic optimized inverse-swap equality from its OLD output A high-pair fact. -/
theorem swapHigh_same (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length)
    (nd : (k::((a++[p,q])++(b++[x,y]))).Nodup)
    (s : State) (m : List Bool)
    (top : (run (swapRegisters k (a++[p,q]) (b++[x,y])) [] s).basis p =
      (run (swapRegisters k (a++[p,q]) (b++[x,y])) [] s).basis q) :
    run (swapHigh k a b p q x y) m s =
      run (swapRegisters k (a++[p,q]) (b++[x,y])) [] s := by
  have small : [k,p,q,x,y].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have ndba : (b++a).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have outside : ∀w∈[p,q,x,y],w∉a := by
    intro w hw ha
    have count := List.nodup_iff_count.mp nd w
    have positive := List.count_pos_iff.mpr ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    all_goals
      simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at count
      omega
  have frame : ∀(t : State)(n : List Bool)(w : Wire),w∈[p,q,x,y] →
      (run (copyRegister none b a) n t).basis w=t.basis w := by
    intro t n w hw
    exact (copyRegister_correct none b a hlen.symm ndba (by simp) t n).2.1 w (outside w hw)
  have hf := copyRegister_counts none (b++[x,y]) (a++[p,q]) (by simp [hlen])
  have hl := copyRegister_counts (some k) a b hlen
  have noFront : measurementCount (swapFront k a b p q x y)=0 := by
    simp only [swapFront,measurementCount_append,hf.2,hl.2,measurementCount]
  let u := run (swapFront k a b p q x y) [] s
  have topU : (run (suffixOld k p q x y (copyRegister none b a)) [] u).basis p =
      (run (suffixOld k p q x y (copyRegister none b a)) [] u).basis q := by
    rw [swap_old_shape k a b p q x y hlen,run_append] at top
    simpa only [List.take_nil,List.drop_nil] using top
  have hc := copyRegister_counts none b a hlen.symm
  have same := suffix_same k p q x y (copyRegister none b a) small hc.2 frame u m topU
  rw [swap_new_shape k a b p q x y hlen,swap_old_shape k a b p q x y hlen]
  simp only [run_append,noFront,List.take_zero,List.drop_zero,List.take_nil,List.drop_nil]
  exact same

/-- A measured receiver prefix uses identical old records; only the new final
swap measurement consumes an additional record, after all old measurements. -/
theorem prefix_swapHigh_same (P : Program) (k : Wire) (a b : List Wire) (p q x y : Wire)
    (hlen : a.length=b.length)
    (nd : (k::((a++[p,q])++(b++[x,y]))).Nodup)
    (s : State) (m : List Bool)
    (top : (run (P++swapRegisters k (a++[p,q]) (b++[x,y])) m s).basis p =
      (run (P++swapRegisters k (a++[p,q]) (b++[x,y])) m s).basis q) :
    run (P++swapHigh k a b p q x y) m s =
      run (P++swapRegisters k (a++[p,q]) (b++[x,y])) m s := by
  have hf := copyRegister_counts none (b++[x,y]) (a++[p,q]) (by simp [hlen])
  have ho := copyRegister_counts (some k) (a++[p,q]) (b++[x,y]) (by simp [hlen])
  have noSwap : measurementCount (swapRegisters k (a++[p,q]) (b++[x,y]))=0 := by
    simp only [swapRegisters,measurementCount_append,hf.2,ho.2]
  rw [append_no_measure P _ noSwap s m] at top
  have same := swapHigh_same k a b p q x y hlen nd (run P m s)
    (m.drop (measurementCount P)) top
  rw [run_append,run_take,same]
  symm
  exact append_no_measure P _ noSwap s m

end ECDSAAdd.Entrant.StairPacket.TickCut.Core

end

section

/- Concrete H3 facade draft; compilation and caller integration remain pending. -/
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Receiver
open ECDSAAdd Arithmetic IntegerPacket TickCut.Core
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def lowA (p : IntegerPacket.Shape) (i : Nat) := List.range' (p.start+i+17) (p.mid-1)
def lowB (p : IntegerPacket.Shape) := List.range' 787 (p.mid-1)
def highP (p : IntegerPacket.Shape) (i : Nat) : Wire := p.start+i+16+p.mid
def highQ (p : IntegerPacket.Shape) (i : Nat) : Wire := p.start+i+17+p.mid
def highX (p : IntegerPacket.Shape) : Wire := 786+p.mid
def highY (p : IntegerPacket.Shape) : Wire := 787+p.mid

theorem range_two (b n : Nat) (hn : 1≤n) :
    List.range' b n ++ [b+n] = List.range' b (n-1) ++ [b+(n-1),b+n] := by
  cases n with
  | zero => omega
  | succ r =>
    change List.range' b (r+1) ++ [b+(r+1)] =
      List.range' b r ++ [b+r,b+(r+1)]
    have eq : List.range' b r ++ [b+r] = List.range' b (r+1) := by
      simpa only [List.range'_one] using (List.range'_append_1 (s:=b) (m:=r) (n:=1))
    rw [←eq]
    simp only [List.append_assoc,List.singleton_append]

theorem ah_shape (p : IntegerPacket.Shape) (i : Nat) (hm : 1≤p.mid) :
    (IntegerPacket.ports p i).ah = lowA p i ++ [highP p i,highQ p i] := by
  have h := range_two (p.start+i+17) p.mid hm
  have hp : p.start+i+17+(p.mid-1)=highP p i := by dsimp [highP]; omega
  rw [hp] at h
  simpa only [IntegerPacket.ports,SkywalkIntegerLayout.ah,lowA,highQ,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem bh_shape (p : IntegerPacket.Shape) (i : Nat) (hm : 1≤p.mid) :
    (IntegerPacket.ports p i).bh = lowB p ++ [highX p,highY p] := by
  have h := range_two 787 p.mid hm
  have hp : 787+(p.mid-1)=highX p := by dsimp [highX]; omega
  rw [hp] at h
  simpa only [IntegerPacket.ports,SkywalkIntegerLayout.bh,lowB,highY,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem low_lengths (p : IntegerPacket.Shape) (i : Nat) : (lowA p i).length=(lowB p).length := by
  simp only [lowA,lowB,List.length_range']

theorem swap_nodup (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid) :
    ((IntegerPacket.ports p i).a0::((lowA p i++[highP p i,highQ p i])++
      (lowB p++[highX p,highY p]))).Nodup := by
  have nd := SkywalkIntegerLayout.route_nodup _ (IntegerPacket.ok p ⟨i,hi⟩)
  change ((IntegerPacket.ports p i).a0::(IntegerPacket.ports p i).b0::
    ((IntegerPacket.ports p i).ah++(IntegerPacket.ports p i).bh)).Nodup at nd
  rw [ah_shape p i hm,bh_shape p i hm] at nd
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp nd w
  simp only [List.count_cons] at h ⊢
  omega

def receiverPrefix (L : SkywalkIntegerLayout) (n : Nat) : Program :=
  [.CX L.previous L.a0] ++ ECDSAAdd.Entrant.W.ReverseCarry.narrowReceiver
    (narrowSkywalkRecordLayout L n) n ++ skywalkSignedHalf L.aSign L.ext ++ [.CX L.a0 L.b0]

def receiverHigh (p : IntegerPacket.Shape) (i : Nat) : Program :=
  receiverPrefix (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length ++
    swapHigh (IntegerPacket.ports p i).a0 (lowA p i) (lowB p)
      (highP p i) (highQ p i) (highX p) (highY p)

theorem receiverHigh_same (p : IntegerPacket.Shape) (i : Nat)
    (hi : i<p.length) (hm : 1≤p.mid) (s : State) (m : List Bool)
    (top : (run (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) m s).basis (highP p i) =
      (run (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) m s).basis (highQ p i)) :
    run (receiverHigh p i) m s = run (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
      (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) m s := by
  have same := prefix_swapHigh_same
    (receiverPrefix (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length)
    (IntegerPacket.ports p i).a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p)
    (low_lengths p i) (swap_nodup p i hi hm) s m
    (by simpa only [receiverPrefix,ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick,
      ah_shape p i hm,bh_shape p i hm] using top)
  simpa only [receiverHigh,receiverPrefix,ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick,
    ah_shape p i hm,bh_shape p i hm] using same

theorem receiverHigh_counts (p : IntegerPacket.Shape) (i : Nat) (hm : 1≤p.mid) :
    toffoliCount (receiverHigh p i)+1 = toffoliCount
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length) ∧
    measurementCount (receiverHigh p i) = measurementCount
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length)+1 ∧
    Challenge.gateSlots (receiverHigh p i) = Challenge.gateSlots
      (ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
        (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length)+7 := by
  have counts := swapHigh_counts (IntegerPacket.ports p i).a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p) (low_lengths p i)
  simp only [receiverHigh,receiverPrefix,ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick,
    ah_shape p i hm,bh_shape p i hm,toffoliCount_append,measurementCount_append,
    Challenge.gateSlots_append]
  omega

def readyPlus (p : IntegerPacket.Shape) (i : Nat) (z : SkywalkRails.State) (b : BasisState) : Prop :=
  IntegerPacket.ready p i z b ∧ ((0 < i) → (b (highP p i)=b (highQ p i)))

theorem onePlus (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (readyPlus p i z) (skywalkIntegerTick (IntegerPacket.ports p i))
      (readyPlus p (i+1) (SkywalkTrace.next z)) := by
  intro s m h
  have old := IntegerPacket.one p hi z odd s m h.1
  refine ⟨old.1,old.2,?_⟩
  intro positive
  have top := one_top_pair p i hi z odd s m h.1
  simpa only [highP,highQ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using top.symm

def receiverSelected (p : IntegerPacket.Shape) (i : Nat) : Program :=
  if i=0 then ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick
    (IntegerPacket.ports p i) (IntegerPacket.ports p i).half.length else receiverHigh p i

theorem singleHigh (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (readyPlus p i z) (skywalkIntegerTick (IntegerPacket.ports p i))
      (receiverSelected p i) := by
  intro s m n h
  have old := IntegerPacket.singleR p ⟨i,hi⟩ z odd s m n h.1
  by_cases zero : i=0
  · simpa only [receiverSelected,zero,if_true] using old
  · simp only [receiverSelected,zero,if_false]
    rw [receiverHigh_same p i hi hm]
    · exact old
    · rw [old]
      exact h.2 (by omega)

def backHigh (p : IntegerPacket.Shape) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => backHigh p (i+1) n ++ receiverSelected p i

private theorem composeHigh {P Q : BasisState → Prop} {A B I J : Program}
    (stage : Triple P A Q) (left : Restores P A I) (right : Restores Q B J) :
    Restores P (A++B) (J++I) := by
  intro s enc dec p
  rw [run_append J I,run_append A B]
  rw [right _ _ _ (stage _ _ p).2]
  exact left _ _ _ p

/-- Stronger ready predicate carries the preceding-tick invariant through the
old forward trajectory. Tick zero keeps the original receiver. -/
theorem roundtripHigh (p : IntegerPacket.Shape) (i n : Nat) (bound : i+n≤p.length)
    (hm : 1≤p.mid) (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (readyPlus p i z) (IntegerPacket.seq p i n) (backHigh p i n) := by
  induction n generalizing i z with
  | zero =>
    intro s a b h
    simp [IntegerPacket.seq,backHigh,run]
  | succ n ih =>
    rw [IntegerPacket.seq,backHigh]
    apply composeHigh (onePlus p i (by omega) z odd)
    · exact singleHigh p i (by omega) hm z odd
    · exact ih (i+1) (by omega) (SkywalkTrace.next z) (IntegerPacket.nextOdd z odd)

end ECDSAAdd.Entrant.StairPacket.TickCut.Receiver

end

section


namespace ECDSAAdd.Entrant.StairPacket.TickCut.Hosted
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

theorem semanticPlus (p : IntegerPacket.Shape) (i n : Nat) (bound : i+n≤p.length)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (readyPlus p i z) (IntegerPacket.seq p i n)
      (readyPlus p (i+n) (SkywalkTrace.next^[n] z)) := by
  induction n generalizing i z with
  | zero =>
    intro s m h
    simpa [IntegerPacket.seq,run] using And.intro (rfl : s.phase=s.phase) h
  | succ n ih =>
    have a := onePlus p i (by omega) z odd
    have b := ih (i+1) (by omega) (SkywalkTrace.next z) (IntegerPacket.nextOdd z odd)
    simpa only [IntegerPacket.seq,Function.iterate_succ_apply,show i+(n+1)=i+1+n by omega] using a.seq b

def onRailsPlus (j : Fin 26) (i : Nat) (z : SkywalkRails.State) (b : BasisState) :=
  readyPlus (Shadow7.shape j) i z (mappedBasis j b)

def unroutedHigh (j : Fin 26) (i n : Nat) : Program :=
  renameProgram (windowNet j) (backHigh (Shadow7.shape j) i n)

theorem routeFramePlus (j : Fin 26) (i n : Nat) (bound : i+n≤15)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (onRailsPlus j i z) (Shadow7.routed j i n)
      (onRailsPlus j (i+n) (SkywalkTrace.next^[n] z)) := by
  intro s m ready
  have h := semanticPlus (Shadow7.shape j) i n bound z odd (pullState (windowNet j) s) m ready
  rw [←Shadow7.pull_routed j i n bound m s] at h
  exact h

theorem routeUndoHigh (j : Fin 26) (i n : Nat) (bound : i+n≤15)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (onRailsPlus j i z) (Shadow7.routed j i n) (unroutedHigh j i n) := by
  intro s m t ready
  have forward := Shadow7.pull_routed j i n bound m s
  let actual := run (Shadow7.routed j i n) m s
  have bk : pullState (windowNet j) (run (unroutedHigh j i n) t actual)=
      run (backHigh (Shadow7.shape j) i n) t (pullState (windowNet j) actual) := by
    rw [unroutedHigh,run_rename _ (netInjective j)]
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have fin := roundtripHigh (Shadow7.shape j) i n bound hm z odd
    (pullState (windowNet j) s) m t ready
  change pullState (windowNet j) actual=_ at forward
  rw [forward,fin] at bk
  apply congrArg₂ State.mk (congrArg State.phase bk)
  funext q
  have h := congrArg (fun x : State => x.basis (windowNet j q)) bk
  change (run (unroutedHigh j i n) t actual).basis (windowNet j (windowNet j q))=
    s.basis (windowNet j (windowNet j q)) at h
  have inv : windowNet j (windowNet j q)=q := by
    apply OB5.sig_invol
    have hj := j.isLt
    simp [start]; omega
  rwa [inv] at h

theorem watch_a (j : Fin 26) (q : Wire)
    (hq : q∈(IntegerPacket.ports (Shadow7.shape j) 1).a) :
    windowNet j q∈Shadow7.watch j := by
  unfold Shadow7.watch
  dsimp only
  apply List.mem_map.mpr
  refine ⟨q,?_,rfl⟩
  simp only [List.mem_append]
  tauto

/-- Archive administration preserves the stronger first successor invariant
because the stock watch contains its entire A rail. -/
theorem watch_congrPlus (j : Fin 26) (s t : State)
    (agree : ∀q∈Shadow7.watch j,t.basis q=s.basis q)
    (z : SkywalkRails.State) (active : onRailsPlus j 1 z s.basis) :
    onRailsPlus j 1 z t.basis := by
  have old := (Shadow7.watch_congr j s t agree z active.1).1
  refine ⟨old,?_⟩
  intro positive
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have hp : highP (Shadow7.shape j) 1∈(IntegerPacket.ports (Shadow7.shape j) 1).a := by
    simp only [SkywalkIntegerLayout.a,ah_shape _ _ hm,List.mem_cons,List.mem_append]
    simp
  have hq : highQ (Shadow7.shape j) 1∈(IntegerPacket.ports (Shadow7.shape j) 1).a := by
    simp only [SkywalkIntegerLayout.a,ah_shape _ _ hm,List.mem_cons,List.mem_append]
    simp
  change t.basis (windowNet j (highP (Shadow7.shape j) 1))=
    t.basis (windowNet j (highQ (Shadow7.shape j) 1))
  rw [agree _ (watch_a j _ hp),agree _ (watch_a j _ hq)]
  exact active.2 positive

def unbodyHigh (j : Fin 26) (reverse : Program) : Program :=
  unroutedHigh j 1 14 ++ (reverse ++ unroutedHigh j 0 1)

/-- The selected new reverse body restores the untouched old forward body.
Both invariant propagation and archive administration use retained old semantics. -/
theorem body_runHigh (j : Fin 26) (admin reverse : Program) (s : State) (m : List Bool)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) (active : Shadow7.onRails j 0 z s.basis)
    (mid : let src:=run (Shadow7.routed j 0 1) m s
      Shadow7.AdminResult j reverse src (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) src)) :
    let out:=run (Shadow7.body j admin) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unbodyHigh j reverse) n out=s := by
  let src := run (Shadow7.routed j 0 1) m s
  let t := m.drop (measurementCount (Shadow7.routed j 0 1))
  let pre := run admin t src
  let n := t.drop (measurementCount admin)
  have strong0 : onRailsPlus j 0 z s.basis := ⟨active,by intro bad; omega⟩
  have head := routeFramePlus j 0 1 (by decide) z odd s m strong0
  have valid : onRailsPlus j 1 (SkywalkTrace.next z) src.basis := head.2
  have pass := watch_congrPlus j src pre mid.unchanged _ valid
  have oldPass := Shadow7.watch_congr j src pre mid.unchanged _ valid.1
  have span := Shadow7.split_run j z odd s m n active pre oldPass.1 oldPass.2
  have last := routeFramePlus j 1 14 (by decide) (SkywalkTrace.next z)
    (IntegerPacket.nextOdd z odd) pre n pass
  dsimp only [Shadow7.body,unbodyHigh]
  simp only [run_append,run_take]
  refine ⟨last.1.trans (mid.phase.trans head.1),span.1,span.2,?_⟩
  intro r
  have endBack := routeUndoHigh j 1 14 (by decide) (SkywalkTrace.next z)
    (IntegerPacket.nextOdd z odd) pre n r pass
  change run (unroutedHigh j 0 1) _ (run reverse _
    (run (unroutedHigh j 1 14) r (run (Shadow7.routed j 1 14) n pre)))=s
  rw [endBack,mid.undo]
  exact routeUndoHigh j 0 1 (by decide) z odd s m _ strong0

end ECDSAAdd.Entrant.StairPacket.TickCut.Hosted

end

section

namespace ECDSAAdd.Entrant.StairPacket.TickCut.Static
open ECDSAAdd Arithmetic RecordedQuantum IntegerPacket TickCut.Core TickCut.Receiver TickCut.Hosted
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem swapHigh_support (k : Wire) (a b : List Wire) (p q x y : Wire) :
    wires (swapHigh k a b p q x y) ⊆ (k::((a++[p,q])++(b++[x,y]))).toFinset := by
  let target := (k::((a++[p,q])++(b++[x,y]))).toFinset
  have back : wires (copyRegister none (b++[x,y]) (a++[p,q])) ⊆ target := by
    intro w hw
    have h := copyRegister_wires_subset none (b++[x,y]) (a++[p,q]) hw
    simp only [target,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,
      Option.toList_none,List.nil_append,or_false] at h ⊢
    tauto
  have low : wires (copyRegister (some k) a b) ⊆ target := by
    intro w hw
    have h := copyRegister_wires_subset (some k) a b hw
    simp only [target,List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,
      Option.toList_some,List.singleton_append,or_false] at h ⊢
    tauto
  have first : wires [.CCX k p x] ⊆ target := by
    intro w hw
    simp [target,wires,Instr.wires] at hw ⊢
    tauto
  have aff : wires (affineErase k p q x y) ⊆ target := by
    intro w hw
    simp [target,affineErase,wires,Instr.wires,correctionWires] at hw ⊢
    tauto
  intro w hw
  simp only [swapHigh,wires_append,Finset.mem_union] at hw
  rcases hw with (((h|h)|h)|h)|h
  · exact back h
  · exact low h
  · exact first h
  · exact aff h
  · exact back h

theorem swapHigh_physical (k : Wire) (a b : List Wire) (p q x y : Wire)
    (nd : (k::((a++[p,q])++(b++[x,y]))).Nodup) : GatePhysical (swapHigh k a b p q x y) := by
  have full := (List.nodup_cons.mp nd).2
  have back := copyRegister_physical none (b++[x,y]) (a++[p,q])
    (List.nodup_append_comm.mpr full) (by simp)
  have ndab : (a++b).Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have low := copyRegister_physical (some k) a b ndab (by
    intro c hc hb
    cases hc
    apply (List.nodup_cons.mp nd).1
    simp [hb])
  have small : [k,p,q,x,y].Nodup := by
    apply List.nodup_iff_count.mpr
    intro w
    have h := List.nodup_iff_count.mp nd w
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.nodup_nil,List.mem_cons,List.not_mem_nil,
    not_or,not_false_eq_true,and_true] at small
  have first : GatePhysical [.CCX k p x] := by
    simp_all [GatePhysical,PhysicalInstr,ProperGate]
  have aff : GatePhysical (affineErase k p q x y) := by
    simp_all [affineErase,GatePhysical,PhysicalInstr,ProperGate]
  simp only [swapHigh,gatePhysical_append]
  exact ⟨⟨⟨⟨back,low⟩,first⟩,aff⟩,back⟩

theorem receiverHigh_support (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid) :
    wires (receiverHigh p i) ⊆ (IntegerPacket.ports p i).wires.toFinset := by
  let L := IntegerPacket.ports p i
  have valid := IntegerPacket.ok p ⟨i,hi⟩
  have hn : 0<L.half.length := by simp [SkywalkIntegerLayout.half]
  have old := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support L L.half.length valid hn le_rfl
  have front : wires (receiverPrefix L L.half.length) ⊆ L.wires.toFinset := by
    intro w hw
    apply old
    change w∈wires (receiverPrefix L L.half.length ++ swapRegisters L.a0 L.ah L.bh)
    rw [wires_append,Finset.mem_union]
    exact Or.inl hw
  have tail := swapHigh_support L.a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p)
  have tailInside : wires (swapHigh L.a0 (lowA p i) (lowB p)
      (highP p i) (highQ p i) (highX p) (highY p)) ⊆ L.wires.toFinset := by
    intro w hw
    have h := tail hw
    rw [←ah_shape p i hm,←bh_shape p i hm] at h
    simp only [SkywalkIntegerLayout.wires,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  intro w hw
  simp only [receiverHigh,wires_append,Finset.mem_union] at hw
  exact hw.elim (fun h=>front h) (fun h=>tailInside h)

theorem receiverHigh_physical (p : IntegerPacket.Shape) (i : Nat) (hi : i<p.length) (hm : 1≤p.mid) :
    GatePhysical (receiverHigh p i) := by
  let L := IntegerPacket.ports p i
  have valid := IntegerPacket.ok p ⟨i,hi⟩
  have hn : 0<L.half.length := by simp [SkywalkIntegerLayout.half]
  have old := ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_physical L L.half.length valid hn le_rfl
  change GatePhysical (receiverPrefix L L.half.length ++ swapRegisters L.a0 L.ah L.bh) at old
  have front := (gatePhysical_append _ _).mp old |>.1
  have tail := swapHigh_physical L.a0 (lowA p i) (lowB p)
    (highP p i) (highQ p i) (highX p) (highY p) (swap_nodup p i hi hm)
  exact (gatePhysical_append _ _).mpr ⟨front,tail⟩

/-- Every positive-index reverse span saves exactly one T per tick. -/
theorem backHigh_counts (p : IntegerPacket.Shape) (i n : Nat)
    (hm : 1≤p.mid) (positive : 0 < i) :
    toffoliCount (backHigh p i n)+n = toffoliCount (IntegerPacket.backR p i n) ∧
    measurementCount (backHigh p i n) = measurementCount (IntegerPacket.backR p i n)+n ∧
    Challenge.gateSlots (backHigh p i n) = Challenge.gateSlots (IntegerPacket.backR p i n)+7*n := by
  induction n generalizing i with
  | zero => simp [backHigh,IntegerPacket.backR,toffoliCount,measurementCount,Challenge.gateSlots]
  | succ n ih =>
    have tail := ih (i+1) (by omega)
    have point := receiverHigh_counts p i hm
    have nonzero : ¬i=0 := by omega
    simp only [backHigh,IntegerPacket.backR,receiverSelected,nonzero,if_false,
      toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
    omega

end ECDSAAdd.Entrant.StairPacket.TickCut.Static

end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

def selected (j : Fin 26) (a n : Nat) : Program :=
  if a=1 ∧ n=14 then unroutedHigh j 1 14 else Shadow7.unrouted j a n

theorem head_eq (j : Fin 26) : unroutedHigh j 0 1=Shadow7.unrouted j 0 1 := by
  rw [(Shadow7.fixed_route j 0 1 (by decide)).2]
  simp [unroutedHigh,backHigh,receiverSelected,IntegerPacket.backR]

def unbodySelected (j : Fin 26) (reverse : Program) :=
  selected j 1 14 ++ (reverse ++ selected j 0 1)

theorem unbody_eq (j : Fin 26) (reverse : Program) :
    unbodySelected j reverse=unbodyHigh j reverse := by
  simp only [unbodySelected,selected,unbodyHigh,show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩,
    and_true,if_true,show ¬((0:Nat)=1 ∧ (1:Nat)=14) by omega,if_false]
  rw [head_eq]

theorem body_runSelected (j : Fin 26) (admin reverse : Program) (s : State) (m : List Bool)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) (active : Shadow7.onRails j 0 z s.basis)
    (mid : let src:=run (Shadow7.routed j 0 1) m s
      Shadow7.AdminResult j reverse src (run admin (m.drop (measurementCount (Shadow7.routed j 0 1))) src)) :
    let out:=run (Shadow7.body j admin) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unbodySelected j reverse) n out=s := by
  simpa only [unbody_eq] using body_runHigh j admin reverse s m z odd active mid

theorem tail_counts (j : Fin 26) :
    toffoliCount (unroutedHigh j 1 14)+14=toffoliCount (Shadow7.unrouted j 1 14) ∧
    measurementCount (unroutedHigh j 1 14)=measurementCount (Shadow7.unrouted j 1 14)+14 ∧
    Challenge.gateSlots (unroutedHigh j 1 14)=Challenge.gateSlots (Shadow7.unrouted j 1 14)+98 := by
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have c := backHigh_counts (Shadow7.shape j) 1 14 hm (by decide)
  rw [(Shadow7.fixed_route j 1 14 (by decide)).2]
  simpa only [unroutedHigh,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots] using c

theorem selected_t (j : Fin 26) (a n : Nat) :
    toffoliCount (selected j a n)=toffoliCount (Shadow7.unrouted j a n) -
      (if a=1 ∧ n=14 then 14 else 0) := by
  by_cases h : a=1 ∧ n=14
  · rcases h with ⟨rfl,rfl⟩
    have c := (tail_counts j).1
    simp only [selected,if_pos (show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩),and_true,if_true]
    omega
  · simp only [selected,h,if_false,Nat.sub_zero]

theorem selected_m (j : Fin 26) (a n : Nat) :
    measurementCount (selected j a n)=measurementCount (Shadow7.unrouted j a n) +
      (if a=1 ∧ n=14 then 14 else 0) := by
  by_cases h : a=1 ∧ n=14
  · rcases h with ⟨rfl,rfl⟩
    simpa only [selected,if_pos (show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩),and_true,if_true] using (tail_counts j).2.1
  · simp only [selected,h,if_false,Nat.add_zero]

theorem selected_slots (j : Fin 26) (a n : Nat) :
    Challenge.gateSlots (selected j a n)=Challenge.gateSlots (Shadow7.unrouted j a n) +
      (if a=1 ∧ n=14 then 98 else 0) := by
  by_cases h : a=1 ∧ n=14
  · rcases h with ⟨rfl,rfl⟩
    simpa only [selected,if_pos (show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩),and_true,if_true] using (tail_counts j).2.2
  · simp only [selected,h,if_false,Nat.add_zero]

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail

end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCut.Receiver TickCut.Hosted TickCut.Static
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

theorem back_physical (p : IntegerPacket.Shape) (i n : Nat) (bound : i+n≤p.length) (hm : 1≤p.mid) :
    GatePhysical (backHigh p i n) := by
  induction n generalizing i with
  | zero => simp [backHigh,GatePhysical]
  | succ n ih =>
    have h := ih (i+1) (by omega)
    have hv := IntegerPacket.ok p ⟨i,by omega⟩
    have hn : 0<(IntegerPacket.ports p i).half.length := by simp [SkywalkIntegerLayout.half]
    have point : GatePhysical (receiverSelected p i) := by
      unfold receiverSelected
      split
      · exact ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_physical _ _ hv hn le_rfl
      · exact receiverHigh_physical p i (by omega) hm
    exact (gatePhysical_append _ _).mpr ⟨h,point⟩

theorem tail_physical (j : Fin 26) : GatePhysical (unroutedHigh j 1 14) := by
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  exact gatePhysical_rename _ (netInjective j) _ (back_physical (Shadow7.shape j) 1 14 (by simp [Shadow7.shape]) hm)

theorem tail_covered (j : Fin 26) (h0 : 0≤j.val) (h1 : j.val≤24) :
    WindowCovered.CoveredW (unroutedHigh j 1 14) := by
  have hm : 1≤(Shadow7.shape j).mid := by simp [Shadow7.shape]
  have all (a n : Nat) (bound : a+n≤15) :
      WindowCovered.CoveredW (renameProgram (windowNet j) (backHigh (Shadow7.shape j) a n)) := by
    induction n generalizing a with
    | zero => intro q hq; simp [backHigh,renameProgram,wires] at hq
    | succ n ih =>
      have ha : a<15 := by omega
      have hv := IntegerPacket.ok (Shadow7.shape j) ⟨a,ha⟩
      have hn : 0<(IntegerPacket.ports (Shadow7.shape j) a).half.length := by simp [SkywalkIntegerLayout.half]
      have sub : wires (receiverSelected (Shadow7.shape j) a) ⊆
          (IntegerPacket.ports (Shadow7.shape j) a).wires.toFinset := by
        unfold receiverSelected
        split
        · exact ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support _ _ hv hn le_rfl
        · exact receiverHigh_support (Shadow7.shape j) a ha hm
      have point : WindowCovered.CoveredW (renameProgram (windowNet j)
          (receiverSelected (Shadow7.shape j) a)) := by
        intro q hq
        rw [renameProgram_support] at hq
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hq
        have mem := List.mem_toFinset.mp (sub hw)
        have dom := WindowCovered7.ports_dom h0 h1 ha mem
        rwa [Shadow7.stable ha mem] at dom
      have tail := ih (a+1) (by omega)
      simpa only [backHigh,renameProgram,List.map_append] using WindowCovered.appW tail point
  exact all 1 14 (by decide)

end ECDSAAdd.Entrant.StairPacket.TickCut.Tail

end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.NativeJ7
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace
open SkywalkRails Partial WideReference EnterProof
open ECDSAAdd.Entrant.StairPacket.NativeJ7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
def window (j : Fin 26) (d:Bool) := Shadow7.body j (withArchive j d)
def unwind (j : Fin 26) (d:Bool) := TickCut.Tail.unbodySelected j (fromArchive j d)
theorem window_run (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (start0:Shadow7.onRails j 0 z s.basis)
    (legal:MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) m s).basis)
    (row:Nat) (limit:row<63145) (frame:Frame (ArchiveJ7.rawPorts (prev j)) ArchivePortAction.raw row
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)))
    (clean:∀k:Fin 157,23≤k.val → ArchiveJ7.rawPorts (prev j) k∈Shadow7.watch j →
      (run (program j d) (m.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) m s)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false) :
    let out:=run (window j d) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind j d) n out=s := by
  apply TickCut.Tail.body_runSelected _ _ _ _ _ z odd start0
  exact (admin j (by omega) h19 d _ _ (SkywalkTrace.next z) (Shadow7.route_frame j 0 1 (by decide) z odd s m start0).2 legal row limit frame clean).1

end ECDSAAdd.Entrant.StairPacket.TickCut.NativeJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.NativeJ7
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace
open SkywalkRails Partial WideReference EnterProof
open ECDSAAdd.Entrant.StairPacket.NativeJ7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
def nextWindow (j : Fin 26) (d:Bool) := Shadow7.enterP j++window j d
def nextUnwind (j : Fin 26) (d:Bool) := unwind j d++Shadow7.enterInvP j

theorem backward_sub : wires EnterProof17.backward ⊆ Finset.range 13 := by decide +kernel
theorem enterInvCover (j : Fin 26) : wires (Shadow7.enterInvP j) ⊆ (EnterJ7.ports j).toFinset := by
  rw [EnterJ7.emittedInv j,renameProgram_support]
  intro q hq
  obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hq
  have lt:w<(EnterJ7.ports j).length:=Finset.mem_range.mp (backward_sub hw)
  rw [List.mem_toFinset,EnterJ7.map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem lt,Option.getD_some]
  exact List.getElem_mem lt

theorem next_window (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (raw s:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (past:SkywalkNat.State) (pg ps cross:Bool) (po:past.v%2=1) (pm:Shadow7.SmallIfFar (Shadow7.sbP (start (prev j))) 15 past)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) past pg ps cross s) :
    let out:=run (nextWindow j d) m s
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (nextUnwind j d) t out=s := by
  let pre:=run (Shadow7.enterP j) m s
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨legal,row,limit,frame⟩:=admits j (by omega) h19 d s m tape (tape.drop (measurementCount (Shadow7.routed j 0 1))) Z parity ready.2.1
    scratch past pg ps cross po pm prior
  have all:=window_run j (by omega) h19 d pre tape Z parity ready.2.1 legal row limit frame
    (fun k hk _=>scratch k hk)
  dsimp only [nextWindow,nextUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records_shadow7 (Shadow7.sbP (start j)) z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  have free:∀q∈EnterJ7.pending j,q∉wires (Shadow7.enterInvP j):=by
    intro q hq used
    have r:=EnterJ7.portsRegion j (List.mem_toFinset.mp (enterInvCover j used))
    have f:=EnterJ7.frame j
    simp only [EnterJ7.pending,List.mem_cons,List.not_mem_nil,or_false] at hq
    simp only [Wire] at *
    omega
  apply unmask (Shadow7.enterP j) (Shadow7.enterInvP j) (EnterJ7.pending j) (EnterJ7.avoid_enter j) free
  exact EnterProof17.return_packed (EnterJ7.layout j) (EnterJ7.map j) _ _ (EnterJ7.inc j) (fun _=>rfl) rfl (EnterJ7.emitted j)
    (EnterJ7.emittedInv j) raw _ z G S small cut input _ _

end ECDSAAdd.Entrant.StairPacket.TickCut.NativeJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.NativeJ7
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace
open SkywalkRails Partial WideReference EnterProof
open ECDSAAdd.Entrant.StairPacket.NativeJ7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
theorem from_domain_matched (j : Fin 26) (h2 : 1≤j.val) (h19 : j.val≤24) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (m:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:∀k:Fin 157,23≤k.val →
      let pre:=run (Shadow7.enterP j) m s
      let tape:=m.drop (measurementCount (Shadow7.enterP j))
      (run (program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1))) (run (Shadow7.routed j 0 1) tape pre)).basis
        (ArchiveJ7.rawPorts (prev j) k)=false)
    (pg ps cross:Bool)
    (prior:PastFacts (prev j) (ArchiveJ7.rawPorts (prev j)) (Shadow7.sbP (start (prev j))) (unsigned (start (prev j)) x p) pg ps cross s) :
    let out:=run (nextWindow j d) m s
    LeaveJ7.Admission.Inputs j out (unsigned (start j) x p) G S ∧ out.phase=s.phase ∧
    (∃row<63145,RowTruth (unsigned (start (prev j)) x p) pg ps row ∧ Kept (ArchiveJ7.codePorts (prev j)) d row out) ∧
    ∀n,run (nextUnwind j d) n out=s:=by
  let z:=unsigned (start j) x p
  let past:=unsigned (start (prev j)) x p
  have nums:=LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have old:=LeaveJ7.Admission.actualNumbers (prev j) (by simp only [prev]; omega) (by simp only [prev]; omega) x p good
  have hist:=pulled_history j rfl domain
  have a:=next_window j (by omega) (by omega) d raw s m z G S nums.odd nums.farSmall cut input hist scratch past pg ps cross
    old.odd old.farSmall prior
  obtain ⟨row,limit,truth,code,_⟩:=real_receipt j (by omega) (by omega) d raw s m z G S nums.odd nums.farSmall cut input hist
    scratch past pg ps cross old.odd old.farSmall prior
  exact ⟨admitted j (by omega) (by omega) d x p raw s m z G S nums domain cut input hist scratch past pg ps cross old.odd old.farSmall
    prior,a.1,⟨row,limit,truth,code⟩,a.2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.TickCut.NativeJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.NativeFirstJ7
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace
open SkywalkRails Partial WideReference EnterProof
open ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
def window (j : Fin 26) (d:Bool) := Shadow7.body j (program j d)
def unwind (j : Fin 26) (d:Bool) := TickCut.Tail.unbodySelected j (ECDSAAdd.Entrant.StairPacket.NativeFirstJ7.reverse j d)
theorem window_run (j : Fin 26) (h : 0≤j.val) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (start0:Shadow7.onRails j 0 z s.basis)
    (legal:MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) m s).basis) :
    let out:=run (window j d) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind j d) n out=s := by
  apply TickCut.Tail.body_runSelected _ _ _ _ _ z odd start0
  exact admin j h d _ _ legal

end ECDSAAdd.Entrant.StairPacket.TickCut.NativeFirstJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.NativeFirstJ7
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace
open SkywalkRails Partial WideReference EnterProof
open ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
attribute [local irreducible] run Shadow7.onRails Shadow7.unrouted
def enteredWindow (j : Fin 26) (d:Bool) := Shadow7.enterP j++window j d
def enteredUnwind (j : Fin 26) (d:Bool) := unwind j d++Shadow7.enterInvP j
theorem entered_window (j : Fin 26) (h1 : 0≤j.val) (h21 : j.val≤24) (d:Bool) (raw v:State) (m:List Bool)
    (z:SkywalkNat.State) (G S:Bool) (odd:z.v%2=1) (small:Shadow7.SmallIfFar (Shadow7.sbP (start j)) 15 z)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 z)) (decide (Shadow.far (Shadow7.sbP (start j)) 15 z ∧ 2^(Shadow7.sbP (start j))≤z.u))
      (pullState (EnterJ7.pull j) raw) v)
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist:∀r:Fin 15,raw.basis (EnterJ7.pull j (windowNet j (IntegerPacket.ports (Shadow7.shape j) r).history))=false)
    (legal0:MeasuredCodec5.legalAt (History5.historyMap base (start j-5)) raw.basis) :
    let out:=run (enteredWindow j d) m v
    let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
    out.phase=v.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀t,run (enteredUnwind j d) t out=v := by
  let pre:=run (Shadow7.enterP j) m v
  let tape:=m.drop (measurementCount (Shadow7.enterP j))
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 z
  let Z:=encode G S T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) z small odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum G S _ _ (by omega)
  have ready:=EnterJ7.ready_from_cut_at j raw v z G S m small cut input hist
  have legal:=legal_congr (history_from_stock j h1 (by omega) raw v pre cut m tape rfl _ parity ready.2) legal0
  have all:=window_run j h1 d pre tape Z parity ready.2 legal
  dsimp only [enteredWindow,enteredUnwind]
  simp only [run_append,run_take]
  refine ⟨all.1.trans ready.1,all.2.1,all.2.2.1.trans (true_records_shadow7 (Shadow7.sbP (start j)) z small odd G S),?_⟩
  intro n
  rw [all.2.2.2 n]
  exact EnterProof17.return_packed (EnterJ7.layout j) (EnterJ7.map j) _ _ (EnterJ7.inc j) (fun _=>rfl) rfl (EnterJ7.emitted j)
    (EnterJ7.emittedInv j) raw _ z G S small cut input _ _

end ECDSAAdd.Entrant.StairPacket.TickCut.NativeFirstJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.NativeFirstJ7
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket SkywalkRails EnterProof Partial WideReference
open ECDSAAdd.Entrant.StairPacket.NativeFirstJ7
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
private theorem flagEq (g sg:Bool) (u v:Int) : (encode g sg u v).g=g := by cases g <;> rfl
theorem firstBack : ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)).phase=raw.phase ∧
    ∀k, run (TickCut.NativeFirstJ7.enteredUnwind WindowParams.first d ++ Shadow7.portalInvP (start WindowParams.first)) k
      (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))=
      pullState (OB5.sig (start WindowParams.first-1)) raw := by
  intro d x p good raw m stage
  have hf : WindowParams.first = j0 := rfl
  rw [hf]
  simp only [start0]
  obtain ⟨G, S, input, cut0, clean⟩ := first_core d x p good raw m stage
  let origin := pullState (OB5.sig 44) raw
  let cut := run (Shadow7.portalP 45) m origin
  let n0 := m.drop (measurementCount (Shadow7.portalP 45))
  have dom := initial 45 x p (by decide) d raw stage
  have numbers := LeaveJ7.Admission.actualNumbers j0 (by decide) (by decide) x p good
  have hist := WideReference.pulled_history j0 rfl dom
  have legal0 := original_legal j0 (by decide) (by decide) d x p good.positive good.odd raw stage
  have inputL : SkywalkIntegerInput (EnterJ7.lay j0) (encode G S (unsigned 45 x p).u (unsigned 45 x p).v).a
      (encode G S (unsigned 45 x p).u (unsigned 45 x p).v).b G raw.basis := by
    have i2 := input; unfold InputAt at i2; rw [flagEq] at i2; exact i2
  have win := entered_window j0 (by decide) (by decide) d raw cut n0 (unsigned 45 x p) G S numbers.odd numbers.farSmall
    cut0 inputL hist legal0
  have vEq' : run (Shadow7.portalP 45 ++ enteredWindow j0 d) m origin = run (enteredWindow j0 d) n0 cut := by
    simp only [run_append, run_take, cut, n0, origin]
  refine ⟨?_, ?_⟩
  · rw [vEq', win.1]; exact cut0.phase
  · intro k
    rw [vEq', run_append, win.2.2.2]
    exact Portal45Flag7.portal_return origin m _ clean (Portal45Flag7.erase_ready _
      (show Shadow7.SmallIfFar 226 15 (unsigned 45 x p) from
        (Shadow7.Envelope.inputs x p 45 (lt_trans good.small good.cap) good.cap (by decide)).1) raw m G S
      (by have i2 := input; unfold InputAt at i2; rw [flagEq] at i2; exact i2))

end ECDSAAdd.Entrant.StairPacket.TickCut.NativeFirstJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut
open ECDSAAdd Arithmetic WindowFold Baselines Challenge
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

abbrev baseParams : Pieces Program := CRTBarrel.params
def params : Pieces Program := {baseParams with unrouted := Tail.selected}

def tcV : Pieces Nat := {CRTWindow.tcV with
  unrouted := fun j a n =>
    CRTWindow.tcV.unrouted j a n - (if a=1 ∧ n=14 then 14 else 0)}
def mcV : Pieces Nat := {CRTWindow.mcV with
  unrouted := fun j a n =>
    CRTWindow.mcV.unrouted j a n + (if a=1 ∧ n=14 then 14 else 0)}
def slotsV : Pieces Nat := {CRTWindow.slotsV with
  unrouted := fun j a n =>
    CRTWindow.slotsV.unrouted j a n + (if a=1 ∧ n=14 then 98 else 0)}

private theorem map_unrouted_update {α β : Type} (P : Pieces α) (f : α → β)
    (u : Fin 26 → Nat → Nat → α) :
    ({P with unrouted := u}.map f)={P.map f with unrouted := fun j a n => f (u j a n)} := rfl

private theorem le_unrouted_update {P V : Pieces Nat} (h : P.Le V)
    {a b : Fin 26 → Nat → Nat → Nat} (hu : ∀j i n,a j i n≤b j i n) :
    Pieces.Le {P with unrouted := a} {V with unrouted := b} :=
  ⟨h.enter,h.enterInv,h.leave,h.leaveInv,h.load,h.restore,h.portal,h.portalInv,h.park,h.parkInv,
    h.exitLoad,h.exitRestore,h.routed,hu,h.pack,h.unpack,h.tick,h.receiver⟩

theorem tc_eq : params.map toffoliCount=tcV := by
  rw [params,map_unrouted_update baseParams toffoliCount Tail.selected,CRTWindow.tc_eq]
  unfold tcV
  apply congrArg (fun u : Fin 26 → Nat → Nat → Nat => ({CRTWindow.tcV with unrouted := u} : Pieces Nat))
  funext j a n
  have old := congrFun (congrFun (congrFun (congrArg Pieces.unrouted CRTWindow.tc_eq) j) a) n
  change toffoliCount (Shadow7.unrouted j a n)=CRTWindow.tcV.unrouted j a n at old
  rw [Tail.selected_t,old]

theorem mc_eq : params.map measurementCount=mcV := by
  rw [params,map_unrouted_update baseParams measurementCount Tail.selected,CRTWindow.mc_eq]
  unfold mcV
  apply congrArg (fun u : Fin 26 → Nat → Nat → Nat => ({CRTWindow.mcV with unrouted := u} : Pieces Nat))
  funext j a n
  have old := congrFun (congrFun (congrFun (congrArg Pieces.unrouted CRTWindow.mc_eq) j) a) n
  change measurementCount (Shadow7.unrouted j a n)=CRTWindow.mcV.unrouted j a n at old
  rw [Tail.selected_m,old]

theorem slots_le : (params.map gateSlots).Le slotsV := by
  rw [params,map_unrouted_update baseParams gateSlots Tail.selected]
  unfold slotsV
  apply le_unrouted_update CRTWindow.slots_le
  intro j a n
  have old := CRTWindow.slots_le.unrouted j a n
  change gateSlots (Shadow7.unrouted j a n)≤CRTWindow.slotsV.unrouted j a n at old
  rw [Tail.selected_slots]
  omega

def forward (d : Bool) : Program := forwardW params d WindowParams.first WindowParams7.rest7
def reverse (d : Bool) : Program := reverseW params d WindowParams.first WindowParams7.rest7

private theorem chainF_update {α : Type} (P : Pieces α) (u : Fin 26 → Nat → Nat → α)
    (d : Bool) : ∀i js,chainF {P with unrouted:=u} d i js=chainF P d i js
  | _,[] => rfl
  | i,j::js => by rw [chainF,chainF,chainF_update P u d j js]; rfl

theorem forward_eq (d : Bool) : forward d=forwardW baseParams d WindowParams.first WindowParams7.rest7 := by
  simp only [forward,params,forwardW,forwardL,firstF,exitF,chainF_update]

theorem counts (d : Bool) :
    toffoliCount (forward d)=127306 ∧ toffoliCount (reverse d)=(if d then 127373 else 127398) ∧
    measurementCount (forward d)=66040 ∧ measurementCount (reverse d)=(if d then 65672 else 65697) := by
  have f := measure_forward toffoliCount toffoliCount_append params d WindowParams.first WindowParams7.rest7
  have r := measure_reverse toffoliCount toffoliCount_append params d WindowParams.first WindowParams7.rest7
  have g := measure_forward measurementCount measurementCount_append params d WindowParams.first WindowParams7.rest7
  have q := measure_reverse measurementCount measurementCount_append params d WindowParams.first WindowParams7.rest7
  change toffoliCount _=(forwardL (params.map toffoliCount) d _ _).sum at f
  change toffoliCount _=(reverseL (params.map toffoliCount) d _ _).sum at r
  change measurementCount _=(forwardL (params.map measurementCount) d _ _).sum at g
  change measurementCount _=(reverseL (params.map measurementCount) d _ _).sum at q
  rw [tc_eq] at f r
  rw [mc_eq] at g q
  refine ⟨f.trans ?_,r.trans ?_,g.trans ?_,q.trans ?_⟩
  all_goals cases d <;> decide +kernel

theorem slot_sums : (forwardL slotsV true WindowParams.first WindowParams7.rest7).sum≤2419094 ∧
    (forwardL slotsV false WindowParams.first WindowParams7.rest7).sum≤2419094 ∧
    (reverseL slotsV true WindowParams.first WindowParams7.rest7).sum≤2403571 ∧
    (reverseL slotsV false WindowParams.first WindowParams7.rest7).sum≤2403571 := by decide +kernel

theorem slots : gateSlots (forward true)≤2419094 ∧ gateSlots (forward false)≤2419094 ∧
    gateSlots (reverse true)≤2403571 ∧ gateSlots (reverse false)≤2403571 := by
  simp only [forward,reverse]
  rw [measure_forward gateSlots gateSlots_append,measure_forward gateSlots gateSlots_append,
    measure_reverse gateSlots gateSlots_append,measure_reverse gateSlots gateSlots_append]
  exact ⟨(forwardL_le slots_le true WindowParams.first WindowParams7.rest7).trans slot_sums.1,
    (forwardL_le slots_le false WindowParams.first WindowParams7.rest7).trans slot_sums.2.1,
    (reverseL_le slots_le true WindowParams.first WindowParams7.rest7).trans slot_sums.2.2.1,
    (reverseL_le slots_le false WindowParams.first WindowParams7.rest7).trans slot_sums.2.2.2⟩

theorem ship_toffoliF_true : toffoliCount (forwardW params true WindowParams.first WindowParams7.rest7)=127306 := (counts true).1
theorem ship_toffoliF_false : toffoliCount (forwardW params false WindowParams.first WindowParams7.rest7)=127306 := (counts false).1
theorem ship_toffoliR_true : toffoliCount (reverseW params true WindowParams.first WindowParams7.rest7)=127373 := (counts true).2.1
theorem ship_toffoliR_false : toffoliCount (reverseW params false WindowParams.first WindowParams7.rest7)=127398 := (counts false).2.1
theorem ship_measureF : measurementCount (forwardW params true WindowParams.first WindowParams7.rest7)=66040 ∧
    measurementCount (forwardW params false WindowParams.first WindowParams7.rest7)=66040 := ⟨(counts true).2.2.1,(counts false).2.2.1⟩
theorem ship_measureR : measurementCount (reverseW params true WindowParams.first WindowParams7.rest7)=65672 ∧
    measurementCount (reverseW params false WindowParams.first WindowParams7.rest7)=65697 := ⟨(counts true).2.2.2,(counts false).2.2.2⟩

theorem ship_slots : gateSlots (forwardW params true WindowParams.first WindowParams7.rest7)≤2419094 ∧
    gateSlots (forwardW params false WindowParams.first WindowParams7.rest7)≤2419094 ∧
    gateSlots (reverseW params true WindowParams.first WindowParams7.rest7)≤2403571 ∧
    gateSlots (reverseW params false WindowParams.first WindowParams7.rest7)≤2403571 := slots

private theorem onE_unrouted_update {α : Type} (P : Pieces α) (Q : α → Prop) (d : Bool)
    (u : Fin 26 → Nat → Nat → α)
    (head : ∀ j, u j 0 1 = P.unrouted j 0 1)
    (tail : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 → Q (u j 1 14))
    (h : P.OnE Q d 0 24) :
    ({P with unrouted := u} : Pieces α).OnE Q d 0 24 := by
  constructor
  · intro j h0 h1
    have v := h.block j h0 h1
    change Q (P.enter j) ∧ Q (P.enterInv j) ∧ Q (P.leave j) ∧ Q (P.leaveInv j) ∧
      Q (P.routed j 0 1) ∧ Q (P.routed j 1 14) ∧ Q (u j 0 1) ∧ Q (u j 1 14)
    rw [head j]
    exact ⟨v.1,v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2.1,v.2.2.2.2.2.2.1,tail j h0 h1⟩
  · exact h.first
  · exact h.later
  · exact h.saved
  · exact h.exit

private theorem params_onE_of (Q : Program → Prop) (d : Bool)
    (h : baseParams.OnE Q d 0 24)
    (high : ∀j:Fin 26,0≤j.val → j.val≤24 → Q (Hosted.unroutedHigh j 1 14)) :
    params.OnE Q d 0 24 := by
  have head : ∀ j, Tail.selected j 0 1 = baseParams.unrouted j 0 1 := by
    intro j
    simp only [Tail.selected, show ¬((0:Nat)=1 ∧ (1:Nat)=14) by omega, if_false,
      baseParams,CRTWindow.params_unrouted,Shadow7.params,ofParts]
  have tail : ∀j:Fin 26,0≤j.val → j.val≤24 → Q (Tail.selected j 1 14) := by
    intro j h0 h1
    simpa only [Tail.selected, show (1:Nat)=1 ∧ (14:Nat)=14 from ⟨rfl,rfl⟩, if_true] using high j h0 h1
  exact onE_unrouted_update baseParams Q d Tail.selected head tail h

theorem params_onE (d : Bool) : params.OnE WindowCovered.CoveredW d 0 24 :=
  params_onE_of _ d (CRTWindow.params_onE d) Tail.tail_covered

theorem params_onE_phys (d : Bool) : params.OnE GatePhysical d 0 24 :=
  params_onE_of _ d (CRTWindow.params_onE_phys d) (fun j _ _ => Tail.tail_physical j)

theorem window_covered (d : Bool) : WindowCovered.CoveredW (forward d) ∧ WindowCovered.CoveredW (reverse d) :=
  ⟨flatten_of WindowCovered.nilW (fun ha hb=>WindowCovered.appW ha hb) _
      (forwardL_onE (params_onE d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide)),
    flatten_of WindowCovered.nilW (fun ha hb=>WindowCovered.appW ha hb) _
      (reverseL_onE (params_onE d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide))⟩

theorem window_physical (d : Bool) : GatePhysical (forward d) ∧ GatePhysical (reverse d) :=
  ⟨flatten_of WindowPhysicalW.nilP (fun ha hb=>WindowPhysicalW.appP ha hb) _
      (forwardL_onE (params_onE_phys d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide)),
    flatten_of WindowPhysicalW.nilP (fun ha hb=>WindowPhysicalW.appP ha hb) _
      (reverseL_onE (params_onE_phys d) _ _ WindowParams7.consec7 rfl WindowParams7.last7 (by decide))⟩

end ECDSAAdd.Entrant.StairPacket.TickCut
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-- dadon's `At240`/`At255` for any block `k` (the saved keys are `window_strong`'s `Key`). -/
structure AtJ (k : Fin 26) (d:Bool) (x p:Nat) (raw s:State) (g sg pg ps:Bool) : Prop where
  domain : Domain (start k) x p raw
  input : InputAt (start k) (signedAt (start k) x p g sg) raw
  cut : PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k) (flagNeg (start k) x p sg)
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p))
      (decide (farAt (Shadow7.sbP (start k)) (start k) x p ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) raw) (eraseSites (EnterJ7.pending k) s)
  facts : PastFacts (NativeJ7.prev k) (ArchiveJ7.rawPorts (NativeJ7.prev k)) (Shadow7.sbP (start (NativeJ7.prev k)))
      (unsigned (start (NativeJ7.prev k)) x p) pg ps
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d (NativeJ7.prev k) (unsigned (start (NativeJ7.prev k)) x p))) s
  pastCanonical : signedAt (start (NativeJ7.prev k)) x p pg ps=WideReference.canonical (start (NativeJ7.prev k)) x p

/-- The hand-off at tick `t` (a block start). -/
def ReadyW (d:Bool) (x p:Nat) (t:Nat) (s:State) : Prop :=
  ∃ k : Fin 26, start k=t ∧ ∃ raw g sg pg ps, AtJ k d x p raw s g sg pg ps

/-- Block `i`'s saved archive key (dadon's `Saved (start i) x p (codePorts) d`). -/
def KeyW (d:Bool) (x p:Nat) (i:Fin 26) (s:State) : Prop :=
  ∃row<63145, Chronology (start i) x p row ∧ Kept (ArchiveJ7.codePorts i) d row s

/-- The window's precondition: the stock walk at tick 120 (dadon's `Before` at 225). -/
def BeforeW (d:Bool) (x p:Nat) (s:State) := ∃raw:State,
  Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis ∧ s=pullState (OB5.sig (start WindowParams.first-1)) raw

/-- par-c2's archive-scratch hypothesis of `NativeJ7.from_domain(_matched)`. -/
def ScratchAt (j : Fin 26) (d:Bool) (m:List Bool) (s:State) : Prop :=
  ∀k:Fin 157,23≤k.val →
    let pre:=run (Shadow7.enterP j) m s
    let tape:=m.drop (measurementCount (Shadow7.enterP j))
    (run (NativeJ7.program j d) (tape.drop (measurementCount (Shadow7.routed j 0 1)))
      (run (Shadow7.routed j 0 1) tape pre)).basis
      (ArchiveJ7.rawPorts (NativeJ7.prev j) k)=false

-- ===== Leaves (statements fixed here; each becomes a theorem) =====

/-- L2: the archive scratch of block `j` is clean after its pack (par-d2's ScratchWrap). -/
abbrev ScratchSpec : Prop :=
  ∀ (j : Fin 26), 1≤j.val → j.val≤24 → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State) (g sg pg ps:Bool)
    (m:List Bool), AtJ j d x p raw s g sg pg ps → ScratchAt j d m s

/-- L3: the (move) leave undoes (GlueB's `Admission.Inputs.roundtrip`, on the window's move leave). -/
abbrev RoundtripSpec : Prop :=
  ∀ (j : Fin 26), 0≤j.val → j.val≤24 → ∀ (v:State) (z:SkywalkNat.State) (G S:Bool),
    LeaveJ7.Admission.Inputs j v z G S → ∀ m n:List Bool, run (CRTBarrel.unleave j) n (run (CRTBarrel.leave j) m v)=v

/-- The block after the window's first block. -/
def firstNext : Fin 26 := ⟨WindowParams.first.val+1,by decide⟩

/-- L9: the first block's endpoint at `start WindowParams.first` (dadon's `NativePack225.stock_endpoint`, first form). -/
abbrev FirstSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m n:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    ∃g s:Bool,
      InputAt (start WindowParams.first) (encode g s (unsigned (start WindowParams.first) x p).u (unsigned (start WindowParams.first) x p).v) raw ∧
      LeaveJ7.Admission.Inputs WindowParams.first
        (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))
        (unsigned (start WindowParams.first) x p) g s ∧
      PackedCut (EnterJ7.lowerPairs firstNext) (EnterJ7.upperPairs firstNext) (EnterJ7.gate firstNext)
        (EnterJ7.flagN firstNext) (EnterJ7.flagF firstNext) (EnterJ7.flagU firstNext)
        (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g s).2 (unsigned (start WindowParams.first+15) x p).u)
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p)))
        (decide (Shadow.far (Shadow7.sbP (start WindowParams.first+15)) 15 (unsigned (start WindowParams.first+15) x p) ∧ 2^(Shadow7.sbP (start WindowParams.first+15))≤(unsigned (start WindowParams.first+15) x p).u))
        (pullState (EnterJ7.pull firstNext)
          (endRaw (start WindowParams.first) raw (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))))
        (eraseSites (EnterJ7.pending firstNext) (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))) ∧
      PastFacts WindowParams.first (ArchiveJ7.rawPorts WindowParams.first) (Shadow7.sbP (start WindowParams.first)) (unsigned (start WindowParams.first) x p) g s
        (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d WindowParams.first (unsigned (start WindowParams.first) x p)))
        (run (Shadow7.leaveP WindowParams.first) n
          (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)))

/-- L10: the first window (portal 120, enter, pack) keeps the phase and undoes (dadon's `NativePack225.first_window`). -/
abbrev FirstBackSpec : Prop :=
  ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw:State) (m:List Bool)
    (stage:Rolling1588.Integer.Stage base d x p (start WindowParams.first) raw.basis),
    (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)).phase=raw.phase ∧
    ∀k, run (TickCut.NativeFirstJ7.enteredUnwind WindowParams.first d ++ Shadow7.portalInvP (start WindowParams.first)) k
      (run (Shadow7.portalP (start WindowParams.first) ++ NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw))=
      pullState (OB5.sig (start WindowParams.first-1)) raw

-- ===== Program bridges =====

theorem prev_of (i k : Fin 26) (hk : k.val=i.val+1) : NativeJ7.prev k=i := Fin.ext (by simp only [NativeJ7.prev]; omega)

theorem start_succ (i k : Fin 26) (hk : k.val=i.val+1) : start k=start i+15 := by simp only [StairPacket.start]; omega

theorem next_eq (d:Bool) (i k : Fin 26) (hk : k.val=i.val+1) :
    (nextF TickCut.params d i k).flatten=NativeJ7.nextWindow k d++CRTBarrel.leave k := by
  have e:=prev_of i k hk
  subst e
  simp only [nextF,TickCut.params,TickCut.baseParams,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeJ7.nextWindow,NativeJ7.window,Shadow7.body,NativeJ7.withArchive,NativeJ7.program,List.append_assoc]

theorem nextR_eq (d:Bool) (i k : Fin 26) (hk : k.val=i.val+1) :
    (nextR TickCut.params d i k).flatten=CRTBarrel.unleave k++TickCut.NativeJ7.nextUnwind k d := by
  have e:=prev_of i k hk
  subst e
  simp only [nextR,TickCut.params,TickCut.baseParams,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    TickCut.NativeJ7.nextUnwind,TickCut.NativeJ7.unwind,TickCut.Tail.unbodySelected,TickCut.Tail.selected,NativeJ7.fromArchive,NativeJ7.reverse,List.append_assoc]

theorem first_eq (d:Bool) :
    (TickCut.params.portal (start WindowParams.first) :: firstF TickCut.params d WindowParams.first).flatten=
      (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d)++CRTBarrel.leave WindowParams.first := by
  simp only [firstF,TickCut.params,TickCut.baseParams,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
    NativeFirstJ7.enteredWindow,NativeFirstJ7.window,Shadow7.body,NativeFirstJ7.program,List.append_assoc]

theorem firstR_eq (d:Bool) :
    (firstR TickCut.params d WindowParams.first++[TickCut.params.portalInv (start WindowParams.first)]).flatten=
      CRTBarrel.unleave WindowParams.first++(TickCut.NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) := by
  simp only [firstR,TickCut.params,TickCut.baseParams,CRTBarrel.params,Shadow7.params,ofParts,List.cons_append,List.nil_append,List.flatten_cons,List.flatten_nil,
    List.append_nil,TickCut.NativeFirstJ7.enteredUnwind,TickCut.NativeFirstJ7.unwind,TickCut.Tail.unbodySelected,TickCut.Tail.selected,NativeFirstJ7.reverse,List.append_assoc]


/-- The move leave runs like the reference leave after block `k`'s head, from any hand-off state. -/
theorem sameAt (L2 : ScratchSpec) (k : Fin 26) (h2 : 1≤k.val) (h19 : k.val≤24) (d:Bool) (x p:Nat) (good:Bounds x p)
    (raw s:State) (g sg pg ps:Bool) (m:List Bool) (pre:AtJ k d x p raw s g sg pg ps) (n:List Bool) :
    run (CRTBarrel.leave k) n (run (NativeJ7.nextWindow k d) m s)=run (Shadow7.leaveP k) n (run (NativeJ7.nextWindow k d) m s) := by
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L2 k (by omega) (by omega) d x p good raw s g sg pg ps m pre
  have native:=TickCut.NativeJ7.from_domain_matched k (by omega) (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  exact (LeaveJ7.Admission.Inputs.crt_pair (by omega) (by omega) native.1).1 n

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- The saved key cells of block `i` are its archive's first 16 code ports. -/
theorem bank_cells (i : Fin 26) (q : Wire) (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    q ∈ cellsRestoreP (start i + 15) := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp h
  have hl : (cellsRestoreP (start i + 15)).length = 16 := by simp [cellsRestoreP]
  have hj : j.val < (cellsRestoreP (start i + 15)).length := by rw [hl]; exact j.isLt
  simp only [ArchiveJ7.codePorts, ArchiveJ7.code_split, List.append_assoc]
  rw [List.getD_append _ _ _ _ hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem _

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

theorem scratch : ScratchSpec := by
  intro j h2 h19 d x p good raw s g sg pg ps m pre
  have numbers := LeaveJ7.Admission.actualNumbers j (by omega) (by omega) x p good
  have hist := WideReference.pulled_history j rfl pre.domain
  let T:=Shadow.reduced (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)
  let Z:=encode g sg T.u T.v
  have to':T.v%2=1:=shadow_odd_shadow7 (Shadow7.sbP (start j)) (unsigned (start j) x p) numbers.farSmall numbers.odd
  have parity:(Z.a+Z.b)%2=1:=encode_odd_sum g sg _ _ (by omega)
  have ready:=EnterJ7.ready_pending_at j raw s (unsigned (start j) x p) g sg m numbers.farSmall pre.cut
    (readInput (start j) x p raw g sg pre.input) hist
  exact NativeJ7.scratch_raw_clean j h2 (by omega) d raw s m x p good pre.domain _ _ _ Z parity ready.2.1 pre.cut

theorem roundtrip : RoundtripSpec := by
  intro j h2 h19 v z G S h m n
  exact (LeaveJ7.Admission.Inputs.crt_pair (by omega) (by omega) h).2 m n

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

abbrev EndpointUpTo (J : Nat) : Prop :=
  ∀ (j k : Fin 26), k.val=j.val+1 → WindowParams.first.val+1≤j.val → j.val≤J → ∀ (d:Bool) (x p:Nat) (good:Bounds x p) (raw s:State)
    (m n:List Bool) (domain:Domain (start j) x p raw) (G S:Bool)
    (cut:PackedCut (EnterJ7.lowerPairs j) (EnterJ7.upperPairs j) (EnterJ7.gate j) (EnterJ7.flagN j) (EnterJ7.flagF j)
      (EnterJ7.flagU j) (PortalValues.negative S (unsigned (start j) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p)))
      (decide (Shadow.far (Shadow7.sbP (start j)) 15 (unsigned (start j) x p) ∧ 2^(Shadow7.sbP (start j))≤(unsigned (start j) x p).u))
      (pullState (EnterJ7.pull j) raw) (eraseSites (EnterJ7.pending j) s))
    (input:SkywalkIntegerInput (EnterJ7.lay j) (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).a
      (encode G S (unsigned (start j) x p).u (unsigned (start j) x p).v).b G raw.basis)
    (scratch:ScratchAt j d m s) (pg ps cross:Bool)
    (prior:PastFacts (NativeJ7.prev j) (ArchiveJ7.rawPorts (NativeJ7.prev j)) (Shadow7.sbP (start (NativeJ7.prev j)))
      (unsigned (start (NativeJ7.prev j)) x p) pg ps cross s),
    PackedCut (EnterJ7.lowerPairs k) (EnterJ7.upperPairs k) (EnterJ7.gate k) (EnterJ7.flagN k) (EnterJ7.flagF k)
      (EnterJ7.flagU k)
      (PortalValues.negative (LeaveJ7.Admission.flags (unsigned (start j) x p) G S).2 (unsigned (start k) x p).u)
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p)))
      (decide (Shadow.far (Shadow7.sbP (start k)) 15 (unsigned (start k) x p) ∧ 2^(Shadow7.sbP (start k))≤(unsigned (start k) x p).u))
      (pullState (EnterJ7.pull k) (endRaw (start j) raw (run (NativeJ7.nextWindow j d) m s)))
      (eraseSites (EnterJ7.pending k) (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))) ∧
    PastFacts j (ArchiveJ7.rawPorts j) (Shadow7.sbP (start j)) (unsigned (start j) x p) G S
      (HighBankSum.crossBit (LeaveJ7.TrueMiddle.d j (unsigned (start j) x p)))
      (run (Shadow7.leaveP j) n (run (NativeJ7.nextWindow j d) m s))

abbrev KeepLeaveUpTo (J : Nat) : Prop :=
  ∀ (k : Fin 26), 1≤k.val → k.val≤J → ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts (NativeJ7.prev k)),
    ∀ (v:State) (n:List Bool), (run (CRTBarrel.leave k) n v).basis q=v.basis q

abbrev KeepOlderUpTo (J : Nat) : Prop :=
  ∀ (i k i' : Fin 26), k.val=i.val+1 → 0≤ i'.val → i'.val+2≤k.val → k.val≤J → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i'), ∀ (s:State) (m:List Bool),
    (run (nextF TickCut.params d i k).flatten m s).basis q=s.basis q

/-- The leaves of a window whose last block is `J`. -/
structure LeavesUpTo (J : Nat) : Prop where
  endpoint : EndpointUpTo J
  scratch : ScratchSpec
  roundtrip : RoundtripSpec
  keepLeave : KeepLeaveUpTo J
  keepOlder : KeepOlderUpTo J
  first : FirstSpec
  firstBack : FirstBackSpec

/-- The last block's frame at the exit (exit ports `ports`). -/
def LastAt (ports : Ports) (J : Fin 26) (d:Bool) (x p:Nat) (s:State) : Prop :=
  ∃row<63145,Chronology (start J) x p row ∧ Frame ports (code d) row s

/-- The exit of a window whose last block is `J`: its step (from the hand-off at `start J+15` to the last frame) and
the keys it keeps. -/
structure ExitLeaves (J : Fin 26) (ports : Ports) : Prop where
  step : ∀ (d:Bool) (x:Nat), Bounds x p → Checked (exitF TickCut.params d (start J+15)).flatten
    (exitR TickCut.params d (start J+15)).flatten (ReadyW d x p (start J+15)) (LastAt ports J d x p)
  keep : ∀ (i : Fin 26), WindowParams.first.val ≤ i.val → i.val < J.val → ∀ (d:Bool), ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i),
    ∀ (s:State) (m:List Bool), (run (exitF TickCut.params d (start J+15)).flatten m s).basis q=s.basis q

theorem interiorG (J : Nat) (hJ : J ≤ 24) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 26) (hk : k.val=i.val+1)
    (h4 : WindowParams.first.val+1≤k.val) (h12 : k.val≤J) :
    Checked (nextF TickCut.params d i k).flatten (nextR TickCut.params d i k).flatten
      (ReadyW d x p (start k)) (ReadyW d x p (start k+15)) := by
  rw [next_eq d i k hk,nextR_eq d i k hk]
  apply pair (F:=NativeJ7.nextWindow k d) (F':=CRTBarrel.leave k) (R:=TickCut.NativeJ7.nextUnwind k d) (R':=CRTBarrel.unleave k)
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  let k0:=k
  let v:=run (NativeJ7.nextWindow k0 d) m s
  let n:=m.drop (measurementCount (NativeJ7.nextWindow k0 d))
  let out:=run (Shadow7.leaveP k0) n v
  let raw':=endRaw (start k0) raw v
  let k1:Fin 26:=⟨k0.val+1,by omega⟩
  have p1:NativeJ7.prev k1=k0:=prev_of k0 k1 rfl
  have s1:start k1=start k0+15:=start_succ k0 k1 rfl
  let flags:=LeaveJ7.Admission.flags (unsigned (start k0) x p) g sg
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have h2 : 1≤k0.val := by omega
  have h19 : k0.val≤24 := by omega
  have curr:=readInput (start k0) x p raw g sg pre.input
  have scr:=L.scratch k0 h2 h19 d x p good raw s g sg pg ps m pre
  have native:=TickCut.NativeJ7.from_domain_matched k0 h2 h19 d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨cut,facts⟩:=L.endpoint k0 k1 rfl h4 h12 d x p good raw s m n pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  have hin:=native.1
  have carried:=stepInput_gen_shadow7 (start k0) (Shadow7.sbP (start k0)) x p (by simp only [StairPacket.start]; omega)
    (by simp only [StairPacket.start]; omega) good raw v g sg pre.domain pre.input hin.farSmall
  have lastPhase:out.phase=raw'.phase:=cutPhase cut
  have prevPhase:s.phase=raw.phase:=cutPhase pre.cut
  have ph:=lastPhase.trans ((endRaw_phase (start k0) x p (by simp only [StairPacket.start]; omega) good raw v
    pre.domain).trans prevPhase.symm)
  have canon:=unique_input pre.input (fixed_input _ _ _ (by simp only [StairPacket.start]; omega) good raw pre.domain)
  have same:run (CRTBarrel.leave k0) n v=run (Shadow7.leaveP k0) n v:=(LeaveJ7.Admission.Inputs.crt_pair (by omega) (by omega) hin).1 n
  show (run (CRTBarrel.leave k0) n v).phase=s.phase ∧ ReadyW d x p (start k+15) (run (CRTBarrel.leave k0) n v) ∧
    (∀t,run (CRTBarrel.unleave k0) t (run (CRTBarrel.leave k0) n v)=v) ∧ (∀t,run (TickCut.NativeJ7.nextUnwind k d) t v=s)
  rw [same]
  refine ⟨ph,⟨k1,s1,raw',flags.1,flags.2,g,sg,?_⟩,fun t=>by rw [← same]; exact L.roundtrip k0 (by omega) h19 v _ g sg hin n t,
    native.2.2.2⟩
  refine ⟨?_,?_,cut,?_,?_⟩
  · rw [s1]; exact carried.1
  · rw [s1]; exact carried.2
  · rw [p1]; exact facts
  · rw [p1]; exact canon

theorem firstStepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) :
    Checked (TickCut.params.portal (start WindowParams.first) :: firstF TickCut.params d WindowParams.first).flatten
      (firstR TickCut.params d WindowParams.first++[TickCut.params.portalInv (start WindowParams.first)]).flatten
      (BeforeW d x p) (ReadyW d x p (start WindowParams.first+15)) := by
  rw [first_eq d,firstR_eq d]
  apply pair (F:=Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) (F':=CRTBarrel.leave WindowParams.first)
    (R:=TickCut.NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) (R':=CRTBarrel.unleave WindowParams.first)
  intro s m h
  obtain ⟨raw,stage,rfl⟩:=h
  let v:=run (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d) m (pullState (OB5.sig (start WindowParams.first-1)) raw)
  let n:=m.drop (measurementCount (Shadow7.portalP (start WindowParams.first)++NativeFirstJ7.enteredWindow WindowParams.first d))
  let out:=run (Shadow7.leaveP WindowParams.first) n v
  let raw':=endRaw (start WindowParams.first) raw v
  obtain ⟨g,sg,input,hin,cut,facts⟩:=L.first d x p good raw m n stage
  let flags:=LeaveJ7.Admission.flags (unsigned (start WindowParams.first) x p) g sg
  have dom:=initial (start WindowParams.first) x p (by decide) d raw stage
  have carried:=stepInput_gen_shadow7 (start WindowParams.first) (Shadow7.sbP (start WindowParams.first)) x p (by decide) (by decide) good raw v g sg dom input hin.farSmall
  have base:out.phase=raw'.phase:=cutPhase cut
  have ph:=base.trans (endRaw_phase (start WindowParams.first) x p (by decide) good raw v dom)
  have back:=L.firstBack d x p good raw m stage
  have same:run (CRTBarrel.leave WindowParams.first) n v=run (Shadow7.leaveP WindowParams.first) n v:=
    (LeaveJ7.Admission.Inputs.crt_pair (by decide) (by decide) hin).1 n
  show (run (CRTBarrel.leave WindowParams.first) n v).phase=(pullState (OB5.sig (start WindowParams.first-1)) raw).phase ∧
    ReadyW d x p (start WindowParams.first+15) (run (CRTBarrel.leave WindowParams.first) n v) ∧
    (∀t,run (CRTBarrel.unleave WindowParams.first) t (run (CRTBarrel.leave WindowParams.first) n v)=v) ∧
    (∀t,run (TickCut.NativeFirstJ7.enteredUnwind WindowParams.first d++Shadow7.portalInvP (start WindowParams.first)) t v=pullState (OB5.sig (start WindowParams.first-1)) raw)
  rw [same]
  exact ⟨ph,⟨firstNext,rfl,raw',flags.1,flags.2,g,sg,carried.1,carried.2,cut,facts,
    unique_input input (fixed_input (start WindowParams.first) x p (by decide) good raw dom)⟩,
    fun t=>by rw [← same]; exact L.roundtrip WindowParams.first (by decide) (by decide) v _ g sg hin n t,back.2⟩

theorem receiptG (J : Nat) (hJ : J ≤ 24) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (good:Bounds x p) (i k : Fin 26) (hk : k.val=i.val+1)
    (h2 : 1≤k.val) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → KeyW d x p i (run (nextF TickCut.params d i k).flatten m s) := by
  intro s m h
  obtain ⟨k1',e0,raw,g,sg,pg,ps,pre⟩:=h
  have same0:k1'=k:=Fin.ext (by have := e0; simp only [StairPacket.start] at this; omega)
  rw [same0] at pre
  have pk:=prev_of i k hk
  rw [next_eq d i k hk,←pk]
  simp only [run_append,run_take]
  have curr:=readInput (start k) x p raw g sg pre.input
  have scr:=L.scratch k h2 (by omega) d x p good raw s g sg pg ps m pre
  have native:=TickCut.NativeJ7.from_domain_matched k h2 (by omega) d x p good raw s m pre.domain g sg pre.cut curr scr pg ps _ pre.facts
  obtain ⟨row,bound,truth,kept⟩:=native.2.2.1
  have chr:Chronology (start (NativeJ7.prev k)) x p row:=by unfold Chronology;rw [←pre.pastCanonical];exact truth
  exact ⟨row,bound,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepLeave k h2 h12 q hq _ _)⟩

theorem keepG (J : Nat) (L : LeavesUpTo J) (d:Bool) (x p:Nat) (i k : Fin 26) (hk : k.val=i.val+1) (h12 : k.val≤J) :
    ∀ s m, ReadyW d x p (start k) s → ∀ i' : Fin 26, WindowParams.first.val ≤ i'.val → i'.val< i.val → KeyW d x p i' s →
      KeyW d x p i' (run (nextF TickCut.params d i k).flatten m s) := by
  intro s m _ i' h1 h2 key
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  obtain ⟨r,lim,chr,kept⟩:=key
  exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>L.keepOlder i k i' hk (by omega) (by omega) h12 d q hq s m)⟩

/-- The window's stock chain, generic in its last block `J` and its interior list `rest`. -/
theorem checkedG (J : Fin 26) (h4 : WindowParams.first.val+1 ≤ J.val) (hJ : J.val ≤ 24) (ports : Ports) (rest : List (Fin 26))
    (consec : Consec WindowParams.first rest) (mem : ∀ k ∈ rest, WindowParams.first.val+1 ≤ k.val ∧ k.val ≤ J.val)
    (exitT : exitTick WindowParams.first rest = start J+15)
    (L : LeavesUpTo J.val) (X : ExitLeaves J ports) (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (forwardW TickCut.params d WindowParams.first rest)
      (reverseW TickCut.params d WindowParams.first rest)
      (BeforeW d x p) (FinalW WindowParams.first J ports d x p) := by
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have bl:blockOf (exitTick WindowParams.first rest)=J.val+1:=by rw [exitT]; exact blockOf_next J
  have h:=window_strong TickCut.params d (ReadyW d x p) (KeyW d x p) (BeforeW d x p) (LastAt ports J d x p)
    WindowParams.first rest consec (firstStepG J.val L d x p good)
    (fun i k hm hk=>interiorG J.val (by omega) L d x p good i k hk (mem k hm).1 (mem k hm).2)
    (fun i k hm hk=>receiptG J.val (by omega) L d x p good i k hk (by have := mem k hm; omega) (by have := mem k hm; omega))
    (fun i k hm hk s m r i' h1 h2=>keepG J.val L d x p i k hk (by have := mem k hm; omega) s m r i' (by omega) h2)
    (by rw [exitT]; exact X.step d x good)
    (by
      intro s m _ i h1 h2 key
      rw [bl] at h2
      revert key
      rw [exitT]
      intro key
      obtain ⟨r,lim,chr,kept⟩:=key
      exact ⟨r,lim,chr,ArchiveWindowPreserve.keep kept (fun q hq=>X.keep i (by omega) (by omega) d q hq s m)⟩)
  refine checked_mono h ?_
  intro s ⟨last,saved⟩
  refine ⟨?_, last⟩
  intro k h1 h2
  obtain ⟨r, lim, chr, kept⟩ := saved k h1 (by rw [bl]; omega)
  exact ⟨r, lim, chr, ArchiveJ7.kept_stock k d r s kept⟩

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
attribute [local irreducible] run

/-- One B-side code cell `OB5.sig t (t+1034+c)`, `c ≤ 8`: unmoved below 1301, else in the fold. -/
theorem bcell (t c : Nat) (ht : t ≤ 420) (hc : c ≤ 8) :
    (OB5.sig t (t+1034+c) = t+1034+c ∧ t+1034+c ≤ 1300) ∨
    (OB5.sig t (t+1034+c) = 3113-(t+1034+c) ∧ 1301 ≤ t+1034+c) := by
  by_cases h : 1301 ≤ t+1034+c
  · exact Or.inr ⟨NativeJ7.sig_moved _ _ (Or.inl ⟨h, by omega⟩), h⟩
  · exact Or.inl ⟨NativeJ7.sig_kept _ _ (by omega) (by omega), by omega⟩

/-- The 16 restore cells of tick `t ≤ 405`, sig-aware. -/
theorem cells_rangeG (t : Nat) (ht : t ≤ 420) (q : Nat) (h : q ∈ cellsRestoreP t) :
    (t+6 ≤ q ∧ q ≤ t+15) ∨ (t+1034 ≤ q ∧ q ≤ t+1042 ∧ q ≤ 1300) ∨ (2071 ≤ q+t ∧ q+t ≤ 2079 ∧ q ≤ 1812) := by
  have b0 := bcell t 0 ht (by omega)
  have b1 := bcell t 1 ht (by omega)
  have b3 := bcell t 3 ht (by omega)
  have b5 := bcell t 5 ht (by omega)
  have b6 := bcell t 6 ht (by omega)
  have b8 := bcell t 8 ht (by omega)
  simp only [Nat.add_zero] at b0
  simp only [cellsRestoreP, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  first
  | omega
  | (rcases b0 with ⟨e, l⟩ | ⟨e, l⟩ <;> rw [e] <;> omega)
  | (rcases b1 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1035 = t+1034+1 by omega]; rw [e]) <;> omega)
  | (rcases b3 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1037 = t+1034+3 by omega]; rw [e]) <;> omega)
  | (rcases b5 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1039 = t+1034+5 by omega]; rw [e]) <;> omega)
  | (rcases b6 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1040 = t+1034+6 by omega]; rw [e]) <;> omega)
  | (rcases b8 with ⟨e, l⟩ | ⟨e, l⟩ <;> (rw [show t+1042 = t+1034+8 by omega]; rw [e]) <;> omega)

theorem key_rangeG (i : Fin 26) (hi : i.val ≤ 24) (q : Nat)
    (h : q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i)) :
    (start i+21 ≤ q ∧ q ≤ start i+30) ∨ (start i+1049 ≤ q ∧ q ≤ start i+1057 ∧ q ≤ 1300) ∨
    (2056 ≤ q+start i ∧ q+start i ≤ 2064 ∧ q ≤ 1812) := by
  have c := cells_rangeG (start i + 15) (by simp only [StairPacket.start]; omega) q (bank_cells i q h)
  omega

theorem keepLeaveG : KeepLeaveUpTo 24 := by
  intro k h2 h18 q hq v n
  have c := key_rangeG (NativeJ7.prev k) (by simp only [NativeJ7.prev]; omega) q hq
  have pk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
  obtain ⟨w1, w2⟩ := start_win7 k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  exact CRTWindow.leave_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega) n v

theorem keepOlderG : KeepOlderUpTo 24 := by
  intro i k i' hk h2 hik h18 d q hq s m
  have hs : start i' + 30 ≤ start k := by simp only [StairPacket.start]; omega
  have c := key_rangeG i' (by omega) q hq
  obtain ⟨w1, w2⟩ := start_win7 k (by omega) (by omega)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, ew, ew', ee, ee', et, et', ea, eb, el, r20, r21⟩ := Shadow7.rail_win w1 w2
  have sk : start k ≤ 405 := by simp only [StairPacket.start]; omega
  have pk : NativeJ7.prev k = i := Fin.ext (by simp only [NativeJ7.prev]; omega)
  rw [next_eq d i k hk]
  simp only [run_append, run_take]
  rw [CRTWindow.leave_keeps k (by omega) (by omega) q (by unfold Shadow7.leaveBox2; simp only [Wire] at *; omega)]
  simp only [NativeJ7.nextWindow, NativeJ7.window, run_append, run_take]
  have native : ¬Shadow7.MayTouch k (windowNet k q) := by
    have mid : (Shadow7.shape k).mid = Shadow7.sbP (start k)+16 := rfl
    rcases c with c | c | c
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have fixed : windowNet k q = q := by
        show OB5.sig (start k + 14) q = q
        exact NativeJ7.sig_kept _ _ (by omega) (by omega)
      rw [fixed]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
    · have moved : windowNet k q = 3113 - q := by
        show OB5.sig (start k + 14) q = _
        exact NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, by omega⟩)
      rw [moved]; unfold Shadow7.MayTouch; rw [mid]; simp only [Wire] at *; omega
  have port : q ∉ EnterJ7.ports k := by
    simp only [EnterJ7.ports, List.mem_cons, List.not_mem_nil, or_false]
    simp only [Wire] at *
    omega
  have admin : q ∉ NativeJ7.support k ++ ArchiveJ7.rawPortsList (NativeJ7.prev k) := by
    rw [List.mem_append, ArchiveJ7.raw_split]
    intro mem
    rcases mem with mem | mem
    · simp only [NativeJ7.support, List.mem_flatMap, List.mem_range'_1, List.mem_cons, List.not_mem_nil,
        or_false] at mem
      obtain ⟨v, ⟨v1, v2⟩, e | e⟩ := mem
      · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base, Wire] at *; omega)
          (by simp only [MappedCompressed.base, Wire] at *; omega)] at e
        simp only [MappedCompressed.base, Wire] at *; omega
      · by_cases mv : 1301 ≤ 1044 + v
        · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨by simp only [MappedCompressed.base]; omega,
            by simp only [MappedCompressed.base]; omega⟩)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
        · rw [NativeJ7.sig_kept _ _ (by simp only [MappedCompressed.base]; omega)
            (by simp only [MappedCompressed.base]; omega)] at e
          simp only [MappedCompressed.base, Wire] at *; omega
    · rw [List.mem_append] at mem
      have tk : start (NativeJ7.prev k) + 15 = start k := by simp only [NativeJ7.prev, StairPacket.start]; omega
      rcases mem with mem | mem
      · simp only [ArchiveJ7.rawHead, cellsLoadP, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
          List.not_mem_nil, or_false, tk] at mem
        rcases mem with ⟨c', hc, e | e⟩ | e
        · simp only [Wire] at *; omega
        · by_cases mv : 1301 ≤ start k + 1034 + c'
          · rw [NativeJ7.sig_moved _ _ (Or.inl ⟨mv, by omega⟩)] at e
            simp only [Wire] at *; omega
          · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)] at e
            simp only [Wire] at *; omega
        · simp only [Shadow7.e0P, Wire] at *; omega
      · obtain ⟨kk, hkk, e⟩ := List.mem_map.mp mem
        have hk' := List.mem_range.mp hkk
        rw [tk] at e
        have qv : (q:Nat) = Shadow7.scratchS (start k) kk := e.symm
        rcases Shadow7.scratchS_cases (start k) kk (by omega) hk' with ⟨-, lo, hi⟩ | ⟨-, lo, hi⟩ <;>
          (simp only [Wire] at *; omega)
  exact Shadow7.ext_head (Shadow7.enterP k) k (NativeJ7.withArchive k d) _ s m _ q native (EnterJ7.notWire k port) admin
    (NativeJ7.admin_cover k (by omega) (by omega) d)
theorem endpoint22 : EndpointUpTo 24 := by
  intro j k hk h4 h18 d x p good raw s m n domain G S cut input scratch pg ps cross prior
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have hne : start j ≠ WideReference.firstBlock := by
    simp only [WideReference.firstBlock, StairPacket.start]; omega
  exact NativeJ7.stock_endpointG j k hk (by omega) h18 hne d x p good raw s m n domain G S cut input scratch pg ps cross
    prior (NativeJ7.band_clean_gen j (by omega) h18 d x p good raw s m domain _ _ _ cut)


/-- Every interior leaf of the window up to block 20 (start 375). -/
theorem leaves22 : LeavesUpTo 24 :=
  ⟨endpoint22, scratch, roundtrip, keepLeaveG, keepOlderG, NativeFirstJ7.first, TickCut.NativeFirstJ7.firstBack⟩

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false


end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.TickCut.Stock
open ECDSAAdd.Entrant.StairPacket.StockWindowW7
open Arithmetic MappedCompressed IntegerPacket WideReference SkywalkRails Partial ArchivePortAction ArchiveStockRows
open StockWindowTicket WindowFold WindowChain Secp256k1
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] run

/-- The generic hand-off at block 21 is the exit-405 hand-off (pairs, flags, pending, raw ports of block 20). -/
theorem exitBridge420 :
    EnterJ7.lowerPairs ⟨25,by decide⟩=Portal420Flag7.loPairs ∧ EnterJ7.upperPairs ⟨25,by decide⟩=Portal420Flag7.hiPairs ∧
    EnterJ7.gate ⟨25,by decide⟩=435 ∧ EnterJ7.flagN ⟨25,by decide⟩=1618 ∧ EnterJ7.flagF ⟨25,by decide⟩=1616 ∧
    EnterJ7.flagU ⟨25,by decide⟩=1617 ∧ EnterJ7.pending ⟨25,by decide⟩=ParkEndpoint4207.src ∧
    ArchiveJ7.rawPorts ⟨24,by decide⟩ 20=1619 ∧ ArchiveJ7.rawPorts ⟨24,by decide⟩ 21=1620 ∧
    ArchiveJ7.rawPorts ⟨24,by decide⟩ 22=1621 := by
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,?_,?_,?_,?_⟩ <;> (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

theorem exitProg420 (d:Bool) : (exitF TickCut.params d 420).flatten=NativePack4207.lastWindow d ∧
    (exitR TickCut.params d 420).flatten=NativePack4207.lastUnwind d := by
  constructor
  · simp only [exitF,TickCut.params,TickCut.baseParams,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack4207.lastWindow,NativePack4207.endSlice,EndTick4207.physP,EndTick4207.P,NativePack4207.program,List.append_assoc]
  · simp only [exitR,TickCut.params,TickCut.baseParams,CRTBarrel.params,Shadow7.params,ofParts,List.flatten_cons,List.flatten_nil,List.append_nil,
      NativePack4207.lastUnwind,NativePack4207.endUndo,EndTick4207.physQ,EndTick4207.Q,NativePack4207.reverse,List.append_assoc]

/-- The exit at 420 (dadon's `step270` rendered at 420). -/
theorem exitStep420 (d:Bool) (x:Nat) (good:Bounds x p) :
    Checked (exitF TickCut.params d (start ⟨24,by decide⟩+15)).flatten
      (exitR TickCut.params d (start ⟨24,by decide⟩+15)).flatten
      (ReadyW d x p (start ⟨24,by decide⟩+15)) (LastAt ArchiveBoundary4207.codePorts ⟨24,by decide⟩ d x p) := by
  have e420 : start ⟨24,by decide⟩+15=420 := rfl
  rw [e420]
  obtain ⟨ef,er⟩:=exitProg420 d
  rw [ef,er]
  intro s m h
  obtain ⟨k,ek,raw,g,sg,pg,ps,pre⟩:=h
  have k20:k=⟨25,by decide⟩:=Fin.ext (by have := ek; simp only [StairPacket.start] at this; show k.val=25; omega)
  subst k20
  obtain ⟨bl,bu,bg,bn,bf,bu',bp,r20,r21,r22⟩:=exitBridge420
  let z:=unsigned 420 x p
  have short:Shadow7.SmallIfFar 39 15 z:=(Shadow7.Envelope.inputs x p 420 (lt_trans good.small good.cap) good.cap (by decide)).1
  have old:=LeaveJ7.Admission.actualNumbers ⟨24,by decide⟩ (by decide) (by decide) x p good
  have eq:farAt 39 420 x p=(2*2^55≤z.u+z.v):=by
    apply propext;unfold farAt Shadow.far Shadow.high Shadow.limb;exact Nat.le_div_iff_mul_le (by positivity)
  have cut:=pre.cut
  have e20:start (⟨25,by decide⟩:Fin 26)=420:=rfl
  have sb:Shadow7.sbP 420=39:=by decide
  rw [bl,bu,bg,bn,bf,bu',bp] at cut
  simp only [e20,sb] at cut
  have facts:=pre.facts
  have mode:s.basis 1619=decide (Shadow.far 46 15 (unsigned 405 x p)):=by rw [←r20]; exact facts.far
  have side:s.basis 1620=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      StairArchiveTrace.afterFlags (decide ((unsigned 405 x p).v<(unsigned 405 x p).u))
        ((Shadow7.physicalCells ArchiveBoundary4207.sourceIdx s).take 5)):=by rw [←r21]; simpa only [Shadow7.physicalCells_eq] using facts.suffix
  have cross:s.basis 1621=(decide (Shadow.far 46 15 (unsigned 405 x p)) &&
      HighBankSum.crossBit (LeaveJ7.TrueMiddle.d ⟨24,by decide⟩ (unsigned 405 x p))):=by rw [←r22]; exact facts.crossed
  have last:=NativePack4207.matched_from_domain d x good.nonzero good.small raw s m pre.domain z short g sg
    (readInput 420 x p raw g sg pre.input) (by simpa only [eq] using cut) (unsigned 405 x p) pg ps _
    old.odd old.farSmall (by simpa only [Shadow7.physicalCells_eq] using facts.records) mode side cross
  obtain ⟨r,lim,truth,frame⟩:=last.2.1
  have pc:signedAt 405 x p pg ps=WideReference.canonical 405 x p:=pre.pastCanonical
  have chr:Chronology 405 x p r:=by unfold Chronology;rw [←pc];exact truth
  exact ⟨last.1,⟨r,lim,chr,frame⟩,last.2.2⟩


/-- A wire bound for a whole program from a per-instruction check. -/
theorem wires_bound405 (P : Program) (b : Nat) (h : P.all (fun i => decide (∀ q ∈ i.wires, q < b)) = true) :
    ∀ q ∈ wires P, q < b := by
  induction P with
  | nil => intro q hq; simp [wires] at hq
  | cons i p ih =>
    intro q hq
    simp only [wires, Finset.mem_union] at hq
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases hq with hq | hq
    · exact of_decide_eq_true h.1 q hq
    · exact ih h.2 q hq

theorem portalInv_low420 : ∀ q ∈ wires (Shadow7.portalInvP 420), q < 1640 :=
  wires_bound405 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem park_low420 : ∀ q ∈ wires (Shadow7.parkP 420), q < 1640 :=
  wires_bound405 _ _ (by (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel))
theorem raw420_ranges : ∀ w ∈ ArchiveBoundary4207.rawPortsList,
    (426 ≤ w ∧ w ≤ 435) ∨ (1650 ≤ w ∧ w ≤ 1659) ∨ (879 ≤ w ∧ w ≤ 881) ∨ (1556 ≤ w ∧ w ≤ 1647) ∨
    (882 ≤ w ∧ w ≤ 923) := by
  (open ECDSAAdd.Entrant.WSlimV3 in decide +kernel)

/-- The exit pieces at 420 never touch the window's key cells (blocks first..19; first = block 1, tick 90). -/
theorem keepExit420 : ∀ (i : Fin 26), WindowParams.first.val ≤ i.val → i.val < 24 → ∀ (d:Bool),
    ∀ q ∈ ArchiveWindowPreserve.bank (ArchiveJ7.codePorts i), ∀ (s:State) (m:List Bool),
    (run (exitF TickCut.params d (start ⟨24,by decide⟩+15)).flatten m s).basis q=s.basis q := by
  intro i h3 h17 d q hq s m
  have hf1 : 0 ≤ WindowParams.first.val := by decide
  have c := key_rangeG i (by omega) q hq
  have si : 45 ≤ start i ∧ start i ≤ 390 := by simp only [StairPacket.start]; omega
  have e420 : start ⟨24,by decide⟩+15=420 := rfl
  rw [e420]
  simp only [exitF, TickCut.params,TickCut.baseParams,CRTBarrel.params,Shadow7.params, ofParts, List.flatten_cons, List.flatten_nil, List.append_nil, run_append, run_take]
  -- exit archive load
  rw [run_preserves_outside (Shadow7.exitLoadP 420 d) _ _ q (fun hit => by
    have r := raw420_ranges q (List.mem_toFinset.mp (ArchiveBoundary4207.load_cover d hit))
    simp only [Wire] at *; omega)]
  -- stock pack at 410
  rw [run_preserves_outside _ _ _ q (fun hit => by
    rw [renameProgram_support] at hit
    obtain ⟨w, hw, e⟩ := Finset.mem_image.mp hit
    have pc := (WindowCovered.pack_cells d 410 (by decide) (by decide)).1 w hw
    obtain ⟨r, r1, r2, er | er⟩ := pc <;> rw [er, OB5.sig_nat] at e <;> unfold OB5.sigNat at e <;>
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩ <;> split_ifs at e <;>
      simp only [MappedCompressed.base, Wire] at * <;> omega)]
  -- the stock tick at 420
  have nt : q ∉ wires (renameProgram (OB5.sig 420) (TickRanges.tick base 420)) :=
    EndTick4207.physical_free EndTick4207.P EndTick4207.supports.1 q (by
      apply WideReference.away (by decide)
      rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 16 ≤ n → n = n - 16 + 16 := fun n h => by omega
        exact ⟨q - 16, by omega, Or.inl (hn q (by omega))⟩
      · rw [NativeJ7.sig_kept _ _ (by omega) (by omega)]
        have hn : ∀ n : Nat, 1044 ≤ n → n = 1028 + (n - 1044) + 16 := fun n h => by omega
        exact ⟨q - 1044, by omega, Or.inr (hn q (by omega))⟩
      · rw [NativeJ7.sig_moved _ _ (Or.inr ⟨by omega, hh⟩)]
        have hn : ∀ n : Nat, n ≤ 1812 → 1301 ≤ 3113 - n → 3113 - n = 1028 + (2069 - n) + 16 := fun n h h' => by omega
        exact ⟨2069 - q, by omega, Or.inr (hn q hh (by omega))⟩)
  rw [run_preserves_outside _ _ _ q nt]
  -- exit portal (inverse) and park
  rw [run_preserves_outside (Shadow7.portalInvP 420) _ _ q (fun hit => by
    have f := portalInv_low420 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.portal_wires 420 (by decide) (by decide)).2 q hit
      have hr : railP 420 = 93 := by decide
      unfold footP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]
  rw [run_preserves_outside (Shadow7.parkP 420) _ _ q (fun hit => by
    have f := park_low420 q hit
    rcases c with ⟨lo, hi⟩ | ⟨lo, hi, hh⟩ | ⟨lo, hi, hh⟩
    all_goals
      have f2 := (Shadow7.park_wires 420 (by decide) (by decide)).1 q hit
      have hr : railP 420 = 93 := by decide
      unfold parkFootP at f2; rw [hr] at f2; simp only [Wire] at *; omega)]

/-- The exit of the window whose last block is 20 (start 405): the exit at 405. -/
theorem exitLeaves420 : ExitLeaves ⟨24,by decide⟩ ArchiveBoundary4207.codePorts :=
  ⟨exitStep420, keepExit420⟩

end ECDSAAdd.Entrant.StairPacket.TickCut.Stock
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCut.CutWindow
open ECDSAAdd Arithmetic WindowFold Baselines Challenge WindowParams
open ECDSAAdd.Entrant.StairPacket.FredCut
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Inherited d9 FredCut pieces, with only positive inverse ticks replaced. -/
def cutParams : Pieces Program := {FredCut.Pcut with unrouted := TickCut.Tail.selected}

/-- The forward program is exactly the already selected d9 program. -/
def forwardCut (d : Bool) : Program := CRTWindow.forwardCut d
def reverseCut (d : Bool) : Program := reverseW cutParams d first WindowParams7.rest7

attribute [local irreducible] TickCut.Tail.selected TickCut.Hosted.unroutedHigh in
theorem rev_cut (d : Bool) :
    Cut 26 (WindowFold.reverseL TickCut.params d WindowParams.first WindowParams7.rest7)
      (WindowFold.reverseL cutParams d WindowParams.first WindowParams7.rest7) := by
  rw [rest7_eq]
  simp only [WindowFold.reverseL, WindowFold.exitR, WindowFold.chainR, WindowFold.nextR, WindowFold.firstR,
    TickCut.params, TickCut.baseParams, cutParams,
    List.cons_append, List.nil_append, List.append_assoc]
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev_exit 24 (by decide) _ (by decide +kernel) (by decide +kernel)
    (avoid_of_check _ _ (by decide +kernel)) (sub_of_check _ _ (by decide +kernel)) (inv_swap_of_eq _ _ _ _ _ _ _ (Eblk_S2 _) (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 23 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 22 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 21 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 20 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 19 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 18 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 17 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 16 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 15 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 14 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 13 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 12 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 11 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 10 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 9 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 8 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 7 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Dblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_rev_end WindowParams.first (start WindowParams.first) (by decide +kernel)
    (inv_of_eq _ 60 1029 304 1028 303 (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ 60 1029 304 1028 303 (by decide +kernel)) (by decide +kernel)
  exact Cut.nil



theorem run_cut (d : Bool) :
    run (forwardCut d) = run (forwardW TickCut.params d first WindowParams7.rest7) := by
  have h := congrArg run (TickCut.forward_eq d)
  exact (CRTWindow.run_cut d).trans h.symm

theorem run_cut_rev (d : Bool) :
    run (reverseCut d) = run (reverseW TickCut.params d first WindowParams7.rest7) :=
  funext fun m => funext fun s => (rev_cut d).run_eq m s

theorem cut_toffoli (d : Bool) :
    toffoliCount (forwardCut d) + 104 = toffoliCount (forwardW TickCut.params d first WindowParams7.rest7) ∧
    toffoliCount (reverseCut d) + 104 = toffoliCount (reverseW TickCut.params d first WindowParams7.rest7) := by
  have h := congrArg toffoliCount (TickCut.forward_eq d)
  exact ⟨(CRTWindow.cut_toffoli d).1.trans h.symm,(rev_cut d).tc_eq⟩

theorem cut_measure (d : Bool) :
    measurementCount (forwardCut d) = measurementCount (forwardW TickCut.params d first WindowParams7.rest7) ∧
    measurementCount (reverseCut d) = measurementCount (reverseW TickCut.params d first WindowParams7.rest7) := by
  have h := congrArg measurementCount (TickCut.forward_eq d)
  exact ⟨(CRTWindow.cut_measure d).1.trans h.symm,(rev_cut d).mc_eq⟩

section
attribute [local irreducible] wires

theorem cut_covered (d : Bool) : WindowCovered.CoveredW (forwardCut d) ∧ WindowCovered.CoveredW (reverseCut d) :=
  ⟨(CRTWindow.cut_covered d).1,
   fun q h => (TickCut.window_covered d).2 q ((rev_cut d).wires_sub h)⟩
end

theorem cut_physical (d : Bool) : GatePhysical (forwardCut d) ∧ GatePhysical (reverseCut d) :=
  ⟨(CRTWindow.cut_physical d).1,
   fun i h => (TickCut.window_physical d).2 i ((rev_cut d).mem i h)⟩

theorem cut_slotsF : gateSlots (forwardCut true) ≤ 2419094 ∧ gateSlots (forwardCut false) ≤ 2419094 :=
  CRTWindow.cut_slotsF

theorem cut_slotsR : gateSlots (reverseCut true) ≤ 2403571 ∧ gateSlots (reverseCut false) ≤ 2403571 :=
  ⟨(rev_cut true).slots_le.trans TickCut.ship_slots.2.2.1,
   (rev_cut false).slots_le.trans TickCut.ship_slots.2.2.2⟩

theorem cut_toffoliF : toffoliCount (forwardCut true) = 127202 ∧ toffoliCount (forwardCut false) = 127202 :=
  CRTWindow.cut_toffoliF

theorem cut_toffoliR : toffoliCount (reverseCut true) = 127269 ∧ toffoliCount (reverseCut false) = 127294 := by
  have a := (cut_toffoli true).2
  have b := (cut_toffoli false).2
  rw [TickCut.ship_toffoliR_true] at a
  rw [TickCut.ship_toffoliR_false] at b
  exact ⟨by omega,by omega⟩

theorem cut_measureF : measurementCount (forwardCut true) = 66040 ∧ measurementCount (forwardCut false) = 66040 :=
  CRTWindow.cut_measureF

theorem cut_measureR : measurementCount (reverseCut true) = 65672 ∧ measurementCount (reverseCut false) = 65697 := by
  rw [(cut_measure true).2,(cut_measure false).2]
  exact TickCut.ship_measureR

end ECDSAAdd.Entrant.StairPacket.TickCut.CutWindow
end
