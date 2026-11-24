import ECDSAAdd.Submission.Entrant.LeaveReductions
import Batteries.Tactic.OpenPrivate

/-!
H3 on the pinned 315eece6 mixed schedule (13 short blocks and 9 wide blocks).
The forward programs and every reverse tick zero are retained. Only positive
reverse ticks use the affine receiver, under the preceding forward invariant.
This source was prepared without a Lean run; no compilation claim is made.
-/

section


namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Core
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Core

end

section


namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Core
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Core

end

section

/- Concrete H3 facade draft; compilation and caller integration remain pending. -/
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Receiver
open ECDSAAdd Arithmetic IntegerPacket TickCutMixed.Core
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Receiver

end

section


namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Hosted
open ECDSAAdd Arithmetic IntegerPacket TickCutMixed.Receiver
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Hosted

end

section

namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Static
open ECDSAAdd Arithmetic RecordedQuantum IntegerPacket TickCutMixed.Core TickCutMixed.Receiver TickCutMixed.Hosted
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Static

end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCutMixed.Receiver TickCutMixed.Hosted TickCutMixed.Static
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Tail

end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Tail
open ECDSAAdd Arithmetic IntegerPacket TickCutMixed.Receiver TickCutMixed.Hosted TickCutMixed.Static
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Tail

end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Wide
open ECDSAAdd Arithmetic IntegerPacket TickCutMixed.Receiver TickCutMixed.Core
open TickCutMixed.Hosted TickCutMixed.Static ECDSAAdd.Entrant.StairPacket.Shadow20
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

def onRailsPlus (j : Fin 9) (i : Nat) (z : SkywalkRails.State) (b : BasisState) :=
  readyPlus (shape20 j) i z (mappedBasis20 j b)

def unroutedHigh (j : Fin 9) (i n : Nat) : Program :=
  renameProgram (windowNet20 j) (backHigh (shape20 j) i n)

theorem routeFramePlus (j : Fin 9) (i n : Nat) (bound : i+n≤20)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Triple (onRailsPlus j i z) (routed20 j i n)
      (onRailsPlus j (i+n) (SkywalkTrace.next^[n] z)) := by
  intro s m ready
  have h := semanticPlus (shape20 j) i n bound z odd (pullState (windowNet20 j) s) m ready
  rw [←pull_routed20 j i n bound m s] at h
  exact h

theorem routeUndoHigh (j : Fin 9) (i n : Nat) (bound : i+n≤20)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) :
    Restores (onRailsPlus j i z) (routed20 j i n) (unroutedHigh j i n) := by
  intro s m t ready
  have forward := pull_routed20 j i n bound m s
  let actual := run (routed20 j i n) m s
  have bk : pullState (windowNet20 j) (run (unroutedHigh j i n) t actual)=
      run (backHigh (shape20 j) i n) t (pullState (windowNet20 j) actual) := by
    rw [unroutedHigh,run_rename _ (net20_injective j)]
  have hm : 1≤(shape20 j).mid := by simp [shape20]
  have fin := roundtripHigh (shape20 j) i n bound hm z odd
    (pullState (windowNet20 j) s) m t ready
  change pullState (windowNet20 j) actual=_ at forward
  rw [forward,fin] at bk
  apply congrArg₂ State.mk (congrArg State.phase bk)
  funext q
  have h := congrArg (fun x : State => x.basis (windowNet20 j q)) bk
  change (run (unroutedHigh j i n) t actual).basis (windowNet20 j (windowNet20 j q))=
    s.basis (windowNet20 j (windowNet20 j q)) at h
  have inv : windowNet20 j (windowNet20 j q)=q := by
    apply OB5.sig_invol
    have hj := j.isLt
    simp [start20]; omega
  rwa [inv] at h

theorem watch_a (j : Fin 9) (q : Wire)
    (hq : q∈(IntegerPacket.ports (shape20 j) 1).a) :
    windowNet20 j q∈watch20 j := by
  unfold watch20
  dsimp only
  apply List.mem_map.mpr
  refine ⟨q,?_,rfl⟩
  simp only [List.mem_append]
  tauto

/-- Archive administration preserves the stronger first successor invariant
because the wide watch contains its entire A rail. -/
theorem watch_congrPlus (j : Fin 9) (s t : State)
    (agree : ∀q∈watch20 j,t.basis q=s.basis q)
    (z : SkywalkRails.State) (active : onRailsPlus j 1 z s.basis) :
    onRailsPlus j 1 z t.basis := by
  have old := (watch20_congr j s t agree z active.1).1
  refine ⟨old,?_⟩
  intro positive
  have hm : 1≤(shape20 j).mid := by simp [shape20]
  have hp : highP (shape20 j) 1∈(IntegerPacket.ports (shape20 j) 1).a := by
    simp only [SkywalkIntegerLayout.a,ah_shape _ _ hm,List.mem_cons,List.mem_append]
    simp
  have hq : highQ (shape20 j) 1∈(IntegerPacket.ports (shape20 j) 1).a := by
    simp only [SkywalkIntegerLayout.a,ah_shape _ _ hm,List.mem_cons,List.mem_append]
    simp
  change t.basis (windowNet20 j (highP (shape20 j) 1))=
    t.basis (windowNet20 j (highQ (shape20 j) 1))
  rw [agree _ (watch_a j _ hp),agree _ (watch_a j _ hq)]
  exact active.2 positive

def unbodyHigh (j : Fin 9) (reverse : Program) : Program :=
  unroutedHigh j 1 19 ++ (reverse ++ unroutedHigh j 0 1)

/-- The selected new reverse body restores the untouched old forward body.
Both invariant propagation and archive administration use retained old semantics. -/
theorem body_runHigh (j : Fin 9) (admin reverse : Program) (s : State) (m : List Bool)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) (active : onRails20 j 0 z s.basis)
    (mid : let src:=run (routed20 j 0 1) m s
      AdminResult20 j reverse src (run admin (m.drop (measurementCount (routed20 j 0 1))) src)) :
    let out:=run (body20 j admin) m s
    out.phase=s.phase ∧ onRails20 j 20 (SkywalkTrace.next^[20] z) out.basis ∧
      readCells (shape20 j) 0 20 (mappedBasis20 j out.basis)=SkywalkTrace.trace 20 z ∧
      ∀n,run (unbodyHigh j reverse) n out=s := by
  let src := run (routed20 j 0 1) m s
  let t := m.drop (measurementCount (routed20 j 0 1))
  let pre := run admin t src
  let n := t.drop (measurementCount admin)
  have strong0 : onRailsPlus j 0 z s.basis := ⟨active,by intro bad; omega⟩
  have head := routeFramePlus j 0 1 (by decide) z odd s m strong0
  have valid : onRailsPlus j 1 (SkywalkTrace.next z) src.basis := head.2
  have pass := watch_congrPlus j src pre mid.unchanged _ valid
  have oldPass := watch20_congr j src pre mid.unchanged _ valid.1
  have span := split_run20 j z odd s m n active pre oldPass.1 oldPass.2
  have last := routeFramePlus j 1 19 (by decide) (SkywalkTrace.next z)
    (IntegerPacket.nextOdd z odd) pre n pass
  dsimp only [body20,unbodyHigh]
  simp only [run_append,run_take]
  refine ⟨last.1.trans (mid.phase.trans head.1),span.1,span.2,?_⟩
  intro r
  have endBack := routeUndoHigh j 1 19 (by decide) (SkywalkTrace.next z)
    (IntegerPacket.nextOdd z odd) pre n r pass
  change run (unroutedHigh j 0 1) _ (run reverse _
    (run (unroutedHigh j 1 19) r (run (routed20 j 1 19) n pre)))=s
  rw [endBack,mid.undo]
  exact routeUndoHigh j 0 1 (by decide) z odd s m _ strong0

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Wide
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeJ7
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
def unwind (j : Fin 26) (d:Bool) := TickCutMixed.Tail.unbodySelected j (fromArchive j d)
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
  apply TickCutMixed.Tail.body_runSelected _ _ _ _ _ z odd start0
  exact (admin j (by omega) h19 d _ _ (SkywalkTrace.next z) (Shadow7.route_frame j 0 1 (by decide) z odd s m start0).2 legal row limit frame clean).1

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeJ7
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeJ7
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeFirstJ7
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
def unwind (j : Fin 26) (d:Bool) := TickCutMixed.Tail.unbodySelected j (ECDSAAdd.Entrant.StairPacket.NativeFirstJ7.reverse j d)
theorem window_run (j : Fin 26) (h : 0≤j.val) (d:Bool) (s:State) (m:List Bool) (z:SkywalkRails.State)
    (odd:(z.a+z.b)%2=1) (start0:Shadow7.onRails j 0 z s.basis)
    (legal:MeasuredCodec5.legalAt (history j) (run (Shadow7.routed j 0 1) m s).basis) :
    let out:=run (window j d) m s
    out.phase=s.phase ∧ Shadow7.onRails j 15 (SkywalkTrace.next^[15] z) out.basis ∧
      readCells (Shadow7.shape j) 0 15 (mappedBasis j out.basis)=SkywalkTrace.trace 15 z ∧
      ∀n,run (unwind j d) n out=s := by
  apply TickCutMixed.Tail.body_runSelected _ _ _ _ _ z odd start0
  exact admin j h d _ _ legal

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeFirstJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeFirstJ7
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeFirstJ7
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeFirstJ7
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
    ∀k, run (TickCutMixed.NativeFirstJ7.enteredUnwind WindowParams.first d ++ Shadow7.portalInvP (start WindowParams.first)) k
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

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.NativeFirstJ7
end


section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Wide
open ECDSAAdd Arithmetic IntegerPacket TickCutMixed.Receiver TickCutMixed.Static
open ECDSAAdd.Entrant.StairPacket.Shadow20
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

theorem head_eq (j : Fin 9) : unroutedHigh j 0 1 = Shadow20.unrouted20 j 0 1 := by
  rw [(fixed_route20 j 0 1 (by decide)).2]
  simp [unroutedHigh,backHigh,receiverSelected,IntegerPacket.backR]

/-- Tick zero is deliberately the inherited receiver. -/
def unbodySelected (j : Fin 9) (reverse : Program) : Program :=
  unroutedHigh j 1 19 ++ (reverse ++ Shadow20.unrouted20 j 0 1)

theorem unbody_eq (j : Fin 9) (reverse : Program) :
    unbodySelected j reverse = unbodyHigh j reverse := by
  simp only [unbodySelected,unbodyHigh,head_eq]

theorem body_runSelected (j : Fin 9) (admin reverse : Program) (s : State) (m : List Bool)
    (z : SkywalkRails.State) (odd : (z.a+z.b)%2=1) (active : onRails20 j 0 z s.basis)
    (mid : let src := run (routed20 j 0 1) m s
      AdminResult20 j reverse src (run admin (m.drop (measurementCount (routed20 j 0 1))) src)) :
    let out := run (body20 j admin) m s
    out.phase=s.phase ∧ onRails20 j 20 (SkywalkTrace.next^[20] z) out.basis ∧
      readCells (shape20 j) 0 20 (mappedBasis20 j out.basis)=SkywalkTrace.trace 20 z ∧
      ∀ n, run (unbodySelected j reverse) n out=s := by
  simpa only [unbody_eq] using body_runHigh j admin reverse s m z odd active mid

theorem tail_counts (j : Fin 9) :
    toffoliCount (unroutedHigh j 1 19)+19=toffoliCount (Shadow20.unrouted20 j 1 19) ∧
    measurementCount (unroutedHigh j 1 19)=measurementCount (Shadow20.unrouted20 j 1 19)+19 ∧
    Challenge.gateSlots (unroutedHigh j 1 19)=Challenge.gateSlots (Shadow20.unrouted20 j 1 19)+133 := by
  have hm : 1≤(shape20 j).mid := by simp [shape20]
  have c := backHigh_counts (shape20 j) 1 19 hm (by decide)
  rw [(fixed_route20 j 1 19 (by decide)).2]
  simpa only [unroutedHigh,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    Baselines.rename_gateSlots] using c

theorem tail_physical (j : Fin 9) : GatePhysical (unroutedHigh j 1 19) := by
  have hm : 1≤(shape20 j).mid := by simp [shape20]
  exact gatePhysical_rename _ (net20_injective j) _
    (TickCutMixed.Tail.back_physical (shape20 j) 1 19 (by simp [shape20]) hm)

theorem tail_covered (j : Fin 9) : WindowCovered.CoveredW (unroutedHigh j 1 19) := by
  have hm : 1≤(shape20 j).mid := by simp [shape20]
  have all (a n : Nat) (bound : a+n≤20) :
      WindowCovered.CoveredW (renameProgram (windowNet20 j) (backHigh (shape20 j) a n)) := by
    induction n generalizing a with
    | zero => intro q hq; simp [backHigh,renameProgram,wires] at hq
    | succ n ih =>
      have ha : a<20 := by omega
      have hv := IntegerPacket.ok (shape20 j) ⟨a,ha⟩
      have hn : 0<(IntegerPacket.ports (shape20 j) a).half.length := by simp [SkywalkIntegerLayout.half]
      have sub : wires (receiverSelected (shape20 j) a) ⊆
          (IntegerPacket.ports (shape20 j) a).wires.toFinset := by
        unfold receiverSelected
        split
        · exact ECDSAAdd.Entrant.W.ReverseCarry.receiverUntick_support _ _ hv hn le_rfl
        · exact receiverHigh_support (shape20 j) a ha hm
      have point : WindowCovered.CoveredW (renameProgram (windowNet20 j)
          (receiverSelected (shape20 j) a)) := by
        intro q hq
        rw [renameProgram_support] at hq
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hq
        have mem := List.mem_toFinset.mp (sub hw)
        have dom := ports20_dom ha mem
        rwa [stable20 ha mem] at dom
      have tail := ih (a+1) (by omega)
      simpa only [backHigh,renameProgram,List.map_append] using WindowCovered.appW tail point
  exact all 1 19 (by decide)

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Wide
end
section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Wide
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace
open SkywalkRails Partial WideReference EnterProof
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.NativeJ20
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

abbrev window20 := Shadow20.NativeJ20.window20
abbrev nextWindow20 := Shadow20.NativeJ20.nextWindow20

def unwind20 (j : Fin 9) (d : Bool) : Program := unbodySelected j (fromArchive20 j d)
def nextUnwind20 (j : Fin 9) (d : Bool) : Program := unwind20 j d ++ enterInvP20 j

theorem window20_run (j : Fin 9) (d : Bool) (s : State) (m : List Bool) (z : SkywalkRails.State)
    (odd : (z.a + z.b) % 2 = 1) (start0 : onRails20 j 0 z s.basis)
    (legal : PackLegal20 j (run (routed20 j 0 1) m s).basis)
    (row : Nat) (limit : row < 63145)
    (frame : Frame (prevRawPorts20 j) raw row
      (run (packProg20 j d) (m.drop (measurementCount (routed20 j 0 1))) (run (routed20 j 0 1) m s)))
    (clean : ∀ k : Fin 157, 23 ≤ k.val → prevRawPorts20 j k ∈ watch20 j →
      (run (packProg20 j d) (m.drop (measurementCount (routed20 j 0 1))) (run (routed20 j 0 1) m s)).basis
        (prevRawPorts20 j k) = false) :
    let out := run (window20 j d) m s
    out.phase = s.phase ∧ onRails20 j 20 (SkywalkTrace.next^[20] z) out.basis ∧
      readCells (shape20 j) 0 20 (mappedBasis20 j out.basis) = SkywalkTrace.trace 20 z ∧
      ∀ n, run (unwind20 j d) n out = s := by
  apply body_runSelected _ _ _ _ _ z odd start0
  exact (admin20 j d _ _ (SkywalkTrace.next z) (route20_frame j 0 1 (by decide) z odd s m start0).2
    legal row limit frame clean).1

theorem next_window20 (j : Fin 9) (d : Bool) (raw s : State) (m : List Bool)
    (z : SkywalkNat.State) (G S : Bool) (odd : z.v % 2 = 1)
    (small : Shadow7.SmallIfFar (sbP20 (start20 j)) 20 z)
    (cut : PackedCut (EnterJ20.lowerPairs j) (EnterJ20.upperPairs j) (EnterJ20.gate j) (EnterJ20.flagN j)
      (EnterJ20.flagF j) (EnterJ20.flagU j) (PortalValues.negative S z.u)
      (decide (Shadow.far (sbP20 (start20 j)) 20 z))
      (decide (Shadow.far (sbP20 (start20 j)) 20 z ∧ 2 ^ sbP20 (start20 j) ≤ z.u))
      (pullState (EnterJ20.pull j) raw) (eraseSites (EnterJ20.pending j) s))
    (input : SkywalkIntegerInput (EnterJ20.lay j) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist : ∀ r : Fin 20, raw.basis (EnterJ20.pull j (windowNet20 j (IntegerPacket.ports (shape20 j) r).history)) = false)
    (scratch : ∀ k : Fin 157, 23 ≤ k.val →
      let pre := run (enterP20 j) m s
      let tape := m.drop (measurementCount (enterP20 j))
      (run (packProg20 j d) (tape.drop (measurementCount (routed20 j 0 1))) (run (routed20 j 0 1) tape pre)).basis
        (prevRawPorts20 j k) = false)
    (past : SkywalkNat.State) (pg ps cross : Bool) (po : past.v % 2 = 1)
    (pm : PrevSmall20 j past) (prior : PrevPast20 j past pg ps cross s) :
    let out := run (nextWindow20 j d) m s
    let T := Shadow.reduced (sbP20 (start20 j)) 20 z
    out.phase = s.phase ∧ onRails20 j 20 (SkywalkTrace.next^[20] (encode G S T.u T.v)) out.basis ∧
      readCells (shape20 j) 0 20 (mappedBasis20 j out.basis) = SkywalkTrace.trace 20 (encode G S z.u z.v) ∧
      ∀ t, run (nextUnwind20 j d) t out = s := by
  let pre := run (enterP20 j) m s
  let tape := m.drop (measurementCount (enterP20 j))
  let T := Shadow.reduced (sbP20 (start20 j)) 20 z
  let Z := encode G S T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd20 (sbP20 (start20 j)) z small odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum G S _ _ (by omega)
  have ready := EnterJ20.ready_pending_at j raw s z G S m small cut input hist
  obtain ⟨legal, row, limit, _, frame⟩ := admits20 j d s m tape (tape.drop (measurementCount (routed20 j 0 1)))
    Z parity ready.2.1 scratch past pg ps cross po pm prior
  have all := window20_run j d pre tape Z parity ready.2.1 legal row limit frame (fun k hk _ => scratch k hk)
  dsimp only [nextWindow20, Shadow20.NativeJ20.nextWindow20, nextUnwind20]
  simp only [run_append, run_take]
  refine ⟨all.1.trans ready.1, all.2.1, all.2.2.1.trans (true_records20 (sbP20 (start20 j)) z small odd G S), ?_⟩
  intro n
  rw [all.2.2.2 n]
  exact EnterJ20.return_pending j raw s z G S small cut input m _

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Wide
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Leaf
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction
open Partial WideReference
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.WideReference20
open ECDSAAdd.Entrant.StairPacket.Shadow20.NativeJ20
open ECDSAAdd.Entrant.StairPacket.Shadow20.LeaveCut20
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

theorem admitted20 (j : Fin 9) (d : Bool) (x p : Nat) (good : Bounds x p) (raw s : State) (m : List Bool)
    (domain : Domain (start20 j) x p raw) (G S : Bool)
    (cut : PackedCut (EnterJ20.lowerPairs j) (EnterJ20.upperPairs j) (EnterJ20.gate j) (EnterJ20.flagN j)
      (EnterJ20.flagF j) (EnterJ20.flagU j) (PortalValues.negative S (unsigned (start20 j) x p).u)
      (decide (Shadow.far (sbP20 (start20 j)) 20 (unsigned (start20 j) x p)))
      (decide (Shadow.far (sbP20 (start20 j)) 20 (unsigned (start20 j) x p) ∧
        2 ^ sbP20 (start20 j) ≤ (unsigned (start20 j) x p).u))
      (pullState (EnterJ20.pull j) raw) (eraseSites (EnterJ20.pending j) s))
    (input : SkywalkIntegerInput (EnterJ20.lay j)
      (SkywalkRails.encode G S (unsigned (start20 j) x p).u (unsigned (start20 j) x p).v).a
      (SkywalkRails.encode G S (unsigned (start20 j) x p).u (unsigned (start20 j) x p).v).b G raw.basis)
    (scratch : ∀ k : Fin 157, 23 ≤ k.val →
      let pre := run (enterP20 j) m s
      let tape := m.drop (measurementCount (enterP20 j))
      (run (packProg20 j d) (tape.drop (measurementCount (routed20 j 0 1))) (run (routed20 j 0 1) tape pre)).basis
        (prevRawPorts20 j k) = false)
    (past : SkywalkNat.State) (pg ps cross : Bool) (po : past.v % 2 = 1)
    (pm : PrevSmall20 j past) (prior : PrevPast20 j past pg ps cross s) :
    let out := run (nextWindow20 j d) m s
    Inputs20 j out (unsigned (start20 j) x p) G S ∧
    out.phase = s.phase ∧
    (∃ row < 63145, PrevRowTruth20 j past pg ps row ∧ Kept (prevCodePorts20 j) d row out ∧
      ∀ k : Fin 3, out.basis (e0P20 (start20 j) + 6 + k.val) = false) ∧
    (∀ q ∈ tailTemps20 j, out.basis q = false) ∧
    (∀ t, run (TickCutMixed.Wide.nextUnwind20 j d) t out = s) := by
  have old := Shadow20.LeaveCut20.admitted20 j d x p good raw s m domain G S cut input scratch past pg ps cross po pm prior
  have numbers := actualNumbers20 j x p good
  have hist := WideReference20.pulled_history20 j domain
  have win := TickCutMixed.Wide.next_window20 j d raw s m (unsigned (start20 j) x p) G S
    numbers.odd numbers.small.1 cut input hist scratch past pg ps cross po pm prior
  exact ⟨old.1, old.2.1, old.2.2.1, old.2.2.2.1, win.2.2.2⟩

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Leaf
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed.Reentry
open ECDSAAdd Arithmetic MappedCompressed IntegerPacket ArchivePortAction StairArchiveRaw StairArchiveTrace
open SkywalkRails Partial WideReference EnterProof
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.Reentry345
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

abbrev nextWindow345 := Shadow20.Reentry345.nextWindow345

def unwind345 (d : Bool) : Program := TickCutMixed.Tail.unbodySelected j20 (fromArchive345 d)
def nextUnwind345 (d : Bool) : Program := unwind345 d ++ Shadow7.enterInvP j20

theorem next_window345 (d : Bool) (raw s : State) (m : List Bool)
    (z : SkywalkNat.State) (G S : Bool) (odd : z.v % 2 = 1) (small : Shadow7.SmallIfFar (Shadow7.sbP 345) 15 z)
    (cut : PackedCut (EnterJ7.lowerPairs j20) (EnterJ7.upperPairs j20) (EnterJ7.gate j20) (EnterJ7.flagN j20)
      (EnterJ7.flagF j20) (EnterJ7.flagU j20) (PortalValues.negative S z.u)
      (decide (Shadow.far (Shadow7.sbP 345) 15 z)) (decide (Shadow.far (Shadow7.sbP 345) 15 z ∧ 2 ^ Shadow7.sbP 345 ≤ z.u))
      (pullState (EnterJ7.pull j20) raw) (eraseSites (EnterJ7.pending j20) s))
    (input : SkywalkIntegerInput (EnterJ7.lay j20) (encode G S z.u z.v).a (encode G S z.u z.v).b G raw.basis)
    (hist : ∀ r : Fin 15, raw.basis (EnterJ7.pull j20 (windowNet j20 (IntegerPacket.ports (Shadow7.shape j20) r).history)) = false)
    (scratch : ∀ k : Fin 157, 23 ≤ k.val →
      let pre := run (Shadow7.enterP j20) m s
      let tape := m.drop (measurementCount (Shadow7.enterP j20))
      (run (packProg345 d) (tape.drop (measurementCount (Shadow7.routed j20 0 1)))
        (run (Shadow7.routed j20 0 1) tape pre)).basis (ArchiveJ20.rawPorts k8 k) = false)
    (past : SkywalkNat.State) (pg ps cross : Bool) (po : past.v % 2 = 1) (pm : Shadow7.SmallIfFar (sbP20 325) 20 past)
    (prior : PastFacts20 k8 (ArchiveJ20.rawPorts k8) past pg ps cross s) :
    let out := run (nextWindow345 d) m s
    let T := Shadow.reduced (Shadow7.sbP 345) 15 z
    out.phase = s.phase ∧ Shadow7.onRails j20 15 (SkywalkTrace.next^[15] (encode G S T.u T.v)) out.basis ∧
      readCells (Shadow7.shape j20) 0 15 (mappedBasis j20 out.basis) = SkywalkTrace.trace 15 (encode G S z.u z.v) ∧
      ∀ t, run (nextUnwind345 d) t out = s := by
  let pre := run (Shadow7.enterP j20) m s
  let tape := m.drop (measurementCount (Shadow7.enterP j20))
  let T := Shadow.reduced (Shadow7.sbP 345) 15 z
  let Z := encode G S T.u T.v
  have to' : T.v % 2 = 1 := shadow_odd_shadow7 (Shadow7.sbP 345) z small odd
  have parity : (Z.a + Z.b) % 2 = 1 := encode_odd_sum G S _ _ (by omega)
  have ready := EnterJ7.ready_pending_at j20 raw s z G S m small cut input hist
  obtain ⟨okA, okB, row, limit, frame⟩ := admits345 d s m tape (tape.drop (measurementCount (Shadow7.routed j20 0 1)))
    Z parity ready.2.1 scratch past pg ps cross po pm prior
  have adm := (admin345 d _ _ (SkywalkTrace.next Z)
    (Shadow7.route_frame j20 0 1 (by decide) Z parity pre tape ready.2.1).2 okA okB row limit frame (fun k hk _ => scratch k hk)).1
  have all := TickCutMixed.Tail.body_runSelected j20 (withArchive345 d) (fromArchive345 d) pre tape Z parity ready.2.1 adm
  dsimp only [nextWindow345, Shadow20.Reentry345.nextWindow345, nextUnwind345,
    Shadow20.Reentry345.window345, unwind345]
  simp only [run_append, run_take]
  refine ⟨all.1.trans ready.1, all.2.1, all.2.2.1.trans (true_records_shadow7 (Shadow7.sbP 345) z small odd G S), ?_⟩
  intro n
  rw [all.2.2.2 n]
  have free : ∀ q ∈ EnterJ7.pending j20, q ∉ wires (Shadow7.enterInvP j20) := by
    intro q hq used
    have r := EnterJ7.portsRegion j20 (List.mem_toFinset.mp (TickCutMixed.NativeJ7.enterInvCover j20 used))
    have f := EnterJ7.frame j20
    simp only [EnterJ7.pending, List.mem_cons, List.not_mem_nil, or_false, Wire] at hq r f ⊢
    omega
  apply unmask (Shadow7.enterP j20) (Shadow7.enterInvP j20) (EnterJ7.pending j20) (EnterJ7.avoid_enter j20) free
  exact EnterProof17.return_packed (EnterJ7.layout j20) (EnterJ7.map j20) _ _ (EnterJ7.inc j20) (fun _ => rfl) rfl
    (EnterJ7.emitted j20) (EnterJ7.emittedInv j20) raw _ z G S small cut input _ _

end ECDSAAdd.Entrant.StairPacket.TickCutMixed.Reentry
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed
open ECDSAAdd Arithmetic IntegerPacket
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

abbrev params15 : WindowFold.Pieces Program := {CRTBarrel.params with unrouted := Tail.selected}
abbrev unrouted15 := Hosted.unroutedHigh
abbrev unrouted20 := Wide.unroutedHigh

def block15R (d : Bool) (i j : Fin 26) : List Program :=
  [CRTBarrel.unleave j, Hosted.unroutedHigh j 1 14, Shadow7.archiveRestoreP i d,
   MixedWindow.unpackW d (start j) (start j - 10), Shadow7.unrouted j 0 1, Shadow7.enterInvP j]


def block20R (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if h : j.val = 0 then
    [leaveInvP20Red j, Wide.unroutedHigh j 1 19, archiveRestore150To20 d, MixedWindow.unpackW d 165 155, Shadow20.unrouted20 j 0 1, enterInvP20 j]
  else
    [leaveInvP20Red j, Wide.unroutedHigh j 1 19, archiveRestoreP20 ⟨j.val - 1, by omega⟩ d,
     MixedWindow.unpackW d s (s - 10), MixedWindow.unpackW d s (s - 15), Shadow20.unrouted20 j 0 1, enterInvP20 j]


def reverseL (d : Bool) : List Program :=
  [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, MixedWindow.recvW 420, Shadow7.portalP 420, Shadow7.parkInvP 420] ++
  (MixedWindow.suffixPairs.reverse.flatMap fun p => block15R d p.1 p.2) ++
  [CRTBarrel.unleave MixedWindow.j20, Hosted.unroutedHigh MixedWindow.j20 1 14, archiveRestoreP20 MixedWindow.k8 d,
   MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330, Shadow7.unrouted MixedWindow.j20 0 1, Shadow7.enterInvP MixedWindow.j20] ++
  ((List.finRange 9).reverse.flatMap (block20R d)) ++
  [leaveInv150To20Red, Hosted.unroutedHigh MixedWindow.j7 1 14, Shadow7.archiveRestoreP MixedWindow.j6 d,
   MixedWindow.unpackW d 150 140, Shadow7.unrouted MixedWindow.j7 0 1, Shadow7.enterInvP MixedWindow.j7] ++
  (MixedWindow.prefixPairs.reverse.flatMap fun p => block15R d p.1 p.2) ++
  [CRTBarrel.unleave MixedWindow.j0, Hosted.unroutedHigh MixedWindow.j0 1 14, MixedWindow.unpackW d 45 45,
   Shadow7.unrouted MixedWindow.j0 0 1, Shadow7.enterInvP MixedWindow.j0, Shadow7.portalInvP 45]


def block15RC (d : Bool) (i j : Fin 26) : List Program :=
  [unleave15C j, Hosted.unroutedHigh j 1 14, Shadow7.archiveRestoreP i d,
   MixedWindow.unpackW d (start j) (start j - 10), Shadow7.unrouted j 0 1, enterInv15C j]

def block20RC (d : Bool) (j : Fin 9) : List Program :=
  let s := start20 j
  if h : j.val = 0 then
    [unleave20C j, Wide.unroutedHigh j 1 19, archiveRestore150To20 d, MixedWindow.unpackW d 165 155, Shadow20.unrouted20 j 0 1, enterInv20C j]
  else
    [unleave20C j, Wide.unroutedHigh j 1 19, archiveRestoreP20 ⟨j.val - 1, by omega⟩ d,
     MixedWindow.unpackW d s (s - 10), MixedWindow.unpackW d s (s - 15), Shadow20.unrouted20 j 0 1, enterInv20C j]

def reverseLC (d : Bool) : List Program :=
  [Shadow7.exitRestoreP 420 d, MixedWindow.unpackW d 420 410, MixedWindow.recvW 420, portalC 420, Shadow7.parkInvP 420] ++
  (MixedWindow.suffixPairs.reverse.flatMap fun p => block15RC d p.1 p.2) ++
  [unleave15C MixedWindow.j20, Hosted.unroutedHigh MixedWindow.j20 1 14, archiveRestoreP20 MixedWindow.k8 d,
   MixedWindow.unpackW d 345 335, MixedWindow.unpackW d 345 330, Shadow7.unrouted MixedWindow.j20 0 1, enterInv15C MixedWindow.j20] ++
  ((List.finRange 9).reverse.flatMap (block20RC d)) ++
  [unleave150C, Hosted.unroutedHigh MixedWindow.j7 1 14, Shadow7.archiveRestoreP MixedWindow.j6 d,
   MixedWindow.unpackW d 150 140, Shadow7.unrouted MixedWindow.j7 0 1, enterInv15C MixedWindow.j7] ++
  (MixedWindow.prefixPairs.reverse.flatMap fun p => block15RC d p.1 p.2) ++
  [unleave15C MixedWindow.j0, Hosted.unroutedHigh MixedWindow.j0 1 14, MixedWindow.unpackW d 45 45,
   Shadow7.unrouted MixedWindow.j0 0 1, enterInv15C MixedWindow.j0, portalInvC 45]


/-- The old forward selection is retained exactly. -/
def forward (d : Bool) : Program := MixedWindow.forwardMixedCut d
/-- The uncut reverse is provided for the admitted mixed-chain proof. -/
def reverseUncut (d : Bool) : Program := (reverseL d).flatten
/-- The selected reverse retains the existing 23 FredCut boundaries. -/
def reverse (d : Bool) : Program := (reverseLC d).flatten

theorem forward_eq (d : Bool) : forward d = MixedWindow.forwardMixedCut d := rfl

end ECDSAAdd.Entrant.StairPacket.TickCutMixed
end

section
open private ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev_exit
  ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15
  ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To15
  ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20
  ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev150To20
  ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev_end
  ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.finRange9_eq
  from ECDSAAdd.Submission.Entrant.LeaveReductions

namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed
open ECDSAAdd Arithmetic Challenge
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false

theorem rev_mixed_cut (d : Bool) : Cut 23 (reverseL d) (reverseLC d) := by
  simp only [reverseL, reverseLC, MixedWindow.prefixPairs, MixedWindow.suffixPairs, ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.finRange9_eq,
    List.reverse_cons, List.reverse_nil, block15R, block15RC, block20R, block20RC,
    List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append, List.append_assoc,
    show (0 : Nat) = 0 from rfl, ↓reduceDIte,
    show ¬(1 : Nat) = 0 by decide, show ¬(2 : Nat) = 0 by decide, show ¬(3 : Nat) = 0 by decide,
    show ¬(4 : Nat) = 0 by decide, show ¬(5 : Nat) = 0 by decide, show ¬(6 : Nat) = 0 by decide,
    show ¬(7 : Nat) = 0 by decide, show ¬(8 : Nat) = 0 by decide]
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev_exit (by decide +kernel) (by decide +kernel)
    (avoid_of_check _ _ (by decide +kernel)) (sub_of_check _ _ (by decide +kernel))
    (inv_swap_of_eq _ _ _ _ _ _ _ (Eblk15_S2 _) (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 23 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 22 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 21 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 20 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To15 (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 7 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev20To20 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk20_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev150To20 (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ Dblk150_S2 (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev15 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (inv_of_eq _ _ _ _ _ _ (Dblk15_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut.bnd_rev_end (by decide +kernel)
    (inv_of_eq _ 60 1029 304 1028 303 (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ 60 1029 304 1028 303 (by decide +kernel)) (by decide +kernel)
  exact Cut.nil


/-- FredCut transport only: this equality relates the two H3 reverse lists.
It makes no equality claim against the original reverse on arbitrary states. -/
theorem reverse_cut_run_eq (d : Bool) : run (reverse d) = run (reverseUncut d) :=
  funext fun m => funext fun s => (rev_mixed_cut d).run_eq m s

end ECDSAAdd.Entrant.StairPacket.TickCutMixed
end

section
namespace ECDSAAdd.Entrant.StairPacket.TickCutMixed
open ECDSAAdd Arithmetic Challenge
open ECDSAAdd.Entrant.StairPacket.Shadow20
open ECDSAAdd.Entrant.StairPacket.Shadow20.MixedFredCut
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- A local replacement carries its resource and static obligations.
The fold below never unfolds the retained archive or leave programs. -/
private structure Piece where
  old : Program
  new : Program
  saving : Nat
  tc : toffoliCount new + saving = toffoliCount old
  mc : measurementCount new = measurementCount old + saving
  slots : gateSlots new = gateSlots old + 7 * saving
  physical : GatePhysical old → GatePhysical new
  covered : WindowCovered.CoveredW old → WindowCovered.CoveredW new

private def Piece.keep (P : Program) : Piece where
  old := P
  new := P
  saving := 0
  tc := Nat.add_zero _
  mc := (Nat.add_zero _).symm
  slots := by simp only [Nat.mul_zero,Nat.add_zero]
  physical := id
  covered := id

private def Piece.short (j : Fin 26) (hj : j.val ≤ 24) : Piece where
  old := Shadow7.unrouted j 1 14
  new := Hosted.unroutedHigh j 1 14
  saving := 14
  tc := (Tail.tail_counts j).1
  mc := (Tail.tail_counts j).2.1
  slots := (Tail.tail_counts j).2.2
  physical := fun _ => Tail.tail_physical j
  covered := fun _ => Tail.tail_covered j (Nat.zero_le _) hj

private def Piece.wide (j : Fin 9) : Piece where
  old := Shadow20.unrouted20 j 1 19
  new := Wide.unroutedHigh j 1 19
  saving := 19
  tc := (Wide.tail_counts j).1
  mc := (Wide.tail_counts j).2.1
  slots := (Wide.tail_counts j).2.2
  physical := fun _ => Wide.tail_physical j
  covered := fun _ => Wide.tail_covered j

/-- Projection equations keep the replacement proof fields opaque when a
concrete schedule is mapped. No retained program is unfolded here. -/
private theorem keep_old (P : Program) : (Piece.keep P).old = P := rfl
private theorem keep_new (P : Program) : (Piece.keep P).new = P := rfl
private theorem keep_saving (P : Program) : (Piece.keep P).saving = 0 := rfl
private theorem short_old (j : Fin 26) (hj : j.val ≤ 24) :
    (Piece.short j hj).old = Shadow7.unrouted j 1 14 := rfl
private theorem short_new (j : Fin 26) (hj : j.val ≤ 24) :
    (Piece.short j hj).new = Hosted.unroutedHigh j 1 14 := rfl
private theorem short_saving (j : Fin 26) (hj : j.val ≤ 24) :
    (Piece.short j hj).saving = 14 := rfl
private theorem wide_old (j : Fin 9) :
    (Piece.wide j).old = Shadow20.unrouted20 j 1 19 := rfl
private theorem wide_new (j : Fin 9) :
    (Piece.wide j).new = Wide.unroutedHigh j 1 19 := by
  dsimp only [Piece.wide]
private theorem wide_saving (j : Fin 9) : (Piece.wide j).saving = 19 := rfl

private def block15Pieces (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24) : List Piece :=
  [Piece.keep (unleave15C j), Piece.short j hj, Piece.keep (Shadow7.archiveRestoreP i d),
   Piece.keep (MixedWindow.unpackW d (start j) (start j - 10)),
   Piece.keep (Shadow7.unrouted j 0 1), Piece.keep (enterInv15C j)]

private def block20Pieces (d : Bool) (j : Fin 9) : List Piece :=
  let s := start20 j
  if h : j.val = 0 then
    [Piece.keep (unleave20C j), Piece.wide j, Piece.keep (archiveRestore150To20 d),
     Piece.keep (MixedWindow.unpackW d 165 155), Piece.keep (Shadow20.unrouted20 j 0 1),
     Piece.keep (enterInv20C j)]
  else
    [Piece.keep (unleave20C j), Piece.wide j,
     Piece.keep (archiveRestoreP20 ⟨j.val - 1, by omega⟩ d),
     Piece.keep (MixedWindow.unpackW d s (s - 10)), Piece.keep (MixedWindow.unpackW d s (s - 15)),
     Piece.keep (Shadow20.unrouted20 j 0 1), Piece.keep (enterInv20C j)]

/-- Only this small bank schedule is concrete; each block proof is generic. -/
private def pieces (d : Bool) : List Piece :=
  [Piece.keep (Shadow7.exitRestoreP 420 d), Piece.keep (MixedWindow.unpackW d 420 410),
   Piece.keep (MixedWindow.recvW 420), Piece.keep (portalC 420), Piece.keep (Shadow7.parkInvP 420)] ++
  block15Pieces d ⟨23, by decide⟩ ⟨24, by decide⟩ (by decide) ++
  block15Pieces d ⟨22, by decide⟩ ⟨23, by decide⟩ (by decide) ++
  block15Pieces d ⟨21, by decide⟩ ⟨22, by decide⟩ (by decide) ++
  block15Pieces d ⟨20, by decide⟩ ⟨21, by decide⟩ (by decide) ++
  [Piece.keep (unleave15C MixedWindow.j20), Piece.short MixedWindow.j20 (by decide),
   Piece.keep (archiveRestoreP20 MixedWindow.k8 d), Piece.keep (MixedWindow.unpackW d 345 335),
   Piece.keep (MixedWindow.unpackW d 345 330), Piece.keep (Shadow7.unrouted MixedWindow.j20 0 1),
   Piece.keep (enterInv15C MixedWindow.j20)] ++
  ((List.finRange 9).reverse.flatMap (block20Pieces d)) ++
  [Piece.keep unleave150C, Piece.short MixedWindow.j7 (by decide),
   Piece.keep (Shadow7.archiveRestoreP MixedWindow.j6 d), Piece.keep (MixedWindow.unpackW d 150 140),
   Piece.keep (Shadow7.unrouted MixedWindow.j7 0 1), Piece.keep (enterInv15C MixedWindow.j7)] ++
  block15Pieces d ⟨5, by decide⟩ ⟨6, by decide⟩ (by decide) ++
  block15Pieces d ⟨4, by decide⟩ ⟨5, by decide⟩ (by decide) ++
  block15Pieces d ⟨3, by decide⟩ ⟨4, by decide⟩ (by decide) ++
  block15Pieces d ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide) ++
  block15Pieces d ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide) ++
  block15Pieces d ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) ++
  [Piece.keep (unleave15C MixedWindow.j0), Piece.short MixedWindow.j0 (by decide),
   Piece.keep (MixedWindow.unpackW d 45 45), Piece.keep (Shadow7.unrouted MixedWindow.j0 0 1),
   Piece.keep (enterInv15C MixedWindow.j0), Piece.keep (portalInvC 45)]

private theorem map_flatMap_local {α β γ : Type} (f : α → List β) (g : β → γ) (xs : List α) :
    (xs.flatMap f).map g = xs.flatMap (fun x => (f x).map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,ih]

private theorem block15_old (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24) :
    (block15Pieces d i j hj).map Piece.old = MixedFredCut.block15RC d i j := rfl
private theorem block15_new (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24) :
    (block15Pieces d i j hj).map Piece.new = block15RC d i j := rfl
private theorem block15_saving (d : Bool) (i j : Fin 26) (hj : j.val ≤ 24) :
    ((block15Pieces d i j hj).map Piece.saving).sum = 14 := rfl

private theorem block20_old (d : Bool) (j : Fin 9) :
    (block20Pieces d j).map Piece.old = MixedFredCut.block20RC d j := by
  by_cases h : j.val = 0 <;>
    simp only [block20Pieces,MixedFredCut.block20RC,h,↓reduceDIte,List.map_cons,List.map_nil,
      keep_old,wide_old]
private theorem block20_new (d : Bool) (j : Fin 9) :
    (block20Pieces d j).map Piece.new = block20RC d j := by
  by_cases h : j.val = 0 <;>
    simp only [block20Pieces,block20RC,h,↓reduceDIte,List.map_cons,List.map_nil,keep_new,wide_new]
private theorem block20_saving (d : Bool) (j : Fin 9) :
    ((block20Pieces d j).map Piece.saving).sum = 19 := by
  by_cases h : j.val = 0 <;>
    simp only [block20Pieces,h,↓reduceDIte,List.map_cons,List.map_nil,keep_saving,wide_saving,
      List.sum_cons,List.sum_nil,Nat.zero_add,Nat.add_zero]

attribute [local irreducible] Piece.keep Piece.short Piece.wide

private theorem pieces_old (d : Bool) :
    (pieces d).map Piece.old = MixedFredCut.reverseLC d := by
  simp only [pieces,MixedFredCut.reverseLC,List.map_append,List.map_cons,List.map_nil,
    map_flatMap_local,block15_old,block20_old,keep_old,short_old,
    MixedWindow.prefixPairs,MixedWindow.suffixPairs,List.reverse_cons,List.reverse_nil,
    List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,List.append_assoc]
private theorem pieces_new (d : Bool) :
    (pieces d).map Piece.new = reverseLC d := by
  simp only [pieces,reverseLC,List.map_append,List.map_cons,List.map_nil,
    map_flatMap_local,block15_new,block20_new,keep_new,short_new,
    MixedWindow.prefixPairs,MixedWindow.suffixPairs,List.reverse_cons,List.reverse_nil,
    List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,List.append_assoc]

private theorem sum_constant {α : Type} (xs : List α) (c : Nat) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul]
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]; omega

private theorem saving_flatMap {α : Type} (xs : List α) (f : α → List Piece) (c : Nat)
    (h : ∀ x, ((f x).map Piece.saving).sum = c) :
    ((xs.flatMap f).map Piece.saving).sum = xs.length * c := by
  induction xs with
  | nil => simp only [List.flatMap_nil,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul]
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,h,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem pieces_saving (d : Bool) : ((pieces d).map Piece.saving).sum = 353 := by
  simp only [pieces,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,block15_saving,
    saving_flatMap _ (block20Pieces d) 19 (block20_saving d),
    List.length_reverse,List.length_finRange,keep_saving,short_saving]
  omega

private theorem fold_counts (ps : List Piece) :
    toffoliCount (ps.map Piece.new).flatten + (ps.map Piece.saving).sum =
      toffoliCount (ps.map Piece.old).flatten ∧
    measurementCount (ps.map Piece.new).flatten =
      measurementCount (ps.map Piece.old).flatten + (ps.map Piece.saving).sum ∧
    gateSlots (ps.map Piece.new).flatten =
      gateSlots (ps.map Piece.old).flatten + 7 * (ps.map Piece.saving).sum := by
  induction ps with
  | nil => simp [toffoliCount,measurementCount,gateSlots]
  | cons p ps ih =>
    have t := p.tc; have m := p.mc; have slots := p.slots
    simp only [List.map_cons,List.flatten_cons,List.sum_cons,toffoliCount_append,
      measurementCount_append,gateSlots_append]
    exact ⟨by omega,by omega,by omega⟩

private theorem fold_physical (ps : List Piece)
    (h : GatePhysical (ps.map Piece.old).flatten) : GatePhysical (ps.map Piece.new).flatten := by
  induction ps with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.map_cons,List.flatten_cons,gatePhysical_append] at h ⊢
    exact ⟨p.physical h.1,ih h.2⟩

private theorem covered_append_iff (P Q : Program) :
    WindowCovered.CoveredW (P ++ Q) ↔ WindowCovered.CoveredW P ∧ WindowCovered.CoveredW Q := by
  constructor
  · intro h
    exact ⟨fun q hq => h q (by rw [wires_append]; exact Finset.mem_union_left _ hq),
      fun q hq => h q (by rw [wires_append]; exact Finset.mem_union_right _ hq)⟩
  · rintro ⟨hP,hQ⟩; exact WindowCovered.appW hP hQ

private theorem fold_covered (ps : List Piece)
    (h : WindowCovered.CoveredW (ps.map Piece.old).flatten) :
    WindowCovered.CoveredW (ps.map Piece.new).flatten := by
  induction ps with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.map_cons,List.flatten_cons,covered_append_iff] at h ⊢
    exact ⟨p.covered h.1,ih h.2⟩

/-- Exact local H3 delta, independently of the direction's inherited constants. -/
theorem resource_delta (d : Bool) :
    toffoliCount (reverse d) + 353 = toffoliCount (MixedWindow.reverseMixedCut d) ∧
    measurementCount (reverse d) = measurementCount (MixedWindow.reverseMixedCut d) + 353 ∧
    gateSlots (reverse d) = gateSlots (MixedWindow.reverseMixedCut d) + 2471 := by
  have h := fold_counts (pieces d)
  simpa only [pieces_old,pieces_new,pieces_saving,reverse,MixedWindow.reverseMixedCut] using h

theorem mixed_counts (d : Bool) :
    toffoliCount (forward d) = 127685 ∧
    toffoliCount (reverse d) = (if d then 127737 else 127759) ∧
    measurementCount (forward d) = 66171 ∧
    measurementCount (reverse d) = (if d then 65809 else 65831) := by
  have h := resource_delta d
  have old := MixedWindow.mixedCut_counts d
  cases d <;> simp only [Bool.false_eq_true,↓reduceIte,forward] at old h ⊢ <;>
    exact ⟨old.1,by omega,old.2.2.1,by omega⟩

theorem slots_le (d : Bool) :
    gateSlots (reverse d) ≤ gateSlots (MixedWindow.reverseMixedCut d) + 2471 :=
  (resource_delta d).2.2.le

theorem physical (d : Bool) : GatePhysical (reverse d) := by
  have old := (MixedWindow.mixedCut_physical d).2
  change GatePhysical (MixedFredCut.reverseLC d).flatten at old
  rw [← pieces_old d] at old
  simpa only [pieces_new,reverse] using fold_physical (pieces d) old

theorem covered (d : Bool) : WindowCovered.CoveredW (reverse d) := by
  have old := (MixedWindow.mixedCut_covered d).2
  change WindowCovered.CoveredW (MixedFredCut.reverseLC d).flatten at old
  rw [← pieces_old d] at old
  simpa only [pieces_new,reverse] using fold_covered (pieces d) old

/-- Compatibility name for the caller's new-cut to new-uncut bridge. -/
theorem reverse_run_eq (d : Bool) : run (reverse d) = run (reverseUncut d) :=
  reverse_cut_run_eq d

end ECDSAAdd.Entrant.StairPacket.TickCutMixed
end
