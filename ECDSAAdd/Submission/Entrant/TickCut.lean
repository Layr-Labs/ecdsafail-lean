-- TickCut (H3 reverse-window receiver): spariev 59c20890, ported onto the margin-16 release (keptparity).
import ECDSAAdd.Submission.Entrant.Stair44Stock

section

/- New H3 proof draft. Strict compilation is required before any reuse claim. -/
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

/- Draft local identity only. This file does not select an H3 caller or claim 700 T.
The admitted forward invariant and routed-walk transport remain required. -/
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

/- New H3 hosted transport draft. No selected caller is changed by this probe. -/
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


theorem sel01 (j : Fin 26) : selected j 0 1 = Shadow7.unrouted j 0 1 := by
  unfold selected
  exact if_neg (by omega)

theorem sel114 (j : Fin 26) : selected j 1 14 = unroutedHigh j 1 14 := by
  unfold selected
  exact if_pos ⟨rfl, rfl⟩


end ECDSAAdd.Entrant.StairPacket.TickCut.Tail

end
