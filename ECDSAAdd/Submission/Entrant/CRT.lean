import ECDSAAdd.Submission.Entrant.Stair44Stock
import ECDSAAdd.Framework.Syntax
import ECDSAAdd.Framework.Semantics
import ECDSAAdd.Framework.WireRenamePool

-- ==== begin folded TickCut ====
section
-- TickCut (H3 reverse-window receiver): spariev 59c20890, ported onto the margin-16 release (keptparity).

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
end
-- ==== end folded TickCut ====

section

-- ==== begin FlagLeave + DeadScan (credited to spariev 65b176b3) ====
section
namespace ECDSAAdd.Entrant.StairPacket.FlagLeave
open Arithmetic GateMirror Partial
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def hit (f u l : Wire) (g : Gate) : Bool :=
  decide (g = .make f u l ∨ g = .pop f u l)

def cut (f u l : Wire) : Nat → List Gate → List Gate
  | 0, gs => gs
  | _+1, [] => []
  | n+1, g::gs => if hit f u l g then .cx u l :: cut f u l n gs
      else g :: cut f u l (n+1) gs

/-- Track the temporary far-flag XOR between its matching adjust gates. -/
def check (f u c l : Wire) : Nat → Bool → List Gate → Bool
  | 0, _, _ => true
  | _+1, _, [] => true
  | n+1, shifted, g::gs =>
    if hit f u l g then !shifted && check f u c l n shifted gs
    else if target g = f then
      if g = .cx c f then check f u c l (n+1) (!shifted) gs else false
    else if target g = u ∨ (shifted = true ∧ target g = c) then false
    else check f u c l (n+1) shifted gs

def Rel (f u c : Wire) (shifted : Bool) (s : State) : Prop :=
  ((s.basis f ^^ (shifted && s.basis c)) && s.basis u) = s.basis u

private theorem transition_frame (g : Gate) (s : State) (q : Wire) (hq : q ≠ target g) :
    (transition g s).basis q = s.basis q := by
  cases g <;> simp_all [transition,front,erase,run,measureAndCorrect,writeBit,target]

private theorem transition_cut (f u l : Wire) (g : Gate) (s : State)
    (hf : f ≠ l) (hu : u ≠ l) (hg : hit f u l g = true)
    (rel : (s.basis f && s.basis u) = s.basis u)
    (ok : ValueOK s g) :
    transition (.cx u l) s = transition g s := by
  have h := of_decide_eq_true hg
  rcases h with rfl | rfl
  · simp only [transition,front,run,rel]
  · change s.basis l = (s.basis f && s.basis u) at ok
    rw [rel] at ok
    simp [transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,writeBit,ok]

private theorem rel_step (f u c : Wire) (g : Gate) (s : State) (shifted : Bool)
    (distinct : f ≠ u ∧ c ≠ f ∧ c ≠ u)
    (hrel : Rel f u c shifted s)
    (notf : target g ≠ f) (notu : target g ≠ u)
    (notc : shifted = true → target g ≠ c) :
    Rel f u c shifted (transition g s) := by
  unfold Rel at *
  rw [transition_frame _ _ _ (Ne.symm notf),transition_frame _ _ _ (Ne.symm notu)]
  cases shifted with
  | false => simpa using hrel
  | true => rw [transition_frame _ _ _ (Ne.symm (notc rfl))]; exact hrel

private theorem rel_toggle (f u c : Wire) (s : State) (shifted : Bool)
    (distinct : f ≠ u ∧ c ≠ f ∧ c ≠ u)
    (hrel : Rel f u c shifted s) : Rel f u c (!shifted) (transition (.cx c f) s) := by
  unfold Rel at *
  simp only [transition,front,run,writeBit,Function.update_self,
    Function.update_of_ne (Ne.symm distinct.1),Function.update_of_ne distinct.2.1]
  cases shifted <;> cases hF : s.basis f <;> cases hC : s.basis c <;> cases hU : s.basis u <;> simp_all

/-- Each replacement has the reference default transition and preserves freshness/erasures. -/
theorem cut_valid (f u c l : Wire) (n : Nat) (shifted : Bool) (gs : List Gate) (s : State)
    (distinct : f ≠ u ∧ c ≠ f ∧ c ≠ u) (fl : f ≠ l) (ul : u ≠ l)
    (checked : check f u c l n shifted gs = true)
    (related : Rel f u c shifted s)
    (phys : ∀ g ∈ gs, proper g = true) (prepared : Prepared s gs) (ready : Ready s gs) :
    (∀ g ∈ cut f u l n gs, proper g = true) ∧ Prepared s (cut f u l n gs) ∧ Ready s (cut f u l n gs) ∧
    run (GateMirror.forward (cut f u l n gs)) [] s = run (GateMirror.forward gs) [] s := by
  induction gs generalizing n shifted s with
  | nil => cases n <;> simp_all [cut,check,Prepared,Ready,forward]
  | cons g gs ih =>
    cases n with
    | zero => exact ⟨phys,prepared,ready,rfl⟩
    | succ n =>
      have pg := phys g List.mem_cons_self
      have tailphys : ∀ x ∈ gs, proper x = true := fun x hx => phys x (List.mem_cons_of_mem _ hx)
      by_cases hitg : hit f u l g = true
      · have checks := checked
        rw [check,if_pos hitg] at checks
        simp only [Bool.and_eq_true,Bool.not_eq_true'] at checks
        have sm : shifted = false := checks.1
        subst shifted
        have eq := transition_cut f u l g s fl ul hitg (by simpa [Rel] using related) prepared.1
        have newrel : Rel f u c false (transition g s) := by
          unfold Rel at *
          simp only [Bool.false_and,Bool.xor_false] at *
          have hg := of_decide_eq_true hitg
          rcases hg with rfl | rfl
          all_goals rw [transition_frame _ _ _ fl,transition_frame _ _ _ ul]; exact related
        obtain ⟨p,h,r,e⟩ := ih n false (transition g s) checks.2 newrel tailphys prepared.2 ready.2
        refine ⟨?_,?_,?_,?_⟩
        · intro x hx
          simp only [cut,hitg,↓reduceIte,List.mem_cons] at hx
          rcases hx with rfl | hx
          · simpa [proper] using ul
          · exact p x hx
        · simpa only [cut,hitg,↓reduceIte,Prepared,eq] using (show True ∧ Prepared (transition g s) (cut f u l n gs) from ⟨trivial,h⟩)
        · simpa only [cut,hitg,↓reduceIte,Ready,eq] using (show True ∧ Ready (transition g s) (cut f u l n gs) from ⟨trivial,r⟩)
        · change run (GateMirror.forward (cut f u l (n+1) (g::gs))) [] s = _
          simp only [cut,hitg,↓reduceIte,GateMirror.forward,List.map_cons]
          change run ([front (.cx u l)] ++ GateMirror.forward (cut f u l n gs)) [] s = run ([front g] ++ GateMirror.forward gs) [] s
          rw [run_append,run_take,List.drop_nil,run_append,run_take,List.drop_nil]
          rw [show run [front (.cx u l)] [] s = transition g s from eq,e]
          rfl
      · have miss : hit f u l g = false := Bool.eq_false_iff.mpr hitg
        have checks := checked
        rw [check,if_neg hitg] at checks
        obtain ⟨shifted',hc,hr⟩ : ∃ shifted', check f u c l (n+1) shifted' gs = true ∧ Rel f u c shifted' (transition g s) := by
          by_cases gf : target g = f
          · rw [if_pos gf] at checks
            by_cases hg : g = .cx c f
            · rw [if_pos hg] at checks
              subst g
              exact ⟨!shifted,checks,rel_toggle f u c s shifted distinct related⟩
            · rw [if_neg hg] at checks
              contradiction
          · rw [if_neg gf] at checks
            by_cases bad : target g = u ∨ (shifted = true ∧ target g = c)
            · rw [if_pos bad] at checks
              contradiction
            · rw [if_neg bad] at checks
              have hu : target g ≠ u := fun h => bad (Or.inl h)
              have hc : shifted = true → target g ≠ c := fun hs h => bad (Or.inr ⟨hs,h⟩)
              exact ⟨shifted,checks,rel_step f u c g s shifted distinct related gf hu hc⟩
        obtain ⟨p,h,r,e⟩ := ih (n+1) shifted' (transition g s) hc hr tailphys prepared.2 ready.2
        refine ⟨?_,?_,?_,?_⟩
        · intro x hx
          rw [cut,if_neg hitg] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact pg
          · exact p x hx
        · simpa only [cut,miss,↓reduceIte,Prepared] using (show ValueOK s g ∧ Prepared (transition g s) (cut f u l (n+1) gs) from ⟨prepared.1,h⟩)
        · simpa only [cut,miss,↓reduceIte,Ready] using (show Fresh s g ∧ Ready (transition g s) (cut f u l (n+1) gs) from ⟨ready.1,r⟩)
        · simp only [cut,miss,↓reduceIte,GateMirror.forward,List.map_cons]
          change run ([front g] ++ GateMirror.forward (cut f u l (n+1) gs)) [] s = run ([front g] ++ GateMirror.forward gs) [] s
          simp only [run_append,run_take,List.drop_nil]
          exact e


theorem cut_proper (f u l : Wire) (n : Nat) (gs : List Gate)
    (phys : ∀ g ∈ gs, proper g = true) : ∀ g ∈ cut f u l n gs, proper g = true := by
  induction gs generalizing n with
  | nil => cases n <;> simp [cut]
  | cons g gs ih =>
    cases n with
    | zero => exact phys
    | succ n =>
      have pg := phys g List.mem_cons_self
      have pt : ∀ x ∈ gs, proper x = true := fun x hx => phys x (List.mem_cons_of_mem _ hx)
      by_cases hh : hit f u l g = true
      · rw [cut,if_pos hh]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · have h := of_decide_eq_true hh
          rcases h with rfl | rfl <;> simp_all [proper]
        · exact ih n pt x hx
      · rw [cut,if_neg hh]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact pg
        · exact ih (n+1) pt x hx

theorem cut_allW {P : Wire → Prop} (f u l : Wire) (n : Nat) (gs : List Gate)
    (box : AllW P gs) : AllW P (cut f u l n gs) := by
  induction gs generalizing n with
  | nil => cases n <;> simpa [cut] using box
  | cons g gs ih =>
    cases n with
    | zero => exact box
    | succ n =>
      have bg := box g List.mem_cons_self
      have bt : AllW P gs := fun x hx => box x (List.mem_cons_of_mem _ hx)
      by_cases hh : hit f u l g = true
      · rw [cut,if_pos hh]
        apply allW_cons
        · intro q hq
          have h := of_decide_eq_true hh
          rcases h with rfl | rfl
          all_goals apply bg q; simp only [Gate.wires,List.mem_cons,List.mem_singleton] at *; tauto
        · exact ih n bt
      · rw [cut,if_neg hh]
        exact allW_cons bg (ih (n+1) bt)

end ECDSAAdd.Entrant.StairPacket.FlagLeave

namespace ECDSAAdd.Entrant.StairPacket.FlagLeave
open GateMirror Partial Challenge
set_option linter.unusedSimpArgs false

def removed (f u l : Wire) : Nat → List Gate → List Gate
  | 0, _ => []
  | _+1, [] => []
  | n+1, g::gs => if hit f u l g then g :: removed f u l n gs else removed f u l (n+1) gs

theorem cut_length (f u l : Wire) (n : Nat) (gs : List Gate) : (cut f u l n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      by_cases h : hit f u l g = true
      · rw [cut,if_pos h]; simp only [List.length_cons,ih]
      · rw [cut,if_neg h]; simp only [List.length_cons,ih]

theorem cut_count (p : Gate → Bool) (f u l : Wire) (n : Nat) (gs : List Gate)
    (zero : p (.cx u l) = false) :
    (cut f u l n gs).countP p + (removed f u l n gs).countP p = gs.countP p := by
  induction gs generalizing n with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => simp [cut,removed]
    | succ n =>
      by_cases h : hit f u l g = true
      · rw [cut,if_pos h,removed,if_pos h]
        simp only [List.countP_cons,zero,Bool.false_eq_true,if_false]
        have e := ih n
        split <;> omega
      · rw [cut,if_neg h,removed,if_neg h]
        simp only [List.countP_cons]
        have e := ih (n+1)
        split <;> omega

theorem cut_append (f u l : Wire) (n : Nat) (as bs : List Gate) :
    cut f u l n (as++bs) = cut f u l n as ++ cut f u l (n-(removed f u l n as).length) bs := by
  induction as generalizing n with
  | nil => cases n <;> simp [cut,removed]
  | cons g gs ih =>
    cases n with
    | zero => simp [cut,removed]
    | succ n =>
      by_cases h : hit f u l g = true
      · simp only [List.cons_append]
        rw [cut,if_pos h,cut,if_pos h,removed,if_pos h]
        simp only [List.length_cons,Nat.add_sub_add_right,List.cons_append]
        rw [ih]
      · simp only [List.cons_append]
        rw [cut,if_neg h,cut,if_neg h,removed,if_neg h]
        simp only [List.cons_append]
        rw [ih]

theorem cut_of_removed_nil (f u l : Wire) (n : Nat) (gs : List Gate)
    (empty : removed f u l n gs = []) : cut f u l n gs = gs := by
  induction gs generalizing n with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      by_cases h : hit f u l g = true
      · rw [removed,if_pos h] at empty
        contradiction
      · rw [removed,if_neg h] at empty
        rw [cut,if_neg h,ih (n+1) empty]


theorem pair_savings (f u l : Wire) (a b : List Gate)
    (ha : removed f u l 2 a = [.make f u l]) (hb : removed f u l 1 b = [.pop f u l]) :
    toffoliCount (GateMirror.forward (cut f u l 2 a)) + toffoliCount (GateMirror.forward (cut f u l 1 b)) + 1 =
      toffoliCount (GateMirror.forward a) + toffoliCount (GateMirror.forward b) ∧
    toffoliCount (inverse (cut f u l 1 b)) + toffoliCount (inverse (cut f u l 2 a)) + 1 =
      toffoliCount (inverse b) + toffoliCount (inverse a) ∧
    measurementCount (GateMirror.forward (cut f u l 2 a)) + measurementCount (GateMirror.forward (cut f u l 1 b)) + 1 =
      measurementCount (GateMirror.forward a) + measurementCount (GateMirror.forward b) ∧
    measurementCount (inverse (cut f u l 1 b)) + measurementCount (inverse (cut f u l 2 a)) + 1 =
      measurementCount (inverse b) + measurementCount (inverse a) ∧
    gateSlots (GateMirror.forward (cut f u l 2 a)) + gateSlots (GateMirror.forward (cut f u l 1 b)) + 1 =
      gateSlots (GateMirror.forward a) + gateSlots (GateMirror.forward b) ∧
    gateSlots (inverse (cut f u l 1 b)) + gateSlots (inverse (cut f u l 2 a)) + 1 =
      gateSlots (inverse b) + gateSlots (inverse a) := by
  have ac := cut_count isCCX f u l 2 a rfl
  have am := cut_count isMake f u l 2 a rfl
  have ap := cut_count isPop f u l 2 a rfl
  have bc := cut_count isCCX f u l 1 b rfl
  have bm := cut_count isMake f u l 1 b rfl
  have bp := cut_count isPop f u l 1 b rfl
  simp only [ha,hb,List.countP_cons,List.countP_nil,isCCX,isMake,isPop,Bool.true_eq_false,if_false,if_true,
    Bool.false_eq_true,Nat.add_zero,Nat.zero_add] at ac am ap bc bm bp
  simp only [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,cut_length]
  omega

end ECDSAAdd.Entrant.StairPacket.FlagLeave

namespace ECDSAAdd.Entrant.StairPacket.FlagLeave
open GateMirror
set_option linter.unusedSimpArgs false

theorem check_prefix (f u c l : Wire) (n : Nat) (shifted : Bool) (a b : List Gate)
    (ok : check f u c l n shifted (a++b) = true) : check f u c l n shifted a = true := by
  induction a generalizing n shifted with
  | nil => cases n <;> rfl
  | cons g gs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.cons_append] at ok
      by_cases hh : hit f u l g = true
      · rw [check,if_pos hh] at ok ⊢
        obtain ⟨hs,ht⟩ := Bool.and_eq_true_iff.mp ok
        exact Bool.and_eq_true_iff.mpr ⟨hs,ih n shifted ht⟩
      · rw [check,if_neg hh] at ok ⊢
        by_cases gf : target g = f
        · rw [if_pos gf] at ok ⊢
          by_cases hg : g = .cx c f
          · rw [if_pos hg] at ok ⊢
            exact ih (n+1) (!shifted) ok
          · rw [if_neg hg] at ok
            contradiction
        · rw [if_neg gf] at ok ⊢
          by_cases bad : target g = u ∨ (shifted = true ∧ target g = c)
          · rw [if_pos bad] at ok
            contradiction
          · rw [if_neg bad] at ok ⊢
            exact ih (n+1) shifted ok
end ECDSAAdd.Entrant.StairPacket.FlagLeave

open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
namespace ECDSAAdd.Entrant.StairPacket.DeadScan
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Measured replacement for the last exchange in the leave scan. -/
def topM (g a b : Wire) : Program :=
  [.CX a b, .measureX a [] [.CZ g b], .CX a b]

theorem eraseProduct (g b a : Wire) (ga : g ≠ a) (ba : b ≠ a)
    (s : State) (m : List Bool) (known : s.basis a = (s.basis g && s.basis b)) :
    run [.measureX a [] [.CZ g b]] m s = run [.CCX g b a] [] s := by
  cases m with
  | nil => simp [run,measureAndCorrect,correct,known,writeBit]
  | cons c m =>
    cases c <;> cases hg : s.basis g <;> cases hb : s.basis b <;>
      simp [run,measureAndCorrect,correct,known,hg,hb,writeBit,ga,ba]

/-- The sum rail is positive and lies opposite the oriented signed rail. -/
theorem topM_eq (g a b : Wire) (ga : g ≠ a) (gb : g ≠ b) (ab : a ≠ b)
    (s : State) (m : List Bool)
    (known : s.basis a = (s.basis g && (s.basis a ^^ s.basis b))) :
    run (topM g a b) m s = run (cswap g b a) [] s := by
  let t : State := ⟨s.phase, writeBit s.basis b (s.basis b ^^ s.basis a)⟩
  have kt : t.basis a = (t.basis g && t.basis b) := by
    simp only [t, writeBit, Function.update_of_ne ab, Function.update_of_ne gb,
      Function.update_self]
    rw [Bool.xor_comm]
    exact known
  have same := eraseProduct g b a ga ab.symm t m kt
  simp only [run] at same
  simp only [topM,cswap,run]
  change (let z := measureAndCorrect a [] [.CZ g b] (m.headD false) t
    State.mk z.phase (writeBit z.basis b (z.basis b ^^ z.basis a))) = _
  rw [same]

theorem noTape (p : Program) (h : measurementCount p = 0) (m : List Bool) (s : State) :
    run p m s = run p [] s := by
  rw [←run_take p m s,h]
  rfl

theorem exchange_mc (g : Wire) (ps : List (Wire×Wire)) : measurementCount (RailPair.exchange g ps) = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [RailPair.exchange,List.flatMap_cons,measurementCount_append] at *
    simp only [cswap] at ih
    simp [cswap,measurementCount,ih]

def scanM (a b g n : Wire) (ps : List (Wire×Wire)) : Program :=
  [.CX a n,.CX b n] ++ RailPair.exchange g ps ++ topM g a b ++
    signComplement n ((ps++[(a,b)]).map Prod.snd)

theorem scanM_eq (a b g n : Wire) (ps : List (Wire×Wire))
    (ga : g ≠ a) (gb : g ≠ b) (ab : a ≠ b)
    (an : a ≠ n) (bn : b ≠ n) (gn : g ≠ n)
    (ap : a ∉ RailPair.sites ps) (bp : b ∉ RailPair.sites ps) (gp : g ∉ RailPair.sites ps)
    (nd : (g::RailPair.sites ps).Nodup) (s : State) (m : List Bool)
    (known : s.basis a = (s.basis g && (s.basis a ^^ s.basis b))) :
    run (scanM a b g n ps) m s = run (RailPair.scan a b g n (ps++[(a,b)])) [] s := by
  let P : Program := [.CX a n,.CX b n] ++ RailPair.exchange g ps
  let S : Program := signComplement n ((ps++[(a,b)]).map Prod.snd)
  let u := run ([.CX a n,.CX b n] : Program) [] s
  let v := run P [] s
  have Pu (q : Wire) (h : q ≠ n) : u.basis q = s.basis q := by
    simp [u,run,writeBit,h]
  have er := RailPair.exchange_run g ps nd u []
  have vp : v = run (RailPair.exchange g ps) [] u := by
    simp [v,P,u,run_append,run_take]
  have Va : v.basis a = s.basis a := by rw [vp]; exact (er.2.1 a ap).trans (Pu a an)
  have Vb : v.basis b = s.basis b := by rw [vp]; exact (er.2.1 b bp).trans (Pu b bn)
  have Vg : v.basis g = s.basis g := by rw [vp]; exact (er.2.1 g gp).trans (Pu g gn)
  have vm : run (topM g a b) m v = run (cswap g b a) [] v :=
    topM_eq g a b ga gb ab v m (by rw [Va,Vb,Vg]; exact known)
  have p0 : measurementCount P = 0 := by simp [P,measurementCount_append,measurementCount,exchange_mc]
  have s0 : measurementCount S = 0 := (signComplement_counts _ _).2
  have old : RailPair.scan a b g n (ps++[(a,b)]) = P ++ cswap g b a ++ S := by
    simp [RailPair.scan,RailPair.exchange,List.flatMap_append,P,S,List.append_assoc]
  rw [old]
  change run (P ++ topM g a b ++ S) m s = _
  simp only [run_append,run_take]
  rw [p0,List.drop_zero,noTape P p0 m s,noTape P p0 [] s]
  change run S _ (run (topM g a b) m v) = run S _ (run (cswap g b a) [] v)
  rw [vm,noTape S s0,noTape S s0]
  simp only [List.drop_nil]

/-- The sign-side condition needed by topM follows solely from signed packet input. -/
theorem sign_relation (L : SkywalkIntegerLayout) (G sg : Bool) (u v : Nat) (s : BasisState)
    (ha : signedRegValue L.a s = (SkywalkRails.encode G sg u v).a)
    (hb : signedRegValue L.b s = (SkywalkRails.encode G sg u v).b)
    (hg : s L.previous = G) :
    s L.aSign = (s L.previous && (s L.aSign ^^ s L.bSign)) := by
  have sign (lo : List Wire) (q : Wire)
      (h : signedRegValue (lo ++ [q]) s = SkywalkRails.signed sg u) :
      s q = PortalValues.negative sg u := by
    have z := (PortalValues.full lo q s _ h).1
    cases sg <;> simpa [SkywalkRails.neg,SkywalkRails.signed,PortalValues.negative] using z
  cases G with
  | false =>
    simp only [hg,Bool.false_and]
    exact (PortalValues.positive (L.a0::L.aMid) L.aSign s (u+v)
      (by simpa only [SkywalkIntegerLayout.a,SkywalkRails.encode,Bool.false_eq_true,ite_false,Nat.cast_add] using ha)).1
  | true =>
    have az : s L.aSign = PortalValues.negative sg u := sign (L.a0::L.aMid) L.aSign ha
    have bz : s L.bSign = false := (PortalValues.positive (L.b0::L.bMid) L.bSign s (u+v)
      (by simpa only [SkywalkIntegerLayout.b,SkywalkRails.encode,ite_true,Nat.cast_add] using hb)).1
    simp [hg,bz]
end ECDSAAdd.Entrant.StairPacket.DeadScan

namespace ECDSAAdd.Entrant.StairPacket.DeadScan
open GateMirror LeaveJ7
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

def fix0M (s h : Nat) : List Gate :=
  (Shadow7.fix0P s h).take 51 ++ [.pop (s+30) (h+802) (s+h+47)] ++ (Shadow7.fix0P s h).drop 52

theorem fix0M_inverse (s h : Nat) : GateMirror.inverse (fix0M s h) =
    GateMirror.inverse (Shadow7.fix0P s h) := rfl

def lowerPairs (j : Fin 26) : List (Wire×Wire) :=
  (List.range 16).map (fun i => (Shadow7.a0P (start j) - 1 + i, Shadow7.b0P (start j) - 1 + i))

theorem fix0M_emitted : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    GateMirror.forward (fix0M (start j) (Shadow7.sbP (start j))) =
    scanM (Shadow7.a0P (start j)+15) (Shadow7.b0P (start j)+15) (start j+30)
      (Shadow7.e0P (start j)+5) (lowerPairs j) := by decide +kernel

theorem scanPairs_split (j : Fin 26) : scanPairs j = lowerPairs j ++
    [(Shadow7.a0P (start j)+15,Shadow7.b0P (start j)+15)] := by
  revert j
  decide +kernel

theorem physical_geometry : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    let a := Shadow7.a0P (start j)+15
    let b := Shadow7.b0P (start j)+15
    let g := start j+30
    let n := Shadow7.e0P (start j)+5
    g ≠ a ∧ g ≠ b ∧ a ≠ b ∧ a ≠ n ∧ b ≠ n ∧ g ≠ n ∧
      a ∉ RailPair.sites (lowerPairs j) ∧ b ∉ RailPair.sites (lowerPairs j) ∧
      g ∉ RailPair.sites (lowerPairs j) ∧ (g::RailPair.sites (lowerPairs j)).Nodup := by
  decide +kernel

theorem fix0M_run (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24)
    (s : State) (m : List Bool) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) s.basis) :
    run (GateMirror.forward (fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s := by
  rw [fix0M_emitted j lo hi,scan_emitted j lo hi,scanPairs_split]
  obtain ⟨ga,gb,ab,an,bn,gn,ap,bp,gp,nd⟩ := physical_geometry j lo hi
  apply scanM_eq _ _ _ _ _ ga gb ab an bn gn ap bp gp nd
  obtain ⟨pl,pr,pa,pb,pg,la,lb⟩ := scan_ports j lo hi
  rw [pa,pb,pg]
  let L := IntegerPacket.ports (Shadow7.shape j) 15
  have hg : mappedBasis j s.basis L.previous = G := by
    have eq := ready.2.2.1
    cases G <;> exact eq
  exact sign_relation L G sg u v (mappedBasis j s.basis) ready.1 ready.2.1 hg

theorem fix0M_counts (s h : Nat) :
    toffoliCount (GateMirror.forward (fix0M s h)) = 16 ∧
    measurementCount (GateMirror.forward (fix0M s h)) = 1 ∧
    Challenge.gateSlots (GateMirror.forward (fix0M s h)) = 71 := by
  simp [fix0M,Shadow7.fix0P,GateMirror.forward,GateMirror.front,GateMirror.erase,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots]

end ECDSAAdd.Entrant.StairPacket.DeadScan

end
-- ==== end FlagLeave + DeadScan ====

-- ==== CRT: merged by merge4.py from CRTBarrelData, CRTBarrel, CRTBitCount, CRTDomain, CRTResources, CRTBarrelMetrics, CRTLinear, CRTMeasurement, CRTPlacement, CRTShapeData, CRTPhysical, CRTBarrelChecks, CRTField, CRTFieldCases, CRTFieldRows, CRTMatrix, CRTFieldRun, CRTTriangle, CRTComponents, CRTCoordinates, CRTWindowRun, CRTBarrelRun, CRTPackedData, CRTPivots, CRTPacked, CRTBasisReceipt, CRTFastField, CRTPackedActions, CRTPrototype, CRTPrototypeReceipt, CRTPackedRun, CRTSlice, CRTTemplateAction, CRTBarrelCorrect ====

-- ==== begin CRTBarrelData ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

/-- Irreducible polynomial and multiplicity for each primary component. -/
def schedule : Nat → List (Nat × Nat)
  | 31 => [(257,1), (7,1), (31,1), (13,1), (73,1), (19,1), (25,1)]
  | 39 => [(257,1), (21,1), (31,1), (13,1), (73,1), (19,1), (25,1), (67,1)]
  | 46 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (1193,1)]
  | 54 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (471,1), (1193,1)]
  | 61 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (471,1), (4593,1), (37,1)]
  | 69 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (313,1), (471,1), (4593,1), (37,1)]
  | 76 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (313,1), (471,1), (4593,1), (5349,1)]
  | 84 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (4593,1), (5349,1), (5981,1), (6891,1)]
  | 91 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (313,1), (471,1), (1193,1), (4593,1), (5349,1), (37,1)]
  | 99 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (1193,1), (4593,1), (5349,1), (5981,1), (6891,1), (37,1)]
  | 106 => [(257,2), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (313,1), (471,1), (1193,1), (4593,1), (5349,1), (5981,1)]
  | 113 => [(257,2), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (313,1), (471,1), (4593,1), (5349,1), (5981,1), (6891,1), (37,1)]
  | 120 => [(257,1), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (313,1), (471,1), (1193,1), (1571,1), (4593,1), (5349,1), (5981,1), (6891,1)]
  | 128 => [(257,2), (21,1), (31,1), (11,1), (13,1), (73,1), (19,1), (25,1), (313,1), (471,1), (1193,1), (1571,1), (4593,1), (5349,1), (5981,1), (6891,1)]
  | _ => []

/-- Pivot donor and row-target mask for each binary elimination column. -/
def pivots : Nat → List (Nat × Nat)
  | 31 => [
      (31,142755072), (31,428265217), (31,713774593), (31,2141109511),
      (31,1092860673), (31,191362579), (31,490283285), (31,784883583),
      (9,2051728897), (31,1007137794), (31,935396103), (31,1720927758),
      (31,212192284), (31,281598008), (31,1815911773), (31,435763898),
      (31,1185321619), (19,956940993), (20,1913881986), (21,740756228),
      (22,1372460552), (31,202858583), (31,296665262), (24,1567450249),
      (31,2061158674), (31,1633220269), (31,179432794), (31,132244747),
      (31,264489494), (31,528978988), (31,1057957976)]
  | 39 => [
      (39,9160954112), (39,27482862337), (39,45804770561), (39,137413459719),
      (39,150400328705), (39,438852115475), (39,190939693333), (39,501355737983),
      (39,119876064257), (39,227366852610), (39,490416554245), (39,422458454538),
      (39,384263152917), (39,240182217258), (39,229820858689), (39,447293489794),
      (18,442828100243), (18,322981668134), (39,83251317324), (21,350524492871),
      (22,164278737038), (39,127893142875), (39,502370782122), (24,361640456833),
      (39,421322806302), (39,242204426175), (39,484408852350), (39,444831694588),
      (39,490810360391), (39,390030801713), (39,221715854946), (39,57151070615),
      (39,484997762685), (39,58667028905), (39,117334057810), (39,234668115620),
      (39,469336231240), (39,46175027413), (39,92350054826)]
  | 46 => [
      (46,73287667968), (46,219863003905), (46,366438339841), (46,1099307482887),
      (46,1203202679809), (46,3510816660499), (46,5856844742933), (46,17548582679423),
      (46,17726560769025), (46,35354039474178), (46,29418258219269), (46,58836285354506),
      (46,54476273968405), (46,45764483598890), (46,44238484472129), (46,29623029924482),
      (46,33641755349651), (46,67248880952614), (46,53717449198156), (20,9407854682925),
      (21,18716627322458), (46,46750015860633), (46,39692066600689), (46,3003240115682),
      (46,39366946062551), (46,14377833726382), (46,54525419117025), (46,45897639113666),
      (29,55271457537337), (46,50683955870322), (46,11981799437231), (46,54112964390531),
      (46,13202960356571), (46,26405920713142), (46,52811841426284), (46,16043033610457),
      (37,62851476291507), (46,1970320376021), (46,64374036561433), (40,67513654771021),
      (46,15762563008168), (46,35507511291933), (46,29769416108733), (46,59538832217466),
      (46,2129655461129), (46,4259310922258)]
  | 54 => [
      (54,17665473712384), (54,52996421137153), (54,88327368561921), (54,264982098149127),
      (54,300270365434881), (54,900712304925715), (54,1501192658518293), (54,4503556024005503),
      (54,4535963436684289), (54,9050868350900226), (54,7531660972441861), (54,15063321713799690),
      (54,13938971670570261), (54,11710689501104682), (54,11326739613942081), (54,7589177787744898),
      (54,8619728056652435), (54,17207741804782886), (54,13744630079834700), (20,2397547110212397),
      (21,4794995138381402), (54,11975832701939609), (54,10159940686034673), (54,771561867931106),
      (54,10066912991379671), (54,3685028683579822), (54,13965271655832033), (54,11742639774348226),
      (29,14159463021264185), (54,12972694361307762), (54,3067936929887151), (54,13858618890071683),
      (54,3383206099490011), (54,6766412198980022), (54,13521210806391660), (54,4109868421204185),
      (38,16088920645894067), (54,16005399636737894), (54,594007939940735), (54,1751529552020353),
      (54,14226242699066341), (54,4923410169137965), (54,7884680484940477), (54,15769360969880954),
      (54,16997179059372905), (49,3966386930812347), (50,7932773861624694), (51,15865547723249388),
      (49,17579245112834141), (54,13553733465007423), (54,471566695885163), (54,943133391770326),
      (54,3119998644732787), (54,6239997289465574)]
  | 61 => [
      (61,72075259511640320), (61,216225778534920961), (61,360376297558201601), (61,1081128892667068167),
      (61,1225279369010209793), (61,1586167781139340307), (61,2235286607834284309), (61,292733932175717247),
      (61,869227091891819521), (61,1738433125261170690), (61,1824048015360704773), (61,1702540991466271242),
      (61,526434535516497173), (61,1052869036167776810), (61,1974931361519567169), (61,1427823949339492994),
      (61,1666542525254505107), (61,811037544873010470), (61,1622075054818478668), (20,1547906275484246829),
      (21,1150257412862395994), (61,831296713348525977), (61,1329239642482390769), (61,136460092828511714),
      (61,1243050456286363863), (61,540545770201022894), (61,1876062980085176801), (61,1230089484280378306),
      (29,1383324118486072633), (61,244609008008133234), (61,1629606274224501679), (61,2079709026085842563),
      (61,603118420539675867), (61,1206236841079351734), (61,388956053180273516), (61,1679185047012362457),
      (38,1593509874504499123), (61,664998735001288550), (61,317587608274272639), (61,916703533536052097),
      (61,2156338776397380581), (61,1892916816455863085), (61,1444427408499862205), (61,943299777975670138),
      (47,1349816378156417897), (47,1428651981551797691), (47,1226030270350592031), (61,1500911959417197957),
      (49,1829114054973046415), (50,1712673070922038558), (61,790772725765897454), (52,1284778788492263537),
      (61,2153233725390109359), (55,691075857540920781), (55,1564583786190334840), (61,609655366782309906),
      (57,1599310175947738905), (61,2112799978854863147), (61,141428699037266813), (61,282857398074533626),
      (61,565714796149067252)]
  | 69 => [
      (69,18451265338810634496), (69,55353796016431903489), (69,92256326694053172481), (69,276768980082151980807),
      (69,313671510717093110785), (69,406058953914910956563), (69,572233373445981110549), (69,74939897755841688447),
      (69,222522122630508286977), (69,445038879545190963202), (69,466956305163592450309), (69,435850500064550285834),
      (69,134767229533552993557), (69,269534459032240769578), (69,505582421852822110529), (69,365522942829070713474),
      (69,426634892735609344659), (69,207625616984789034278), (69,415251218060451400268), (20,396264007067711709997),
      (21,294465907072472729178), (69,212811955313309036441), (69,340285351370296899313), (69,34933784434913013218),
      (69,318220905784108515543), (69,138379721474711486894), (69,480272132002629343713), (69,314902907004691002306),
      (29,354130978873487637817), (69,62619898154182474354), (69,417179212776340861871), (69,532405519126760861315),
      (69,154398317875613078747), (69,308796635751226157494), (69,99572744808798376812), (69,429871373100275321049),
      (69,407938531351352508339), (39,574714541517469319381), (40,503793040455104332202), (69,491541232977193860146),
      (69,266601469618074482865), (42,69204937639960441271), (43,122200628572642468718), (69,525720440017673860159),
      (69,378205589443678747771), (69,472622676577611138189), (69,426795467651958147354), (69,164272018482993964885),
      (51,358714146550913268683), (69,5052207741057090295), (51,301803095899936377668), (69,112623690923517846505),
      (53,498017382454737480337), (69,205117429968752410547), (57,235355817598989260279), (69,174833677295175335628),
      (69,508318476647640859476), (69,260630491289685395069), (69,500063790655585186891), (69,354491538731336067222),
      (69,63347034882837827884), (69,126694069765675655768), (63,489625266221317444059), (69,542567576929984964358),
      (66,369833387705514867809), (66,223157941347162290370), (69,335000486915934816582), (69,63935759724572157867),
      (69,127871519449144315734)]
  | 76 => [
      (76,18451265338810634496), (76,55353796016431903489), (76,92256326694053172481), (76,276768980082151980807),
      (76,313671510717093110785), (76,941014532052487953427), (76,1568357553426296897813), (76,4705072660256939144063),
      (76,4741974420689348432897), (76,9483943475662871255042), (76,23709853838037627486469), (76,47419707655802778251786),
      (76,9155225081577523733781), (76,18310450163120182250026), (76,29227162944618593976641), (76,58454320030940448752258),
      (76,8063586939251363713683), (76,16127165752596132078886), (76,32254331489283137489484), (20,73039542169335925973805),
      (21,47444343759474086659674), (76,73280365231276842987417), (76,67929155637442094020337), (76,38404161457750780374498),
      (76,13655216871076114333911), (76,27310433742048881017262), (76,38277650739033500604897), (76,22783037188782924870594),
      (29,48057411153486388116793), (76,3530607784011578178162), (76,56310813756116282258351), (76,39823970396128105803395),
      (76,72797676480143827342555), (76,48141204018880093497782), (76,2497649474391040086892), (76,22768878446362542328025),
      (76,58884117245010631131059), (39,2013560579266814345429), (40,4027121158533628690858), (76,64372615960233371106354),
      (76,74570086598520148392113), (42,52476404851048796582327), (43,13532983570159486493550), (76,71176750242325256549439),
      (76,31774564002897335598203), (76,55757514665485137331341), (76,16401675835484429846810), (76,15087687974114021222229),
      (51,17145251253626605239243), (76,11829415158988879676151), (51,15944642070405636148036), (76,14224382907311324832745),
      (53,16085516124739308595857), (76,26731535407963087634355), (57,38770604187578242586103), (76,10652584311162200653516),
      (76,31941570378248716813140), (76,16475318532080381265533), (76,36711022407347435009099), (76,73422044814694870018198),
      (76,56621064364876323082540), (76,14754962120217350087256), (63,46717165914937453793755), (76,5080466619062534661894),
      (76,61059621390209939684449), (66,8653002517364361151651), (67,17306005034728722303302), (68,34612010069457444606604),
      (69,69224020138914889213208), (76,47444175990211082590186), (76,52603013291220163143681), (76,404611018314335236659),
      (76,809222036628670473318), (76,1618444073257340946636), (76,3236888146514681893272), (76,6473776293029363786544)]
  | 84 => [
      (84,4723519685922516439296), (84,14170559057767549317889), (84,23617598429612582196481), (84,70852795288837739052807),
      (84,80299834660640091792385), (84,240899503981821483998227), (84,401499173303041290305813), (84,1204497519909101919368063),
      (84,1213944559280978355000321), (84,2427889118561857627936770), (84,6069722796404569820938501), (84,12139445592809139410792970),
      (84,19334041826724693585257749), (84,6154590418891845009001002), (84,7030248303274591848431937), (84,14054221254799509842363010),
      (84,12037569389370796016702099), (84,10885569192086638321804582), (84,10772746845569838013368908), (20,14268512691570668119401261),
      (21,16254148656150589484058202), (84,14228085502686224375525273), (84,14312182974343818477287153), (84,16051401507015720862445026),
      (84,8409144491018399342002391), (84,16812151980867673089900974), (84,12403765390380070013295073), (84,17450457679438672897356738),
      (29,16075788249978037434039609), (84,544776217386627047062130), (84,16744526659604149686383535), (84,15656822214179113121689219),
      (84,17715865584647977792902363), (84,9246207534751470913464758), (84,18486258190548043249242988), (84,2679222750513646625999065),
      (38,2600270084031491141730227), (39,5195564385436455383990118), (40,10391127952625153470103244), (41,14336224781590488583503256),
      (84,14775359207951964529297367), (84,3154217397656216386277294), (84,12456948865874509256793055), (45,11342036929220509579401041),
      (84,18407600983480158194716237), (84,13186415396107782087027492), (47,13194458770848826213446433), (84,8570760639095529371650272),
      (84,14477400638124528915858595), (84,15834670998895104536381766), (52,13451865764700055837038127), (52,8853672162351238907750653),
      (84,12042299172777056980252935), (55,189716806017641307855237), (56,379433612035282615710474), (57,758867224070565231420948),
      (58,1511477543135629104303144), (84,17317894229833351400119937), (84,5691610416661252052930525), (84,10965483925032186100544821),
      (84,4067037692971338288072463), (84,8134075385942676576144926), (84,16268150771885353152289852), (84,17125386973697583510463307),
      (84,8159699129540377215256214), (71,7142598996391487284760713), (84,8078797159695418021981246), (84,7002120754038922741155289),
      (84,3639805434277454061524503), (84,17618064845174030754181515), (71,18556744347851515893235379), (84,11064875540211340330922058),
      (74,10978273351732659907218811), (84,2213750825388493849548685), (84,13803284712153781746349548), (84,17239659814561012727878479),
      (84,1117406153847370950225703), (84,2234812307694741900451406), (84,4469624615389483800902812), (84,8939249230778967601805624),
      (84,17878498461557935203611248), (82,6383596243852950107081263), (83,12767192487705900214162526), (84,7918438375802218237709404)]
  | 91 => [
      (91,77390146537475029290520832), (91,232170439612425087871562497), (91,386950732687375146452604161), (91,1160852198062125439350275847),
      (91,1315632491137075455251178497), (91,1703131152206474518707493907), (91,2400114823097218689302692117), (91,314303000766728266830148479),
      (91,933310808572925683286381569), (91,1866621617140485650747152386), (91,1958560203050008775318880517), (91,1828096589805918064268767754),
      (91,550973719688627506457699605), (91,1101947435238446920496695850), (91,2118952430133144686258749761), (91,1529911020473084043034690178),
      (91,1787795917203234575483966099), (91,867597998461573893030749478), (91,1735195991631402314774497868), (20,1699588792043386255177032493),
      (21,1209151793457060251838465626), (91,926122870628524214902501273), (91,1462241999742118376518432497), (91,116697110027091147184106978),
      (91,1329294235308670317432799447), (91,569564650112395666034262446), (91,2050848877916152318673082849), (91,1338641122561152744525771714),
      (29,1519264585270020743395523897), (91,235729101164528849740855922), (91,1759829826274435372692157359), (91,2207174814417320173453520515),
      (91,693514839778725513920713947), (91,1287236631041449685185604022), (91,389413856075380123620889452), (91,1802854136198340981696874713),
      (91,1762464891658501295641919411), (39,2400570711075060625663000789), (40,2093147586213351899984167338), (91,2077570126762735782521863218),
      (91,1159557304962885669444450481), (42,285849595688275368814768567), (43,478085286016436749361603438), (91,2239280062995735932844454975),
      (91,1579962202130325967746546811), (91,1991377008009748440801592461), (91,1796334121895462481217685786), (91,634419812952794182034007893),
      (51,1487610535973459782455098315), (91,12113320914613492572472055), (51,1254267350529772956356954948), (91,478793283472829535629255657),
      (91,2028124133887957990781987473), (91,1348233407162588619760686370), (91,2316210069625366803893256405), (56,437418107647460899460066107),
      (91,1668887357812960348531677148), (58,61060507926459908240724725), (59,65982634520895915181516266), (60,75844665759368966643469268),
      (61,56731986281195107329939368), (91,805431882766258400838111813), (66,1603568158462486604153659577), (67,1024515196940417626279592306),
      (68,2049030393880835252559184612), (66,517782799868245699655026270), (67,941817180318563202527759548), (68,1883634360637126405055519096),
      (91,1741732865516861024831759522), (70,2182946254735088236096048841), (71,2276868693176097258299825554), (72,2464713570058115302707378980),
      (91,764900902855210521156814445), (91,821584066445446071478030207), (75,393092723400693963284408265), (76,786185446801387926568816530),
      (77,1572370893602775853137633060), (78,1055717970911472492382993992), (91,1447280573937855155181495569), (80,1555998371209801197097393897),
      (81,1022972926125523180302515666), (82,2045945852251046360605031332), (83,1383897868565323369868228424), (91,1168284370448108749159939543),
      (85,2138509794414460862201696783), (91,1577240520465433932243585678), (91,338963933076459809580196621), (91,677927866152919619160393242),
      (91,1355855732305839238320786484), (91,187918802079263198416616293), (91,375837604158526396833232586)]
  | 99 => [
      (99,19811877512724464450679673088), (99,59435632538173393352039019265), (99,99059387563622322253398365441), (99,297178162690866966760187559687),
      (99,336801917716315895618866766849), (99,436001574920531239204615281683), (99,614429394639010920422321848597), (99,80461567974651249788661101439),
      (99,238927566771496685111739126785), (99,477855133542993370124396189698), (99,501391411857670412400640442629), (99,467992726744056546044628136458),
      (99,158447343230528679837124879637), (99,283600869388870409014777334314), (99,541989071233837451942107218241), (99,390725294507670326217041314434),
      (99,467888405511735631084160848531), (99,229024269766923671050364986662), (99,446786186598317375928854530636), (20,430558810196056082434240160557),
      (21,313749857652389462796130862682), (99,232447006468977647622599126937), (99,371182406679917587072947828465), (99,36243675771750136102890991074),
      (99,345330654644426254234619871447), (99,155864928028371086576391553454), (99,527684512102467408962026002913), (99,354588959349368618487008310210),
      (29,392795379110733147671048469817), (99,59978972732302171368953182834), (99,452901289127888492824011092911), (99,570629723547169797630513720963),
      (99,176597371387208208617457259739), (99,326380766572642864930438392246), (99,117965131529951634960904115052), (99,458305458553545899201910655193),
      (37,438417570394502123665555652531), (99,621961297650071537852725788885), (99,275997705340077453063407074841), (40,611161657283974282943704661325),
      (99,67496842240019383025036428968), (99,476284407877770305081217445917), (99,396519713298800829161188944573), (99,258249329626317379565956224378),
      (99,436453289679940679294152045833), (99,179660157360068404644794526226), (99,459007014632686259877949202891), (99,563691717413796745582414668381),
      (99,213508215864237340099913426289), (99,398751746065884650095196457698), (99,262707713903710393127245092292), (99,411658712702810050480822490469),
      (55,68222777023757484624706802727), (54,171906405665351260643506919075), (99,590076072675042834932459767692), (99,29784136267695187577595894963),
      (99,340088345042622256876303417351), (99,145382018321429955027384401934), (60,598002493024554701790588971099), (61,502758564049296449637668376758),
      (62,470727031127308620518915088748), (62,572137188227567380692783457204), (99,211675440553621561982951056900), (99,359890910857729208728687251513),
      (66,482421861528789546373637272211), (67,430050968574556579098008872230), (68,312134548744029421435298761292), (68,623630249529613235637395567850),
      (99,89468639774689986590101200190), (99,11897694427265949551172014213), (72,597779983008826897943951533335), (73,502313544017840841944393501230),
      (74,469836991064397405132365337692), (75,235184550006565804996453673144), (76,437133311380286224721885155696), (77,181020200760759495500260745952),
      (78,362040401521518991000521491904), (79,30834381043225028057533418368), (80,53520602062247455477547210496), (80,248177353995335369018330181274),
      (99,335470773738956760927001648558), (99,141367364432043271767590022593), (99,270850238030175799971462830147), (99,462624712438122873543540172997),
      (99,232003002876432793143570780554), (99,543396239155981627014454803287), (99,393546056312150300085400041134), (88,291918435210072992489213343007),
      (99,629107919250722020064979027810), (99,183297862183274985877625393637), (99,366595724366549971755250787274), (93,130805594360769222967754481541),
      (93,231177663413604521971073492763), (99,342374170308612465768070174247), (99,445617365147588737903154970109), (96,584426308349639636247192815111),
      (99,356362535333596874928828774388), (99,148038377919297011724088583649), (99,296076755838594023448177167298)]
  | 106 => [
      (106,19811877513593607498373332992), (106,59435632540780822495119998977), (106,99059387567968037491866664961), (106,297178162703904112473670615047),
      (106,336801917731091316544301694977), (106,1010405753193273924342312075283), (106,1684009588655456541974332506133), (106,5052028765966369620303400861823),
      (106,5091652520993359652525880705025), (106,15274957562977965039741603610883), (106,25458262603974068588447977963781), (106,76374787811313453235251789432591),
      (106,31936319370592269235174626099473), (106,54922583522773658108100132148019), (106,41226813499223589490804400657749), (106,77301015565765408397718179512319),
      (18,31048933364384784461466969571329), (19,62083494546213151132147736117250), (106,76729122311387695990377067577348), (106,46267318321488587305596285353992),
      (106,62704666827895176125158368018453), (106,80649624060023381636192301350954), (106,43492062455883715458356047249492), (106,32876996102242458804284429959336),
      (106,8336720180081403032102044369299), (106,16648241509079410726748501181222), (106,36536649411136298927894864791519), (28,80117740126544856215656938147373),
      (106,35681522860347963820971518268023), (106,46182393204328141751275086231193), (32,23876505416946879789392270018545), (32,70347005211230749258789774673939),
      (106,6277017403890190204107253635125), (106,16567957624405111072521765840991), (106,33135915247437092633056776933566), (106,66245968909358523629410746343804),
      (106,52040802057749423272980822787129), (38,48658838652276710552086918433867), (39,22441937448466648471674474666134), (106,13180190267100508244436420179221),
      (43,583534650745962517363349245915), (43,1167069301491925025930605469622), (43,2309249238207668527807755927404), (106,4602888468513211868743894728408),
      (47,5819639097738612931768100408499), (47,11625220805041155505408227055974), (47,23225513558382510740154933916364), (106,46435379215292940948542023427480),
      (51,77536534766982931730413790526333), (106,58382666233058537571307640876956), (51,67722636782416465587983101934883), (106,79264165678843194204058055140128),
      (106,54475077782387048154780822062971), (106,43731015723993266215758874233229), (106,32403859981134855967157290177306), (106,64783449567515128639003179165236),
      (106,75132649447978412472195058650216), (106,55765902635691009774437069527248), (106,13387918955777536492137878204832), (106,26751563266496563959088029000512),
      (61,71252553137150665864338864159633), (62,57196177811444372085123028514594), (63,9251811127324129627631494950468), (106,63233732607802719657564726626653),
      (106,10272242989433298649816741508515), (106,20529151963770605343181509880646), (67,69487060580959701079790006768865), (106,48680714211583605856777101306799),
      (69,49973438126482053145637378507711), (106,44969516884556437391925185326780), (106,59931636811514217790700109175225), (106,5065868366008390859366312981362),
      (106,10117369857576481465620417767140), (106,20220024670076613664926311960008), (106,40425953265096520753675549907856), (106,80826668994782766508699933685536),
      (106,44311308296168161472177221561920), (106,1554985159540181656736183068855), (106,3095874244023656737295292125550), (81,39556713179673170501824466290565),
      (81,74210746449390330844349342658006), (106,56441010520953694041224512141680), (83,64874374222011140610081987899081), (84,75021895187294190027423492103570),
      (106,30430508858355836576477921318381), (92,70993385706968114330714297030785), (93,57628585376873275208702672941314), (106,56653420962083480487447077706016),
      (106,5180207132824706244105049190976), (90,49534150971488127611748122652132), (106,34853195365934509712731124252488), (92,74461113240420411830682587009085),
      (93,50778340166295875467362605539450), (106,46296929980954586919157458930433), (106,11535195431025123750393655864845), (106,23070390862050247500787311729690),
      (106,46140781724100495001574623459380), (98,54294026642786054996637791664715), (106,36787627504744922538837845083390), (104,20594078795510955562441098245047),
      (105,41188157591021911124882196490094), (102,68369198930779997875350854884644), (106,33963318605386945320935786654128), (106,28860415363481044708837499616755),
      (105,57313256547917288687598638057553), (106,24674198861587237142729562920729)]
  | 113 => [
      (113,324597801168477628881551882256384), (113,973793403505432886644655646769153), (113,1622989005842388144407759411281921), (113,4868967017527164433223276304465927),
      (113,5518162619864119690975453953392641), (113,7143449803497983996189546670456851), (113,10066811201765555208546097479876629), (113,1318282329696686941931787011686527),
      (113,3914589253984202363211052632834049), (113,6551470903417777347184825530777859), (113,8214796891876071702700069086298373), (113,4848758902464184764352030274488079),
      (113,6084278699932300540841614758707473), (113,6305743861683255938773511271813939), (113,5419167348373224491686248638125397), (113,6969143120352733682103289349373951),
      (18,8613557693449779118158425384812545), (19,5754481299986175528669798193430530), (113,2545913476854362451705545818636292), (113,4581413680315383239251742287724552),
      (113,464734408172359599476630083665941), (113,929425105690816490019154146492458), (113,1324658121793227901752666496434260), (113,2649263404593477751773860410687656),
      (113,10340709456365053482911387413053843), (113,8787924815968035651587770329465638), (113,4205466546578841198027511338829791), (28,2465420972936955103224675431157293),
      (113,2930526120314776981671486300820087), (113,8772504166222769011120581104973465), (32,2119297435993878150770905240913905), (32,3294375695590387521003089695066131),
      (113,9871518266527087972358582762231861), (113,2512182756648410801313130364069983), (113,4813539372846364200289840276295870), (113,9092684764278560838372017034207612),
      (113,3267578699509048841135050988356665), (38,9800095852436533676478316962352203), (39,8241969205988430028731975754258582), (113,9687557214548715126197304008422677),
      (43,5038040195977612825504450828816347), (43,9940996374868404955403113129287606), (43,8410309390502911434755548538421100), (113,7620565306442785381874477209386712),
      (47,6179643903028896089969754048384179), (47,1001138414284935980007416813754726), (47,2002276804226072736740425388602060), (113,4004553593170991008669115490133400),
      (51,1589868028283461613170129853578109), (113,3720849210479888826492930526572444), (51,5554277240287469361363121503681827), (113,1357414286606171911050255184749344),
      (113,3732808847015196605077642523101051), (113,9471056481187716009694996953516429), (113,10180058245852337298904484124463898), (113,9001967089958181782875758201218612),
      (113,6434905502974010714437442055326824), (113,982245989578626787041625853171920), (113,1964396135518274526282281000710560), (113,3928792247330842310546732631614272),
      (113,3209681674186784336873337757186961), (62,8937755222665544260784795126287539), (113,591526496303294297797311970209348), (64,3319563304714652874678774877915485),
      (65,6639080747619412848785178102338234), (113,6627113532347049044598595487708495), (113,2572097490245667020650850164499395), (113,4691247561933817980618051060680582),
      (113,9382419706239305122209667251277580), (113,9568853122484323200013719762050584), (113,10375619331766439724793391541009456), (113,6445266495147945684973542907059455),
      (113,3759109284371517441167774138522977), (113,7307309892509020750036112285153986), (113,3131527594688111202276745040459140), (113,6127971172289401708956497645595400),
      (113,459664574136654886903792112358928), (78,291652220333501764539119691531461), (79,124969520521984336099587630369162), (113,837299492828660759402315595788923),
      (113,1302121133488112349253810334984633), (113,4138210815066024420462691719719391), (83,9381004886652285925957924813383955), (113,1724558065195638159084896201933208),
      (113,3639088738703064579147332882593797), (86,9527441514486796616429848401610767), (87,10292882080196071609714484247662622), (88,9007915087695152773871610400874556),
      (113,1703978902262887819495887087972466), (90,7742437764008930930844521570658539), (91,3602473398616039302422102101774806), (113,1661852587155069473044442911990740),
      (93,3840932960923064135177437316386031), (94,7146204315087187083884923984550366), (113,2997134290707896004776642123762126), (113,8332692583727353666845636049706867),
      (97,2377966624625064854405611817341481), (98,4755933249250129708811223634682962), (113,5930937118419828885382432088812790), (101,2228910533521214428080822805711813),
      (113,5500117762791927148690456406122286), (113,10208554273171588465024680739093821), (103,6623082226638701782651114197194857), (104,4484163504499881942157015838830802),
      (113,7143661679605859871152787775419950), (107,5368998871471774136069120279266535), (107,10227456584553893170791357279430762), (113,358546546622201782169998602514800),
      (113,2787403718878303160785438125061843), (113,5574807437756606321570876250123686), (111,3830372024954114868341824587836831), (112,7660744049908229736683649175673662),
      (113,399431943774349166172822200064913)]
  | 120 => [
      (120,324597801168481087644969533509888), (120,973793403505443262934908600529665), (120,1622989005842405438224847667549441), (120,4868967017527216314674542995111687),
      (120,5518162619864178489964439381992449), (120,16554487859592535469893219354598419), (120,27590813099320892449822037741306133), (120,82772439297962677349466091272369023),
      (120,83421634900299639523985785127408641), (120,166843269800599279042605854429206530), (120,417108174501495984744475809147044101), (120,834216349002985047348217686308123146),
      (120,1328625237524457269687613319896458517), (120,422940233110646521334389345706691114), (120,483114984725178816487629552255172929), (120,965798730561792488329301466647691906),
      (120,827215469610852927729456267831317139), (120,748050618853717494176551820671395110), (120,740297526236951900648024885562067532), (20,980524725965711069019291984153944877),
      (21,1116976590439825284716204092671411802), (120,977746590699666932786405919730085785), (120,983525724946794842242660464614422257), (120,1103043912441563518486333141403266530),
      (120,577872009220201825078906095819686103), (120,1155322286931333276290478269033873838), (120,852380267183024191265257718659471841), (120,1199186320534736447141649072462083010),
      (29,1104719756657226986939966591753239865), (120,37436736597024869258436403786644082), (120,1150675110239999055939906920444736431), (120,1075928629906971066602097217835970179),
      (120,1217425012902320941950089986486506715), (120,635394543580584003502204959314028982), (120,1270365989661053564058140654904824684), (120,184114785474485593842294084273817817),
      (120,178689199546917256845622194926714803), (39,533048267929781939721802249597288661), (40,1065835795976722513367870486544777642), (120,586583119641529891186434583787338802),
      (120,702574824046644602060016264072198321), (42,1031019109990749938474025176307003831), (43,184698291206863987354050680570372974), (120,942686225105405476845910612695397439),
      (120,537981044534592967464720480481754235), (120,875933312892399016534856914009834637), (120,1328369813526964178595933487256013082), (120,1045321417911074062220641604246579029),
      (51,853434771867163432538395575980751819), (120,655958808910790600776625052451848951), (51,1000778315878025271567824414991698756), (120,953155533237478296093264035164365801),
      (120,384614082530334429713188547894946449), (120,769228165039139590630974383260652834), (120,1063958237712950894560863346582946005), (56,651142489054673893412179835840736059),
      (120,1068206660438299365346887660433135580), (58,926708744831857019834109364617106165), (59,1050544348585973780297786558829864426), (60,301633259668471104459824565514750932),
      (61,603266422100618467454820487488772008), (120,189985363238027944880088645626057285), (120,786442408599560548258171200761274553), (120,666504400987496269563186665347432818),
      (120,904052080631075133849095642505446116), (120,1259724612153727104173249698950612424), (69,1260017471668645311205218924045887679), (70,394291131701672358875909718227472766),
      (71,788582161370005542277117091253691132), (120,670395314575252705013787268222787350), (120,1159318906754338235492068537612178283), (120,84327512691570081711224647223224022),
      (74,434684186095828907117763200725180651), (74,1271316567633126020961467494828515645), (120,107125885222945182247220791554810513), (120,321331207931226835761160509809846195),
      (120,642662415862453671522321019619692390), (120,1285324831724907343044642039239384780), (120,341100479481516359026263713418788248), (120,682200958963032718052527426837576496),
      (82,1246989415601326762670670508120610477), (83,409988261230861753419880345090141530), (120,278391492163555201384388108547304660), (120,35990867700797352923089883261375921),
      (120,498643110992184472846951485608454011), (120,831018284612332857861671653397932429), (120,1239658954495932821039833508242346778), (90,1315891433909463856569706797055709781),
      (120,205808649493294159021040129597342366), (120,544652014450865457515648935435863970), (120,495787311657035476439505826702310181), (120,759608832288472083450285132528282459),
      (120,717519059266017846063099721303578294), (94,1281535481953152700160789207594939435), (120,78237149571332489527503717197771025), (120,892495988894908790470337223575748191),
      (120,90960494948628145591639894180702903), (120,181920989897256291183279788361405806), (120,605069994785510655729664520901219589), (105,1139912015882854253580374597069362643),
      (103,224536625193163070057418577167832191), (103,523925629731390070169483565138237223), (103,298467425862066973533304338562658274), (120,809494032221720549593715863053989326),
      (105,1127112300485897500399076383058021249), (120,718403129585604317023488415059959771), (120,522875981251855216832631761581397697), (120,1045751962503710433665263523162795394),
      (120,339624879139129434087803211194345059), (120,679249758278258868175606422388690118), (113,1216214264207311332529218355154534383), (120,308600741535890755516277023722756541),
      (113,863436057748421063645299702045300008), (120,833638945542492830853006117072931891), (117,1183631176226757176399646678794669529), (116,1250886088250763090428448836406864309),
      (120,172098180909298773555654999476776116), (120,771597167852518016019867911777187845), (120,327484468595444761068927878069202617), (120,654968937190889522137855756138405234)]
  | 128 => [
      (128,83097037099131158437112200578531328), (128,249291111297393475311336601735593985), (128,415485185495655792185561002892656641), (128,1246455556486967376556683006748590087),
      (128,1412649630685229693430896481790066689), (128,4237948892055689080292664154777190419), (128,7063248153426148467154441661774364693), (128,21189744460278445401463319365726437503),
      (128,21355938534476707718140360992616677377), (128,64067815603430123152307165141811527939), (128,106779692672382972094585807141643485445), (128,320339078017147053882019019975160497935),
      (128,254746017483320070081121277332647117073), (128,146686704010551368255982348069440262963), (128,237890950752786517893279360872318571861), (128,161746511227279495389693792665414369279),
      (18,184628332022394778585052240598248194049), (19,249210745958350792615070048113245290498), (128,287607201459471515457802694079742476292), (128,40007294357245757623537266722964766728),
      (128,147026979862801452515056704259459710997), (128,294008125782976379828450375748297556010), (128,27875247033701315284260988524130730068), (128,55695088367501676997079766616261525672),
      (128,294266384368350522081251964342380986771), (128,27183144963159727074747546986426532646), (128,326362886494194080997284074212525279199), (28,203204693671771369998910916820044942893),
      (128,10338054846741358302081914608972927607), (128,11013421735867777569818313872861902489), (32,180550226719086472059340760398043367409), (32,51579620170001698510270110132964935699),
      (128,142566130213753154433824736405762627637), (128,252237977788794617343992316010113591391), (128,283408724528610412202540708320597627070), (128,6464745601878658696555183017179718012),
      (128,23480933207016837772388062771829965881), (38,67674300936337655747748860113830513739), (39,135271929115063421058368198539609053334), (128,289951353095418730989579338328755713301),
      (43,178532532723344727746568389869828558811), (43,215419207145857585718802134248073437110), (43,311789406432519114761292410432014729068), (128,164247447586965146416089633866288889560),
      (47,14461313764596719896167389473040321715), (47,28922613134426023276274684215058667878), (47,57845200742526658398272303227085337292), (128,115690385461603540612723309870154671512),
      (51,305967989941604816910238617192416508797), (128,158487145597836551555288309788142235548), (51,39281573855719653715027526901644868899), (128,62222575308599973036266487697561674528),
      (128,171027733437483614576940515492484794235), (128,62933880110675567460703583366632655245), (128,125811380653769078804707661623977218842), (128,251622736454652081290234501624446658100),
      (128,282122501188645800379073440765145926760), (128,9112470005583464740411739426811844816), (128,18124440671580195694271149370293957024), (128,36248856485924593893338790563796902720),
      (61,303053868903636654568302588813760347025), (62,140042892192177772915089315045392414498), (63,279978120466792087664886992779216219716), (128,77990742595080873980895031621523867997),
      (128,209031621113999499628342670611059897763), (128,196995995476988719848607522688753331014), (67,175944633942325611638369332040406078689), (128,218790931107708192980362490337575234479),
      (69,132641665380186860929443852723334595519), (128,129728855124056254074929804502672060092), (71,137470314060362167652290989835126839737), (72,274823075577741146778786616951155733362),
      (128,337546047482063443605532475621330408854), (74,276192931325086506342369693537452484355), (75,65417625481551985983972356542207479302), (128,210790999959607971904665700082151529963),
      (128,82726844284321100930449987472047292633), (128,42862640861636022962226903129155722599), (79,37509908609722807548192767255096485403), (128,133205647649652267199364279327022518499),
      (128,313966512235108474501841590453274840043), (128,157967851210512630690130897156180350934), (128,315935702421025261380261794312360701868), (128,156814459599624601224215777794388680536),
      (128,313562317970666287261085250609964695216), (128,161479437332072474385677482846627921248), (128,333110036747808854344845866858186581293), (128,111532576601368918758288706603839854007),
      (89,233601356725273853142349933597393187971), (90,321489603269487735456603361086026082566), (91,102506799834336941996647207457387565580), (128,194488403623649815448075212909635828725),
      (128,4351339137586874039178329513664257147), (128,7695550706811493731544912742294693005), (128,11658698561360746225985024181391021409), (128,23317397122721492451970048362782042818),
      (128,46537702350670304357620661233657927044), (99,135921167921794620584621406511487181559), (99,314726871426812692189021371597738052625), (128,116269737583925375722385360747768533469),
      (128,254688390386148051620984259977866860911), (128,278562736376234453649074136901107495646), (128,18040443711948963593598022917267744188), (128,135162084178140879327306439435914654277),
      (105,241600145797815881306806096801825922487), (106,262133060546652941501297781890777037678), (107,48984035850461901197428051790063367900), (128,76192508692637101400211982224380021601),
      (109,265046811268205267262633904166681774965), (110,43180792330448538832191984564419827434), (128,12353367145759861277881347128413438060), (114,241192959705172640389376017496630538387),
      (115,260986381362420230698211671515316183334), (114,31681365028003513336064890448741219885), (115,63362730056007026672129780897482439770), (128,86568886180473916372051921266751666319),
      (128,95417955702511482875771597708340413795), (128,190835911405022965751543195416680827590), (119,161554037930366058450656841943011056169), (120,323108075860732116901313683886022112338),
      (128,152308615630940070869977422347773317971), (128,209192610818645192190817093794780773519), (128,85795812818107552038709654911786085685), (128,171591625636215104077419309823572171370),
      (125,310293380931177481359710285100717079189), (128,34218815354453174633900217274935360363), (127,226035273001464610518970757180428389443), (128,136875261417812698535600869099741441452)]
  | _ => []

/-- Input, flag and output masks of each rank-one product. -/
def products : Nat → Bool → List (Nat × Nat × Nat)
  | 7, false => [(1,9362,3), (2,28086,1), (3,18724,2)]
  | 7, true => [(1,18724,3), (2,28086,1), (3,9362,2)]
  | 11, false => [(1,35606,7), (2,40250,5), (4,14964,1), (3,5676,2), (5,45410,4), (6,42830,3)]
  | 11, true => [(1,13416,7), (2,11868,5), (4,38702,1), (3,6708,2), (5,41798,4), (6,47474,3)]
  | 13, false => [(1,41798,7), (2,47474,3), (4,11868,6), (3,6708,2), (5,36122,4), (6,38702,5)]
  | 13, true => [(1,45410,7), (2,42830,3), (4,40250,6), (3,5676,2), (5,11352,4), (6,14964,5)]
  | 19, false => [(11,28180,5), (3,10680,1), (5,14090,10), (4,5340,8), (7,19906,9), (9,21360,6), (1,31432,2), (14,28838,15), (8,2670,4)]
  | 19, true => [(11,10358,5), (3,7572,1), (5,20716,10), (4,15144,8), (7,17330,9), (9,3786,6), (1,4958,2), (14,25870,15), (8,30288,4)]
  | 25, false => [(14,17330,9), (12,7572,8), (2,15144,1), (9,3786,6), (8,4958,4), (13,10358,10), (10,20716,5), (7,25870,15), (1,30288,2)]
  | 25, true => [(14,19906,9), (12,10680,8), (2,5340,1), (9,21360,6), (8,31432,4), (13,28180,10), (10,14090,5), (7,28838,15), (1,2670,2)]
  | 31, false => [(11,2114,3), (1,4228,14), (15,12684,9), (14,10570,4), (2,23254,1), (7,21140,2), (13,16912,12), (4,27482,8), (8,8456,7)]
  | 31, true => [(11,16912,3), (1,8456,14), (15,12684,9), (14,21140,4), (2,27482,1), (7,10570,2), (13,2114,12), (4,23254,8), (8,4228,7)]
  | 37, false => [(8,5592,4), (13,14386,24), (5,13022,9), (27,48452,13), (16,60540,2), (3,39490,19), (20,59024,10), (4,54350,8), (31,17632,29), (24,62280,6), (22,34166,21), (1,25574,1), (2,43164,18)]
  | 37, true => [(8,19262,4), (13,35574,24), (5,7306,9), (27,42510,13), (16,20630,2), (3,61882,19), (20,50922,10), (4,55904,8), (31,48550,29), (24,36308,6), (22,11512,21), (1,59922,1), (2,60720,18)]
  | 67, false => [(25,678,42), (56,26936,9), (33,27550,35), (23,55528,13), (32,35872,14), (55,21704,3), (29,21282,34), (30,40030,16), (3,53116,50), (19,35180,62), (6,31046,22), (21,61482,40), (28,46236,23), (48,51760,18), (44,32428,5)]
  | 67, true => [(25,55876,42), (56,35450,9), (33,20542,35), (23,62380,13), (32,13694,14), (55,50898,3), (29,29108,34), (30,17172,16), (3,12960,50), (19,22620,62), (6,64528,22), (21,42060,40), (28,5364,23), (48,24450,18), (44,19318,5)]
  | 73, false => [(1,32190,8), (8,36936,9), (9,60918,1), (7,28728,55), (56,61944,14), (63,33216,57), (53,5386,21), (30,48478,58), (43,43092,47), (51,6284,35), (46,56558,60), (29,50274,31), (4,2308,16), (32,16672,18), (36,18468,2)]
  | 73, true => [(1,60918,8), (8,36936,9), (9,32190,1), (7,57456,55), (56,64638,14), (63,7182,57), (53,34114,21), (30,54762,58), (43,20648,47), (51,35012,35), (46,47580,60), (29,12568,31), (4,1154,16), (32,9234,18), (36,8336,2)]
  | 313, false => [(155,57956,171), (242,1266,128), (105,59030,43), (81,942,37), (216,2264,23), (137,2934,50), (174,54446,84), (154,25754,254), (52,45108,170), (169,17494,45), (201,38198,33), (96,53600,12), (205,28978,57), (121,64902,86), (180,36020,111), (167,58200,228), (168,49832,97), (15,8688,133), (179,7244,200), (158,32926,148), (45,40146,92), (20,65300,184), (54,16950,169), (34,48418,17)]
  | 313, true => [(155,39196,171), (242,15488,128), (105,42396,43), (81,55040,37), (216,27714,23), (137,47938,50), (174,54446,84), (154,25754,254), (52,45108,170), (169,43146,45), (201,45734,33), (96,6700,12), (205,12856,57), (121,34558,86), (180,46278,111), (167,27422,228), (168,21772,97), (15,15890,133), (179,51426,200), (158,58372,148), (45,11494,92), (20,41980,184), (54,45320,169), (34,4852,17)]
  | _, _ => []

/-- Per erased input coordinate, bits k*d+j select CZ(tag[k], output[j]). -/
def eraseMasks : Nat → Bool → List Nat
  | 7, false => [954437176, 477218588]
  | 7, true => [749914924, 886263092]
  | 11, false => [73366397898640, 215273929855728, 179310540924904]
  | 11, true => [177498600732904, 249809912568632, 214364201661552]
  | 13, false => [108837207532824, 248392170031736, 177289623630760]
  | 13, true => [177870652452328, 109518228609432, 73546383957712]
  | 19, false => [672036325805778464, 856976472988007008, 493195967688046016, 910094624233094032]
  | 19, true => [175355288354305424, 478250024237092528, 889245052255243616, 702410165007424192]
  | 21, false => [12984042326850909232, 7525579197569984624, 7332108020503111104, 15749302140901972624]
  | 21, true => [13083014871924389264, 7651748164377537072, 7052854040635728352, 15186308173458494144]
  | 25, false => [711540861358474544, 265375212226485088, 458393767547316176, 317490383610301072]
  | 25, true => [240986334144953744, 482254078858816048, 969010726820169056, 696962713456178752]
  | 31, false => [709071326929344288, 822030861247146096, 1015228432634484432, 354535663464672144]
  | 31, true => [179458060983631248, 542314836382942896, 964299005465813472, 702069630206328384]
  | 37, false => [229654388483330148765792, 497088824562340280901856, 1067955561146355649008000, 963545632539502301226752, 719307955772544808307232]
  | 37, true => [565500812776888266303008, 1129784140478963243108448, 801746075996135820375744, 433562712194768571525504, 906083758922943343710976]
  | 67, false => [30588138722095498866395209856, 50598683261311998531331465600, 21949856472897642872947426048, 43899410640553691736579671552, 8570654043323645973219843072, 15903367973556921048003131456]
  | 67, true => [14036009072113560608353622080, 35879636729802525448719771840, 70521031188847034041713709440, 61794557049180989316974027520, 43123011472178205974199879168, 7017855781512567711329324032]
  | 73, false => [11862924987758325478818074816, 22487910010000513985322987904, 44956477208039838330453582656, 1473121591660438710238217728, 2965581347837190515028728832, 5931464854494948422159837248]
  | 73, true => [10282260121001544265194870848, 20545177356255204070335848640, 39852410024645802697222541696, 11338521953728951718424980224, 22677346065125553722392004096, 45374030220980725719474801664]
  | 257, false => [0, 1329248278504009256834117639467958528, 2663709136277370641153569795824747264, 5327438554964349656344047508057622272, 10654877189467560484959875181515706112, 21309754379244610702107578301418184448, 42619508758490435052401254101656354560, 85239017516980874827168991072957923072]
  | 257, true => [0, 1329248278504009256834117639467958528, 3992916849962163149913871602476450304, 9315061696018727182624952928012731392, 19964564046318671231789345126251497472, 41258376370831861988224979953584181248, 83851173034307174677054636532792565760, 169031574064399265227085137719903404032]
  | 313, false => [86574122467770779953795156791093691136, 173143032276735773904205677580161582592, 7332905266369540116364833554452385024, 98576252841582957615955734761837369600, 282391538300275961424438932662373200128, 309402851572592339845408056026813456384, 277188915931602765545428251307468242944, 212761024367214013275351473852128592128]
  | 313, true => [6688046472168239524582798916092788992, 14710533598308215609658750488274928384, 30755507692442527242189973503655347712, 57564502058839421396534495972898278400, 109765642462373350960089968752675035136, 212848517588809139383989592701083889664, 86743896332003592331333701489212284928, 173487813025955640041948416362711924736]
  | 471, false => [257048253033682677601934886936900993536, 88574477695036615835485239415962928896, 91904071195901608150842409912829807616, 183813314326713291046184091686338763008, 283057442741692334309474518517414965248, 224498098349029708062005899248762249472, 192282211806401519189661953759841009920, 298000695939803426885384380317186621696]
  | 471, true => [9367455389391041106394642083152494848, 12072990206188763508193833572811047680, 28117657431239025963930976349034219008, 57569735155121502609875207111970524160, 108425950549963797921285720607598876672, 215522673183681536419572931442049036288, 88088844312693359604556431086171774976, 174827507303748157749887098463088295936]
  | 1193, false => [1227316578898899697248833524463799068781391645696, 993131520466897774368198058845195913664134125568, 524761403602892631800361886382930956886942430208, 556201289978811289824378622072161501893417263104, 1112402579957623877722971877852383059016109048832, 474055470901554483387621498342510395422854447104, 948110941803110264850696779358184713978565035008, 884164693789409604400022983088036795730794774528, 306829144044492496835761263294787486472652718080, 613658289450114462622928190778866962119784924160]
  | 1193, true => [1036783722729269994784513103650070325898000204800, 612065806766507603680348370584661460891601996800, 1224130219736440297927860645992443563354153293824, 144445319734914840183390435546952678974792675328, 288890638107372281492568193626303852396811411456, 1192786605492564816726071258946432212285197434880, 922645719756767733609774252918267835023076982784, 1408054389184069030376956315188744468451560194048, 1354608534833810049446523543414214507769052397568, 1249142680029421842496205905192942690271473958912]
  | 1571, false => [1059534441212338394727200739901652069144342824960, 1158778702261269603671941431190839215275731064832, 856055767191637587214412663373456592024710950912, 250609897052372257492791094258860692890685825024, 501219794104744514986820128557006767156857193472, 127064852646215295094776027577972066248479047680, 254129705292431889532656438056184535622984335360, 509686658277569740215260912455744582401029177344, 1019374710351714388595707321040730742449670718464, 1260518039270955394064887886116305734060941509632]
  | 1571, true => [1181209465247127624106555731659858759399517979648, 476204971465339314094625608119031425181623520256, 950982693876844497429763959748096041005685413888, 440462356627539097144577273770179299868265164800, 879497466922171174752962025577081812871255449600, 1431424565675582789991549014474062954391419797504, 1399920246328887226700702650689307112053122629632, 1338338856689328932801806665821978500550996721664, 1215177471204130093984194390406505188546482405376, 589891109458440179951899137098466686528842366976]
  | 4593, false => [5957536844422055124259828583524839035567345835051166216192, 5639504449089639231319925718510461344824962841471237513216, 5000375041396173267403378485627577753838998527338638000128, 3723647973352590472037520115545490634905790884697826496512, 5426466050923079026544509690468012313332365437841594060800, 1777163473083194964802133936629095632258207711230775660544, 2403282485424718079755181408862676341732698199172611575808, 1345671400324048646538647932063085387834432549253411246080, 3902257899009172512724947162073314977281394041171141984256, 1528946558263874002806974232947430229315827546199311777792, 3057893490672189463070294381259120338194852210296162877440, 6117319476976588672776646412747384213082982143385871060992]
  | 4593, true => [5737399029818614119461104835680823452341234964816124186624, 5196163454656583981104897418150300601878066316808267247616, 4113693052438696613892283141227785272166835031275208728576, 1951816490887159190650140722803155109818591397165442056192, 2913169587270238611377389497042172606895309810466763669504, 107363026243731517613639843923431349894775153875747012608, 5521284200403806335697854614225641756049771975954194104320, 1071690117841213762431771810737744257106409684442790232064, 4673041221588476454829154628905670708517375874973360979968, 3070513203422459580823014309103939241066921801517445939200, 6141026780897972159835606748082539657047919916941641252864, 6006483947714344140347444039569585346050066151464685797376]
  | 5349, false => [5430294204762656975596986184611007716633372010470707310592, 4583486300085557882981546546333794569763351976421105889280, 4137475840677676452646602284455887830131014869234527289344, 1997850320204457456690130811597548099646524330501902270464, 3994168144959415183046130013391064405455007766128812560384, 3745127977595635074425816490744756993394003911908901916672, 5789672556635248382887410526304543826377638059997636857856, 129583533081446798207173163210009894632684514587868397568, 257634570622050008302515738091043436999151995631088697344, 516801262640546754196760958319508429189670235991405760512, 6064250574611119040297972125548818309353978268472657838080, 5852931909376445506365041258133828789044906812217770381312]
  | 5349, true => [5283558374151939083369817556170272405801484673255034851328, 4290015012917197397457998265883505058251508994510008889344, 3396140384057434407134754311953863640693971029906660810752, 515179032819509602020372874389617210411799677064360017920, 1030358439692094502974193181202024057792300139067356577792, 3222843746120080115537864361815545742189851751181040418816, 5139506395873049926732973800039836303588421182919453048832, 2853415022019556652068903073447412216003833261465621233664, 5705297548498225109089731398588725991391778998492667052032, 5133493361518403301265293735398239220108257896580433051648, 2889015842801215123512874288796289457765747986882271117312, 5779563806998876979172959539878610885591403523172034674688]
  | 5981, false => [1430759614679020328925700888211475552192189823430432927744, 2861518855213621501140255040798206934979286636539219570688, 5179703212664494712723831585584303383949858972600438411264, 3830178210700895284231776450311981205855853802856063799296, 53640900883245435007097696167263611324771278864135684096, 107281801857834722348706377157367936479676499079524126720, 1240742507251045315891052317491939291761591878657692663808, 2479952518961224748368264483289525510695702779355681263616, 5887656645216733815695715608484406330692915605704862076928, 5355097313849772122732895366746019919679963253250566656000, 3495857647477878989212803556252264335699933131089664540672, 714613559569077220034335884629678834465609772983625191424]
  | 5981, true => [1852159362473107435995115359057857055866561259005668233216, 3704318725037536423576884067286736141244569427588881068032, 2494589428940980175550592498552109868584172500545429331968, 3161540921919398599197992886645824607596211936996116971520, 1824578181440482901542017427005024298976356759286816276480, 3647624241575840622523476916376446308630084866020298915840, 2404150498231855876239804655971576250968023956812149948416, 4806768126869770553797438238429634330954960139410087870464, 4796274928314182680436824624810877537457650987904561315840, 5020416321487012366016662284620184984771982257942818717696, 5171249078971299896838212726347932810046955861569267826688, 4065396796700338191994971732291499368851354567842522464256]
  | 6891, false => [5919220152760018422596474461414709479063793483761613545472, 483561745546945189419960947025545732001090923025974452224, 965590995553024489982893099538279733840560180015728218112, 4699200658115694765805552417370745236714676964511602278400, 3122831702332499352257037358880419919110733263654709563392, 387750557251666199351383117994678764957008307742451306496, 5856344438392554050838800159650536380423038954070510145536, 1098191226357882530046357932105571675405993024598469771264, 2194849583030502320712926858478060979906444983019383033856, 1629145919432729317217935441025940478616353104643661758464, 3258291838956824787514251169581306453423626532444209942528, 6098160944073349595938390877678705329058388083524990144512]
  | 6891, true => [5148632884877926638093930393621612056896886718149628530688, 2798171031130134961943394078125170437507965774544303566848, 5594809192574984878315953521084088469867436566613160124416, 628627123336854566945794380641657462124661671087092842496, 1257254620818105989857536966284936900750410741111985373184, 4498502542247604831161905825116214452294951283771807301632, 4683989151453614670122455182203622313669026041391881781248, 4312872565554154567239283976479420896973926814918361481216, 2350175517209418949677323825773365476456326673768610529280, 2704450590313831964131596571974188435181496787520648642560, 5407369059322538742259446888094097744647215355161011552256, 2573550194714202300784376739451472269853569045826306572288]
  | _, _ => []

/-- Exact T, M, forward slots and inverse slots for the physical barrel. -/
def measuredCosts : Nat → Nat × Nat × Nat × Nat
  | 31 => (59,11,2105,2101)
  | 39 => (78,17,3442,3364)
  | 46 => (94,14,3825,3821)
  | 54 => (114,14,4767,4763)
  | 61 => (132,19,6179,6200)
  | 69 => (152,19,7392,7413)
  | 76 => (169,14,8141,8137)
  | 84 => (189,14,9864,9860)
  | 91 => (207,19,11478,11499)
  | 99 => (227,19,13257,13278)
  | 106 => (244,14,14262,14258)
  | 113 => (262,19,16464,16485)
  | 120 => (279,14,18138,18134)
  | 128 => (299,14,20068,20064)
  | _ => (0,0,0,0)

def measuredField : Nat → Nat × Nat × Nat × Nat
  | 3 => (0,0,0,0)
  | 7 => (3,0,35,35)
  | 11 => (6,3,210,210)
  | 13 => (6,3,214,210)
  | 19 => (9,4,331,331)
  | 21 => (7,0,99,99)
  | 25 => (9,4,331,331)
  | 31 => (7,0,81,81)
  | 37 => (13,5,509,534)
  | 67 => (15,6,707,633)
  | 73 => (13,0,129,129)
  | 257 => (12,0,92,92)
  | 313 => (20,0,153,153)
  | 471 => (20,0,166,166)
  | 1193 => (25,0,304,304)
  | 1571 => (25,0,293,293)
  | 4593 => (30,0,391,391)
  | 5349 => (30,0,374,374)
  | 5981 => (30,0,417,417)
  | 6891 => (30,0,411,411)
  | _ => (0,0,0,0)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelData ====

-- ==== begin CRTBarrel ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Arithmetic.MappedCompressed

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def fieldDegree (p : Nat) : Nat := Nat.log2 p

def mulX (p d a : Nat) : Nat :=
  let b := 2 * a
  if b.testBit d then b ^^^ p else b

def powers (p d n : Nat) : Array Nat := Id.run do
  let mut a := 1
  let mut out := #[]
  for _ in [:n] do
    out := out.push a
    a := mulX p d a
  return out

def residues (n : Nat) : Array Nat := Id.run do
  let mut rows := #[]
  for (p, m) in schedule n do
    let d := fieldDegree p
    let cols := powers p d n
    for j in [:m] do
      for k in [:d] do
        let mut row := 0
        for i in [:n] do
          if (i &&& j) == j && cols[i]!.testBit k then
            row := row ||| (1 <<< i)
        rows := rows.push row
  return rows

def selected (n mask : Nat) : List Nat := (List.range n).filter (fun i => mask.testBit i)

def elimStep (n i : Nat) (row : Nat × Nat) : List (Nat × Nat) :=
  (if row.1 < n then [(row.1,i)] else []) ++ (selected n row.2).map (fun j => (i,j))

def basisNetwork (n : Nat) : List (Nat × Nat) :=
  ((pivots n).zipIdx.flatMap (fun (row,i) => elimStep n i row)).reverse

def revCore7 : Program := [
  .CX 24 20, .CX 27 20, .CX 30 20, .CX 33 20, .CX 36 20, .CX 1 0,
  .CCX 20 0 1, .CX 1 0, .CX 23 20, .CX 24 20, .CX 26 20, .CX 27 20,
  .CX 29 20, .CX 30 20, .CX 32 20, .CX 33 20, .CX 35 20, .CX 36 20,
  .CCX 20 0 1, .CX 24 20, .CX 27 20, .CX 30 20, .CX 33 20, .CX 36 20,
  .CCX 20 1 0, .CX 23 20, .CX 24 20, .CX 26 20, .CX 27 20, .CX 29 20,
  .CX 30 20, .CX 32 20, .CX 33 20, .CX 35 20, .CX 36 20
]

def revCore21 : Program := [
  .CX 24 20, .CX 25 20, .CX 27 20, .CX 30 20, .CX 31 20, .CX 33 20,
  .CX 36 20, .CX 37 20, .CX 2 1, .CX 2 0, .CX 2 3, .CCX 20 1 2,
  .CX 2 3, .CX 2 0, .CX 2 1, .CX 23 20, .CX 24 20, .CX 29 20,
  .CX 30 20, .CX 35 20, .CX 36 20, .CX 1 0, .CX 2 0, .CX 3 0,
  .CCX 20 0 3, .CX 3 0, .CX 2 0, .CX 1 0, .CX 24 20, .CX 25 20,
  .CX 27 20, .CX 30 20, .CX 31 20, .CX 33 20, .CX 36 20, .CX 37 20,
  .CX 3 2, .CX 3 1, .CCX 20 2 3, .CX 3 1, .CX 3 2, .CX 23 20,
  .CX 24 20, .CX 26 20, .CX 27 20, .CX 29 20, .CX 30 20, .CX 32 20,
  .CX 33 20, .CX 35 20, .CX 36 20, .CX 0 1, .CX 0 2, .CCX 20 3 0,
  .CX 0 2, .CX 0 1, .CX 24 20, .CX 25 20, .CX 27 20, .CX 30 20,
  .CX 31 20, .CX 33 20, .CX 36 20, .CX 37 20, .CX 0 3, .CCX 20 1 0,
  .CX 0 3, .CX 23 20, .CX 25 20, .CX 27 20, .CX 29 20, .CX 31 20,
  .CX 33 20, .CX 35 20, .CX 37 20, .CX 2 0, .CX 3 0, .CCX 20 0 2,
  .CX 3 0, .CX 2 0, .CX 24 20, .CX 25 20, .CX 27 20, .CX 30 20,
  .CX 31 20, .CX 33 20, .CX 36 20, .CX 37 20, .CX 2 1, .CCX 20 1 0,
  .CX 2 1, .CX 23 20, .CX 25 20, .CX 26 20, .CX 29 20, .CX 31 20,
  .CX 32 20, .CX 35 20, .CX 37 20
]

def revCore31 : Program := [
  .CX 25 20, .CX 30 20, .CX 35 20, .CX 0 1, .CX 0 2, .CCX 20 3 0,
  .CX 0 2, .CX 0 1, .CX 23 20, .CX 24 20, .CX 25 20, .CX 28 20,
  .CX 29 20, .CX 30 20, .CX 33 20, .CX 34 20, .CX 35 20, .CX 3 1,
  .CCX 20 1 3, .CX 3 1, .CX 23 20, .CX 26 20, .CX 28 20, .CX 31 20,
  .CX 33 20, .CX 36 20, .CX 2 1, .CCX 20 1 2, .CX 2 1, .CX 23 20,
  .CX 24 20, .CX 28 20, .CX 29 20, .CX 33 20, .CX 34 20, .CX 1 2,
  .CX 1 3, .CCX 20 0 1, .CX 1 3, .CX 1 2, .CX 23 20, .CX 24 20,
  .CX 25 20, .CX 28 20, .CX 29 20, .CX 30 20, .CX 33 20, .CX 34 20,
  .CX 35 20, .CX 2 0, .CCX 20 0 2, .CX 2 0, .CX 23 20, .CX 26 20,
  .CX 28 20, .CX 31 20, .CX 33 20, .CX 36 20, .CX 0 2, .CX 0 3,
  .CCX 20 1 0, .CX 0 3, .CX 0 2, .CX 24 20, .CX 26 20, .CX 29 20,
  .CX 31 20, .CX 34 20, .CX 36 20, .CX 3 2, .CCX 20 2 3, .CX 3 2,
  .CX 23 20, .CX 25 20, .CX 26 20, .CX 28 20, .CX 30 20, .CX 31 20,
  .CX 33 20, .CX 35 20, .CX 36 20
]

def primaryShift8 : Program := [
  .CX 23 20, .CX 25 20, .CX 27 20, .CX 29 20, .CX 31 20, .CX 33 20,
  .CX 35 20, .CX 37 20, .CCX 20 0 1, .CCX 20 2 3, .CCX 20 4 5, .CCX 20 6 7,
  .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 32 20, .CX 33 20,
  .CX 36 20, .CX 37 20, .CX 1 0, .CCX 20 0 2, .CX 1 0, .CX 5 4,
  .CCX 20 4 6, .CX 5 4, .CX 23 20, .CX 25 20, .CX 27 20, .CX 29 20,
  .CX 31 20, .CX 33 20, .CX 35 20, .CX 37 20, .CX 2 3, .CCX 20 1 2,
  .CX 2 3, .CX 6 7, .CCX 20 5 6, .CX 6 7, .CX 23 20, .CX 26 20,
  .CX 28 20, .CX 29 20, .CX 31 20, .CX 34 20, .CX 36 20, .CX 37 20,
  .CX 1 0, .CX 2 0, .CX 3 0, .CCX 20 0 4, .CX 3 0, .CX 2 0,
  .CX 1 0, .CX 23 20, .CX 27 20, .CX 31 20, .CX 35 20, .CX 3 1,
  .CX 4 5, .CCX 20 1 4, .CX 4 5, .CX 3 1, .CX 24 20, .CX 28 20,
  .CX 32 20, .CX 36 20, .CX 3 2, .CX 4 6, .CCX 20 2 4, .CX 4 6,
  .CX 3 2, .CX 25 20, .CX 29 20, .CX 33 20, .CX 37 20, .CX 4 5,
  .CX 4 6, .CX 4 7, .CCX 20 3 4, .CX 4 7, .CX 4 6, .CX 4 5,
  .CX 26 20, .CX 27 20, .CX 28 20, .CX 29 20, .CX 34 20, .CX 35 20,
  .CX 36 20, .CX 37 20
]

def orderNineSix : Program := [
  .CX 0 1, .CX 0 2, .CX 5 2, .CX 24 20, .CX 25 20, .CX 28 20,
  .CX 29 20, .CX 33 20, .CX 34 20, .CX 37 20, .CCX 20 2 0, .CX 5 2,
  .CX 0 2, .CX 0 1, .CX 5 2, .CX 5 3, .CCX 20 3 5, .CX 5 3,
  .CX 4 2, .CX 0 2, .CX 25 20, .CX 30 20, .CX 34 20, .CCX 20 2 1,
  .CX 0 2, .CX 4 2, .CX 3 2, .CX 1 2, .CX 24 20, .CX 25 20,
  .CX 26 20, .CX 27 20, .CX 33 20, .CX 34 20, .CX 35 20, .CX 36 20,
  .CCX 20 2 4, .CX 1 2, .CX 3 2, .CX 5 2, .CX 3 4, .CX 3 5,
  .CX 5 0, .CX 25 20, .CX 30 20, .CX 34 20, .CCX 20 0 3, .CX 5 0,
  .CX 3 5, .CX 3 4, .CX 2 4, .CX 2 3, .CX 2 0, .CX 25 20,
  .CX 30 20, .CX 34 20, .CCX 20 0 2, .CX 2 0, .CX 26 20, .CX 27 20,
  .CX 28 20, .CX 29 20, .CX 35 20, .CX 36 20, .CX 37 20, .CCX 20 4 2,
  .CX 2 3, .CX 2 4, .CX 0 1, .CX 0 2, .CX 0 3, .CX 23 20,
  .CX 26 20, .CX 29 20, .CX 32 20, .CX 35 20, .CCX 20 3 0, .CX 0 3,
  .CX 0 2, .CX 0 1, .CX 4 1, .CX 4 5, .CCX 20 5 4, .CX 4 5,
  .CX 4 1, .CX 1 2, .CX 2 0, .CX 3 0, .CX 4 0, .CX 25 20,
  .CX 30 20, .CX 34 20, .CCX 20 0 1, .CX 4 0, .CX 3 0, .CX 2 0,
  .CX 1 3, .CX 24 20, .CX 26 20, .CX 27 20, .CX 30 20, .CX 33 20,
  .CX 35 20, .CX 36 20, .CCX 20 3 1, .CX 1 3, .CX 1 2, .CX 0 4,
  .CX 25 20, .CX 30 20, .CX 34 20, .CCX 20 4 0, .CX 0 4, .CX 3 1,
  .CX 5 1, .CX 25 20, .CX 30 20, .CX 34 20, .CCX 20 1 2, .CX 5 1,
  .CX 3 1, .CX 23 20, .CX 24 20, .CX 27 20, .CX 29 20, .CX 30 20,
  .CX 32 20, .CX 33 20, .CX 36 20
]

def orderSeventeen313 : Program := [
  .CX 4 7, .CX 4 6, .CX 4 5, .CX 4 3, .CX 4 0, .CX 3 5,
  .CX 3 4, .CX 3 2, .CX 2 6, .CX 2 5, .CX 2 3, .CX 3 2,
  .CX 1 4, .CX 4 1, .CX 0 3, .CX 0 1, .CX 23 20, .CX 25 20,
  .CX 27 20, .CX 29 20, .CX 31 20, .CX 33 20, .CX 35 20, .CX 37 20,
  .CCX 20 4 0, .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 3 5, .CX 3 4,
  .CX 2 7, .CX 2 6, .CX 2 3, .CX 3 2, .CX 1 6, .CX 1 5,
  .CX 1 2, .CX 2 1, .CX 0 6, .CX 0 3, .CX 0 1, .CX 1 0,
  .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 32 20, .CX 33 20,
  .CX 36 20, .CX 37 20, .CCX 20 4 0, .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3,
  .CX 4 6, .CX 4 5, .CX 4 3, .CX 4 0, .CX 3 4, .CX 2 6,
  .CX 2 4, .CX 2 1, .CX 2 0, .CX 1 7, .CX 1 5, .CX 1 3,
  .CX 3 1, .CX 0 7, .CX 0 3, .CX 23 20, .CX 25 20, .CX 26 20,
  .CX 28 20, .CX 31 20, .CX 33 20, .CX 34 20, .CX 36 20, .CCX 20 4 0,
  .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 3 7, .CX 3 6, .CX 3 5,
  .CX 3 1, .CX 2 7, .CX 2 3, .CX 1 7, .CX 1 5, .CX 1 2,
  .CX 1 0, .CX 2 1, .CX 0 7, .CX 0 5, .CX 0 4, .CX 0 1,
  .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 30 20, .CX 31 20,
  .CX 34 20, .CX 35 20, .CCX 20 4 0, .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3,
  .CX 3 5, .CX 3 0, .CX 2 6, .CX 2 5, .CX 2 4, .CX 1 7,
  .CX 1 6, .CX 1 5, .CX 0 6, .CX 0 3, .CX 26 20, .CX 27 20,
  .CX 28 20, .CX 29 20, .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20,
  .CCX 20 4 0, .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 3 6, .CX 3 4,
  .CX 3 0, .CX 2 7, .CX 2 6, .CX 2 5, .CX 2 4, .CX 2 1,
  .CX 1 7, .CX 1 6, .CX 1 2, .CX 2 1, .CX 0 7, .CX 0 6,
  .CX 0 5, .CX 30 20, .CX 31 20, .CX 32 20, .CX 33 20, .CX 34 20,
  .CX 35 20, .CX 36 20, .CX 37 20
]

def orderSeventeen471 : Program := [
  .CX 3 7, .CX 3 4, .CX 3 1, .CX 3 0, .CX 2 5, .CX 2 4,
  .CX 2 3, .CX 3 2, .CX 1 6, .CX 1 5, .CX 1 4, .CX 1 3,
  .CX 3 1, .CX 0 3, .CX 0 2, .CX 2 0, .CX 23 20, .CX 25 20,
  .CX 27 20, .CX 29 20, .CX 31 20, .CX 33 20, .CX 35 20, .CX 37 20,
  .CCX 20 4 0, .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 4 7, .CX 4 3,
  .CX 4 1, .CX 4 0, .CX 3 4, .CX 3 2, .CX 4 3, .CX 2 7,
  .CX 2 6, .CX 2 3, .CX 3 2, .CX 1 6, .CX 1 5, .CX 1 2,
  .CX 2 1, .CX 0 7, .CX 0 3, .CX 0 1, .CX 24 20, .CX 25 20,
  .CX 28 20, .CX 29 20, .CX 32 20, .CX 33 20, .CX 36 20, .CX 37 20,
  .CCX 20 4 0, .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 3 6, .CX 3 4,
  .CX 2 5, .CX 1 7, .CX 1 5, .CX 1 3, .CX 3 1, .CX 0 6,
  .CX 0 3, .CX 0 2, .CX 2 0, .CX 23 20, .CX 25 20, .CX 26 20,
  .CX 28 20, .CX 31 20, .CX 33 20, .CX 34 20, .CX 36 20, .CCX 20 4 0,
  .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 4 0, .CX 3 5, .CX 3 1,
  .CX 3 0, .CX 2 5, .CX 2 4, .CX 2 3, .CX 2 1, .CX 3 2,
  .CX 1 6, .CX 1 4, .CX 1 3, .CX 1 2, .CX 1 0, .CX 0 7,
  .CX 0 4, .CX 0 3, .CX 3 0, .CX 24 20, .CX 25 20, .CX 28 20,
  .CX 29 20, .CX 30 20, .CX 31 20, .CX 34 20, .CX 35 20, .CCX 20 4 0,
  .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 4 0, .CX 3 7, .CX 3 5,
  .CX 3 4, .CX 3 2, .CX 3 1, .CX 2 4, .CX 2 3, .CX 2 1,
  .CX 2 0, .CX 1 7, .CX 1 3, .CX 1 2, .CX 1 0, .CX 0 7,
  .CX 0 6, .CX 0 4, .CX 0 2, .CX 0 1, .CX 26 20, .CX 27 20,
  .CX 28 20, .CX 29 20, .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20,
  .CCX 20 4 0, .CCX 20 5 1, .CCX 20 6 2, .CCX 20 7 3, .CX 3 7, .CX 3 5,
  .CX 3 4, .CX 3 2, .CX 3 1, .CX 2 7, .CX 2 6, .CX 2 3,
  .CX 2 1, .CX 2 0, .CX 3 2, .CX 1 7, .CX 1 6, .CX 1 4,
  .CX 0 5, .CX 0 1, .CX 30 20, .CX 31 20, .CX 32 20, .CX 33 20,
  .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20
]

def dihedralCore1193 : Program := [
  .CX 9 8, .CX 9 6, .CX 9 4, .CX 9 3, .CX 9 1, .CX 8 5,
  .CX 8 4, .CX 8 3, .CX 8 2, .CX 8 1, .CX 8 0, .CX 7 9,
  .CX 7 8, .CX 7 6, .CX 7 5, .CX 7 4, .CX 7 3, .CX 7 1,
  .CX 6 9, .CX 6 8, .CX 6 7, .CX 6 5, .CX 6 1, .CX 6 0,
  .CX 7 6, .CX 5 9, .CX 9 5, .CX 4 8, .CX 8 4, .CX 3 7,
  .CX 7 3, .CX 2 6, .CX 6 2, .CX 1 5, .CX 5 1, .CX 0 4,
  .CX 0 1, .CX 1 0, .CX 23 20, .CX 25 20, .CX 27 20, .CX 29 20,
  .CX 31 20, .CX 33 20, .CX 35 20, .CX 37 20, .CCX 20 5 0, .CCX 20 6 1,
  .CCX 20 7 2, .CCX 20 8 3, .CCX 20 9 4, .CX 5 9, .CX 5 4, .CX 5 3,
  .CX 5 2, .CX 5 0, .CX 4 5, .CX 4 1, .CX 5 4, .CX 3 9,
  .CX 3 8, .CX 3 4, .CX 4 3, .CX 2 8, .CX 2 7, .CX 2 3,
  .CX 3 2, .CX 1 7, .CX 1 6, .CX 1 2, .CX 2 1, .CX 0 6,
  .CX 0 5, .CX 0 1, .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20,
  .CX 32 20, .CX 33 20, .CX 36 20, .CX 37 20, .CCX 20 5 0, .CCX 20 6 1,
  .CCX 20 7 2, .CCX 20 8 3, .CCX 20 9 4, .CX 9 7, .CX 9 6, .CX 9 5,
  .CX 9 4, .CX 9 1, .CX 9 0, .CX 8 9, .CX 8 7, .CX 8 6,
  .CX 8 5, .CX 8 4, .CX 8 1, .CX 8 0, .CX 7 9, .CX 7 8,
  .CX 7 6, .CX 7 5, .CX 7 4, .CX 7 1, .CX 7 0, .CX 8 7,
  .CX 6 9, .CX 6 8, .CX 6 4, .CX 6 1, .CX 5 6, .CX 5 0,
  .CX 6 5, .CX 4 6, .CX 4 3, .CX 4 2, .CX 3 9, .CX 3 7,
  .CX 3 4, .CX 4 3, .CX 2 8, .CX 2 5, .CX 2 3, .CX 3 2,
  .CX 1 7, .CX 1 6, .CX 1 2, .CX 0 6, .CX 0 5, .CX 5 0,
  .CX 23 20, .CX 25 20, .CX 26 20, .CX 28 20, .CX 31 20, .CX 33 20,
  .CX 34 20, .CX 36 20, .CCX 20 5 0, .CCX 20 6 1, .CCX 20 7 2, .CCX 20 8 3,
  .CCX 20 9 4, .CX 9 6, .CX 9 5, .CX 9 3, .CX 9 0, .CX 8 9,
  .CX 8 4, .CX 8 3, .CX 8 1, .CX 8 0, .CX 7 9, .CX 7 8,
  .CX 7 5, .CX 7 4, .CX 7 3, .CX 7 1, .CX 8 7, .CX 6 9,
  .CX 6 5, .CX 6 3, .CX 6 0, .CX 9 6, .CX 5 8, .CX 5 0,
  .CX 8 5, .CX 4 6, .CX 4 5, .CX 4 3, .CX 4 2, .CX 4 1,
  .CX 4 0, .CX 3 9, .CX 3 8, .CX 3 7, .CX 3 1, .CX 7 3,
  .CX 2 9, .CX 2 8, .CX 2 4, .CX 2 3, .CX 3 2, .CX 1 7,
  .CX 1 6, .CX 6 1, .CX 0 8, .CX 0 5, .CX 5 0, .CX 24 20,
  .CX 25 20, .CX 28 20, .CX 29 20, .CX 30 20, .CX 31 20, .CX 34 20,
  .CX 35 20, .CCX 20 5 0, .CCX 20 6 1, .CCX 20 7 2, .CCX 20 8 3, .CCX 20 9 4,
  .CX 9 7, .CX 9 6, .CX 9 5, .CX 9 4, .CX 9 2, .CX 9 1,
  .CX 9 0, .CX 8 9, .CX 8 3, .CX 9 8, .CX 4 9, .CX 4 8,
  .CX 4 7, .CX 4 6, .CX 4 5, .CX 4 2, .CX 4 0, .CX 3 9,
  .CX 3 8, .CX 8 3, .CX 2 6, .CX 2 4, .CX 2 0, .CX 1 8,
  .CX 1 5, .CX 1 4, .CX 1 2, .CX 0 8, .CX 0 3, .CX 0 2,
  .CX 0 1, .CX 1 0, .CX 26 20, .CX 27 20, .CX 28 20, .CX 29 20,
  .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20, .CCX 20 5 0, .CCX 20 6 1,
  .CCX 20 7 2, .CCX 20 8 3, .CCX 20 9 4, .CX 9 8, .CX 9 6, .CX 9 5,
  .CX 9 3, .CX 9 2, .CX 8 9, .CX 8 6, .CX 8 5, .CX 8 4,
  .CX 8 3, .CX 8 2, .CX 9 8, .CX 7 9, .CX 7 3, .CX 6 9,
  .CX 6 8, .CX 6 4, .CX 6 3, .CX 6 1, .CX 6 0, .CX 8 6,
  .CX 5 7, .CX 5 3, .CX 5 2, .CX 5 1, .CX 7 5, .CX 4 8,
  .CX 4 6, .CX 6 4, .CX 3 8, .CX 3 7, .CX 3 0, .CX 7 3,
  .CX 2 9, .CX 2 5, .CX 2 1, .CX 1 9, .CX 1 8, .CX 1 7,
  .CX 1 6, .CX 6 1, .CX 0 9, .CX 0 8, .CX 0 5, .CX 0 3,
  .CX 0 2, .CX 2 0, .CX 30 20, .CX 31 20, .CX 32 20, .CX 33 20,
  .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20
]

def dihedralCore1571 : Program := [
  .CX 9 7, .CX 9 5, .CX 9 4, .CX 9 3, .CX 9 2, .CX 9 1,
  .CX 9 0, .CX 8 9, .CX 8 7, .CX 8 5, .CX 8 4, .CX 8 2,
  .CX 8 0, .CX 7 9, .CX 7 8, .CX 7 0, .CX 8 7, .CX 6 8,
  .CX 6 5, .CX 6 3, .CX 6 2, .CX 6 1, .CX 6 0, .CX 5 9,
  .CX 9 5, .CX 4 8, .CX 8 4, .CX 3 7, .CX 7 3, .CX 2 6,
  .CX 6 2, .CX 1 5, .CX 5 1, .CX 0 4, .CX 0 3, .CX 3 0,
  .CX 23 20, .CX 25 20, .CX 27 20, .CX 29 20, .CX 31 20, .CX 33 20,
  .CX 35 20, .CX 37 20, .CCX 20 5 0, .CCX 20 6 1, .CCX 20 7 2, .CCX 20 8 3,
  .CCX 20 9 4, .CX 5 9, .CX 5 4, .CX 5 2, .CX 5 1, .CX 5 0,
  .CX 4 5, .CX 4 3, .CX 5 4, .CX 3 9, .CX 3 8, .CX 3 4,
  .CX 4 3, .CX 2 8, .CX 2 7, .CX 2 3, .CX 3 2, .CX 1 7,
  .CX 1 6, .CX 1 2, .CX 2 1, .CX 0 6, .CX 0 5, .CX 0 1,
  .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 32 20, .CX 33 20,
  .CX 36 20, .CX 37 20, .CCX 20 5 0, .CCX 20 6 1, .CCX 20 7 2, .CCX 20 8 3,
  .CCX 20 9 4, .CX 9 8, .CX 9 5, .CX 9 4, .CX 9 3, .CX 9 0,
  .CX 8 9, .CX 8 5, .CX 8 4, .CX 8 3, .CX 8 0, .CX 9 8,
  .CX 7 9, .CX 7 5, .CX 7 4, .CX 7 3, .CX 7 0, .CX 6 8,
  .CX 6 7, .CX 6 4, .CX 6 2, .CX 6 1, .CX 5 9, .CX 5 7,
  .CX 5 4, .CX 5 3, .CX 5 0, .CX 7 5, .CX 4 9, .CX 4 7,
  .CX 4 6, .CX 4 3, .CX 6 4, .CX 3 9, .CX 3 7, .CX 3 4,
  .CX 4 3, .CX 2 8, .CX 2 5, .CX 2 3, .CX 3 2, .CX 1 7,
  .CX 1 6, .CX 1 2, .CX 0 6, .CX 0 5, .CX 5 0, .CX 23 20,
  .CX 25 20, .CX 26 20, .CX 28 20, .CX 31 20, .CX 33 20, .CX 34 20,
  .CX 36 20, .CCX 20 5 0, .CCX 20 6 1, .CCX 20 7 2, .CCX 20 8 3, .CCX 20 9 4,
  .CX 9 7, .CX 9 5, .CX 9 4, .CX 9 2, .CX 9 0, .CX 8 6,
  .CX 8 5, .CX 8 4, .CX 8 3, .CX 8 1, .CX 8 0, .CX 7 9,
  .CX 7 6, .CX 7 5, .CX 7 4, .CX 7 2, .CX 7 1, .CX 7 0,
  .CX 9 7, .CX 6 7, .CX 6 1, .CX 7 6, .CX 5 8, .CX 5 0,
  .CX 8 5, .CX 4 8, .CX 4 7, .CX 3 9, .CX 3 7, .CX 3 5,
  .CX 3 2, .CX 2 9, .CX 2 8, .CX 2 4, .CX 2 3, .CX 3 2,
  .CX 1 7, .CX 1 6, .CX 6 1, .CX 0 8, .CX 0 5, .CX 5 0,
  .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 30 20, .CX 31 20,
  .CX 34 20, .CX 35 20, .CCX 20 5 0, .CCX 20 6 1, .CCX 20 7 2, .CCX 20 8 3,
  .CCX 20 9 4, .CX 9 7, .CX 9 3, .CX 9 2, .CX 9 1, .CX 8 9,
  .CX 8 3, .CX 9 8, .CX 4 6, .CX 4 2, .CX 4 1, .CX 3 9,
  .CX 3 8, .CX 8 3, .CX 2 7, .CX 2 5, .CX 2 4, .CX 2 3,
  .CX 2 1, .CX 2 0, .CX 1 5, .CX 1 4, .CX 1 2, .CX 0 9,
  .CX 0 7, .CX 0 5, .CX 0 4, .CX 0 3, .CX 3 0, .CX 26 20,
  .CX 27 20, .CX 28 20, .CX 29 20, .CX 34 20, .CX 35 20, .CX 36 20,
  .CX 37 20, .CCX 20 5 0, .CCX 20 6 1, .CCX 20 7 2, .CCX 20 8 3, .CCX 20 9 4,
  .CX 9 8, .CX 9 7, .CX 9 6, .CX 9 5, .CX 9 4, .CX 8 9,
  .CX 8 6, .CX 8 5, .CX 8 4, .CX 8 3, .CX 8 2, .CX 7 4,
  .CX 7 3, .CX 6 9, .CX 6 5, .CX 6 4, .CX 6 2, .CX 6 0,
  .CX 9 6, .CX 5 6, .CX 5 4, .CX 5 2, .CX 5 1, .CX 6 5,
  .CX 4 8, .CX 4 7, .CX 4 2, .CX 7 4, .CX 3 8, .CX 3 6,
  .CX 3 5, .CX 3 0, .CX 5 3, .CX 2 6, .CX 2 5, .CX 2 4,
  .CX 2 0, .CX 1 9, .CX 1 6, .CX 1 0, .CX 6 1, .CX 0 9,
  .CX 0 8, .CX 0 7, .CX 0 1, .CX 30 20, .CX 31 20, .CX 32 20,
  .CX 33 20, .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20
]

def dihedralCore4593 : Program := [
  .CX 11 7, .CX 11 4, .CX 11 3, .CX 11 0, .CX 10 11, .CX 10 5,
  .CX 10 4, .CX 10 3, .CX 10 1, .CX 11 10, .CX 9 11, .CX 9 10,
  .CX 9 7, .CX 9 6, .CX 9 5, .CX 9 3, .CX 9 2, .CX 8 2,
  .CX 8 1, .CX 8 0, .CX 7 11, .CX 7 10, .CX 7 9, .CX 7 6,
  .CX 7 4, .CX 7 3, .CX 7 2, .CX 7 1, .CX 9 7, .CX 6 11,
  .CX 11 6, .CX 5 10, .CX 10 5, .CX 4 9, .CX 9 4, .CX 3 8,
  .CX 8 3, .CX 2 7, .CX 7 2, .CX 1 6, .CX 6 1, .CX 0 5,
  .CX 0 1, .CX 23 20, .CX 25 20, .CX 27 20, .CX 29 20, .CX 31 20,
  .CX 33 20, .CX 35 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2,
  .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 6 11, .CX 6 5, .CX 6 4,
  .CX 6 3, .CX 6 2, .CX 5 6, .CX 5 1, .CX 5 0, .CX 6 5,
  .CX 4 11, .CX 4 10, .CX 4 5, .CX 5 4, .CX 3 10, .CX 3 9,
  .CX 3 4, .CX 4 3, .CX 2 9, .CX 2 8, .CX 2 3, .CX 3 2,
  .CX 1 8, .CX 1 7, .CX 1 2, .CX 2 1, .CX 0 7, .CX 0 6,
  .CX 0 1, .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 32 20,
  .CX 33 20, .CX 36 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2,
  .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 8, .CX 11 5, .CX 11 1,
  .CX 11 0, .CX 10 11, .CX 10 9, .CX 10 8, .CX 10 5, .CX 10 1,
  .CX 10 0, .CX 9 11, .CX 9 10, .CX 9 8, .CX 9 5, .CX 9 1,
  .CX 9 0, .CX 10 9, .CX 8 11, .CX 8 10, .CX 8 5, .CX 8 1,
  .CX 8 0, .CX 10 8, .CX 7 11, .CX 7 10, .CX 7 6, .CX 7 4,
  .CX 7 3, .CX 7 2, .CX 7 1, .CX 7 0, .CX 6 7, .CX 6 0,
  .CX 7 6, .CX 5 11, .CX 5 10, .CX 5 6, .CX 5 1, .CX 5 0,
  .CX 6 5, .CX 4 11, .CX 4 9, .CX 4 5, .CX 5 4, .CX 3 10,
  .CX 3 8, .CX 3 4, .CX 4 3, .CX 2 9, .CX 2 6, .CX 2 3,
  .CX 3 2, .CX 1 8, .CX 1 7, .CX 1 2, .CX 0 7, .CX 0 6,
  .CX 6 0, .CX 23 20, .CX 25 20, .CX 26 20, .CX 28 20, .CX 31 20,
  .CX 33 20, .CX 34 20, .CX 36 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2,
  .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 9, .CX 11 6,
  .CX 11 5, .CX 11 4, .CX 10 11, .CX 10 9, .CX 10 8, .CX 10 6,
  .CX 10 4, .CX 10 1, .CX 10 0, .CX 11 10, .CX 9 11, .CX 9 10,
  .CX 9 7, .CX 9 5, .CX 9 4, .CX 9 1, .CX 9 0, .CX 8 10,
  .CX 8 9, .CX 8 6, .CX 8 5, .CX 8 1, .CX 9 8, .CX 7 8,
  .CX 7 1, .CX 8 7, .CX 6 9, .CX 6 0, .CX 9 6, .CX 5 10,
  .CX 5 9, .CX 5 7, .CX 5 6, .CX 5 4, .CX 5 3, .CX 5 0,
  .CX 4 10, .CX 4 9, .CX 4 7, .CX 4 5, .CX 4 3, .CX 4 2,
  .CX 4 1, .CX 3 11, .CX 3 10, .CX 3 9, .CX 3 8, .CX 3 5,
  .CX 3 4, .CX 3 2, .CX 2 10, .CX 2 9, .CX 2 4, .CX 2 3,
  .CX 3 2, .CX 1 8, .CX 1 7, .CX 7 1, .CX 0 9, .CX 0 6,
  .CX 6 0, .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 30 20,
  .CX 31 20, .CX 34 20, .CX 35 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2,
  .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 9, .CX 11 7,
  .CX 11 6, .CX 11 5, .CX 11 4, .CX 10 11, .CX 10 9, .CX 10 8,
  .CX 10 5, .CX 10 4, .CX 11 10, .CX 9 10, .CX 9 3, .CX 10 9,
  .CX 6 11, .CX 6 0, .CX 11 6, .CX 5 10, .CX 5 8, .CX 5 6,
  .CX 5 4, .CX 5 3, .CX 6 5, .CX 4 10, .CX 4 8, .CX 4 7,
  .CX 4 5, .CX 4 3, .CX 4 2, .CX 4 1, .CX 3 10, .CX 3 9,
  .CX 9 3, .CX 2 11, .CX 2 10, .CX 2 9, .CX 2 8, .CX 2 7,
  .CX 2 5, .CX 2 3, .CX 2 1, .CX 2 0, .CX 3 2, .CX 1 10,
  .CX 1 9, .CX 1 8, .CX 1 6, .CX 1 4, .CX 0 11, .CX 0 6,
  .CX 6 0, .CX 26 20, .CX 27 20, .CX 28 20, .CX 29 20, .CX 34 20,
  .CX 35 20, .CX 36 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2,
  .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 8, .CX 11 7,
  .CX 11 3, .CX 11 2, .CX 11 0, .CX 10 11, .CX 10 4, .CX 11 10,
  .CX 9 11, .CX 9 8, .CX 9 7, .CX 9 6, .CX 9 4, .CX 9 3,
  .CX 9 2, .CX 8 10, .CX 8 7, .CX 8 5, .CX 8 4, .CX 8 3,
  .CX 8 2, .CX 8 0, .CX 10 8, .CX 7 8, .CX 7 4, .CX 7 3,
  .CX 7 1, .CX 7 0, .CX 6 10, .CX 6 5, .CX 6 3, .CX 6 2,
  .CX 6 1, .CX 5 8, .CX 5 7, .CX 7 5, .CX 4 9, .CX 4 6,
  .CX 4 3, .CX 4 2, .CX 4 1, .CX 4 0, .CX 6 4, .CX 3 11,
  .CX 3 9, .CX 3 6, .CX 3 4, .CX 3 2, .CX 3 1, .CX 3 0,
  .CX 4 3, .CX 2 10, .CX 2 5, .CX 2 1, .CX 5 2, .CX 1 10,
  .CX 1 9, .CX 1 8, .CX 1 7, .CX 1 6, .CX 1 2, .CX 0 11,
  .CX 0 10, .CX 0 9, .CX 0 8, .CX 0 7, .CX 0 3, .CX 30 20,
  .CX 31 20, .CX 32 20, .CX 33 20, .CX 34 20, .CX 35 20, .CX 36 20,
  .CX 37 20
]

def dihedralCore5349 : Program := [
  .CX 11 9, .CX 11 8, .CX 11 6, .CX 11 3, .CX 11 0, .CX 10 11,
  .CX 10 8, .CX 10 6, .CX 10 5, .CX 10 4, .CX 10 3, .CX 10 2,
  .CX 10 1, .CX 10 0, .CX 11 10, .CX 9 11, .CX 9 10, .CX 9 8,
  .CX 9 5, .CX 9 4, .CX 8 11, .CX 8 4, .CX 7 9, .CX 7 4,
  .CX 7 3, .CX 7 1, .CX 7 0, .CX 6 11, .CX 11 6, .CX 5 10,
  .CX 10 5, .CX 4 9, .CX 9 4, .CX 3 8, .CX 8 3, .CX 2 7,
  .CX 7 2, .CX 1 6, .CX 6 1, .CX 0 5, .CX 0 3, .CX 23 20,
  .CX 25 20, .CX 27 20, .CX 29 20, .CX 31 20, .CX 33 20, .CX 35 20,
  .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4,
  .CCX 20 11 5, .CX 6 11, .CX 6 5, .CX 6 4, .CX 6 2, .CX 6 1,
  .CX 5 6, .CX 5 3, .CX 5 0, .CX 6 5, .CX 4 11, .CX 4 10,
  .CX 4 5, .CX 5 4, .CX 3 10, .CX 3 9, .CX 3 4, .CX 4 3,
  .CX 2 9, .CX 2 8, .CX 2 3, .CX 3 2, .CX 1 8, .CX 1 7,
  .CX 1 2, .CX 2 1, .CX 0 7, .CX 0 6, .CX 0 1, .CX 24 20,
  .CX 25 20, .CX 28 20, .CX 29 20, .CX 32 20, .CX 33 20, .CX 36 20,
  .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4,
  .CCX 20 11 5, .CX 11 10, .CX 11 9, .CX 11 7, .CX 11 5, .CX 11 3,
  .CX 11 0, .CX 10 11, .CX 10 9, .CX 10 7, .CX 10 5, .CX 10 3,
  .CX 10 0, .CX 9 11, .CX 9 10, .CX 9 7, .CX 9 5, .CX 9 3,
  .CX 9 0, .CX 8 11, .CX 8 10, .CX 8 9, .CX 8 7, .CX 8 6,
  .CX 8 5, .CX 8 3, .CX 7 11, .CX 7 10, .CX 7 9, .CX 7 8,
  .CX 7 5, .CX 7 3, .CX 7 0, .CX 8 7, .CX 6 7, .CX 6 0,
  .CX 7 6, .CX 5 9, .CX 5 8, .CX 5 6, .CX 5 4, .CX 5 2,
  .CX 5 1, .CX 5 0, .CX 4 11, .CX 4 9, .CX 4 5, .CX 5 4,
  .CX 3 10, .CX 3 8, .CX 3 4, .CX 4 3, .CX 2 9, .CX 2 6,
  .CX 2 3, .CX 3 2, .CX 1 8, .CX 1 7, .CX 1 2, .CX 0 7,
  .CX 0 6, .CX 6 0, .CX 23 20, .CX 25 20, .CX 26 20, .CX 28 20,
  .CX 31 20, .CX 33 20, .CX 34 20, .CX 36 20, .CCX 20 6 0, .CCX 20 7 1,
  .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 7,
  .CX 11 6, .CX 11 4, .CX 11 2, .CX 11 1, .CX 11 0, .CX 10 11,
  .CX 10 8, .CX 10 7, .CX 10 4, .CX 10 1, .CX 9 11, .CX 9 10,
  .CX 9 7, .CX 9 5, .CX 9 4, .CX 9 3, .CX 9 2, .CX 10 9,
  .CX 8 11, .CX 8 10, .CX 8 9, .CX 8 4, .CX 7 8, .CX 7 1,
  .CX 8 7, .CX 6 9, .CX 6 0, .CX 9 6, .CX 5 10, .CX 5 8,
  .CX 5 4, .CX 5 2, .CX 5 1, .CX 4 11, .CX 4 9, .CX 4 8,
  .CX 4 7, .CX 4 6, .CX 4 2, .CX 6 4, .CX 3 11, .CX 3 10,
  .CX 3 9, .CX 3 8, .CX 3 5, .CX 3 4, .CX 3 2, .CX 2 10,
  .CX 2 9, .CX 2 4, .CX 2 3, .CX 3 2, .CX 1 8, .CX 1 7,
  .CX 7 1, .CX 0 9, .CX 0 6, .CX 6 0, .CX 24 20, .CX 25 20,
  .CX 28 20, .CX 29 20, .CX 30 20, .CX 31 20, .CX 34 20, .CX 35 20,
  .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5,
  .CX 11 6, .CX 11 4, .CX 11 3, .CX 11 0, .CX 10 11, .CX 10 8,
  .CX 10 7, .CX 10 4, .CX 10 3, .CX 9 10, .CX 9 3, .CX 10 9,
  .CX 8 11, .CX 8 2, .CX 11 8, .CX 5 11, .CX 5 10, .CX 5 9,
  .CX 5 7, .CX 5 3, .CX 5 2, .CX 5 0, .CX 4 10, .CX 4 9,
  .CX 4 7, .CX 4 6, .CX 4 2, .CX 4 1, .CX 4 0, .CX 3 10,
  .CX 3 9, .CX 9 3, .CX 2 11, .CX 2 8, .CX 8 2, .CX 1 9,
  .CX 1 8, .CX 1 7, .CX 1 5, .CX 1 3, .CX 1 0, .CX 3 1,
  .CX 0 10, .CX 0 7, .CX 0 5, .CX 0 3, .CX 0 2, .CX 0 1,
  .CX 26 20, .CX 27 20, .CX 28 20, .CX 29 20, .CX 34 20, .CX 35 20,
  .CX 36 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3,
  .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 5, .CX 11 4, .CX 10 11,
  .CX 10 4, .CX 11 10, .CX 9 11, .CX 9 8, .CX 9 7, .CX 9 3,
  .CX 9 0, .CX 8 4, .CX 8 2, .CX 7 11, .CX 7 8, .CX 7 6,
  .CX 7 5, .CX 7 3, .CX 7 2, .CX 8 7, .CX 6 7, .CX 6 5,
  .CX 6 3, .CX 6 2, .CX 6 1, .CX 6 0, .CX 7 6, .CX 5 10,
  .CX 4 8, .CX 4 7, .CX 4 1, .CX 4 0, .CX 7 4, .CX 3 9,
  .CX 3 8, .CX 3 7, .CX 3 6, .CX 3 2, .CX 3 0, .CX 6 3,
  .CX 2 6, .CX 2 4, .CX 2 3, .CX 2 1, .CX 2 0, .CX 1 11,
  .CX 1 8, .CX 1 7, .CX 1 4, .CX 1 0, .CX 4 1, .CX 0 11,
  .CX 0 10, .CX 0 9, .CX 0 7, .CX 0 6, .CX 0 5, .CX 0 1,
  .CX 30 20, .CX 31 20, .CX 32 20, .CX 33 20, .CX 34 20, .CX 35 20,
  .CX 36 20, .CX 37 20
]

def dihedralCore5981 : Program := [
  .CX 11 10, .CX 11 9, .CX 11 5, .CX 11 4, .CX 11 3, .CX 11 2,
  .CX 11 0, .CX 10 4, .CX 10 2, .CX 10 0, .CX 9 10, .CX 9 8,
  .CX 9 7, .CX 9 5, .CX 9 1, .CX 9 0, .CX 10 9, .CX 8 11,
  .CX 8 5, .CX 8 3, .CX 8 0, .CX 7 11, .CX 7 9, .CX 7 6,
  .CX 7 1, .CX 6 11, .CX 11 6, .CX 5 10, .CX 10 5, .CX 4 9,
  .CX 9 4, .CX 3 8, .CX 8 3, .CX 2 7, .CX 7 2, .CX 1 6,
  .CX 6 1, .CX 0 5, .CX 0 3, .CX 0 2, .CX 0 1, .CX 1 0,
  .CX 23 20, .CX 25 20, .CX 27 20, .CX 29 20, .CX 31 20, .CX 33 20,
  .CX 35 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3,
  .CCX 20 10 4, .CCX 20 11 5, .CX 6 11, .CX 6 5, .CX 6 4, .CX 6 0,
  .CX 5 6, .CX 5 3, .CX 5 2, .CX 5 1, .CX 6 5, .CX 4 11,
  .CX 4 10, .CX 4 5, .CX 5 4, .CX 3 10, .CX 3 9, .CX 3 4,
  .CX 4 3, .CX 2 9, .CX 2 8, .CX 2 3, .CX 3 2, .CX 1 8,
  .CX 1 7, .CX 1 2, .CX 2 1, .CX 0 7, .CX 0 6, .CX 0 1,
  .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 32 20, .CX 33 20,
  .CX 36 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3,
  .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 7, .CX 11 6, .CX 11 5,
  .CX 11 3, .CX 11 2, .CX 11 1, .CX 11 0, .CX 10 11, .CX 10 7,
  .CX 10 6, .CX 10 5, .CX 10 3, .CX 10 2, .CX 10 1, .CX 10 0,
  .CX 9 11, .CX 9 10, .CX 9 8, .CX 9 7, .CX 9 5, .CX 9 3,
  .CX 9 2, .CX 9 1, .CX 8 11, .CX 8 10, .CX 8 9, .CX 8 7,
  .CX 8 5, .CX 8 3, .CX 8 2, .CX 8 1, .CX 9 8, .CX 7 11,
  .CX 7 10, .CX 7 9, .CX 7 6, .CX 7 5, .CX 7 3, .CX 7 2,
  .CX 7 1, .CX 7 0, .CX 9 7, .CX 6 7, .CX 6 0, .CX 7 6,
  .CX 5 9, .CX 5 7, .CX 5 6, .CX 5 4, .CX 4 11, .CX 4 9,
  .CX 4 5, .CX 5 4, .CX 3 10, .CX 3 8, .CX 3 4, .CX 4 3,
  .CX 2 9, .CX 2 6, .CX 2 3, .CX 3 2, .CX 1 8, .CX 1 7,
  .CX 1 2, .CX 0 7, .CX 0 6, .CX 6 0, .CX 23 20, .CX 25 20,
  .CX 26 20, .CX 28 20, .CX 31 20, .CX 33 20, .CX 34 20, .CX 36 20,
  .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5,
  .CX 11 9, .CX 11 8, .CX 11 7, .CX 11 4, .CX 11 2, .CX 11 0,
  .CX 10 11, .CX 10 9, .CX 10 8, .CX 10 6, .CX 10 5, .CX 10 4,
  .CX 10 3, .CX 10 1, .CX 10 0, .CX 9 11, .CX 9 10, .CX 9 5,
  .CX 9 2, .CX 9 0, .CX 8 9, .CX 8 7, .CX 8 6, .CX 8 4,
  .CX 8 3, .CX 8 2, .CX 9 8, .CX 7 8, .CX 7 1, .CX 8 7,
  .CX 6 9, .CX 6 0, .CX 9 6, .CX 5 10, .CX 5 9, .CX 5 8,
  .CX 5 7, .CX 5 6, .CX 5 3, .CX 5 2, .CX 5 0, .CX 6 5,
  .CX 4 10, .CX 4 8, .CX 4 6, .CX 4 5, .CX 4 3, .CX 4 1,
  .CX 4 0, .CX 3 11, .CX 3 10, .CX 3 9, .CX 3 8, .CX 3 5,
  .CX 3 4, .CX 3 2, .CX 2 10, .CX 2 9, .CX 2 4, .CX 2 3,
  .CX 3 2, .CX 1 8, .CX 1 7, .CX 7 1, .CX 0 9, .CX 0 6,
  .CX 6 0, .CX 24 20, .CX 25 20, .CX 28 20, .CX 29 20, .CX 30 20,
  .CX 31 20, .CX 34 20, .CX 35 20, .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2,
  .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 8, .CX 11 5,
  .CX 11 4, .CX 11 2, .CX 11 1, .CX 11 0, .CX 10 9, .CX 10 7,
  .CX 10 6, .CX 10 4, .CX 10 3, .CX 10 1, .CX 10 0, .CX 9 10,
  .CX 9 3, .CX 10 9, .CX 8 11, .CX 8 2, .CX 11 8, .CX 7 10,
  .CX 7 9, .CX 7 6, .CX 7 5, .CX 7 3, .CX 7 0, .CX 9 7,
  .CX 6 10, .CX 6 9, .CX 6 7, .CX 6 5, .CX 6 3, .CX 6 0,
  .CX 7 6, .CX 5 10, .CX 5 9, .CX 5 7, .CX 5 6, .CX 5 3,
  .CX 5 0, .CX 6 5, .CX 4 10, .CX 4 8, .CX 4 5, .CX 4 2,
  .CX 5 4, .CX 3 10, .CX 3 9, .CX 9 3, .CX 2 11, .CX 2 8,
  .CX 8 2, .CX 1 9, .CX 1 8, .CX 1 6, .CX 1 3, .CX 1 2,
  .CX 1 0, .CX 0 11, .CX 0 10, .CX 0 8, .CX 0 5, .CX 0 2,
  .CX 0 1, .CX 1 0, .CX 26 20, .CX 27 20, .CX 28 20, .CX 29 20,
  .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1,
  .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 5,
  .CX 11 4, .CX 10 11, .CX 10 4, .CX 11 10, .CX 9 11, .CX 9 10,
  .CX 9 7, .CX 9 6, .CX 9 5, .CX 9 1, .CX 8 11, .CX 8 10,
  .CX 8 6, .CX 8 5, .CX 8 1, .CX 8 0, .CX 7 11, .CX 7 10,
  .CX 7 5, .CX 7 4, .CX 7 3, .CX 7 2, .CX 7 1, .CX 7 0,
  .CX 6 7, .CX 6 5, .CX 6 2, .CX 6 1, .CX 7 6, .CX 5 8,
  .CX 5 7, .CX 5 4, .CX 5 2, .CX 5 0, .CX 7 5, .CX 4 10,
  .CX 4 8, .CX 4 7, .CX 4 5, .CX 4 2, .CX 4 0, .CX 5 4,
  .CX 3 9, .CX 3 8, .CX 3 7, .CX 3 6, .CX 3 2, .CX 3 1,
  .CX 6 3, .CX 2 11, .CX 2 10, .CX 2 8, .CX 2 7, .CX 2 5,
  .CX 2 4, .CX 2 0, .CX 4 2, .CX 1 11, .CX 1 9, .CX 1 5,
  .CX 1 3, .CX 0 9, .CX 0 8, .CX 0 3, .CX 0 2, .CX 0 1,
  .CX 1 0, .CX 30 20, .CX 31 20, .CX 32 20, .CX 33 20, .CX 34 20,
  .CX 35 20, .CX 36 20, .CX 37 20
]

def dihedralCore6891 : Program := [
  .CX 11 9, .CX 11 8, .CX 11 7, .CX 11 3, .CX 11 0, .CX 10 9,
  .CX 10 6, .CX 10 5, .CX 10 4, .CX 10 1, .CX 9 11, .CX 9 10,
  .CX 9 7, .CX 9 4, .CX 9 3, .CX 9 1, .CX 8 11, .CX 8 10,
  .CX 8 5, .CX 8 4, .CX 8 2, .CX 10 8, .CX 7 11, .CX 7 9,
  .CX 7 8, .CX 7 5, .CX 7 4, .CX 7 3, .CX 7 0, .CX 8 7,
  .CX 6 11, .CX 11 6, .CX 5 10, .CX 10 5, .CX 4 9, .CX 9 4,
  .CX 3 8, .CX 8 3, .CX 2 7, .CX 7 2, .CX 1 6, .CX 6 1,
  .CX 0 5, .CX 0 4, .CX 0 2, .CX 23 20, .CX 25 20, .CX 27 20,
  .CX 29 20, .CX 31 20, .CX 33 20, .CX 35 20, .CX 37 20, .CCX 20 6 0,
  .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 6 11,
  .CX 6 5, .CX 6 3, .CX 6 1, .CX 5 6, .CX 5 4, .CX 5 2,
  .CX 5 0, .CX 6 5, .CX 4 11, .CX 4 10, .CX 4 5, .CX 5 4,
  .CX 3 10, .CX 3 9, .CX 3 4, .CX 4 3, .CX 2 9, .CX 2 8,
  .CX 2 3, .CX 3 2, .CX 1 8, .CX 1 7, .CX 1 2, .CX 2 1,
  .CX 0 7, .CX 0 6, .CX 0 1, .CX 24 20, .CX 25 20, .CX 28 20,
  .CX 29 20, .CX 32 20, .CX 33 20, .CX 36 20, .CX 37 20, .CCX 20 6 0,
  .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10,
  .CX 11 9, .CX 11 8, .CX 11 7, .CX 11 5, .CX 11 4, .CX 11 2,
  .CX 11 0, .CX 10 11, .CX 10 9, .CX 10 8, .CX 10 7, .CX 10 5,
  .CX 10 4, .CX 10 2, .CX 10 0, .CX 11 10, .CX 9 11, .CX 9 8,
  .CX 9 7, .CX 9 5, .CX 9 4, .CX 9 2, .CX 9 0, .CX 8 11,
  .CX 8 9, .CX 8 7, .CX 8 5, .CX 8 4, .CX 8 2, .CX 8 0,
  .CX 7 11, .CX 7 9, .CX 7 8, .CX 7 6, .CX 7 5, .CX 7 4,
  .CX 7 2, .CX 6 7, .CX 6 0, .CX 7 6, .CX 5 10, .CX 5 9,
  .CX 5 8, .CX 5 3, .CX 5 1, .CX 5 0, .CX 4 11, .CX 4 9,
  .CX 4 5, .CX 5 4, .CX 3 10, .CX 3 8, .CX 3 4, .CX 4 3,
  .CX 2 9, .CX 2 6, .CX 2 3, .CX 3 2, .CX 1 8, .CX 1 7,
  .CX 1 2, .CX 0 7, .CX 0 6, .CX 6 0, .CX 23 20, .CX 25 20,
  .CX 26 20, .CX 28 20, .CX 31 20, .CX 33 20, .CX 34 20, .CX 36 20,
  .CCX 20 6 0, .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5,
  .CX 11 9, .CX 11 8, .CX 11 7, .CX 11 6, .CX 11 4, .CX 11 3,
  .CX 11 1, .CX 10 11, .CX 10 7, .CX 10 6, .CX 10 5, .CX 10 3,
  .CX 10 2, .CX 11 10, .CX 9 11, .CX 9 10, .CX 9 8, .CX 9 7,
  .CX 9 4, .CX 9 3, .CX 9 1, .CX 9 0, .CX 10 9, .CX 8 11,
  .CX 8 10, .CX 8 7, .CX 8 6, .CX 8 5, .CX 8 4, .CX 8 3,
  .CX 8 2, .CX 8 0, .CX 7 8, .CX 7 1, .CX 8 7, .CX 6 9,
  .CX 6 0, .CX 9 6, .CX 5 11, .CX 5 9, .CX 5 8, .CX 5 7,
  .CX 5 3, .CX 5 2, .CX 5 1, .CX 5 0, .CX 7 5, .CX 4 8,
  .CX 4 5, .CX 4 2, .CX 4 0, .CX 3 11, .CX 3 10, .CX 3 9,
  .CX 3 8, .CX 3 5, .CX 3 4, .CX 3 2, .CX 2 10, .CX 2 9,
  .CX 2 4, .CX 2 3, .CX 3 2, .CX 1 8, .CX 1 7, .CX 7 1,
  .CX 0 9, .CX 0 6, .CX 6 0, .CX 24 20, .CX 25 20, .CX 28 20,
  .CX 29 20, .CX 30 20, .CX 31 20, .CX 34 20, .CX 35 20, .CCX 20 6 0,
  .CCX 20 7 1, .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 9,
  .CX 11 8, .CX 11 7, .CX 11 6, .CX 11 5, .CX 11 3, .CX 11 2,
  .CX 11 1, .CX 11 0, .CX 10 11, .CX 10 8, .CX 10 7, .CX 10 6,
  .CX 10 1, .CX 10 0, .CX 9 10, .CX 9 3, .CX 10 9, .CX 8 11,
  .CX 8 2, .CX 11 8, .CX 7 10, .CX 7 9, .CX 7 8, .CX 7 5,
  .CX 7 4, .CX 7 3, .CX 7 2, .CX 7 1, .CX 8 7, .CX 5 10,
  .CX 5 9, .CX 5 8, .CX 5 7, .CX 5 4, .CX 5 3, .CX 5 2,
  .CX 5 1, .CX 7 5, .CX 4 11, .CX 4 7, .CX 4 6, .CX 4 5,
  .CX 4 2, .CX 4 1, .CX 3 10, .CX 3 9, .CX 9 3, .CX 2 11,
  .CX 2 8, .CX 8 2, .CX 1 11, .CX 1 10, .CX 1 9, .CX 1 4,
  .CX 1 3, .CX 1 2, .CX 0 11, .CX 0 10, .CX 0 7, .CX 0 5,
  .CX 0 1, .CX 1 0, .CX 26 20, .CX 27 20, .CX 28 20, .CX 29 20,
  .CX 34 20, .CX 35 20, .CX 36 20, .CX 37 20, .CCX 20 6 0, .CCX 20 7 1,
  .CCX 20 8 2, .CCX 20 9 3, .CCX 20 10 4, .CCX 20 11 5, .CX 11 10, .CX 11 5,
  .CX 11 4, .CX 10 11, .CX 10 4, .CX 11 10, .CX 9 11, .CX 9 10,
  .CX 9 7, .CX 9 4, .CX 9 2, .CX 9 0, .CX 8 5, .CX 8 3,
  .CX 8 2, .CX 7 11, .CX 7 10, .CX 7 8, .CX 7 6, .CX 7 5,
  .CX 7 0, .CX 8 7, .CX 6 7, .CX 6 5, .CX 6 1, .CX 7 6,
  .CX 5 8, .CX 5 7, .CX 5 4, .CX 5 1, .CX 5 0, .CX 7 5,
  .CX 4 10, .CX 4 8, .CX 4 7, .CX 4 5, .CX 4 1, .CX 4 0,
  .CX 5 4, .CX 3 9, .CX 3 8, .CX 3 7, .CX 3 6, .CX 3 0,
  .CX 6 3, .CX 2 10, .CX 2 9, .CX 2 4, .CX 2 3, .CX 2 0,
  .CX 3 2, .CX 1 11, .CX 1 10, .CX 1 8, .CX 1 7, .CX 1 5,
  .CX 1 4, .CX 1 0, .CX 4 1, .CX 0 11, .CX 0 8, .CX 0 5,
  .CX 0 1, .CX 30 20, .CX 31 20, .CX 32 20, .CX 33 20, .CX 34 20,
  .CX 35 20, .CX 36 20, .CX 37 20
]

def fieldCore (p : Nat) (mirror : Bool) : Program := Id.run do
  if p == 7 then return if mirror then revCore7.reverse else revCore7
  if p == 21 then return if mirror then revCore21.reverse else revCore21
  if p == 31 then return if mirror then revCore31.reverse else revCore31
  if p == 73 then return if mirror then orderNineSix.reverse else orderNineSix
  if p == 471 then return if mirror then orderSeventeen471.reverse else orderSeventeen471
  if p == 313 then return if mirror then orderSeventeen313.reverse else orderSeventeen313
  if p == 257 then return if mirror then primaryShift8.reverse else primaryShift8
  if p == 1193 then return if mirror then dihedralCore1193.reverse else dihedralCore1193
  if p == 1571 then return if mirror then dihedralCore1571.reverse else dihedralCore1571
  if p == 4593 then return if mirror then dihedralCore4593.reverse else dihedralCore4593
  if p == 5349 then return if mirror then dihedralCore5349.reverse else dihedralCore5349
  if p == 5981 then return if mirror then dihedralCore5981.reverse else dihedralCore5981
  if p == 6891 then return if mirror then dihedralCore6891.reverse else dihedralCore6891
  let d := fieldDegree p
  if d == 1 then return []
  let xs := List.range d
  let ys := (List.range d).map (12 + ·)
  let (a,b) := (20,21)
  let tags := (List.range 16).map (22 + ·)
  let copy := (xs.zip ys).map (fun (x,y) => Instr.CX x y)
  let ops := (products p mirror).flatMap fun (xm,tm,om) => Id.run do
    let left := (selected d xm).map (fun i => Instr.CX (xs[i]!) a)
    let right := (selected 16 tm).map (fun k => Instr.CX (tags[k]!) b)
    let out := selected d om
    let compute := match out with
      | [] => []
      | j0 :: rest =>
        let fan := rest.map (fun j => Instr.CX (ys[j0]!) (ys[j]!))
        fan ++ [Instr.CCX a b (ys[j0]!)] ++ fan.reverse
    return left ++ right ++ compute ++ right.reverse ++ left.reverse
  let erase := (List.range d).map fun i =>
    let mask := (eraseMasks p mirror)[i]!
    let pairs := (List.range 16).flatMap fun k => (List.range d).filterMap fun j =>
      if mask.testBit (k*d+j) then some (Correction.CZ (tags[k]!) (ys[j]!))
      else none
    Instr.measureX (xs[i]!) [] (.Z (ys[i]!) :: pairs)
  let move := (xs.zip ys).flatMap (fun (x,y) => [Instr.CX y x, Instr.CX x y])
  return copy ++ ops ++ erase ++ move

def fieldPlace (n offset q : Nat) : Wire :=
  if q < 12 then offset + q else if q < 22 then n + 16 + (q-12) else n + (q-22)

def stage (n offset d m h : Nat) : Program :=
  let inc := 2^h
  if m ≤ inc then [] else
  let toggle := ((List.range 16).filter fun k => k.testBit h).map
    (fun k => Instr.CX (n+k) (n+24))
  let mix := (List.range (m-inc)).reverse.flatMap fun j =>
    (List.range d).map (fun i => Instr.CCX (n+24) (offset+d*j+i) (offset+d*(j+inc)+i))
  toggle ++ mix ++ toggle.reverse

def triangular (n offset d m : Nat) : Program :=
  (List.range 4).flatMap (stage n offset d m)

structure R8Step where
  tags : List Nat
  pre : List (Nat × Nat)
  src : Nat
  dst : Nat

def pascalR8Steps (mir : Bool) : List R8Step :=
  if mir then [
    ⟨[8, 9, 10, 11, 12, 13, 14, 15], [(1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0)], 0, 8⟩,
    ⟨[7, 8, 9, 10, 11, 12, 13, 14], [(3,1), (5,1), (7,1), (8,9)], 1, 8⟩,
    ⟨[6, 7, 8, 9, 10, 11, 12, 13], [(3,2), (6,2), (7,2), (8,10)], 2, 8⟩,
    ⟨[5, 6, 7, 8, 9, 10, 11, 12], [(7,3), (8,9), (8,10), (8,11)], 3, 8⟩,
    ⟨[4, 5, 6, 7, 8, 9, 10, 11], [(5,4), (6,4), (7,4), (8,12)], 4, 8⟩,
    ⟨[3, 4, 5, 6, 7, 8, 9, 10], [(7,5), (8,9), (8,12), (8,13)], 5, 8⟩,
    ⟨[2, 3, 4, 5, 6, 7, 8, 9], [(7,6), (8,10), (8,12), (8,14)], 6, 8⟩,
    ⟨[1, 2, 3, 4, 5, 6, 7, 8], [(8,9), (8,10), (8,11), (8,12), (8,13), (8,14), (8,15)], 7, 8⟩
  ]
  else [
    ⟨[1, 2, 3, 4, 5, 6, 7, 8], [(1,0), (2,0), (3,0), (4,0), (5,0), (6,0), (7,0)], 0, 8⟩,
    ⟨[2, 3, 4, 5, 6, 7, 8, 9], [(3,1), (5,1), (7,1), (8,9)], 1, 8⟩,
    ⟨[3, 4, 5, 6, 7, 8, 9, 10], [(3,2), (6,2), (7,2), (8,10)], 2, 8⟩,
    ⟨[4, 5, 6, 7, 8, 9, 10, 11], [(7,3), (8,9), (8,10), (8,11)], 3, 8⟩,
    ⟨[5, 6, 7, 8, 9, 10, 11, 12], [(5,4), (6,4), (7,4), (8,12)], 4, 8⟩,
    ⟨[6, 7, 8, 9, 10, 11, 12, 13], [(7,5), (8,9), (8,12), (8,13)], 5, 8⟩,
    ⟨[7, 8, 9, 10, 11, 12, 13, 14], [(7,6), (8,10), (8,12), (8,14)], 6, 8⟩,
    ⟨[8, 9, 10, 11, 12, 13, 14, 15], [(8,9), (8,10), (8,11), (8,12), (8,13), (8,14), (8,15)], 7, 8⟩
  ]

def r8Step (n off : Nat) (st : R8Step) : Program :=
  let toggle := st.tags.map (fun k => Instr.CX (n+k) (n+24))
  let pre := st.pre.map (fun p => Instr.CX (off+p.1) (off+p.2))
  toggle ++ pre ++ [Instr.CCX (n+24) (off+st.src) (off+st.dst)] ++ pre.reverse ++ toggle.reverse

def pascalR8 (n off : Nat) (mir : Bool) : Program :=
  (pascalR8Steps mir).flatMap (r8Step n off)

def primary (n offset p m : Nat) (mirror : Bool) : Program :=
  let d := fieldDegree p
  let scalar := (List.range m).flatMap fun j =>
    renameProgram (fieldPlace n (offset+d*j)) (fieldCore p mirror)
  let shift := if d == 8 && m == 2 then pascalR8 n offset mirror
    else let t := triangular n offset d m; if mirror then t.reverse else t
  scalar ++ shift

def components (n : Nat) (mirror : Bool) : Nat → List (Nat × Nat) → Program
  | _, [] => []
  | offset, (p,m) :: tail => primary n offset p m mirror ++
      components n mirror (offset + fieldDegree p * m) tail

def logical (n : Nat) (mirror : Bool) : Program :=
  let basis := (basisNetwork n).map (fun (i,j) => Instr.CX i j)
  basis ++ components n mirror 0 (schedule n) ++ basis.reverse

def barrelWidth (s : Nat) : Nat :=
  (if 224 ≤ s+15 ∧ s+15 ≤ 286 then min 256 (511-(s+15)) else if 257 ≤ s+15 then 512-(s+15) else min 257 (Partial.railP (s+15))) - Shadow7.sbP s

def place (s q : Nat) : Wire :=
  let n := barrelWidth s
  if q < n then Shadow7.bankW s q else if q < n+16 then Partial.tagsP.getD (q-n) 1560
  else Shadow7.poolW s (17 + (q-n-16)%10)

def barrel (s : Nat) (mirror : Bool) : Program :=
  renameProgram (place s) (logical (barrelWidth s) mirror)

def barrelT (s : Nat) (_mirror : Bool) : Nat := (measuredCosts (barrelWidth s)).1
def barrelM (s : Nat) (_mirror : Bool) : Nat := (measuredCosts (barrelWidth s)).2.1
def barrelSlots (s : Nat) (mirror : Bool) : Nat :=
  let v := (measuredCosts (barrelWidth s)).2.2
  if mirror then v.2 else v.1

def beforeReference (s : Nat) : List GateMirror.Gate :=
  let b := Shadow7.sbP s
  Shadow7.fix0P s b ++ Partial.leaveFix1 s b ++ Shadow7.fix2P s b ++ Partial.leaveFix3 s b ++
    Partial.leaveFix4 s b ++ Shadow7.leaveFix5Move s b ++ Shadow7.leaveAdjust s

def afterReference (s : Nat) : List GateMirror.Gate :=
  let b := Shadow7.sbP s
  Shadow7.fix8P s b ++ Shadow7.glueG3 s ++ Shadow7.leaveJoinMove s ++ Shadow7.fix10P s b ++
    Partial.leaveFix11 s b ++ Partial.leaveFix12 s b ++ Shadow7.leaveLowStore s ++
    Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

-- ==== begin DeadJoin (credited to spariev 65b176b3) ====
end ECDSAAdd.Entrant.StairPacket.CRTBarrel

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
def wordOpen (a : Wire) : List HighBankJoin.Column → List Gate
  | [] => []
  | r::rs => toggleG a r.hot ++ pairGM r.low a r.shadow r.tube ++ wordOpen a rs

def wordClose (a : Wire) : List HighBankJoin.Column → List Gate
  | [] => []
  | r::rs => wordClose a rs ++ toggleG a r.hot

theorem word_split (a : Wire) (rs tail : List HighBankJoin.Column) :
    wordGM a (rs++tail) = wordOpen a rs ++ (wordGM a tail ++ wordClose a rs) := by
  induction rs with
  | nil => simp [wordGM,wordOpen,wordClose]
  | cons r rs ih => simp only [List.cons_append,wordGM,wordOpen,wordClose,ih,List.append_assoc]

def cols16 (s : Nat) : List HighBankJoin.Column :=
  (List.range 16).map fun i => ⟨decide (i < Shadow7.lowsP s),
    if i < 16 then some (tagsP.getD i 0) else none, Shadow7.a0P s - 1 + i, Shadow7.bankW s i⟩

def lastCol (s : Nat) : HighBankJoin.Column :=
  ⟨false,none,Shadow7.a0P s - 1 + 16,Shadow7.bankW s 16⟩

theorem cols_split : ∀ j : Fin 26, j.val≤24 →
    Shadow7.columnsP (start j) = cols16 (start j) ++ [lastCol (start j)] := by
  intro j hi
  have high : ¬16 < Shadow7.lowsP (start j) := by revert j; decide +kernel
  simp only [Shadow7.columnsP,cols16,List.range_succ,List.map_append,List.map_cons,List.map_nil,
    decide_eq_false high,show ¬16<16 by decide,if_false,lastCol]

def postEntry (s : Nat) : List Gate :=
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++
  Shadow7.leaveFix5Move s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++
  Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.glueG3 s ++ keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordOpen 1614 (cols16 s)

def pair16 (s : Nat) : List Gate :=
  [.cx (Shadow7.a0P s - 1 + 16) (Shadow7.bankW s 16),.cx (Shadow7.bankW s 16) (Shadow7.a0P s - 1 + 16),
   .pop 1614 (Shadow7.bankW s 16) (Shadow7.a0P s - 1 + 16)]

def afterWord (s : Nat) : List Gate :=
  wordClose 1614 (cols16 s) ++ Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++
  leaveFix12 s (Shadow7.sbP s) ++ Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++
  Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem post_keeps_checked : ∀ j : Fin 26, j.val≤24 →
    (postEntry (start j)).all (fun g => decide (target g ≠ Shadow7.a0P (start j) - 1 + 16)) = true := by
  decide +kernel


theorem pair_layout_checked : ∀ j : Fin 26, j.val≤24 →
  [1614,Shadow7.a0P (start j) - 1 + 16,Shadow7.bankW (start j) 16].Nodup := by decide +kernel

def shortenedOps (s : Nat) : List Gate :=
  LeaveJ7.entryOps s ++ postEntry s ++ afterWord s



-- Explicit 3d shape; cached 83c has a different kept width.

def referenceOps (s : Nat) : List Gate :=
  Shadow7.fix0P s (Shadow7.sbP s) ++ leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++ Shadow7.leaveFix5Move s (Shadow7.sbP s) ++
  Shadow7.leaveAdjust s ++ Shadow7.leaveBarrel s ++ Shadow7.fix8P s (Shadow7.sbP s) ++
  Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (Shadow7.columnsP s)) ++
  Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++
  Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem reference_shape (j : Fin 26) (hi : j.val≤24) :
    referenceOps (start j) = LeaveJ7.entryOps (start j) ++
      (postEntry (start j) ++ (pair16 (start j) ++ afterWord (start j))) := by
  simp only [referenceOps,LeaveJ7.entryOps,postEntry,afterWord,cols_split j hi,word_split,
    wordGM,toggleG,pairGM,lastCol,pair16,Bool.false_eq_true,if_false,
    List.append_nil,List.nil_append,List.append_assoc]

theorem wordOpenClose (a : Wire) (rs : List HighBankJoin.Column) :
    wordGM a rs = wordOpen a rs ++ wordClose a rs := by
  simpa only [List.append_nil,wordGM,List.nil_append] using word_split a rs []

def afterShort (s : Nat) : List Gate :=
  Shadow7.fix8P s (Shadow7.sbP s) ++
  Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (cols16 s)) ++
  Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++
  Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem shortened_shape (s : Nat) : shortenedOps s = CRTBarrel.beforeReference s ++
    (Shadow7.leaveBarrel s ++ afterShort s) := by
  simp only [shortenedOps,postEntry,afterWord,afterShort,LeaveJ7.entryOps,
    CRTBarrel.beforeReference,wordOpenClose,List.append_assoc]

def scanTail (s : Nat) : List Gate :=
  leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++ postEntry s ++ afterWord s

def scanShortenedOps (s : Nat) : List Gate := DeadScan.fix0M s (Shadow7.sbP s) ++ scanTail s

theorem shortened_scan_shape (s : Nat) : shortenedOps s =
    Shadow7.fix0P s (Shadow7.sbP s) ++ scanTail s := by
  simp only [shortenedOps,LeaveJ7.entryOps,scanTail,List.append_assoc]

theorem scan_physical : ∀ j : Fin 26, j.val≤24 →
    (DeadScan.fix0M (start j) (Shadow7.sbP (start j))).all proper=true := by decide +kernel

def beforeScanTail (s : Nat) : List Gate :=
  leaveFix1 s (Shadow7.sbP s) ++ Shadow7.fix2P s (Shadow7.sbP s) ++
  leaveFix3 s (Shadow7.sbP s) ++ leaveFix4 s (Shadow7.sbP s) ++
  Shadow7.leaveFix5Move s (Shadow7.sbP s) ++ Shadow7.leaveAdjust s

def beforeScan (s : Nat) : List Gate :=
  DeadScan.fix0M s (Shadow7.sbP s) ++ beforeScanTail s

def beforeAll (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s+3) (Shadow7.e0P s+4) 1559 2 (beforeScan s)

def afterAll (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s+3) (Shadow7.e0P s+4) 1559 1 (afterShort s)

def allOps (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s+3) (Shadow7.e0P s+4) 1559 2 (scanShortenedOps s)

theorem scan_shortened_shape (s : Nat) : scanShortenedOps s = beforeScan s ++
    (Shadow7.leaveBarrel s ++ afterShort s) := by
  simp only [scanShortenedOps,scanTail,postEntry,afterWord,beforeScan,beforeScanTail,afterShort,
    wordOpenClose,List.append_assoc]

theorem all_checked : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.check (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) 1559
      2 false (scanShortenedOps (start j)) = true := by decide +kernel

theorem before_all_checked : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.check (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) 1559
      2 false (beforeScan (start j)) = true := by
  intro j hi
  exact FlagLeave.check_prefix _ _ _ _ 2 false (beforeScan (start j))
    (Shadow7.leaveBarrel (start j) ++ afterShort (start j))
    (by rw [←scan_shortened_shape]; exact all_checked j hi)

theorem removed_before : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.removed (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 2 (beforeScan (start j)) =
      [.make (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] := by decide +kernel

theorem removed_barrel : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.removed (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1
      (Shadow7.leaveBarrel (start j)) = [] := by decide +kernel

theorem all_split (j : Fin 26) (hi : j.val≤24) : allOps (start j) =
    beforeAll (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterAll (start j)) := by
  rw [allOps,scan_shortened_shape,FlagLeave.cut_append,removed_before j hi]
  simp only [List.length_singleton,show 2-1=1 by decide]
  rw [FlagLeave.cut_append,removed_barrel j hi]
  simp only [List.length_nil,Nat.sub_zero]
  rw [FlagLeave.cut_of_removed_nil _ _ _ _ _ (removed_barrel j hi)]
  rfl

def afterReference (s : Nat) : List Gate :=
  Shadow7.fix8P s (Shadow7.sbP s) ++
  Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (Shadow7.columnsP s)) ++
  Shadow7.fix10P s (Shadow7.sbP s) ++ leaveFix11 s (Shadow7.sbP s) ++ leaveFix12 s (Shadow7.sbP s) ++
  Shadow7.leaveLowStore s ++ Shadow7.leaveStoreMapped s ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

def afterOpen (s : Nat) : List Gate :=
  Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.glueG3 s ++ keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++
    wordOpen 1614 (cols16 s)
theorem inverse_append (a b : List Gate) : inverse (a ++ b) = inverse b ++ inverse a := by
  simp only [inverse,List.map_append,List.reverse_append]

theorem cut_metrics (a c : List Gate) (active sh tu : Wire) :
    let old := a ++ ([Gate.cx sh tu,Gate.cx tu sh,Gate.pop active tu sh] ++ c)
    let new := a ++ c
    toffoliCount (GateMirror.forward old) = toffoliCount (GateMirror.forward new) ∧
    toffoliCount (GateMirror.inverse old) = toffoliCount (GateMirror.inverse new)+1 ∧
    measurementCount (GateMirror.forward old) = measurementCount (GateMirror.forward new)+1 ∧
    measurementCount (GateMirror.inverse old) = measurementCount (GateMirror.inverse new) ∧
    gateSlots (GateMirror.forward old) = gateSlots (GateMirror.forward new)+4 ∧
    gateSlots (GateMirror.inverse old) = gateSlots (GateMirror.inverse new)+3 := by
  dsimp only
  simp only [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,
    List.countP_append,List.length_append,List.countP_cons,List.countP_nil,List.length_cons,
    List.length_nil,isCCX,isMake,isPop,if_false,if_true,Bool.false_eq_true]
  omega


set_option linter.constructorNameAsVariable false

theorem after_short_metrics (j : Fin 26) (hi : j.val≤24) :
    toffoliCount (GateMirror.forward (afterReference (start j))) =
      toffoliCount (GateMirror.forward (afterShort (start j))) ∧
    toffoliCount (GateMirror.inverse (afterReference (start j))) =
      toffoliCount (GateMirror.inverse (afterShort (start j)))+1 ∧
    measurementCount (GateMirror.forward (afterReference (start j))) =
      measurementCount (GateMirror.forward (afterShort (start j)))+1 ∧
    measurementCount (GateMirror.inverse (afterReference (start j))) =
      measurementCount (GateMirror.inverse (afterShort (start j))) ∧
    gateSlots (GateMirror.forward (afterReference (start j))) =
      gateSlots (GateMirror.forward (afterShort (start j)))+4 ∧
    gateSlots (GateMirror.inverse (afterReference (start j))) =
      gateSlots (GateMirror.inverse (afterShort (start j)))+3 := by
  have oldshape : afterReference (start j) = afterOpen (start j) ++
      (pair16 (start j) ++ afterWord (start j)) := by
    simp only [afterReference,afterOpen,afterWord,cols_split j hi,word_split,wordGM,toggleG,
      pairGM,lastCol,pair16,Bool.false_eq_true,if_false,List.append_nil,List.nil_append,List.append_assoc]
  have newshape : afterShort (start j) = afterOpen (start j) ++ afterWord (start j) := by
    simp only [afterShort,afterOpen,afterWord,wordOpenClose,List.append_assoc]
  rw [oldshape,newshape]
  exact cut_metrics _ _ _ _ _

theorem before_scan_metrics (s : Nat) :
    toffoliCount (GateMirror.forward (beforeScan s))+1 = toffoliCount (GateMirror.forward (CRTBarrel.beforeReference s)) ∧
    toffoliCount (GateMirror.inverse (beforeScan s)) = toffoliCount (GateMirror.inverse (CRTBarrel.beforeReference s)) ∧
    measurementCount (GateMirror.forward (beforeScan s)) = measurementCount (GateMirror.forward (CRTBarrel.beforeReference s))+1 ∧
    measurementCount (GateMirror.inverse (beforeScan s)) = measurementCount (GateMirror.inverse (CRTBarrel.beforeReference s)) ∧
    gateSlots (GateMirror.forward (beforeScan s)) = gateSlots (GateMirror.forward (CRTBarrel.beforeReference s))+1 ∧
    gateSlots (GateMirror.inverse (beforeScan s)) = gateSlots (GateMirror.inverse (CRTBarrel.beforeReference s)) := by
  have oldshape : CRTBarrel.beforeReference s = Shadow7.fix0P s (Shadow7.sbP s) ++ beforeScanTail s := by
    simp only [CRTBarrel.beforeReference,beforeScanTail,List.append_assoc]
  obtain ⟨nt,nm,ns⟩ := DeadScan.fix0M_counts s (Shadow7.sbP s)
  obtain ⟨ot,_it,om,_im,os,_is⟩ := (Shadow7.counts_fix0P s (Shadow7.sbP s)).programs
  simp only [Nat.add_zero] at ot os
  simp only [beforeScan,oldshape,forward_app,inverse_append,DeadScan.fix0M_inverse,
    toffoliCount_append,measurementCount_append,gateSlots_append,nt,nm,ns,ot,om,os]
  refine ⟨?_,trivial,?_,trivial,?_,trivial⟩ <;> omega

end ECDSAAdd.Entrant.StairPacket.DeadJoin

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem removed_after : ∀ j : Fin 26, j.val≤24 →
    FlagLeave.removed (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559 1 (afterShort (start j)) =
      [.pop (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559] := by decide +kernel

theorem all_local_deltas (j : Fin 26) (hi : j.val≤24) :
    toffoliCount (GateMirror.forward (beforeAll (start j))) +
      toffoliCount (GateMirror.forward (afterAll (start j))) + 2 =
      toffoliCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      toffoliCount (GateMirror.forward (afterReference (start j))) ∧
    toffoliCount (inverse (afterAll (start j))) + toffoliCount (inverse (beforeAll (start j))) + 2 =
      toffoliCount (inverse (afterReference (start j))) + toffoliCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    measurementCount (GateMirror.forward (beforeAll (start j))) +
      measurementCount (GateMirror.forward (afterAll (start j))) + 1 =
      measurementCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      measurementCount (GateMirror.forward (afterReference (start j))) ∧
    measurementCount (inverse (afterAll (start j))) + measurementCount (inverse (beforeAll (start j))) + 1 =
      measurementCount (inverse (afterReference (start j))) + measurementCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    gateSlots (GateMirror.forward (beforeAll (start j))) + gateSlots (GateMirror.forward (afterAll (start j))) + 4 =
      gateSlots (GateMirror.forward (CRTBarrel.beforeReference (start j))) + gateSlots (GateMirror.forward (afterReference (start j))) ∧
    gateSlots (inverse (afterAll (start j))) + gateSlots (inverse (beforeAll (start j))) + 4 =
      gateSlots (inverse (afterReference (start j))) + gateSlots (inverse (CRTBarrel.beforeReference (start j))) := by
  have flag := FlagLeave.pair_savings (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) 1559
    (beforeScan (start j)) (afterShort (start j)) (removed_before j hi) (removed_after j hi)
  have scan := before_scan_metrics (start j)
  have join := after_short_metrics j hi
  dsimp only [beforeAll,afterAll]
  omega
end ECDSAAdd.Entrant.StairPacket.DeadJoin

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem scan_replacement_member (s h : Nat) (g : Gate) (hg : g ∈ DeadScan.fix0M s h) :
    ∃ old ∈ Shadow7.fix0P s h, g.wires=old.wires ∧ proper g=proper old := by
  have shape : Shadow7.fix0P s h = (Shadow7.fix0P s h).take 51 ++
      [.ccx (s+30) (h+802) (s+h+47)] ++ (Shadow7.fix0P s h).drop 52 := rfl
  rcases List.mem_append.mp hg with pre | tail
  · rcases List.mem_append.mp pre with head | cell
    · exact ⟨g,List.mem_of_mem_take head,rfl,rfl⟩
    · have eg : g = .pop (s+30) (h+802) (s+h+47) := List.mem_singleton.mp cell
      subst g
      refine ⟨.ccx (s+30) (h+802) (s+h+47),?_,rfl,rfl⟩
      rw [shape]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  · exact ⟨g,List.mem_of_mem_drop tail,rfl,rfl⟩

theorem before_scan_member (s : Nat) (g : Gate) (hg : g∈beforeScan s) :
    ∃ old∈CRTBarrel.beforeReference s,g.wires=old.wires ∧ proper g=proper old := by
  have shape : CRTBarrel.beforeReference s = Shadow7.fix0P s (Shadow7.sbP s) ++ beforeScanTail s := by
    simp only [CRTBarrel.beforeReference,beforeScanTail,List.append_assoc]
  rw [beforeScan,List.mem_append] at hg
  rcases hg with head | tail
  · obtain ⟨old,ho,hw,hp⟩ := scan_replacement_member s (Shadow7.sbP s) g head
    exact ⟨old,by rw [shape]; exact List.mem_append_left _ ho,hw,hp⟩
  · exact ⟨g,by rw [shape]; exact List.mem_append_right _ tail,rfl,rfl⟩

theorem before_scan_allW {P : Wire → Prop} (s : Nat)
    (h : AllW P (CRTBarrel.beforeReference s)) : AllW P (beforeScan s) := by
  intro g hg q hq
  obtain ⟨old,ho,hw,hp⟩ := before_scan_member s g hg
  exact h old ho q (hw ▸ hq)

theorem before_scan_proper (s : Nat) (h : Proper (CRTBarrel.beforeReference s)) : Proper (beforeScan s) := by
  intro g hg
  obtain ⟨old,ho,hw,hp⟩ := before_scan_member s g hg
  exact hp.trans (h old ho)

theorem after_short_member (j : Fin 26) (hi : j.val≤24) (g : Gate) (hg : g∈afterShort (start j)) :
    g∈afterReference (start j) := by
  have oldshape : afterReference (start j) = afterOpen (start j) ++
      (pair16 (start j) ++ afterWord (start j)) := by
    simp only [afterReference,afterOpen,afterWord,cols_split j hi,word_split,wordGM,toggleG,
      pairGM,lastCol,pair16,Bool.false_eq_true,if_false,List.append_nil,List.nil_append,List.append_assoc]
  have newshape : afterShort (start j) = afterOpen (start j) ++ afterWord (start j) := by
    simp only [afterShort,afterOpen,afterWord,wordOpenClose,List.append_assoc]
  rw [oldshape]
  rw [newshape,List.mem_append] at hg
  rcases hg with head | tail
  · exact List.mem_append_left _ head
  · exact List.mem_append_right _ (List.mem_append_right _ tail)

theorem after_short_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val≤24)
    (h : AllW P (afterReference (start j))) : AllW P (afterShort (start j)) :=
  fun g hg q hq => h g (after_short_member j hi g hg) q hq

theorem after_short_proper (j : Fin 26) (hi : j.val≤24)
    (h : Proper (afterReference (start j))) : Proper (afterShort (start j)) :=
  fun g hg => h g (after_short_member j hi g hg)
end ECDSAAdd.Entrant.StairPacket.DeadJoin


-- ==== begin FlagCut57 (credited to ercumentyildirim ae9d602d) ====
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-- Prefix of `beforeScan` before Fix5Move's row-0 swap. -/
def beforePre5 (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  DeadScan.fix0M s b ++ leaveFix1 s b ++ Shadow7.fix2P s b ++ leaveFix3 s b ++
    leaveFix4 s b ++ (Shadow7.fix5P s b).take 27

/-- Stock Fix5Move row-0 controlled swap. -/
def row0Old (s : Nat) : List Gate :=
  [.cx (Shadow7.a0P s - 1 + 0) (Shadow7.e0P s + 6),
   .ccx (tagsP.getD 0 0) (Shadow7.e0P s + 6) (Shadow7.a0P s - 1 + 0),
   .cx (Shadow7.a0P s - 1 + 0) (Shadow7.e0P s + 6)]

/-- Row-0 swap specialized for `e0+6 = 0`: fresh Toffoli copy plus CNOT. -/
def row0New (s : Nat) : List Gate :=
  [.make (tagsP.getD 0 0) (Shadow7.a0P s - 1 + 0) (Shadow7.e0P s + 6),
   .cx (Shadow7.e0P s + 6) (Shadow7.a0P s - 1 + 0)]

/-- Suffix of `beforeScan` after Fix5Move's row-0 swap. -/
def beforePost5 (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  rowGates (Shadow7.e0P s + 6) ((Shadow7.moveRows s).drop 1) ++ (Shadow7.fix5P s b).drop 43 ++
    Shadow7.leaveAdjust s

theorem moveRows_cut5 (s : Nat) :
    Shadow7.moveRows s = (tagsP.getD 0 0, Shadow7.a0P s - 1 + 0) :: (Shadow7.moveRows s).drop 1 := rfl

theorem beforeScan_split5 (s : Nat) :
    beforeScan s = beforePre5 s ++ (row0Old s ++ beforePost5 s) := by
  have e := moveRows_cut5 s
  simp only [beforeScan, beforeScanTail, beforePre5, row0Old, beforePost5, Shadow7.leaveFix5Move]
  conv_lhs => rw [e]
  simp only [rowGates, List.append_assoc, List.cons_append, List.nil_append]

def beforePre5Cut (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 (beforePre5 s)

def before5 (s : Nat) : List Gate :=
  beforePre5Cut s ++ (row0New s ++ beforePost5 s)

theorem removed_pre5 : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 2 (beforePre5 (start j)) =
      [.make (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] := by decide +kernel

theorem removed_post5 : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 1
      (row0Old (start j) ++ beforePost5 (start j)) = [] := by decide +kernel

theorem beforeAll_split5 (j : Fin 26) (hi : j.val ≤ 24) :
    beforeAll (start j) = beforePre5Cut (start j) ++ (row0Old (start j) ++ beforePost5 (start j)) := by
  rw [beforeAll, beforeScan_split5, FlagLeave.cut_append, removed_pre5 j hi]
  simp only [List.length_singleton, show 2 - 1 = 1 by decide]
  rw [FlagLeave.cut_of_removed_nil _ _ _ _ _ (removed_post5 j hi)]
  rfl

/-- `leaveLowStore` after its leading 3 flag gates. -/
def lowRest7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s - 1; let bs := (List.range L).map (Shadow7.b0P s + ·)
  [.cx (Shadow7.a0P s - 1) 1557, .x 1557, .make (Shadow7.b0P s - 1) 1557 1558] ++
  (List.range L).map (fun i => .make 1556 (Shadow7.a0P s + i) (Shadow7.b0P s + i)) ++ xsG bs ++
    addG bs ((List.range (L-1)).map (1559 + ·)) 1558 ++ xsG bs ++
    [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557]

/-- `leaveStoreMapped` up to its carry chain. -/
def storeHead7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 2; let H := Shadow7.liveW s - L
  [.x 1558, .x top] ++ xsG ((List.range H).map (fun i => Shadow7.bankW s (L+i)))

def topW7 (s : Nat) : Wire := Shadow7.a0P s + Shadow7.lowsP s - 2

/-- Prefix of `afterShort` up through the flag erasure at the start of `leaveLowStore`. -/
def afterPre7Head (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  Shadow7.fix8P s b ++ Shadow7.glueG3 s ++ (keptG (tagsP.getD · 0) (fun i => Shadow7.a0P s - 1 + i) 1613 0 8 ++ wordGM 1614 (cols16 s)) ++
  Shadow7.fix10P s b ++ leaveFix11 s b ++ leaveFix12 s b ++
  [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559]

def afterPre7Tail (s : Nat) : List Gate := lowRest7 s ++ storeHead7 s

/-- The store chain below level 0. -/
def chainMid7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 2; let H := Shadow7.liveW s - L
  chainG (Shadow7.storeW s) (fun i => if i = 0 then top else Shadow7.bankW s (L+i-1))
    [.cx (Shadow7.storeW s (H+1)) 1557, .x 1557] 1 H

/-- Suffix of `afterShort` after the store chain's level-0 pop. -/
def afterPost7 (s : Nat) : List Gate :=
  let L := Shadow7.lowsP s; let top := Shadow7.a0P s + L - 2; let H := Shadow7.liveW s - L
  let hi := (List.range H).map (fun i => Shadow7.bankW s (L+i))
  let seq2 := (List.range L).map (Shadow7.b0P s - 1 + ·)
  xsG hi.reverse ++ [.x top, .x 1558, .make 1556 1557 1558, .x 1558] ++ xsG seq2 ++
    chainG (1558 + ·) (Shadow7.b0P s - 1 + ·) [.cx (1558+L) 1556, .x 1556] 0 L ++
    xsG seq2.reverse ++ [.x 1558] ++ Shadow7.leaveLowClose s ++ Shadow7.leaveClose s

theorem store0_7 (s : Nat) : Shadow7.storeW s 0 = 1558 := by
  simp only [Shadow7.storeW, Partial.storeW]
  split_ifs <;> ((try unfold Shadow7.e0P at *); (try unfold Wire at *); omega)

theorem store1_7 (s : Nat) : Shadow7.storeW s 1 = 1559 := by
  simp only [Shadow7.storeW, Partial.storeW]
  split_ifs <;> ((try unfold Shadow7.e0P at *); (try unfold Wire at *); omega)

theorem afterShort_split7 (s : Nat) :
    afterShort s = afterPre7Head s ++ (afterPre7Tail s ++
      ([.make 1558 (topW7 s) 1559] ++ (chainMid7 s ++ ([.pop 1558 (topW7 s) 1559] ++ afterPost7 s)))) := by
  simp only [afterShort, afterPre7Head, afterPre7Tail, lowRest7, storeHead7, topW7, chainMid7, afterPost7,
    Shadow7.leaveLowStore, Shadow7.leaveStoreMapped, Partial.chainG, Nat.zero_add, store0_7, store1_7,
    if_pos rfl, ite_true, if_true, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]

def afterPre7HeadCut (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 1 (afterPre7Head s)

def after7 (s : Nat) : List Gate :=
  afterPre7HeadCut s ++ (afterPre7Tail s ++
    ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s))))

theorem removed_afterPre7Head : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 1 (afterPre7Head (start j)) =
      [.pop (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559] := by decide +kernel

theorem afterAll_split7 (j : Fin 26) (hi : j.val ≤ 24) :
    afterAll (start j) = afterPre7HeadCut (start j) ++ (afterPre7Tail (start j) ++
      ([.make 1558 (topW7 (start j)) 1559] ++ (chainMid7 (start j) ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j))))) := by
  rw [afterAll, afterShort_split7, FlagLeave.cut_append, removed_afterPre7Head j hi]
  simp only [List.length_singleton, Nat.sub_self, FlagLeave.cut]
  rfl

theorem before5_deltas (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (before5 (start j))) = toffoliCount (GateMirror.forward (beforeAll (start j))) ∧
    toffoliCount (inverse (before5 (start j))) + 1 = toffoliCount (inverse (beforeAll (start j))) ∧
    measurementCount (GateMirror.forward (before5 (start j))) = measurementCount (GateMirror.forward (beforeAll (start j))) ∧
    measurementCount (inverse (before5 (start j))) = measurementCount (inverse (beforeAll (start j))) + 1 ∧
    gateSlots (GateMirror.forward (before5 (start j))) + 1 = gateSlots (GateMirror.forward (beforeAll (start j))) ∧
    gateSlots (inverse (before5 (start j))) = gateSlots (inverse (beforeAll (start j))) := by
  rw [beforeAll_split5 j hi, before5]
  simp only [row0Old, row0New, toffoli_forward, toffoli_inverse, meas_forward, meas_inverse, slots_forward, slots_inverse,
    List.countP_append, List.length_append, List.countP_cons, List.countP_nil, List.length_cons,
    List.length_nil, isCCX, isMake, isPop, if_false, if_true, Bool.false_eq_true]
  refine ⟨?_, ?_, trivial, ?_, ?_, ?_⟩ <;> omega

theorem after7_deltas (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (after7 (start j))) + 1 = toffoliCount (GateMirror.forward (afterAll (start j))) ∧
    toffoliCount (inverse (after7 (start j))) + 1 = toffoliCount (inverse (afterAll (start j))) ∧
    measurementCount (GateMirror.forward (after7 (start j))) + 1 = measurementCount (GateMirror.forward (afterAll (start j))) ∧
    measurementCount (inverse (after7 (start j))) + 1 = measurementCount (inverse (afterAll (start j))) ∧
    gateSlots (GateMirror.forward (after7 (start j))) + 1 = gateSlots (GateMirror.forward (afterAll (start j))) ∧
    gateSlots (inverse (after7 (start j))) + 1 = gateSlots (inverse (afterAll (start j))) := by
  rw [afterAll_split7 j hi, after7]
  have c1 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have c2 : ∀ a b t : Wire, toffoliCount (inverse [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have c3 : ∀ a b t : Wire, toffoliCount (GateMirror.forward [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have c4 : ∀ a b t : Wire, toffoliCount (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have c5 : ∀ b t : Wire, toffoliCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have c6 : ∀ b t : Wire, toffoliCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d1 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.make a b t]) = 0 := fun _ _ _ => rfl
  have d2 : ∀ a b t : Wire, measurementCount (inverse [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have d3 : ∀ a b t : Wire, measurementCount (GateMirror.forward [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have d4 : ∀ a b t : Wire, measurementCount (inverse [Gate.pop a b t]) = 0 := fun _ _ _ => rfl
  have d5 : ∀ b t : Wire, measurementCount (GateMirror.forward [Gate.cx b t]) = 0 := fun _ _ => rfl
  have d6 : ∀ b t : Wire, measurementCount (inverse [Gate.cx b t]) = 0 := fun _ _ => rfl
  have e1 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.make a b t]) = 1 := fun _ _ _ => rfl
  have e2 : ∀ a b t : Wire, gateSlots (inverse [Gate.make a b t]) = 2 := fun _ _ _ => rfl
  have e3 : ∀ a b t : Wire, gateSlots (GateMirror.forward [Gate.pop a b t]) = 2 := fun _ _ _ => rfl
  have e4 : ∀ a b t : Wire, gateSlots (inverse [Gate.pop a b t]) = 1 := fun _ _ _ => rfl
  have e5 : ∀ b t : Wire, gateSlots (GateMirror.forward [Gate.cx b t]) = 1 := fun _ _ => rfl
  have e6 : ∀ b t : Wire, gateSlots (inverse [Gate.cx b t]) = 1 := fun _ _ => rfl
  simp only [forward_app, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append,
    c1, c2, c3, c4, c5, c6, d1, d2, d3, d4, d5, d6, e1, e2, e3, e4, e5, e6]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem all_local_deltas57 (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (before5 (start j))) +
      toffoliCount (GateMirror.forward (after7 (start j))) + 3 =
      toffoliCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      toffoliCount (GateMirror.forward (afterReference (start j))) ∧
    toffoliCount (inverse (after7 (start j))) + toffoliCount (inverse (before5 (start j))) + 4 =
      toffoliCount (inverse (afterReference (start j))) + toffoliCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    measurementCount (GateMirror.forward (before5 (start j))) +
      measurementCount (GateMirror.forward (after7 (start j))) + 2 =
      measurementCount (GateMirror.forward (CRTBarrel.beforeReference (start j))) +
      measurementCount (GateMirror.forward (afterReference (start j))) ∧
    measurementCount (inverse (after7 (start j))) + measurementCount (inverse (before5 (start j))) + 1 =
      measurementCount (inverse (afterReference (start j))) + measurementCount (inverse (CRTBarrel.beforeReference (start j))) ∧
    gateSlots (GateMirror.forward (before5 (start j))) + gateSlots (GateMirror.forward (after7 (start j))) + 6 =
      gateSlots (GateMirror.forward (CRTBarrel.beforeReference (start j))) + gateSlots (GateMirror.forward (afterReference (start j))) ∧
    gateSlots (inverse (after7 (start j))) + gateSlots (inverse (before5 (start j))) + 5 =
      gateSlots (inverse (afterReference (start j))) + gateSlots (inverse (CRTBarrel.beforeReference (start j))) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := all_local_deltas j hi
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := before5_deltas j hi
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := after7_deltas j hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem row0New_proper : ∀ j : Fin 26, j.val ≤ 24 →
    (row0New (start j)).all proper = true := by decide +kernel

theorem top_cx_proper : ∀ j : Fin 26, j.val ≤ 24 →
    proper (.cx (topW7 (start j)) 1559) = true := by decide +kernel

theorem before5_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (beforeAll (start j))) : AllW P (before5 (start j)) := by
  rw [beforeAll_split5 j hi] at h
  intro x hx q hq
  rw [before5] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx) q hq
  · rcases List.mem_append.mp hx with hx | hx
    · refine h (.ccx (tagsP.getD 0 0) (Shadow7.e0P (start j) + 6) (Shadow7.a0P (start j) - 1 + 0))
        (List.mem_append_right _ (List.mem_append_left _ (by simp [row0Old]))) q ?_
      simp only [row0New, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;>
        simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢ <;> tauto
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx)) q hq

theorem before5_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (beforeAll (start j))) : Proper (before5 (start j)) := by
  rw [beforeAll_split5 j hi] at h
  intro x hx
  rw [before5] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x (List.mem_append_left _ hx)
  · rcases List.mem_append.mp hx with hx | hx
    · exact List.all_eq_true.mp (row0New_proper j hi) x hx
    · exact h x (List.mem_append_right _ (List.mem_append_right _ hx))

theorem after7_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (afterAll (start j))) : AllW P (after7 (start j)) := by
  rw [afterAll_split7 j hi] at h
  intro x hx q hq
  rw [after7] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx | rfl | hx | rfl | hx
  · exact h x (by simp [hx]) q hq
  · exact h x (by simp [hx]) q hq
  · refine h (.make 1558 (topW7 (start j)) 1559) (by simp) q ?_
    simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto
  · exact h x (by simp [hx]) q hq
  · refine h (.pop 1558 (topW7 (start j)) 1559) (by simp) q ?_
    simp only [GateMirror.Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; tauto
  · exact h x (by simp [hx]) q hq

theorem after7_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (afterAll (start j))) : Proper (after7 (start j)) := by
  rw [afterAll_split7 j hi] at h
  intro x hx
  rw [after7] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx | rfl | hx | rfl | hx
  · exact h x (by simp [hx])
  · exact h x (by simp [hx])
  · exact top_cx_proper j hi
  · exact h x (by simp [hx])
  · exact top_cx_proper j hi
  · exact h x (by simp [hx])

end ECDSAAdd.Entrant.StairPacket.DeadJoin
-- ==== end FlagCut57 ====

-- ==== begin KeptParity (credited to GordoAR a2ce2c3a; margin-16 port: bank rows a0P-1+i) ====
namespace ECDSAAdd.Entrant.StairPacket.KeptParity
open Arithmetic Partial GateMirror Challenge
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000

/-- The 8-row kept pass on local wires: 0 = the digit `1613`, 1..8 = tags 0..7, 9..16 = the cells of rows 0..7. -/
def old : List Gate := [.ccx 1 0 9, .ccx 2 0 10, .ccx 3 0 11, .ccx 4 0 12, .ccx 5 0 13, .ccx 6 0 14, .ccx 7 0 15, .ccx 8 0 16]

/-- Row 0 by parity: the tags are one-hot, so `tag0 & d = d ^ (tag1 & d) ^ .. ^ (tag7 & d)` whenever the digit can be set
only with a hot tag below 8 (`relation`). Row 0's Toffoli becomes one CX; the parity is carried on cell 0. -/
def replacement : List Gate := [.cx 0 9,
  .cx 10 9, .ccx 2 0 10, .cx 10 9,
  .cx 11 9, .ccx 3 0 11, .cx 11 9,
  .cx 12 9, .ccx 4 0 12, .cx 12 9,
  .cx 13 9, .ccx 5 0 13, .cx 13 9,
  .cx 14 9, .ccx 6 0 14, .cx 14 9,
  .cx 15 9, .ccx 7 0 15, .cx 15 9,
  .cx 16 9, .ccx 8 0 16, .cx 16 9]

def port (s : Nat) : Wire → Wire
  | 0 => 1613
  | i+1 => if i < 8 then tagsP.getD i 0 else Shadow7.a0P s - 1 + (i-7)

def placed (s : Nat) : List Gate := [.cx (port s 0) (port s 9),
  .cx (port s 10) (port s 9), .ccx (port s 2) (port s 0) (port s 10), .cx (port s 10) (port s 9),
  .cx (port s 11) (port s 9), .ccx (port s 3) (port s 0) (port s 11), .cx (port s 11) (port s 9),
  .cx (port s 12) (port s 9), .ccx (port s 4) (port s 0) (port s 12), .cx (port s 12) (port s 9),
  .cx (port s 13) (port s 9), .ccx (port s 5) (port s 0) (port s 13), .cx (port s 13) (port s 9),
  .cx (port s 14) (port s 9), .ccx (port s 6) (port s 0) (port s 14), .cx (port s 14) (port s 9),
  .cx (port s 15) (port s 9), .ccx (port s 7) (port s 0) (port s 15), .cx (port s 15) (port s 9),
  .cx (port s 16) (port s 9), .ccx (port s 8) (port s 0) (port s 16), .cx (port s 16) (port s 9)]

theorem physical : ∀ j : Fin 26, j.val ≤ 24 → (placed (start j)).all proper = true := by decide +kernel

theorem wiresCovered : ∀ j : Fin 26, j.val ≤ 24 → (placed (start j)).all (fun g =>
    g.wires.all (fun q => ((Shadow7.moveKept (start j)).flatMap Gate.wires).contains q)) = true := by decide +kernel

theorem counts : toffoliCount (GateMirror.forward replacement) + 1 = toffoliCount (GateMirror.forward old) ∧
    toffoliCount (inverse replacement) + 1 = toffoliCount (inverse old) ∧
    measurementCount (GateMirror.forward replacement) = measurementCount (GateMirror.forward old) ∧
    measurementCount (inverse replacement) = measurementCount (inverse old) ∧
    gateSlots (GateMirror.forward replacement) = gateSlots (GateMirror.forward old) + 14 ∧
    gateSlots (inverse replacement) = gateSlots (inverse old) + 14 := by decide

/-- The placed pass has one Toffoli fewer each way, no measurement, and 14 more slots each way: both passes are the
local passes renamed by `port s` (GordoAR's proof). -/
theorem cellCounts (s : Nat) :
    toffoliCount (GateMirror.forward (placed s)) + 1 = toffoliCount (GateMirror.forward (Shadow7.moveKept s)) ∧
    toffoliCount (inverse (placed s)) + 1 = toffoliCount (inverse (Shadow7.moveKept s)) ∧
    measurementCount (GateMirror.forward (placed s)) = measurementCount (GateMirror.forward (Shadow7.moveKept s)) ∧
    measurementCount (inverse (placed s)) = measurementCount (inverse (Shadow7.moveKept s)) ∧
    gateSlots (GateMirror.forward (placed s)) = gateSlots (GateMirror.forward (Shadow7.moveKept s)) + 14 ∧
    gateSlots (inverse (placed s)) = gateSlots (inverse (Shadow7.moveKept s)) + 14 := by
  have nf : GateMirror.forward (placed s) = renameProgram (port s) (GateMirror.forward replacement) := rfl
  have nr : inverse (placed s) = renameProgram (port s) (inverse replacement) := rfl
  have ofw : GateMirror.forward (Shadow7.moveKept s) = renameProgram (port s) (GateMirror.forward old) := rfl
  have obw : inverse (Shadow7.moveKept s) = renameProgram (port s) (inverse old) := rfl
  rw [nf, nr, ofw, obw]
  simp only [renameProgram_counts, Baselines.rename_gateSlots]
  exact counts

end ECDSAAdd.Entrant.StairPacket.KeptParity

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false

/-- `afterPre7Head` after its kept pass. -/
def afterPre7Rest (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  wordGM 1614 (cols16 s) ++ Shadow7.fix10P s b ++ leaveFix11 s b ++ leaveFix12 s b ++
  [.cx (Shadow7.e0P s + 3) 1560, .cx 1559 1560, .pop (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559]

/-- `afterPre7Head` in front of its kept pass. -/
def keptHead (s : Nat) : List Gate := Shadow7.fix8P s (Shadow7.sbP s) ++ Shadow7.glueG3 s

theorem afterPre7Head_kept (s : Nat) :
    afterPre7Head s = (keptHead s ++ Shadow7.moveKept s) ++ afterPre7Rest s := by
  simp only [afterPre7Head, keptHead, afterPre7Rest, Shadow7.moveKept, List.append_assoc]

theorem removed_keptHead : ∀ j : Fin 26, j.val ≤ 24 →
    FlagLeave.removed (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) 1559 1
      (keptHead (start j) ++ Shadow7.moveKept (start j)) = [] := by decide +kernel

/-- `after7` behind its kept pass. -/
def afterRest7 (s : Nat) : List Gate :=
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 1 (afterPre7Rest s) ++ (afterPre7Tail s ++
    ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s))))

/-- KeptParity: `after7` with the kept pass replaced by the parity pass. -/
def after7K (s : Nat) : List Gate := keptHead s ++ (KeptParity.placed s ++ afterRest7 s)

theorem after7_kept (j : Fin 26) (hi : j.val ≤ 24) :
    after7 (start j) = keptHead (start j) ++ (Shadow7.moveKept (start j) ++ afterRest7 (start j)) := by
  rw [after7, afterPre7HeadCut, afterPre7Head_kept, FlagLeave.cut_append, removed_keptHead j hi,
    FlagLeave.cut_of_removed_nil _ _ _ _ _ (removed_keptHead j hi)]
  simp only [List.length_nil, Nat.sub_zero, afterRest7, List.append_assoc]

theorem after7K_counts (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (after7K (start j))) + 1 = toffoliCount (GateMirror.forward (after7 (start j))) ∧
    toffoliCount (inverse (after7K (start j))) + 1 = toffoliCount (inverse (after7 (start j))) ∧
    measurementCount (GateMirror.forward (after7K (start j))) = measurementCount (GateMirror.forward (after7 (start j))) ∧
    measurementCount (inverse (after7K (start j))) = measurementCount (inverse (after7 (start j))) ∧
    gateSlots (GateMirror.forward (after7K (start j))) = gateSlots (GateMirror.forward (after7 (start j))) + 14 ∧
    gateSlots (inverse (after7K (start j))) = gateSlots (inverse (after7 (start j))) + 14 := by
  obtain ⟨a, b, c, d, e, f⟩ := KeptParity.cellCounts (start j)
  rw [after7_kept j hi, after7K]
  simp only [forward_app, inverse_append, toffoliCount_append, measurementCount_append, gateSlots_append]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem after7K_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (afterAll (start j))) : AllW P (after7K (start j)) := by
  have old := after7_allW j hi h
  rw [after7_kept j hi, allW_append_iff, allW_append_iff] at old
  rw [after7K, allW_append_iff, allW_append_iff]
  refine ⟨old.1, ?_, old.2.2⟩
  intro g hg q hq
  have inc := List.all_eq_true.mp (List.all_eq_true.mp (KeptParity.wiresCovered j hi) g hg) q hq
  obtain ⟨k, hk, hw⟩ := List.mem_flatMap.mp (List.contains_iff_mem.mp inc)
  exact old.2.1 k hk q hw

theorem after7K_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (afterAll (start j))) : Proper (after7K (start j)) := by
  have keep : (after7 (start j)).all proper = true := List.all_eq_true.mpr (after7_proper j hi h)
  rw [after7_kept j hi] at keep
  simp only [List.all_append, Bool.and_eq_true] at keep
  have all : (after7K (start j)).all proper = true := by
    rw [after7K]
    simp only [List.all_append, Bool.and_eq_true]
    exact ⟨keep.1, KeptParity.physical j hi, keep.2.2⟩
  intro g hg
  exact List.all_eq_true.mp all g hg

end ECDSAAdd.Entrant.StairPacket.DeadJoin
-- ==== end KeptParity defs ====

-- ==== begin SelectorReceiver (credited to spariev 59c20890 LeaveCutsCore150: DI7Affine + PBReceiver selector half; margin-16 port) ====
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 1024
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic GateMirror DeadJoin
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

abbrev Expr := Bool × List Wire

def parity (qs : List Wire) (s : BasisState) : Bool :=
  qs.foldr (fun q b => s q ^^ b) false

def eval (e : Expr) (s : BasisState) : Bool := e.1 ^^ parity e.2 s

def toggleOld (q : Wire) : List Wire → List Wire
  | [] => [q]
  | x::xs => if q=x then xs else x::toggleOld q xs

theorem parity_toggleOld (q : Wire) (qs : List Wire) (s : BasisState) :
    parity (toggleOld q qs) s = (s q ^^ parity qs s) := by
  induction qs with
  | nil => simp [toggleOld,parity]
  | cons x xs ih =>
    by_cases h : q=x
    · subst x; simp [toggleOld,parity,Bool.xor_assoc]
    · rw [toggleOld,if_neg h]
      change (s x ^^ parity (toggleOld q xs) s) = (s q ^^ (s x ^^ parity xs s))
      rw [ih]
      cases s q <;> cases s x <;> cases parity xs s <;> rfl

/-- Normalize parity without permuting unaffected wires. -/
def toggle (q : Wire) (qs : List Wire) : List Wire :=
  if qs.contains q then toggleOld q qs else q::qs

theorem parity_toggle (q : Wire) (qs : List Wire) (s : BasisState) :
    parity (toggle q qs) s = (s q ^^ parity qs s) := by
  unfold toggle
  split
  · exact parity_toggleOld q qs s
  · rfl

def add (a b : Expr) : Expr :=
  (a.1 ^^ b.1, a.2.foldr toggle b.2)

theorem eval_add (a b : Expr) (s : BasisState) :
    eval (add a b) s = (eval a s ^^ eval b s) := by
  obtain ⟨ac,aq⟩ := a
  obtain ⟨bc,bq⟩ := b
  have h : parity (aq.foldr toggle bq) s = (parity aq s ^^ parity bq s) := by
    induction aq with
    | nil => simp [parity]
    | cons q qs ih =>
      change parity (toggle q (qs.foldr toggle bq)) s = (s q ^^ parity qs s ^^ parity bq s)
      rw [parity_toggle,ih,Bool.xor_assoc]
  simp only [add,eval,h]
  cases ac <;> cases bc <;> cases parity aq s <;> cases parity bq s <;> rfl

/-- Pull back one wire through a default mirror transition. Nonlinear targets
are rejected; erased targets pull back to zero. -/
def wirePull (g : Gate) (q : Wire) : Option Expr :=
  if q ≠ target g then some (false,[q]) else
  match g with
  | .x t => some (true,[t])
  | .cx c t => some (false,[t,c])
  | .pop _ _ _ => some (false,[])
  | _ => none

theorem wirePull_sound (g : Gate) (q : Wire) (e : Expr)
    (h : wirePull g q = some e) (s : State) :
    eval e s.basis = (transition g s).basis q := by
  unfold wirePull at h
  split_ifs at h with hq
  · cases h
    cases g <;> simp only [target] at hq <;> simp [eval,parity,transition,front,erase,run,measureAndCorrect,
      ECDSAAdd.correct,writeBit,Function.update_of_ne hq]
  · have eq : q=target g := by simpa using hq
    cases g <;> simp only [target] at eq <;> subst q
    all_goals try { simp at h }
    all_goals cases h
    all_goals simp [eval,parity,transition,front,erase,run,measureAndCorrect,
      ECDSAAdd.correct,writeBit,Bool.xor_comm]

def pullTerms (g : Gate) : List Wire → Option Expr
  | [] => some (false,[])
  | q::qs => do
      let a ← wirePull g q
      let b ← pullTerms g qs
      pure (add a b)

theorem pullTerms_sound (g : Gate) (qs : List Wire) (e : Expr)
    (h : pullTerms g qs = some e) (s : State) :
    eval e s.basis = parity qs (transition g s).basis := by
  induction qs generalizing e with
  | nil => simp [pullTerms] at h; subst e; rfl
  | cons q qs ih =>
    simp only [pullTerms] at h
    cases ha : wirePull g q with
    | none => simp [ha] at h
    | some a =>
      cases hb : pullTerms g qs with
      | none => simp [ha,hb] at h
      | some b =>
        simp [ha,hb] at h
        subst e
        rw [eval_add,wirePull_sound g q a ha s,ih b hb]
        rfl

def stepSlow (g : Gate) (e : Expr) : Option Expr := do
  let b ← pullTerms g e.2
  pure (add (e.1,[]) b)

theorem stepSlow_sound (g : Gate) (e out : Expr) (h : stepSlow g e = some out) (s : State) :
    eval out s.basis = eval e (transition g s).basis := by
  simp only [stepSlow] at h
  cases hb : pullTerms g e.2 with
  | none => simp [hb] at h
  | some b =>
    simp [hb] at h; subst out
    rw [eval_add,pullTerms_sound g e.2 b hb s]
    simp [eval,parity]

/-- An untouched affine support needs no normalization or symbolic substitution. -/
def step (g : Gate) (e : Expr) : Option Expr :=
  if e.2.contains (target g) then stepSlow g e else some e

theorem parity_same (qs : List Wire) (a b : BasisState) (h : ∀q∈qs,a q=b q) :
    parity qs a=parity qs b := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (a q ^^ parity qs a)=(b q ^^ parity qs b)
    rw [h q List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem step_sound (g : Gate) (e out : Expr) (h : step g e = some out) (s : State) :
    eval out s.basis = eval e (transition g s).basis := by
  unfold step at h
  split at h
  · exact stepSlow_sound g e out h s
  · have absent : ¬target g ∈ e.2 := by simpa using ‹¬e.2.contains (target g) = true›
    cases h
    unfold eval
    congr 1
    apply parity_same
    intro q hq
    have neq : q ≠ target g := fun eq => absent (eq ▸ hq)
    cases g <;> simp only [target] at neq <;>
      simp [transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,
        writeBit,Function.update_of_ne neq]

def pull : List Gate → Expr → Option Expr
  | [], e => some e
  | g::gs, e => do
      let b ← pull gs e
      step g b

theorem pull_sound (gs : List Gate) (e out : Expr) (h : pull gs e = some out) (s : State) :
    eval out s.basis = eval e (run (GateMirror.forward gs) [] s).basis := by
  induction gs generalizing out s with
  | nil => simp [pull] at h; subst out; rfl
  | cons g gs ih =>
    simp only [pull] at h
    cases hb : pull gs e with
    | none => simp [hb] at h
    | some b =>
      simp only [hb,Option.bind_some] at h
      rw [step_sound g b out h s,ih b hb (transition g s)]
      change _ = eval e (run ([front g] ++ GateMirror.forward gs) [] s).basis
      rw [run_append,run_take,List.drop_nil]
      rfl

end ECDSAAdd.Entrant.StairPacket.DI7Affine
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic Partial GateMirror
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem update_nested (f : BasisState) (t : Wire) (a b : Bool) :
    Function.update (Function.update f t a) t b = Function.update f t b := by
  funext q
  by_cases h : q=t
  · subst q; simp
  · simp [Function.update_of_ne h]

def cxs (qs : List Wire) (t : Wire) : List Gate := qs.map (fun q => .cx q t)
def clear (c : Bool) (qs : List Wire) (t : Wire) : List Gate :=
  (if c then [Gate.x t] else []) ++ cxs qs t

theorem parity_congr (qs : List Wire) (a b : BasisState) (h : ∀ q∈qs,a q=b q) :
    parity qs a=parity qs b := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    change (a q ^^ parity qs a) = (b q ^^ parity qs b)
    rw [h q List.mem_cons_self,ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem cxs_run (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) (m : List Bool) :
    run (GateMirror.forward (cxs qs t)) m s =
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ parity qs s.basis)⟩ := by
  induction qs generalizing s m with
  | nil =>
    simp only [cxs,List.map_nil,GateMirror.forward,List.map_nil,run,parity,List.foldr_nil,Bool.xor_false]
    cases s
    simp [writeBit]
  | cons q qs ih =>
    have qt := away q List.mem_cons_self
    have tail := fun x hx => away x (List.mem_cons_of_mem _ hx)
    have p : parity qs (writeBit s.basis t (s.basis t ^^ s.basis q))=parity qs s.basis :=
      parity_congr qs _ _ (fun x hx => Function.update_of_ne (tail x hx) _ _)
    change run ([Instr.CX q t] ++ GateMirror.forward (cxs qs t)) m s = _
    rw [run_append,run_take]
    change run (GateMirror.forward (cxs qs t)) _ ⟨s.phase,writeBit s.basis t (s.basis t ^^ s.basis q)⟩ = _
    rw [ih tail]
    rw [p]
    simp only [writeBit,Function.update_self,update_nested]
    simp only [parity,List.foldr_cons,Bool.xor_assoc]

theorem clear_run (c : Bool) (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) (m : List Bool) :
    run (GateMirror.forward (clear c qs t)) m s =
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ (c ^^ parity qs s.basis))⟩ := by
  cases c with
  | false => simpa [clear] using cxs_run qs t away s m
  | true =>
    have p : parity qs (writeBit s.basis t (!s.basis t))=parity qs s.basis :=
      parity_congr qs _ _ (fun x hx => Function.update_of_ne (away x hx) _ _)
    simp only [clear,if_true,forward_app,run_append,run_take]
    change run (GateMirror.forward (cxs qs t)) _ ⟨s.phase,writeBit s.basis t (!s.basis t)⟩ = _
    rw [cxs_run qs t away]
    rw [p]
    simp only [writeBit,Function.update_self,update_nested]
    congr 1
    cases s.basis t <;> cases parity qs s.basis <;> rfl

end ECDSAAdd.Entrant.StairPacket.DI7Affine
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror Challenge DI7Affine
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def selectorPop (s : Nat) : Gate := .pop 1560 (OB5.sig (s+14) (s+1048)) 1565
def selectorSources (s : Nat) : List Wire := [1559,1561,1562,1563,1564,Shadow7.e0P s+7]
def selectorExpr (s : Nat) : Expr := (false,1565::selectorSources s)
/-- The flag-cut kept-pass suffix that holds the selector pop (`leaveFix12`). -/
def selCut (s : Nat) : List Gate := FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 1 (afterPre7Rest s)
def selPre (s : Nat) : List Gate := (selCut s).takeWhile (fun g => g != selectorPop s)
def selPost (s : Nat) : List Gate := (selCut s).drop ((selPre s).length + 1)
def receiver (t : Wire) (c : Bool) (qs : List Wire) : List Gate :=
  (if c then [Gate.x t] else []) ++ qs.map (fun q => Gate.cx q t)
theorem clear_receiver (c : Bool) (qs : List Wire) (t : Wire) : clear c qs t = receiver t c qs := rfl

/-- `afterRest7` with the selector pop replaced by its XOR receiver. -/
def afterRest7S (s : Nat) : List Gate :=
  (selPre s ++ (receiver 1565 false (selectorSources s) ++ selPost s)) ++ (afterPre7Tail s ++
    ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s))))

/-- Selector receiver (spariev 59c20890): `after7K` with the selector pop replaced by its XOR receiver. -/
def after7S (s : Nat) : List Gate := keptHead s ++ (KeptParity.placed s ++ afterRest7S s)

private theorem sel_split_first (gs : List Gate) (g : Gate) (present : g ∈ gs) :
    gs = gs.takeWhile (fun x => x != g) ++ g :: gs.drop ((gs.takeWhile (fun x => x != g)).length+1) := by
  induction gs with
  | nil => simp at present
  | cons x xs ih =>
    by_cases h : x=g
    · subst x; simp
    · have member : g∈xs := by simpa [h,Ne.symm h] using present
      simpa [List.takeWhile_cons,h,Ne.symm h,Nat.add_assoc] using congrArg (List.cons x) (ih member)

theorem sel_present : ∀ j : Fin 26, j.val ≤ 24 → selectorPop (start j) ∈ selCut (start j) := by decide +kernel

theorem selCut_shape (j : Fin 26) (hi : j.val ≤ 24) :
    selCut (start j) = selPre (start j) ++ (selectorPop (start j) :: selPost (start j)) :=
  sel_split_first _ _ (sel_present j hi)

def selTail (s : Nat) : List Gate := afterPre7Tail s ++
  ([.cx (topW7 s) 1559] ++ (chainMid7 s ++ ([.cx (topW7 s) 1559] ++ afterPost7 s)))

theorem after7K_sel (j : Fin 26) (hi : j.val ≤ 24) :
    after7K (start j) = (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j))) ++
      (selectorPop (start j) :: (selPost (start j) ++ selTail (start j))) := by
  have e : afterRest7 (start j) = selCut (start j) ++ selTail (start j) := rfl
  rw [after7K, e, selCut_shape j hi]
  simp only [List.append_assoc, List.cons_append]

theorem after7S_sel (s : Nat) :
    after7S s = (keptHead s ++ (KeptParity.placed s ++ selPre s)) ++
      (receiver 1565 false (selectorSources s) ++ (selPost s ++ selTail s)) := by
  simp only [after7S, afterRest7S, selTail, List.append_assoc]
theorem recv_counts (a b : List Gate) (x y t : Wire) (qs : List Wire) (c : Bool) :
    toffoliCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) =
      toffoliCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    toffoliCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      toffoliCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 1 =
      measurementCount (GateMirror.forward (a ++ (Gate.pop x y t :: b))) ∧
    measurementCount (GateMirror.inverse (a ++ (receiver t c qs ++ b))) =
      measurementCount (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) ∧
    gateSlots (GateMirror.forward (a ++ (receiver t c qs ++ b))) + 2 =
      gateSlots (GateMirror.forward (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat ∧
    gateSlots (GateMirror.inverse (a ++ (receiver t c qs ++ b))) + 1 =
      gateSlots (GateMirror.inverse (a ++ (Gate.pop x y t :: b))) + qs.length + c.toNat := by
  have hm : (qs.map (fun q => Gate.cx q t)).countP isMake = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simp [isMake, ih]
  have hp : (qs.map (fun q => Gate.cx q t)).countP isPop = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simp [isPop, ih]
  have hc : (qs.map (fun q => Gate.cx q t)).countP isCCX = 0 := by
    induction qs with
    | nil => rfl
    | cons q qs ih => simp [isCCX, ih]
  cases c <;> simp [toffoli_forward,toffoli_inverse,meas_forward,meas_inverse,slots_forward,slots_inverse,
    receiver,List.countP_append,List.countP_cons,isMake,isPop,isCCX,hm,hp,hc,List.length_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]


theorem after7S_counts (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (after7S (start j))) = toffoliCount (GateMirror.forward (after7K (start j))) ∧
    toffoliCount (inverse (after7S (start j))) + 1 = toffoliCount (inverse (after7K (start j))) ∧
    measurementCount (GateMirror.forward (after7S (start j))) + 1 = measurementCount (GateMirror.forward (after7K (start j))) ∧
    measurementCount (inverse (after7S (start j))) = measurementCount (inverse (after7K (start j))) ∧
    gateSlots (GateMirror.forward (after7S (start j))) + 2 = gateSlots (GateMirror.forward (after7K (start j))) + 6 ∧
    gateSlots (inverse (after7S (start j))) + 1 = gateSlots (inverse (after7K (start j))) + 6 := by
  rw [after7S_sel, after7K_sel j hi]
  have c := recv_counts (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j)))
    (selPost (start j) ++ selTail (start j)) 1560 (OB5.sig (start j+14) (start j+1048)) 1565
    (selectorSources (start j)) false
  simpa only [selectorPop, selectorSources, List.length_cons, List.length_nil, Bool.toNat_false, Nat.add_zero] using c

theorem recv_wiresCovered : ∀ j : Fin 26, j.val ≤ 24 → (receiver 1565 false (selectorSources (start j))).all (fun g =>
    g.wires.all (fun q => ((after7K (start j)).flatMap Gate.wires).contains q)) = true := by decide +kernel

theorem recv_physical : ∀ j : Fin 26, j.val ≤ 24 →
    (receiver 1565 false (selectorSources (start j))).all proper = true := by decide +kernel

theorem after7S_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (h : AllW P (afterAll (start j))) : AllW P (after7S (start j)) := by
  have old := after7K_allW j hi h
  have whole := old
  rw [after7K_sel j hi, allW_append_iff] at old
  have recv : AllW P (receiver 1565 false (selectorSources (start j))) := by
    intro g hg q hq
    have inc := List.all_eq_true.mp (List.all_eq_true.mp (recv_wiresCovered j hi) g hg) q hq
    obtain ⟨k, hk, hw⟩ := List.mem_flatMap.mp (List.contains_iff_mem.mp inc)
    exact whole k hk q hw
  rw [after7S_sel]
  exact allW_append_iff.mpr ⟨old.1, allW_append_iff.mpr ⟨recv, fun g hg => old.2 g (List.mem_cons_of_mem _ hg)⟩⟩

theorem after7S_proper (j : Fin 26) (hi : j.val ≤ 24)
    (h : Proper (afterAll (start j))) : Proper (after7S (start j)) := by
  have keep : (after7K (start j)).all proper = true := List.all_eq_true.mpr (after7K_proper j hi h)
  rw [after7K_sel j hi] at keep
  simp only [List.all_append, List.all_cons, Bool.and_eq_true] at keep
  have all : (after7S (start j)).all proper = true := by
    rw [after7S_sel]
    simp only [List.all_append, Bool.and_eq_true]
    exact ⟨keep.1, recv_physical j hi, keep.2.2⟩
  intro g hg
  exact List.all_eq_true.mp all g hg

end ECDSAAdd.Entrant.StairPacket.DeadJoin
end
-- ==== end SelectorReceiver defs ====

-- ==== begin ScanRowGordo defs (margin 16, credited to GordoAR e2530dcd) ====
section
namespace ECDSAAdd.Entrant.StairPacket.ScanRowGordo
open Arithmetic GateMirror Partial Challenge MeasuredCodec5
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

def firstRows (s h : Nat) : List Gate := (Shadow7.fix0P s h).take 47

def cell (s h : Nat) : List Gate :=
  [.cx (s+h+46) (h+801), .ccx (s+30) (h+801) (s+h+46), .cx (s+h+46) (h+801)]

def shortCell (s h : Nat) : List Gate :=
  let a := s+h+46
  let b := h+801
  let z := h+1579
  [.cx a b, .cx b a, .cx z a, .pop (s+30) b a, .cx z a, .cx b a, .cx a b]

def suffix (s h : Nat) : List Gate := ((Shadow7.fix0P s h).drop 50).take 18

def lastTwo (h : Nat) : List Gate := [.cx (h+1579) (h+801), .cx (h+1579) (h+802)]

def port (s h : Nat) : Wire → Wire
  | 0 => s+30
  | 1 => s+h+46
  | 2 => h+801
  | _ => h+1579

def before5Tail (s : Nat) : List Gate :=
  let h := Shadow7.sbP s
  let preTail := (DeadScan.fix0M s h).drop 50 ++ leaveFix1 s h ++ Shadow7.fix2P s h ++
    leaveFix3 s h ++ leaveFix4 s h ++ (Shadow7.fix5P s h).take 27
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 preTail ++
    (DeadJoin.row0New s ++ DeadJoin.beforePost5 s)

def before5Row (s : Nat) : List Gate :=
  let h := Shadow7.sbP s
  firstRows s h ++ (shortCell s h ++ before5Tail s)

end ECDSAAdd.Entrant.StairPacket.ScanRowGordo
end
-- ==== end ScanRowGordo defs ====

section
namespace ECDSAAdd.Entrant.StairPacket.AdjustShort
open Arithmetic Partial GateMirror

/-- Tightened high-bank adjust width: on early blocks (`s < 225`) and late blocks (`270 ≤ s`),
the signed rail width `wpP s` has an unused top bit above `Shadow.high (sbP s) 15 z + 1`. -/
def adjW (s : Nat) : Nat :=
  if s < 225 ∨ 270 ≤ s then Shadow7.wpP s - 1 else Shadow7.wpP s

def core (s : Nat) : List Gate :=
  adjustG ((List.range (adjW s)).map (Shadow7.bankW s))
    ((List.range (adjW s - 1)).map (Shadow7.poolW s))
    (Shadow7.e0P s + 3) 1596

def beforePost5Pre (s : Nat) : List Gate :=
  let b := Shadow7.sbP s
  rowGates (Shadow7.e0P s + 6) ((Shadow7.moveRows s).drop 1) ++ (Shadow7.fix5P s b).drop 43 ++
    [.cx (Shadow7.e0P s + 6) (Shadow7.e0P s + 3)]

def beforePost5Short (s : Nat) : List Gate :=
  beforePost5Pre s ++ core s

def before5Pre (s : Nat) : List Gate :=
  DeadJoin.beforePre5Cut s ++ (DeadJoin.row0New s ++ beforePost5Pre s)

def before5Short (s : Nat) : List Gate :=
  DeadJoin.beforePre5Cut s ++ (DeadJoin.row0New s ++ beforePost5Short s)

def before5TailShort (s : Nat) : List Gate :=
  let h := Shadow7.sbP s
  let preTail := (DeadScan.fix0M s h).drop 50 ++ leaveFix1 s h ++ Shadow7.fix2P s h ++
    leaveFix3 s h ++ leaveFix4 s h ++ (Shadow7.fix5P s h).take 27
  FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 preTail ++
    (DeadJoin.row0New s ++ beforePost5Short s)

def before5RowPrefix (s : Nat) : List Gate :=
  let h := Shadow7.sbP s
  let preTail := (DeadScan.fix0M s h).drop 50 ++ leaveFix1 s h ++ Shadow7.fix2P s h ++
    leaveFix3 s h ++ leaveFix4 s h ++ (Shadow7.fix5P s h).take 27
  ScanRowGordo.firstRows s h ++ (ScanRowGordo.shortCell s h ++
    (FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 preTail ++
      (DeadJoin.row0New s ++ beforePost5Pre s)))

def before5RowShort (s : Nat) : List Gate :=
  let h := Shadow7.sbP s
  ScanRowGordo.firstRows s h ++ (ScanRowGordo.shortCell s h ++ before5TailShort s)

theorem beforePost5_split (s : Nat) :
    DeadJoin.beforePost5 s = beforePost5Pre s ++ Shadow7.leaveAdjustCore s := by
  simp only [DeadJoin.beforePost5, beforePost5Pre, Shadow7.leaveAdjust, List.append_assoc]

theorem before5_split_core (s : Nat) :
    DeadJoin.before5 s = before5Pre s ++ Shadow7.leaveAdjustCore s := by
  simp only [DeadJoin.before5, before5Pre, beforePost5_split, List.append_assoc]

theorem before5Short_split_core (s : Nat) :
    before5Short s = before5Pre s ++ core s := by
  simp only [before5Short, before5Pre, beforePost5Short, List.append_assoc]

theorem before5Row_split_core (s : Nat) :
    ScanRowGordo.before5Row s = before5RowPrefix s ++ Shadow7.leaveAdjustCore s := by
  simp only [ScanRowGordo.before5Row, ScanRowGordo.before5Tail, before5RowPrefix, beforePost5_split, List.append_assoc]

theorem before5RowShort_split_core (s : Nat) :
    before5RowShort s = before5RowPrefix s ++ core s := by
  simp only [before5RowShort, before5TailShort, before5RowPrefix, beforePost5Short, List.append_assoc]

end ECDSAAdd.Entrant.StairPacket.AdjustShort
end

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def before (s : Nat) : List GateMirror.Gate := AdjustShort.before5RowShort s
def afterPart (s : Nat) : List GateMirror.Gate := DeadJoin.after7S s
-- ==== end DeadJoin ====

def leave (j : Fin 26) : Program :=
  let s := start j
  if j.val ≤ 24 then
    GateMirror.forward (before s) ++ barrel s false ++ GateMirror.forward (afterPart s)
  else Shadow7.leaveMoveP j

def unleave (j : Fin 26) : Program :=
  let s := start j
  if j.val ≤ 24 then
    GateMirror.inverse (afterPart s) ++ barrel s true ++ GateMirror.inverse (before s)
  else Shadow7.leaveMoveInvP j

def params : WindowFold.Pieces Program := { Shadow7.params with leave := leave, leaveInv := unleave, unrouted := TickCut.Tail.selected }

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrel ====

-- ==== begin CRTBitCount ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

/-- Count eight set bits with three additions on independent groups of bits. -/
def byteCount (n : Nat) : Nat :=
  let pairs := (n &&& 85) + ((n >>> 1) &&& 85)
  let fours := (pairs &&& 51) + ((pairs >>> 2) &&& 51)
  (fours &&& 15) + (fours >>> 4)

private theorem byte_checked : ∀ i : Fin 256, (selected 8 i.val).length = byteCount i.val := by decide +kernel

private theorem byte_count (m : Nat) : (selected 8 m).length = byteCount (m%256) := by
  have h : selected 8 m = selected 8 (m % 2^8) := by
    apply List.filter_congr
    intro i hi
    have sm := List.mem_range.mp hi
    simpa only [sm,decide_true,Bool.true_and] using (Nat.testBit_mod_two_pow m 8 i).symm
  rw [h]
  exact byte_checked ⟨_,Nat.mod_lt _ (by decide)⟩

private theorem select_split (a b m : Nat) : (selected (a+b) m).length =
    (selected a m).length + (selected b (m >>> a)).length := by
  simp only [selected,List.range_add,List.filter_append,List.length_append,List.filter_map,
    List.length_map,Function.comp_def,Nat.testBit_shiftRight]

def chunkCount (remainder : Nat) : Nat → Nat → Nat
  | 0, m => (selected remainder m).length
  | c+1, m => byteCount (m%256) + chunkCount remainder c (m >>> 8)

private theorem chunks_length (r c m : Nat) : (selected (8*c+r) m).length = chunkCount r c m := by
  induction c generalizing m with
  | zero => simp [chunkCount]
  | succ c ih =>
    rw [show 8*(c+1)+r = 8+(8*c+r) by omega,select_split,byte_count,ih]
    rfl

def fastCount (n m : Nat) := chunkCount (n%8) (n/8) m

theorem selected_length (n m : Nat) : (selected n m).length = fastCount n m := by
  have e := chunks_length (n%8) (n/8) m
  simpa only [Nat.div_add_mod] using e

def basisSize (n : Nat) : Nat :=
  ((pivots n).map (fun (donor,mask) => (if donor<n then 1 else 0) + fastCount n mask)).sum

theorem basis_size (n : Nat) : (basisNetwork n).length = basisSize n := by
  unfold basisNetwork basisSize
  rw [List.length_reverse, List.length_flatMap]
  have each (row : Nat × Nat) (i : Nat) : (elimStep n i row).length =
      (if row.1 < n then 1 else 0) + fastCount n row.2 := by
    simp only [elimStep,List.length_append,List.length_map,selected_length]
    split <;> rfl
  simp only [each]
  have eq (xs : List (Nat × Nat)) (i : Nat) :
      (xs.zipIdx i).map (fun (row,_) => (if row.1<n then 1 else 0) + fastCount n row.2) =
      xs.map (fun row => (if row.1<n then 1 else 0) + fastCount n row.2) := by
    induction xs generalizing i with
    | nil => rfl
    | cons x xs ih => simp only [List.zipIdx_cons,List.map_cons]; rw [ih]
  exact congrArg List.sum (eq _ 0)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBitCount ====

-- ==== begin CRTDomain ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

def UsedField (p : Nat) : Prop :=
  p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 19 ∨ p = 21 ∨ p = 25 ∨ p = 31 ∨ p = 37 ∨ p = 67 ∨ p = 73 ∨ p = 257 ∨ p = 313 ∨ p = 471 ∨ p = 1193 ∨ p = 1571 ∨ p = 4593 ∨ p = 5349 ∨ p = 5981 ∨ p = 6891

instance (p : Nat) : Decidable (UsedField p) := by
  unfold UsedField
  infer_instance

def UsedWidth (n : Nat) : Prop :=
  n = 31 ∨ n = 39 ∨ n = 46 ∨ n = 54 ∨ n = 61 ∨ n = 69 ∨ n = 76 ∨ n = 84 ∨ n = 91 ∨ n = 99 ∨ n = 106 ∨ n = 113 ∨ n = 120 ∨ n = 128

instance (n : Nat) : Decidable (UsedWidth n) := by
  unfold UsedWidth
  infer_instance

theorem usedWidth : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 → UsedWidth (barrelWidth (start j)) := by
  decide +kernel

theorem schedule_fields (n : Nat) (hn : UsedWidth n) :
    ∀ pair ∈ schedule n, UsedField pair.1 := by
  have h : (schedule n).all (fun x => decide (UsedField x.1)) = true := by
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  intro pair hp
  exact of_decide_eq_true (List.all_eq_true.mp h pair hp)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTDomain ====

-- ==== begin CRTResources ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.Challenge ECDSAAdd.Baselines

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Resources

structure Count where
  t : Nat
  m : Nat
  slots : Nat
  deriving DecidableEq

def count (p : Program) : Count := ⟨toffoliCount p, measurementCount p, gateSlots p⟩
def zero : Count := ⟨0,0,0⟩
def add (a b : Count) : Count := ⟨a.t+b.t,a.m+b.m,a.slots+b.slots⟩
def scale (k : Nat) (a : Count) : Count := ⟨k*a.t,k*a.m,k*a.slots⟩

theorem append (p q : Program) : count (p++q) = add (count p) (count q) := by
  simp [count, add]

theorem reverse (p : Program) : count p.reverse = count p := by
  simp [count, toffoliCount_reverse, measurementCount_reverse]

theorem renamed (f : Wire → Wire) (p : Program) : count (renameProgram f p) = count p := by
  simp only [count, (renameProgram_counts f p).1, (renameProgram_counts f p).2, rename_gateSlots]

theorem flatConstant {α} (xs : List α) (f : α → Program) (r : Count)
    (h : ∀ x ∈ xs, count (f x) = r) : count (xs.flatMap f) = scale xs.length r := by
  induction xs with
  | nil => cases r; simp [count, scale, toffoliCount, measurementCount]
  | cons x xs ih =>
    rw [List.flatMap_cons, append, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    cases r
    simp [scale, add, Nat.succ_mul, Nat.add_comm]

theorem cxMap {α} (xs : List α) (a b : α → Wire) :
    count (xs.map (fun x => Instr.CX (a x) (b x))) = ⟨0,0,xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change count ([_] ++ _) = _
    rw [append, ih]
    simp [count, add, toffoliCount, measurementCount, gateSlots, instructionSlots, Nat.add_comm]

theorem ccxMap {α} (xs : List α) (a b c : α → Wire) :
    count (xs.map (fun x => Instr.CCX (a x) (b x) (c x))) = ⟨xs.length,0,xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change count ([_] ++ _) = _
    rw [append, ih]
    simp [count, add, toffoliCount, measurementCount, gateSlots, instructionSlots, Nat.add_comm]

def stagePrice (d m h : Nat) : Count :=
  let inc := 2^h
  let edits := (m-inc)*d
  let tags := ((List.range 16).filter fun k => k.testBit h).length
  if m ≤ inc then zero else ⟨edits,0,tags+edits+tags⟩

theorem stage_count (n off d m h : Nat) :
    count (stage n off d m h) = stagePrice d m h := by
  unfold stage stagePrice
  dsimp only
  by_cases short : m ≤ 2^h
  · simp only [if_pos short]; rfl
  · simp only [if_neg short]
    rw [append, append, reverse]
    rw [cxMap]
    rw [flatConstant _ _ ⟨d,0,d⟩]
    · simp [add, scale]
    · intro j _
      simpa only [List.length_range] using
        (ccxMap (List.range d) (fun _ => n+24) (fun i => off+d*j+i)
          (fun i => off+d*(j+2^h)+i))

def sumBy {α} (f : α → Count) (xs : List α) : Count :=
  xs.foldr (fun x r => add (f x) r) zero

theorem flatSum {α} (xs : List α) (f : α → Program) (g : α → Count)
    (h : ∀ x ∈ xs, count (f x) = g x) : count (xs.flatMap f) = sumBy g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, append, h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    rfl

def r8StepPrice (st : R8Step) : Count :=
  ⟨1, 0, st.tags.length + st.pre.length + 1 + st.pre.length + st.tags.length⟩

theorem r8Step_count (n off : Nat) (st : R8Step) : count (r8Step n off st) = r8StepPrice st := by
  unfold r8Step r8StepPrice
  dsimp only
  rw [append, append, append, append, reverse, reverse, cxMap, cxMap]
  have h1 : count [Instr.CCX (n+24) (off+st.src) (off+st.dst)] = ⟨1, 0, 1⟩ := by
    simp [count, toffoliCount, measurementCount, gateSlots, instructionSlots]
  rw [h1]
  simp [add]

def r8Price (mir : Bool) : Count := sumBy r8StepPrice (pascalR8Steps mir)

private theorem r8Price_eq : ∀ mir : Bool, r8Price mir = ⟨8, 0, 212⟩ := by decide +kernel

theorem pascalR8_count (n off : Nat) (mir : Bool) : count (pascalR8 n off mir) = r8Price mir :=
  flatSum _ _ _ (fun st _ => r8Step_count n off st)

def stdTriPrice (d m : Nat) := sumBy (stagePrice d m) (List.range 4)

def triPrice (d m : Nat) := if d == 8 && m == 2 then ⟨8, 0, 212⟩ else stdTriPrice d m

theorem triangular_count (n off d m : Nat) : count (triangular n off d m) = stdTriPrice d m :=
  flatSum _ _ _ (fun i _ => stage_count n off d m i)

theorem primary_count (n off p m : Nat) (mir : Bool) : count (primary n off p m mir) =
    add (scale m (count (fieldCore p mir))) (triPrice (fieldDegree p) m) := by
  unfold primary triPrice; dsimp only
  rw [append, flatConstant _ _ (count (fieldCore p mir)) (fun _ _ => renamed _ _), List.length_range]
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · rw [if_pos h82, if_pos h82, pascalR8_count, r8Price_eq]
  · rw [if_neg h82, if_neg h82]; cases mir <;> simp [reverse, triangular_count]

def fieldPrice (p : Nat) (mir : Bool) : Count :=
  let x := measuredField p
  ⟨x.1, x.2.1, if mir then x.2.2.2 else x.2.2.1⟩

def partsPrice (mir : Bool) (parts : List (Nat × Nat)) : Count :=
  sumBy (fun (p,m) => add (scale m (fieldPrice p mir)) (triPrice (fieldDegree p) m)) parts

theorem components_count (n : Nat) (mir : Bool) (off : Nat) (parts : List (Nat × Nat))
    (h : ∀ pair ∈ parts, count (fieldCore pair.1 mir) = fieldPrice pair.1 mir) :
    count (components n mir off parts) = partsPrice mir parts := by
  induction parts generalizing off with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    rw [components, append, primary_count, h (p,m) (by simp),
      ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    rfl

def windowPrice (n : Nat) (mir : Bool) : Count :=
  let basis : Count := ⟨0,0,(basisNetwork n).length⟩
  add (add basis (partsPrice mir (schedule n))) basis

theorem logical_count (n : Nat) (mir : Bool)
    (h : ∀ pair ∈ schedule n, count (fieldCore pair.1 mir) = fieldPrice pair.1 mir) :
    count (logical n mir) = windowPrice n mir := by
  unfold logical windowPrice
  rw [append, append, reverse, components_count _ _ _ _ h]
  have b := cxMap (basisNetwork n) Prod.fst Prod.snd
  exact congrArg (fun v => add (add v (partsPrice mir (schedule n))) v) b

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Resources

end
-- ==== end CRTResources ====

-- ==== begin CRTBarrelMetrics ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Resources
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

theorem field_count (p : Nat) (hp : UsedField p) (mir : Bool) :
    count (fieldCore p mir) = fieldPrice p mir := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

def listedPrice (n : Nat) (mir : Bool) : Count :=
  let z := measuredCosts n
  ⟨z.1, z.2.1, if mir then z.2.2.2 else z.2.2.1⟩

private theorem window_price (n : Nat) (hn : UsedWidth n) (mir : Bool) :
    windowPrice n mir = listedPrice n mir := by
  unfold windowPrice
  rw [basis_size]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

theorem barrel_metrics (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    toffoliCount (barrel (start j) mir) = barrelT (start j) mir ∧
    measurementCount (barrel (start j) mir) = barrelM (start j) mir ∧
    Challenge.gateSlots (barrel (start j) mir) = barrelSlots (start j) mir := by
  have hn := usedWidth j lo hi
  have h : count (barrel (start j) mir) = listedPrice (barrelWidth (start j)) mir := by
    unfold barrel
    rw [renamed, logical_count _ _ (fun pair hm => field_count _ (schedule_fields _ hn pair hm) _),
        window_price _ hn]
  exact ⟨congrArg Count.t h, congrArg Count.m h, congrArg Count.slots h⟩

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelMetrics ====

-- ==== begin CRTLinear ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

/-- Evaluate a binary matrix row against the indicated number of input bits. -/
def rowValue (x : Nat → Bool) (row : Nat) : Nat → Bool
  | 0 => false
  | n+1 => rowValue x row n ^^ (row.testBit n && x n)

theorem rowValue_xor (x : Nat → Bool) (a b n : Nat) :
    rowValue x (a ^^^ b) n = (rowValue x a n ^^ rowValue x b n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rowValue, ih, Nat.testBit_xor]
    cases rowValue x a n <;> cases rowValue x b n <;> cases a.testBit n <;>
      cases b.testBit n <;> cases x n <;> rfl

def cnotProgram (ops : List (Wire × Wire)) : Program :=
  ops.map fun (a,b) => .CX a b

theorem inverse_cnot (a b : Wire) (hab : a ≠ b) (s : State) (m n : List Bool) :
    run [.CX a b] n (run [.CX a b] m s) = s := by
  cases s with
  | mk ph bits =>
    change State.mk ph _ = State.mk ph bits
    congr 1
    funext q
    by_cases e : q = b
    · subst q; simp [run, writeBit, Function.update_of_ne hab]
    · simp [run, writeBit, Function.update_of_ne e]

theorem reverse_cnots (ops : List (Wire × Wire)) (apart : ∀ p ∈ ops, p.1 ≠ p.2)
    (s : State) (m n : List Bool) :
    run (cnotProgram ops.reverse) n (run (cnotProgram ops) m s) = s := by
  induction ops generalizing s m n with
  | nil => rfl
  | cons p tail ih =>
    obtain ⟨a,b⟩ := p
    have sep := apart (a,b) (by simp)
    have rest : ∀ p ∈ tail, p.1 ≠ p.2 := fun p hp => apart p (List.mem_cons_of_mem _ hp)
    change run (cnotProgram (((a,b) :: tail).reverse)) n
      (run (cnotProgram tail) m (run [.CX a b] m s)) = s
    rw [List.reverse_cons, cnotProgram, List.map_append]
    rw [run_append, run_take]
    change run [.CX a b] _ (run (cnotProgram tail.reverse) n
      (run (cnotProgram tail) m (run [.CX a b] m s))) = s
    rw [ih rest]
    exact inverse_cnot a b sep s m _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTLinear ====

-- ==== begin CRTMeasurement ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTMeasurement ====

-- ==== begin CRTPlacement ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.RecordedQuantum

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement

/-- A proper gate whose targets, controls and both correction lists stay in S. -/
def Fits (S : Wire → Prop) (P : Program) : Prop :=
  ∀ i ∈ P, PhysicalInstr (.gate i) ∧ ∀ q ∈ i.wires, S q

theorem fits_append {S : Wire → Prop} {p q : Program} (hp : Fits S p) (hq : Fits S q) :
    Fits S (p++q) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact hp i hi
  · exact hq i hi

theorem fits_reverse {S : Wire → Prop} {p : Program} (hp : Fits S p) : Fits S p.reverse :=
  fun i hi => hp i (List.mem_reverse.mp hi)

theorem fits_flatMap {α} {S : Wire → Prop} (xs : List α) (f : α → Program)
    (h : ∀ x ∈ xs, Fits S (f x)) : Fits S (xs.flatMap f) := by
  intro i hi
  obtain ⟨x,hx,hit⟩ := List.mem_flatMap.mp hi
  exact h x hx i hit

theorem fits_map {α} {S : Wire → Prop} (xs : List α) (f : α → Instr)
    (h : ∀ x ∈ xs, PhysicalInstr (.gate (f x)) ∧ ∀ q ∈ (f x).wires, S q) : Fits S (xs.map f) := by
  intro i hi
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
  exact h x hx

theorem support {S : Wire → Prop} {p : Program} (h : Fits S p) : ∀ q ∈ wires p, S q := by
  induction p with
  | nil => simp [wires]
  | cons i p ih =>
    intro q hq
    rcases Finset.mem_union.mp hq with a | a
    · exact (h i (by simp)).2 q a
    · exact ih (fun j hj => h j (List.mem_cons_of_mem i hj)) q a

theorem fits_rename {S T : Wire → Prop} (f : Wire → Wire) (p : Program) (hp : Fits S p)
    (bound : ∀ q, S q → T (f q)) (inj : ∀ a, S a → ∀ b, S b → f a = f b → a = b) :
    Fits T (renameProgram f p) := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  obtain ⟨phy, sub⟩ := hp i hi
  constructor
  · cases i with
    | X t => trivial
    | measureX t c0 c1 => trivial
    | CX a b =>
      intro e
      exact phy (inj a (sub a (by simp [Instr.wires])) b (sub b (by simp [Instr.wires])) e)
    | CCX a b c =>
      have sa := sub a (by simp [Instr.wires])
      have sb := sub b (by simp [Instr.wires])
      have sc := sub c (by simp [Instr.wires])
      exact ⟨fun e => phy.1 (inj a sa c sc e), fun e => phy.2 (inj b sb c sc e)⟩
  · intro q hq
    rw [renameInstr_support, Finset.mem_image] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact bound a (sub a ha)

def fieldScope (d q : Nat) : Prop := q < d ∨ 12 ≤ q ∧ q < 38

instance (d q : Nat) : Decidable (fieldScope d q) := by unfold fieldScope; infer_instance

def physicalBit : Instr → Bool
  | .CX a b => decide (a ≠ b)
  | .CCX a b c => decide (a ≠ c ∧ b ≠ c)
  | _ => true

def coreTest (p : Nat) (mir : Bool) : Bool :=
  (fieldCore p mir).all fun i => physicalBit i && decide (∀ q ∈ i.wires, fieldScope (fieldDegree p) q)

theorem fits_core_of_test (p : Nat) (mir : Bool) (h : coreTest p mir = true) :
    Fits (fieldScope (fieldDegree p)) (fieldCore p mir) := by
  intro i hi
  have ok := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true] at ok
  obtain ⟨hi, bound⟩ := ok
  refine ⟨?_, of_decide_eq_true bound⟩
  cases i <;> simp_all [physicalBit, PhysicalInstr, ProperGate]

theorem field_place_maps {n off d : Nat} (small : d ≤ 12) (endp : off+d ≤ n) :
    (∀ q, fieldScope d q → fieldPlace n off q < n+26) ∧
    (∀ a, fieldScope d a → ∀ b, fieldScope d b → fieldPlace n off a = fieldPlace n off b → a = b) := by
  constructor
  · intro q hq
    unfold fieldScope at hq
    simp only [fieldPlace]
    split <;> (try split) <;> (try unfold Wire at *) <;> omega
  · intro a ha b hb he
    unfold fieldScope at ha hb
    simp only [fieldPlace] at he
    split at he <;> (try split at he) <;> (try split at he) <;> (try split at he) <;>
      (try unfold Wire at *) <;> omega

theorem stage_fits (n off d m h : Nat) (hd : 0 < d) (endp : off+d*m ≤ n) :
    Fits (· < n+26) (stage n off d m h) := by
  unfold stage
  dsimp only
  split
  · simp [Fits]
  · rename_i wide
    have toggle : Fits (· < n+26) (((List.range 16).filter (fun k => k.testBit h)).map
        (fun k => Instr.CX (n+k) (n+24))) := by
      apply fits_map
      intro k hk
      have sk := List.mem_range.mp (List.mem_filter.mp hk).1
      simp [PhysicalInstr, ProperGate, Instr.wires]
      unfold Wire at *
      omega
    apply fits_append (fits_append toggle ?_) (fits_reverse toggle)
    apply fits_flatMap
    intro j hj
    have sj := List.mem_range.mp (List.mem_reverse.mp hj)
    apply fits_map
    intro i hi
    have si := List.mem_range.mp hi
    have hp := Nat.two_pow_pos h
    have step : d*j < d*(j+2^h) := Nat.mul_lt_mul_of_pos_left (by omega) hd
    have bound : d*(j+2^h)+i < d*m := calc
      _ < d*(j+2^h)+d := Nat.add_lt_add_left si _
      _ = d*(j+2^h+1) := (Nat.mul_succ _ _).symm
      _ ≤ d*m := Nat.mul_le_mul_left _ (by omega)
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *
    omega

def r8StepGood (st : R8Step) : Bool :=
  (st.tags.all (fun k => decide (k < 16))) &&
  (st.pre.all (fun p => decide (p.1 < 16 ∧ p.2 < 16 ∧ p.1 ≠ p.2))) &&
  decide (st.src < 16 ∧ st.dst < 16 ∧ st.src ≠ st.dst)

theorem pascalR8Steps_good : ∀ mir : Bool, (pascalR8Steps mir).all r8StepGood = true := by decide +kernel

theorem r8Step_fits (n off : Nat) (st : R8Step) (hg : r8StepGood st = true) (endp : off + 16 ≤ n) :
    Fits (· < n + 26) (r8Step n off st) := by
  unfold r8StepGood at hg
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨htags, hpre⟩, hsrc, hdst, hne⟩ := hg
  unfold r8Step
  dsimp only
  have ht : Fits (· < n + 26) (st.tags.map (fun k => Instr.CX (n + k) (n + 24))) := by
    apply fits_map
    intro k hk
    have sk := htags k hk
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *; omega
  have hp : Fits (· < n + 26) (st.pre.map (fun p => Instr.CX (off + p.1) (off + p.2))) := by
    apply fits_map
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hpre p hp
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *; omega
  have hc : Fits (· < n + 26) [Instr.CCX (n + 24) (off + st.src) (off + st.dst)] := by
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    simp [PhysicalInstr, ProperGate, Instr.wires]
    unfold Wire at *; omega
  exact fits_append (fits_append (fits_append (fits_append ht hp) hc) (fits_reverse hp)) (fits_reverse ht)

theorem pascalR8_fits (n off : Nat) (mir : Bool) (endp : off + 16 ≤ n) :
    Fits (· < n + 26) (pascalR8 n off mir) :=
  fits_flatMap _ _ (fun st hst => r8Step_fits n off st (List.all_eq_true.mp (pascalR8Steps_good mir) st hst) endp)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement

end
-- ==== end CRTPlacement ====

-- ==== begin CRTShapeData ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.RecordedQuantum

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

-- [carbon-replay: crt-fast]
private def crScopeB (d q : Nat) : Bool := Nat.blt q d || (Nat.ble 12 q && Nat.blt q 38)

private theorem crScopeB_ok {d q : Nat} (h : crScopeB d q = true) : fieldScope d q := by
  unfold crScopeB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
  exact h

private def crCorrScopeB (d : Nat) : List Correction → Bool
  | [] => true
  | .Z t :: cs => crScopeB d t && crCorrScopeB d cs
  | .CZ a b :: cs => crScopeB d a && crScopeB d b && crCorrScopeB d cs

private theorem crCorrScopeB_ok (d : Nat) (cs : List Correction) (h : crCorrScopeB d cs = true) :
    ∀ q ∈ correctionWires cs, fieldScope d q := by
  induction cs with
  | nil => intro q hq; simp [correctionWires] at hq
  | cons c cs ih =>
    cases c with
    | Z t =>
      simp only [crCorrScopeB, Bool.and_eq_true] at h
      intro q hq
      rcases Finset.mem_union.mp hq with ht | hcs
      · exact Finset.mem_singleton.mp ht ▸ crScopeB_ok h.1
      · exact ih h.2 q hcs
    | CZ a b =>
      simp only [crCorrScopeB, Bool.and_eq_true] at h
      intro q hq
      rcases Finset.mem_union.mp hq with hab | hcs
      · rcases Finset.mem_insert.mp hab with rfl | hb
        · exact crScopeB_ok h.1.1
        · exact Finset.mem_singleton.mp hb ▸ crScopeB_ok h.1.2
      · exact ih h.2 q hcs

private def crInstrScopeB (d : Nat) : Instr → Bool
  | .X t => crScopeB d t
  | .CX a b => !Nat.beq a b && crScopeB d a && crScopeB d b
  | .CCX a b c => !Nat.beq a c && !Nat.beq b c && crScopeB d a && crScopeB d b && crScopeB d c
  | .measureX t c0 c1 => crScopeB d t && crCorrScopeB d c0 && crCorrScopeB d c1

private theorem crFits_of_fast (p : Nat) (mir : Bool)
    (h : (fieldCore p mir).all (crInstrScopeB (fieldDegree p)) = true) :
    Fits (fieldScope (fieldDegree p)) (fieldCore p mir) := by
  intro i hi
  have ok := List.all_eq_true.mp h i hi
  cases i with
  | X t =>
    refine ⟨trivial, fun q hq => ?_⟩
    exact Finset.mem_singleton.mp hq ▸ crScopeB_ok ok
  | CX a b =>
    simp only [crInstrScopeB, Bool.and_eq_true, Bool.not_eq_true'] at ok
    refine ⟨Nat.ne_of_beq_eq_false ok.1.1, fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hb
    · exact crScopeB_ok ok.1.2
    · exact Finset.mem_singleton.mp hb ▸ crScopeB_ok ok.2
  | CCX a b c =>
    simp only [crInstrScopeB, Bool.and_eq_true, Bool.not_eq_true'] at ok
    refine ⟨⟨Nat.ne_of_beq_eq_false ok.1.1.1.1, Nat.ne_of_beq_eq_false ok.1.1.1.2⟩, fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hbc
    · exact crScopeB_ok ok.1.1.2
    · rcases Finset.mem_insert.mp hbc with rfl | hc
      · exact crScopeB_ok ok.1.2
      · exact Finset.mem_singleton.mp hc ▸ crScopeB_ok ok.2
  | measureX t c0 c1 =>
    simp only [crInstrScopeB, Bool.and_eq_true] at ok
    refine ⟨trivial, fun q hq => ?_⟩
    rcases Finset.mem_union.mp hq with htc0 | hc1
    · rcases Finset.mem_union.mp htc0 with ht | hc0
      · exact Finset.mem_singleton.mp ht ▸ crScopeB_ok ok.1.1
      · exact crCorrScopeB_ok _ c0 ok.1.2 q hc0
    · exact crCorrScopeB_ok _ c1 ok.2 q hc1

theorem fits_core (p : Nat) (hp : UsedField p) (mir : Bool) :
    Fits (fieldScope (fieldDegree p)) (fieldCore p mir) := by
  apply crFits_of_fast
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases mir <;> decide +kernel

theorem used_degree (p : Nat) (hp : UsedField p) : 0 < fieldDegree p ∧ fieldDegree p ≤ 12 := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def pivotTest (n : Nat) : Bool :=
  (pivots n).zipIdx.all fun ((donor,mask),i) => decide (i < n ∧ (donor < n → donor ≠ i) ∧ mask.testBit i = false)

theorem good_pivots (n : Nat) (hn : UsedWidth n) : pivotTest n = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def extent (parts : List (Nat × Nat)) : Nat :=
  parts.foldr (fun (p,m) r => fieldDegree p * m + r) 0

theorem schedule_extent (n : Nat) (hn : UsedWidth n) : extent (schedule n) = n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

/-- replay memory (build-chain s5-mem2): one decide per block, each its own kernel check (the single Fin 26 decide
peaked at about +3 to +4.5 GB; per block <= +0.2 GB). -/
private theorem place_nodup_0 : ((List.range (barrelWidth (start ⟨0, by decide⟩)+26)).map (place (start ⟨0, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_1 : ((List.range (barrelWidth (start ⟨1, by decide⟩)+26)).map (place (start ⟨1, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_2 : ((List.range (barrelWidth (start ⟨2, by decide⟩)+26)).map (place (start ⟨2, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_3 : ((List.range (barrelWidth (start ⟨3, by decide⟩)+26)).map (place (start ⟨3, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_4 : ((List.range (barrelWidth (start ⟨4, by decide⟩)+26)).map (place (start ⟨4, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_5 : ((List.range (barrelWidth (start ⟨5, by decide⟩)+26)).map (place (start ⟨5, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_6 : ((List.range (barrelWidth (start ⟨6, by decide⟩)+26)).map (place (start ⟨6, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_7 : ((List.range (barrelWidth (start ⟨7, by decide⟩)+26)).map (place (start ⟨7, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_8 : ((List.range (barrelWidth (start ⟨8, by decide⟩)+26)).map (place (start ⟨8, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_9 : ((List.range (barrelWidth (start ⟨9, by decide⟩)+26)).map (place (start ⟨9, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_10 : ((List.range (barrelWidth (start ⟨10, by decide⟩)+26)).map (place (start ⟨10, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_11 : ((List.range (barrelWidth (start ⟨11, by decide⟩)+26)).map (place (start ⟨11, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_12 : ((List.range (barrelWidth (start ⟨12, by decide⟩)+26)).map (place (start ⟨12, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_13 : ((List.range (barrelWidth (start ⟨13, by decide⟩)+26)).map (place (start ⟨13, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_14 : ((List.range (barrelWidth (start ⟨14, by decide⟩)+26)).map (place (start ⟨14, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_15 : ((List.range (barrelWidth (start ⟨15, by decide⟩)+26)).map (place (start ⟨15, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_16 : ((List.range (barrelWidth (start ⟨16, by decide⟩)+26)).map (place (start ⟨16, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_17 : ((List.range (barrelWidth (start ⟨17, by decide⟩)+26)).map (place (start ⟨17, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_18 : ((List.range (barrelWidth (start ⟨18, by decide⟩)+26)).map (place (start ⟨18, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_19 : ((List.range (barrelWidth (start ⟨19, by decide⟩)+26)).map (place (start ⟨19, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_20 : ((List.range (barrelWidth (start ⟨20, by decide⟩)+26)).map (place (start ⟨20, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_21 : ((List.range (barrelWidth (start ⟨21, by decide⟩)+26)).map (place (start ⟨21, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_22 : ((List.range (barrelWidth (start ⟨22, by decide⟩)+26)).map (place (start ⟨22, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_23 : ((List.range (barrelWidth (start ⟨23, by decide⟩)+26)).map (place (start ⟨23, by decide⟩))).Nodup := by
  decide +kernel
private theorem place_nodup_24 : ((List.range (barrelWidth (start ⟨24, by decide⟩)+26)).map (place (start ⟨24, by decide⟩))).Nodup := by
  decide +kernel

private theorem place_nodup : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    ((List.range (barrelWidth (start j)+26)).map (place (start j))).Nodup := by
  intro j lo hi
  rcases j with ⟨k, hk⟩
  change k ≤ 24 at hi
  interval_cases k
  exacts [place_nodup_0, place_nodup_1, place_nodup_2, place_nodup_3, place_nodup_4, place_nodup_5, place_nodup_6, place_nodup_7, place_nodup_8, place_nodup_9, place_nodup_10, place_nodup_11, place_nodup_12, place_nodup_13, place_nodup_14, place_nodup_15, place_nodup_16, place_nodup_17, place_nodup_18, place_nodup_19, place_nodup_20, place_nodup_21, place_nodup_22, place_nodup_23, place_nodup_24]

theorem place_inj (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) : ∀ a, a < barrelWidth (start j)+26 →
    ∀ b, b < barrelWidth (start j)+26 → place (start j) a = place (start j) b → a = b := by
  intro a ha b hb
  exact List.inj_on_of_nodup_map (place_nodup j lo hi) (List.mem_range.mpr ha) (List.mem_range.mpr hb)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Placement

end
-- ==== end CRTShapeData ====

-- ==== begin CRTPhysical ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket
open ECDSAAdd.RecordedQuantum

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Placement

theorem basis_pairs (n : Nat) (hn : UsedWidth n) :
    ∀ pair ∈ basisNetwork n, pair.1 < n ∧ pair.2 < n ∧ pair.1 ≠ pair.2 := by
  intro pair hp
  obtain ⟨⟨⟨donor,mask⟩,i⟩,hit,hlist⟩ := List.mem_flatMap.mp (List.mem_reverse.mp hp)
  have h := of_decide_eq_true (List.all_eq_true.mp (good_pivots n hn) _ hit)
  change i < n ∧ (donor < n → donor ≠ i) ∧ mask.testBit i = false at h
  change pair ∈ (if donor < n then [(donor,i)] else []) ++ (selected n mask).map (fun j => (i,j)) at hlist
  rcases List.mem_append.mp hlist with hd | ht
  · split at hd
    · rename_i within
      simp only [List.mem_singleton] at hd
      subst pair
      exact ⟨within,h.1,h.2.1 within⟩
    · simp at hd
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
    obtain ⟨bound,bit⟩ := List.mem_filter.mp hj
    refine ⟨h.1,List.mem_range.mp bound,?_⟩
    change i ≠ j
    rintro rfl
    simp [h.2.2] at bit

theorem basis_fits (n : Nat) (hn : UsedWidth n) :
    Fits (· < n+26) ((basisNetwork n).map fun (i,j) => Instr.CX i j) := by
  apply fits_map
  intro pair hp
  obtain ⟨a,b⟩ := pair
  obtain ⟨ha,hb,apart⟩ := basis_pairs n hn (a,b) hp
  change a < n at ha
  change b < n at hb
  refine ⟨apart,?_⟩
  intro q hq
  simp only [Instr.wires, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with eq | eq
  · subst q; exact Nat.lt_of_lt_of_le ha (Nat.le_add_right _ _)
  · subst q; exact Nat.lt_of_lt_of_le hb (Nat.le_add_right _ _)

theorem primary_fits (n off p m : Nat) (hp : UsedField p) (endp : off+fieldDegree p*m ≤ n) (mir : Bool) :
    Fits (· < n+26) (primary n off p m mir) := by
  obtain ⟨pos,small⟩ := used_degree p hp
  unfold primary
  apply fits_append
  · apply fits_flatMap
    intro j hj
    have next := Nat.mul_le_mul_left (fieldDegree p) (List.mem_range.mp hj : j+1 ≤ m)
    rw [Nat.mul_succ] at next
    have bounds := field_place_maps (n := n) (off := off+fieldDegree p*j) small (by omega)
    exact fits_rename _ _ (fits_core p hp mir) bounds.1 bounds.2
  · by_cases h82 : (fieldDegree p == 8 && m == 2) = true
    · rw [if_pos h82]
      simp only [Bool.and_eq_true, beq_iff_eq] at h82
      have h16 : fieldDegree p * m = 16 := by rw [h82.1, h82.2]
      exact pascalR8_fits n off mir (by omega)
    · rw [if_neg h82]
      have tri := fits_flatMap (List.range 4) (stage n off (fieldDegree p) m)
                    (fun h _ => stage_fits n off (fieldDegree p) m h pos endp)
      cases mir
      · exact tri
      · exact fits_reverse tri

theorem components_fits (n : Nat) (mir : Bool) (off : Nat) (parts : List (Nat × Nat))
    (endp : off+extent parts ≤ n) (fields : ∀ pair ∈ parts, UsedField pair.1) :
    Fits (· < n+26) (components n mir off parts) := by
  induction parts generalizing off with
  | nil => simp [components,Fits]
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    change off+(fieldDegree p*m + extent tail) ≤ n at endp
    exact fits_append (primary_fits n off p m (fields (p,m) (by simp)) (by omega) mir)
      (ih _ (by omega) (fun x hx => fields x (List.mem_cons_of_mem _ hx)))

theorem logical_fits (n : Nat) (hn : UsedWidth n) (mir : Bool) : Fits (· < n+26) (logical n mir) := by
  have basis := basis_fits n hn
  exact fits_append (fits_append basis (components_fits n mir 0 (schedule n)
    (by rw [schedule_extent n hn]; omega) (schedule_fields n hn))) (fits_reverse basis)

theorem barrel_phys (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    GatePhysical (barrel (start j) mir) := by
  have logicalOK := logical_fits _ (usedWidth j lo hi) mir
  have physicalOK := fits_rename (T := fun _ => True) (place (start j)) _ logicalOK
    (fun _ _ => trivial) (place_inj j lo hi)
  exact fun i hit => (physicalOK i hit).1

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTPhysical ====

-- ==== begin CRTBarrelChecks ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel

private theorem tag_mem : ∀ i : Fin 16, Partial.tagsP.getD i.val 1560 ∈ Partial.tagsP := by
  decide +kernel

theorem barrelWidth_le : ∀ j : Fin 26, 0 ≤ j.val → j.val ≤ 24 →
    barrelWidth (start j) ≤ Shadow7.wpP (start j) + 15 := by decide +kernel

theorem place_mem (s x : Nat) :
    (∃ i, i < barrelWidth s ∧ place s x = Shadow7.bankW s i) ∨
    (∃ k, k < 10 ∧ place s x = Shadow7.poolW s (17+k)) ∨ place s x ∈ Partial.tagsP := by
  by_cases h : x < barrelWidth s
  · exact Or.inl ⟨x, h, by simp [place, h]⟩
  by_cases t : x < barrelWidth s + 16
  · apply Or.inr (Or.inr ?_)
    have k : x - barrelWidth s < 16 := by omega
    simpa only [place, if_neg h, if_pos t] using tag_mem ⟨_, k⟩
  · right; left
    exact ⟨(x - barrelWidth s - 16) % 10, Nat.mod_lt _ (by decide), by simp [place, h, t]⟩

theorem barrel_wires (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool) :
    ∀ q ∈ wires (barrel (start j) mir),
      (∃ i, i < Shadow7.wpP (start j)+15 ∧ q = Shadow7.bankW (start j) i) ∨
      (∃ k, k < 10 ∧ q = Shadow7.poolW (start j) (17+k)) ∨ q ∈ Partial.tagsP := by
  intro q h
  rw [barrel, renameProgram_support, Finset.mem_image] at h
  obtain ⟨x, _, rfl⟩ := h
  rcases place_mem (start j) x with ⟨i, hiw, eq⟩ | rest
  · exact Or.inl ⟨i, Nat.lt_of_lt_of_le hiw (barrelWidth_le j lo hi), eq⟩
  · exact Or.inr rest

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelChecks ====

-- ==== begin CRTField ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field
open CodecBitSliceVerify

/-- A column packs the value of one wire for each possible input row. -/
def rowWord (cols : Cols) (row : Nat) : Nat := packBits (cols.map (·.testBit row))

theorem run_columns (P : Program) (input output : Cols) (mask row : Nat)
    (hm : mask.testBit row = true) (hb : ∀ i ∈ P, target i < input.length)
    (checked : eval mask P input = (true, output)) (phase : Bool) (tape : List Bool) :
    run P tape ⟨phase, MeasuredCodec5.bitsOf (rowWord input row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord output row)⟩ := by
  have initial : Rel input (rowWord input row) row := fun q => pack_rows input row q
  have proof := eval_sound mask row hm P input _ hb initial (congrArg Prod.fst checked)
  rw [MeasuredCodec5.run_sim, MeasuredCodec5.sim_safe P _ proof.1]
  apply congrArg (State.mk phase)
  funext q
  change (MeasuredCodec5.bitRun P _).testBit q = (rowWord output row).testBit q
  rw [proof.2 q, checked]
  exact (pack_rows output row q).symm

/-- Slot zero means no tag. Slot k+1 selects k; each slot contains all 2^d input words. -/
def tagColumn (d k : Nat) : Nat := CertificateBits.mask d <<< ((k+1)*2^d)

def inputColumn (d q : Nat) : Nat :=
  if q < d then CertificateBits.input (d+5) q else if 22 ≤ q ∧ q < 38 then tagColumn d (q-22) else 0

def inputCols (d : Nat) : Cols := (List.range 38).map (inputColumn d)

/-- The opposite direction's erasure masks give the rows of this scalar minus identity. -/
def rowMask (p : Nat) (mir : Bool) (i : Nat) := (eraseMasks p (!mir)).getD i 0

def outputColumn (p : Nat) (mir : Bool) (q : Nat) : Nat :=
  let d := fieldDegree p
  if q < d then
    let extra := (List.range 16).flatMap fun k => (selected d ((rowMask p mir q) >>> (k*d))).map
      fun j => tagColumn d k &&& inputColumn d j
    extra.foldl Nat.xor (inputColumn d q)
  else inputColumn d q

def outputCols (p : Nat) (mir : Bool) : Cols := (List.range 38).map (outputColumn p mir)

def fieldTest (p : Nat) (mir : Bool) : Bool :=
  let P := fieldCore p mir
  let d := fieldDegree p
  (P.all (fun i => decide (target i < 38))) &&
    (eval (CertificateBits.mask (d+5)) P (inputCols d) == (true, outputCols p mir))

theorem run_field_of_test (p : Nat) (mir : Bool) (tested : fieldTest p mir = true)
    (row : Nat) (small : row < 2^(fieldDegree p+5)) (phase : Bool) (m : List Bool) :
    run (fieldCore p mir) m ⟨phase, MeasuredCodec5.bitsOf (rowWord (inputCols (fieldDegree p)) row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord (outputCols p mir) row)⟩ := by
  simp only [fieldTest, Bool.and_eq_true] at tested
  obtain ⟨bound, check⟩ := tested
  apply run_columns _ _ _ (CertificateBits.mask (fieldDegree p+5)) row
  · exact CertificateBits.mask_bit _ _ small
  · intro i hi
    simpa [inputCols] using (of_decide_eq_true (List.all_eq_true.mp bound i hi))
  · exact beq_iff_eq.mp check

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

end
-- ==== end CRTField ====

-- ==== begin CRTFieldCases ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

private theorem field_tested_257_f : fieldTest 257 false = true := by decide +kernel

private theorem field_tested_257_t : fieldTest 257 true = true := by decide +kernel

private theorem field_tested_313_f : fieldTest 313 false = true := by decide +kernel

private theorem field_tested_313_t : fieldTest 313 true = true := by decide +kernel

private theorem field_tested_471_f : fieldTest 471 false = true := by decide +kernel

private theorem field_tested_471_t : fieldTest 471 true = true := by decide +kernel

private theorem field_tested_1193_f : fieldTest 1193 false = true := by decide +kernel

private theorem field_tested_1193_t : fieldTest 1193 true = true := by decide +kernel

private theorem field_tested_1571_f : fieldTest 1571 false = true := by decide +kernel

private theorem field_tested_1571_t : fieldTest 1571 true = true := by decide +kernel

private theorem field_tested_4593_f : fieldTest 4593 false = true := by decide +kernel

private theorem field_tested_4593_t : fieldTest 4593 true = true := by decide +kernel

private theorem field_tested_5349_f : fieldTest 5349 false = true := by decide +kernel

private theorem field_tested_5349_t : fieldTest 5349 true = true := by decide +kernel

private theorem field_tested_5981_f : fieldTest 5981 false = true := by decide +kernel

private theorem field_tested_5981_t : fieldTest 5981 true = true := by decide +kernel

private theorem field_tested_6891_f : fieldTest 6891 false = true := by decide +kernel

private theorem field_tested_6891_t : fieldTest 6891 true = true := by decide +kernel

theorem field_tested (p : Nat) (hp : UsedField p) (mir : Bool) : fieldTest p mir = true := by
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir <;> decide +kernel
  · cases mir
    · exact field_tested_257_f
    · exact field_tested_257_t
  · cases mir
    · exact field_tested_313_f
    · exact field_tested_313_t
  · cases mir
    · exact field_tested_471_f
    · exact field_tested_471_t
  · cases mir
    · exact field_tested_1193_f
    · exact field_tested_1193_t
  · cases mir
    · exact field_tested_1571_f
    · exact field_tested_1571_t
  · cases mir
    · exact field_tested_4593_f
    · exact field_tested_4593_t
  · cases mir
    · exact field_tested_5349_f
    · exact field_tested_5349_t
  · cases mir
    · exact field_tested_5981_f
    · exact field_tested_5981_t
  · cases mir
    · exact field_tested_6891_f
    · exact field_tested_6891_t

theorem run_field (p : Nat) (hp : UsedField p) (mir : Bool) (row : Nat) (small : row < 2^(fieldDegree p+5))
    (phase : Bool) (m : List Bool) :
    run (fieldCore p mir) m ⟨phase, MeasuredCodec5.bitsOf (rowWord (inputCols (fieldDegree p)) row)⟩ =
      ⟨phase, MeasuredCodec5.bitsOf (rowWord (outputCols p mir) row)⟩ :=
  run_field_of_test p mir (field_tested p hp mir) row small phase m

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

end
-- ==== end CRTFieldCases ====

-- ==== begin CRTFieldRows ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

/-- Apply a scalar matrix to one row, allowing the row entries to be Boolean values or linear forms. -/
def accumulate {α : Type} (p : Nat) (mir : Bool) (q : Nat) (combine : α → α → α)
    (source : Nat → α) (term : Nat → Nat → α) : α :=
  let d := fieldDegree p
  ((List.range 16).flatMap fun k => (selected d (rowMask p mir q >>> (k*d))).map (term k)).foldl combine (source q)

private theorem map_fold {α β} (f : α → β) (op : α → α → α) (op' : β → β → β)
    (pres : ∀ a b, f (op a b) = op' (f a) (f b)) (xs : List α) (a : α) :
    f (xs.foldl op a) = (xs.map f).foldl op' (f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons]; rw [ih,pres]

theorem map_accumulate {α β} (p : Nat) (mir : Bool) (q : Nat) (f : α → β)
    (op : α → α → α) (op' : β → β → β) (pres : ∀ a b, f (op a b) = op' (f a) (f b))
    (src : Nat → α) (term : Nat → Nat → α) :
    f (accumulate p mir q op src term) =
      accumulate p mir q op' (fun j => f (src j)) (fun k j => f (term k j)) := by
  unfold accumulate
  rw [map_fold _ _ _ pres]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]

/-- Linear forms for the output coefficient bits under a fixed selector. -/
def scalarRow (p : Nat) (mir : Bool) (hot : Nat → Bool) (data : Nat → Nat) (q : Nat) : Nat :=
  accumulate p mir q Nat.xor data (fun k j => if hot k then data j else 0)

theorem rowValue_zero (x : Nat → Bool) (n : Nat) : rowValue x 0 n = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rowValue,ih]

theorem accumulate_congr {α} (p : Nat) (mir : Bool) (q : Nat) (op : α → α → α)
    (src src' : Nat → α) (a b : Nat → Nat → α) (hs : src q = src' q)
    (ht : ∀ k, ∀ j < fieldDegree p, a k j = b k j) :
    accumulate p mir q op src a = accumulate p mir q op src' b := by
  have same k : (selected (fieldDegree p) (rowMask p mir q >>> (k*fieldDegree p))).map (a k) =
      (selected (fieldDegree p) (rowMask p mir q >>> (k*fieldDegree p))).map (b k) := by
    apply List.map_congr_left
    intro j hj
    exact ht k j (List.mem_range.mp (List.mem_filter.mp hj).1)
  unfold accumulate
  simp only [same,hs]

theorem output_bit (p : Nat) (mir : Bool) (q : Nat) (hq : q < fieldDegree p) (row dim : Nat)
    (x : Nat → Bool) (hot : Nat → Bool) (data : Nat → Nat)
    (ht : ∀ k, (tagColumn (fieldDegree p) k).testBit row = hot k)
    (hd : ∀ j < fieldDegree p, (inputColumn (fieldDegree p) j).testBit row = rowValue x (data j) dim) :
    (outputColumn p mir q).testBit row = rowValue x (scalarRow p mir hot data q) dim := by
  simp only [outputColumn, if_pos hq]
  change ((accumulate p mir q Nat.xor (inputColumn (fieldDegree p))
    (fun k j => tagColumn (fieldDegree p) k &&& inputColumn (fieldDegree p) j))).testBit row = _
  rw [map_accumulate p mir q (fun a : Nat => a.testBit row) Nat.xor Bool.xor (fun _ _ => Nat.testBit_xor ..)]
  unfold scalarRow
  rw [map_accumulate p mir q (fun a => rowValue x a dim) Nat.xor Bool.xor (fun a b => rowValue_xor x a b dim)]
  apply accumulate_congr
  · exact hd q hq
  · intro k j hj
    rw [Nat.testBit_and,ht,hd j hj]
    cases hot k <;> simp [rowValue_zero]

def packedRow (d slot v : Nat) : Nat := v+slot*2^d

theorem packedRow_lt {d slot v : Nat} (sv : v < 2^d) (ss : slot < 32) : packedRow d slot v < 2^(d+5) := by
  have h := Nat.mul_le_mul_right (2^d) (show slot+1 ≤ 32 by omega)
  simp only [Nat.succ_mul] at h
  unfold packedRow
  rw [Nat.pow_add, show 2^5 = 32 by decide]
  omega

theorem data_bit {d q slot v : Nat} (sq : q < d) (sv : v < 2^d) (ss : slot < 32) :
    (inputColumn d q).testBit (packedRow d slot v) = v.testBit q := by
  rw [inputColumn,if_pos sq,CertificateBits.input_bit _ _ _ (packedRow_lt sv ss)]
  have low : packedRow d slot v % 2^d = v := by simp [packedRow, Nat.mod_eq_of_lt sv]
  have bit := congrArg (fun a : Nat => a.testBit q) low
  simpa only [Nat.testBit_mod_two_pow,sq,decide_true,Bool.true_and] using bit

theorem tag_bit {d slot v : Nat} (sv : v < 2^d) (k : Nat) :
    (tagColumn d k).testBit (packedRow d slot v) = decide (slot = k+1) := by
  let b := 2^d
  change ((2^b-1) <<< ((k+1)*b)).testBit (v+slot*b) = _
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  change v < b at sv
  rcases lt_trichotomy slot (k+1) with low | eq | high
  · have h := Nat.mul_le_mul_right b (show slot+1 ≤ k+1 by omega)
    rw [Nat.succ_mul] at h
    simp [show ¬v+slot*b ≥ (k+1)*b by omega,show slot ≠ k+1 by omega]
  · subst slot
    simp [sv]
  · have h := Nat.mul_le_mul_right b (show k+1+1 ≤ slot by omega)
    rw [Nat.succ_mul] at h
    simp [show ¬v+slot*b-(k+1)*b < b by omega,show slot ≠ k+1 by omega]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Field

end
-- ==== end CRTFieldRows ====

-- ==== begin CRTMatrix ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Matrix

abbrev Rows := Array Nat

def read (rows : Rows) (q : Nat) := (rows[q]?).getD 0

def basis (rows : Rows) (word : Nat → Bool) (dim : Nat) (outside : BasisState) (q : Wire) : Bool :=
  if q < rows.size then rowValue word (read rows q) dim else outside q

def applyPair (rows : Rows) (op : Wire × Wire) : Rows :=
  rows.setIfInBounds op.2 (read rows op.2 ^^^ read rows op.1)

def applyOps (ops : List (Wire × Wire)) (rows : Rows) : Rows := ops.foldl applyPair rows

@[simp] theorem applyPair_size (rows : Rows) (op : Wire × Wire) : (applyPair rows op).size = rows.size := by
  simp [applyPair]

@[simp] theorem applyOps_size (ops : List (Wire × Wire)) (rows : Rows) : (applyOps ops rows).size = rows.size := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih => exact (ih (applyPair rows op)).trans (applyPair_size rows op)

theorem run_ops (ops : List (Wire × Wire)) (rows : Rows) (x : Nat → Bool) (dim : Nat)
    (outside : BasisState) (ph : Bool) (m : List Bool)
    (within : ∀ op ∈ ops, op.1 < rows.size ∧ op.2 < rows.size) :
    run (cnotProgram ops) m ⟨ph,basis rows x dim outside⟩ =
      ⟨ph,basis (applyOps ops rows) x dim outside⟩ := by
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih =>
    obtain ⟨a,b⟩ := op
    obtain ⟨ha,hb⟩ := within (a,b) (by simp)
    change a < rows.size at ha
    change b < rows.size at hb
    have step : writeBit (basis rows x dim outside) b
        (basis rows x dim outside b ^^ basis rows x dim outside a) =
        basis (applyPair rows (a,b)) x dim outside := by
      funext q
      by_cases e : q = b
      · subst q
        simp [basis,read,applyPair,writeBit,ha,hb,rowValue_xor]
      · simp [basis,read,applyPair,writeBit,Function.update_of_ne e,Ne.symm e]
    change run (cnotProgram tail) m ⟨ph,_⟩ = _
    rw [step]
    apply ih
    intro op ho
    simpa only [applyPair_size] using within op (List.mem_cons_of_mem _ ho)

theorem apply_map (ops : List (Wire × Wire)) (f : Nat → Nat) (zero : f 0 = 0)
    (linear : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (rows : Rows) :
    applyOps ops (rows.map f) = (applyOps ops rows).map f := by
  have mapRead (r : Rows) (i : Nat) : read (r.map f) i = f (read r i) := by
    unfold read
    rw [Array.getElem?_map]
    cases r[i]? <;> simp [zero]
  have step (r : Rows) (p : Wire × Wire) : applyPair (r.map f) p = (applyPair r p).map f := by
    unfold applyPair
    rw [mapRead,mapRead,←linear]
    apply Array.ext_getElem?; intro i
    simp only [Array.getElem?_map, Array.getElem?_setIfInBounds, Array.size_map]
    split <;> (try split) <;> rfl
  induction ops generalizing rows with
  | nil => rfl
  | cons op tail ih =>
    change applyOps tail (applyPair (rows.map f) op) = (applyOps tail (applyPair rows op)).map f
    rw [step,ih]

def units (n : Nat) : Rows := Array.ofFn (fun i : Fin n => 2^i.val)

theorem value_unit (x : Nat → Bool) (i dim : Nat) :
    rowValue x (2^i) dim = if i < dim then x i else false := by
  induction dim with
  | zero => simp [rowValue]
  | succ n ih =>
    simp only [rowValue,ih,Nat.testBit_two_pow]
    by_cases e : i = n
    · subst i; simp
    · by_cases h : i<n
      · simp [e,h,show i < n+1 by omega]
      · simp [e,h,show ¬i < n+1 by omega]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Matrix

end
-- ==== end CRTMatrix ====

-- ==== begin CRTFieldRun ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Field Placement Matrix CodecBitSliceVerify

def flags (n slot q : Nat) : Bool := decide (n ≤ q ∧ q < n+16 ∧ slot = q-n+1)

def frame (rows : Rows) (x : Nat → Bool) (dim slot : Nat) (ph : Bool) : State :=
  ⟨ph, Matrix.basis rows x dim (flags rows.size slot)⟩

def scalarRows (rows : Rows) (p : Nat) (mir : Bool) (slot off : Nat) : Rows :=
  Array.ofFn fun q : Fin rows.size =>
    if off ≤ q.val ∧ q.val < off + fieldDegree p then
      scalarRow p mir (fun k => decide (slot = k+1)) (fun j => read rows (off+j)) (q.val-off)
    else read rows q.val

@[simp] theorem scalarRows_size (r : Rows) (p : Nat) (mir : Bool) (s o : Nat) :
    (scalarRows r p mir s o).size = r.size := by simp [scalarRows]

theorem scalar_read {r : Rows} {q : Nat} (hq : q < r.size) (p : Nat) (mir : Bool) (slot off : Nat) :
    read (scalarRows r p mir slot off) q =
      if off ≤ q ∧ q < off+fieldDegree p then
        scalarRow p mir (fun k => decide (slot = k+1)) (fun j => read r (off+j)) (q-off)
      else read r q := by
  simp [scalarRows,Matrix.read,hq]

def fieldPool (d : Nat) := (Finset.range 38).filter (fieldScope d)

theorem fieldPool_iff {d q : Nat} (sd : d ≤ 12) : q ∈ fieldPool d ↔ fieldScope d q := by
  simp only [fieldPool,Finset.mem_filter,Finset.mem_range]
  unfold fieldScope
  omega

private theorem pack_lt (bs : List Bool) : packBits bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp [packBits, Nat.bit, Nat.pow_succ] <;> omega

def fieldWord (d : Nat) (getBit : Nat → Bool) : Nat := packBits ((List.range d).map getBit)

theorem fieldWord_small (d : Nat) (v : Nat → Bool) : fieldWord d v < 2^d := by
  simpa [fieldWord] using pack_lt ((List.range d).map v)

theorem fieldWord_bit (d : Nat) (v : Nat → Bool) (q : Nat) (hq : q < d) :
    (fieldWord d v).testBit q = v q := by
  simp [fieldWord,pack_testBit,List.getElem?_map,List.getElem?_range hq]

private theorem column_bit (f : Nat → Nat) (row q : Nat) (hq : q < 38) :
    (rowWord ((List.range 38).map f) row).testBit q = (f q).testBit row := by
  rw [rowWord,pack_rows,List.getElem?_map,List.getElem?_range hq]
  rfl

theorem frame_field (r : Rows) (p : Nat) (hp : UsedField p) (mir : Bool) (off slot dim : Nat)
    (small : slot < 32) (endp : off+fieldDegree p ≤ r.size) (x : Nat → Bool) (ph : Bool) (m : List Bool) :
    run (renameProgram (fieldPlace r.size off) (fieldCore p mir)) m (frame r x dim slot ph) =
      frame (scalarRows r p mir slot off) x dim slot ph := by
  let d := fieldDegree p
  let f := fieldPlace r.size off
  let data := fun j => read r (off+j)
  let v := fieldWord d (fun j => rowValue x (data j) dim)
  let row := packedRow d slot v
  have sd := (used_degree p hp).2
  have sv : v < 2^d := fieldWord_small _ _
  have val (j : Nat) (hj : j < d) : (inputColumn d j).testBit row = rowValue x (data j) dim :=
    (data_bit hj sv small).trans (fieldWord_bit _ _ _ hj)
  have tags (k : Nat) : (tagColumn d k).testBit row = decide (slot=k+1) := tag_bit sv k
  have live := Placement.support (fits_core p hp mir)
  have sub : wires (fieldCore p mir) ⊆ fieldPool d := fun _ h => (fieldPool_iff sd).mpr (live _ h)
  have maps := field_place_maps sd endp
  have inj : ∀ a ∈ fieldPool d, ∀ b ∈ fieldPool d, f a = f b → a = b :=
    fun a ha b hb => maps.2 a ((fieldPool_iff sd).mp ha) b ((fieldPool_iff sd).mp hb)
  have point (q : Nat) (hq : fieldScope d q) :
      (inputColumn d q).testBit row = (frame r x dim slot ph).basis (f q) := by
    by_cases left : q < d
    · have lt : q < 12 := by omega
      have inside : off+q < r.size := by omega
      simpa [frame,Matrix.basis,f,fieldPlace,lt,inside,data] using val q left
    · obtain hq := hq.resolve_left left
      by_cases mid : q < 22
      · simp [frame,Matrix.basis,f,fieldPlace,inputColumn,left,flags,show ¬q<12 by omega,mid,
          show ¬22≤q by omega,show ¬r.size+16+(q-12)<r.size by omega,
          show ¬r.size+16+(q-12)<r.size+16 by omega]
      · have inside : r.size+(q-22) < r.size+16 := by omega
        simp [frame,Matrix.basis,f,fieldPlace,inputColumn,left,flags,show ¬q<12 by omega,mid,
          show 22≤q by omega,hq.2,inside,tags]
  have rel := run_rename_pool f (fieldPool d) inj (fieldCore p mir) sub m
    ⟨ph,MeasuredCodec5.bitsOf (rowWord (inputCols d) row)⟩ (frame r x dim slot ph) rfl (by
      intro q hq
      have bound := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
      exact (column_bit (inputColumn d) row q bound).trans (point q ((fieldPool_iff sd).mp hq)))
  rw [run_field p hp mir row (packedRow_lt sv small)] at rel
  refine State.extensionality _ _ ?_ ?_
  · exact rel.1
  funext q
  by_cases inPool : q ∈ (fieldPool d).image f
  · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp inPool
    rw [rel.2 a ha]
    have shape := (fieldPool_iff sd).mp ha
    have sa := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    change (rowWord (outputCols p mir) row).testBit a = _
    rw [show (rowWord (outputCols p mir) row).testBit a = (outputColumn p mir a).testBit row from
      column_bit _ _ _ sa]
    by_cases left : a < d
    · have a8 : a < 12 := by omega
      have inside : off+a < r.size := by omega
      have inSlice : off ≤ off+a ∧ off+a < off+fieldDegree p := ⟨by omega, Nat.add_lt_add_left left _⟩
      rw [output_bit p mir a left row dim x _ data tags val]
      simp [frame,Matrix.basis,f,fieldPlace,a8,inside,scalar_read inside,inSlice,data]
    · rw [outputColumn,if_neg left]
      rw [point a shape]
      have edge : r.size ≤ f a := by
        obtain ⟨a8,_⟩ := shape.resolve_left left
        unfold f fieldPlace
        simp only [show ¬a<12 by omega,if_false]
        split <;> (try unfold Wire at *) <;> omega
      simp only [frame,Matrix.basis,scalarRows_size,if_neg (Nat.not_lt_of_ge edge)]
  · rw [run_rename_pool_outside f (fieldPool d) (fieldCore p mir) sub m _ q inPool]
    by_cases inside : q < r.size
    · have outsideSlice : ¬(off ≤ q ∧ q < off+fieldDegree p) := by
        rintro ⟨lower,upper⟩
        apply inPool
        have sq : q-off < d := (Nat.sub_lt_iff_lt_add lower).mpr (Nat.add_comm off d ▸ upper)
        refine Finset.mem_image.mpr ⟨q-off,(fieldPool_iff sd).mpr (Or.inl sq),?_⟩
        simpa only [f,fieldPlace,if_pos (Nat.lt_of_lt_of_le sq sd)] using Nat.add_sub_of_le lower
      simp [frame,Matrix.basis,inside,scalar_read inside,outsideSlice]
    · simp [frame,Matrix.basis,inside]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTFieldRun ====

-- ==== begin CRTTriangle ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix

def controlled (c : Wire) (pairs : List (Wire × Wire)) : Program :=
  pairs.map (fun (a,b) => Instr.CCX c a b)

theorem run_controlled (c : Wire) (pairs : List (Wire × Wire)) (m : List Bool) (s : State)
    (apart : ∀ p ∈ pairs, p.2 ≠ c) :
    run (controlled c pairs) m s = if s.basis c then run (cnotProgram pairs) m s else s := by
  induction pairs generalizing s with
  | nil => simp [controlled,cnotProgram,run]
  | cons p tail ih =>
    obtain ⟨a,b⟩ := p
    have ne : b ≠ c := apart (a,b) (by simp)
    have rest : ∀ p ∈ tail, p.2 ≠ c := fun p hp => apart p (List.mem_cons_of_mem _ hp)
    cases s with
    | mk ph bits =>
      cases bit : bits c <;>
        simp only [controlled,cnotProgram,List.map_cons,run,bit,Bool.false_and,Bool.xor_false,
          Bool.true_and,Bool.false_eq_true,if_false,if_true]
      · simpa [writeBit,Function.update_eq_self,controlled,cnotProgram,bit] using ih ⟨ph,bits⟩ rest
      · have unchanged : writeBit bits b (bits b ^^ bits a) c = true := by
          simp [writeBit,Function.update_of_ne ne.symm,bit]
        simpa [controlled,cnotProgram,unchanged] using ih ⟨ph,writeBit bits b (bits b ^^ bits a)⟩ rest

def xorAt (bits : BasisState) : List Wire → Bool
  | [] => false
  | w::ws => bits w ^^ xorAt bits ws

private theorem xorAt_congr (xs : List Wire) (u v : BasisState) (h : ∀ q ∈ xs, u q = v q) :
    xorAt u xs = xorAt v xs := by
  induction xs with
  | nil => rfl
  | cons q xs ih => rw [xorAt,xorAt,h q (by simp),ih (fun j hj => h j (List.mem_cons_of_mem _ hj))]

def toggles (xs : List Wire) (t : Wire) : Program := xs.map (fun q => Instr.CX q t)

theorem run_toggles (xs : List Wire) (t : Wire) (sep : t ∉ xs) (m : List Bool) (ph : Bool) (bits : BasisState) :
    run (toggles xs t) m ⟨ph,bits⟩ = ⟨ph,writeBit bits t (bits t ^^ xorAt bits xs)⟩ := by
  induction xs generalizing bits with
  | nil => simp [toggles,xorAt,run,writeBit,Function.update_eq_self]
  | cons q xs ih =>
    have hn : t ∉ xs := fun h => sep (List.mem_cons_of_mem _ h)
    change run (toggles xs t) m ⟨ph,writeBit bits t (bits t ^^ bits q)⟩ = _
    rw [ih hn]
    have same : xorAt (writeBit bits t (bits t ^^ bits q)) xs = xorAt bits xs := by
      apply xorAt_congr
      intro j hj
      have ne : j ≠ t := fun eq => hn (eq ▸ hj)
      simp [writeBit,Function.update_of_ne ne]
    rw [same]
    simp [xorAt,writeBit,Function.update_idem]

def tagSources (n h : Nat) : List Wire :=
  ((List.range 16).filter (fun k => k.testBit h)).map (n+·)

def enabled (n slot h : Nat) := xorAt (flags n slot) (tagSources n h)

def editPairs (off d m h : Nat) : List (Wire × Wire) :=
  (List.range (m-2^h)).reverse.flatMap fun j => (List.range d).map
    (fun i => (off+d*j+i, off+d*(j+2^h)+i))

def oriented {α : Type} (mir : Bool) (xs : List α) := if mir then xs.reverse else xs

def stageRows (rows : Rows) (slot off d m h : Nat) (mir : Bool) : Rows :=
  if m ≤ 2^h then rows else if enabled rows.size slot h then
    applyOps (oriented mir (editPairs off d m h)) rows else rows

@[simp] theorem stageRows_size (rows : Rows) (s o d m h : Nat) (mir : Bool) :
    (stageRows rows s o d m h mir).size = rows.size := by
  unfold stageRows
  split <;> (try split) <;> simp

theorem tagSource_bounds {n h q : Nat} (hit : q ∈ tagSources n h) : n ≤ q ∧ q < n+16 := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hit
  have sk := List.mem_range.mp (List.mem_filter.mp hk).1
  omega

theorem edit_bounds (rows : Rows) (off d m h : Nat) (mir : Bool) (endp : off+d*m ≤ rows.size) :
    ∀ p ∈ oriented mir (editPairs off d m h), p.1 < rows.size ∧ p.2 < rows.size := by
  intro p hp
  have mem : p ∈ editPairs off d m h := by cases mir <;> simpa [oriented] using hp
  obtain ⟨j,hj,atj⟩ := List.mem_flatMap.mp mem
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp atj
  have ji := List.mem_range.mp (List.mem_reverse.mp hj)
  have si := List.mem_range.mp hi
  unfold Wire at *
  have maxj := Nat.mul_le_mul_left d (show j+2^h+1 ≤ m by omega)
  rw [Nat.mul_succ] at maxj
  have ord := Nat.mul_le_mul_left d (Nat.le_add_right j (2^h))
  dsimp only
  omega


def withTag (r : Rows) (x : Nat → Bool) (dim slot h : Nat) (ph : Bool) : State :=
  ⟨ph, Matrix.basis r x dim (writeBit (flags r.size slot) (r.size+24) (enabled r.size slot h))⟩

private theorem toggle_frame (r : Rows) (x : Nat → Bool) (dim slot h : Nat) (ph : Bool) (tape : List Bool) :
    run (toggles (tagSources r.size h) (r.size+24)) tape (frame r x dim slot ph) =
      withTag r x dim slot h ph := by
  have external (q : Wire) (hq : r.size ≤ q) : (frame r x dim slot ph).basis q = flags r.size slot q := by
    simp only [frame,Matrix.basis,if_neg (Nat.not_lt_of_ge hq)]
  have parity := xorAt_congr (tagSources r.size h) (frame r x dim slot ph).basis (flags r.size slot)
    (fun q hq => external q (tagSource_bounds hq).1)
  have sep : r.size+24 ∉ tagSources r.size h := fun hq => by have := (tagSource_bounds hq).2; omega
  change run _ _ ⟨ph,(frame r x dim slot ph).basis⟩ = _
  rw [run_toggles _ _ sep,parity,external _ (by omega)]
  apply congrArg (State.mk ph)
  funext q
  by_cases eq : q = r.size+24
  · subst q; simp [Matrix.basis,flags,writeBit,enabled]
  · by_cases inside : q < r.size <;> simp [frame,Matrix.basis,inside,writeBit,Function.update_of_ne eq]

private theorem tag_restore (r : Rows) (x : Nat → Bool) (dim slot h : Nat) (ph : Bool) (tape : List Bool) :
    run (toggles (tagSources r.size h) (r.size+24)).reverse tape (withTag r x dim slot h ph) =
      frame r x dim slot ph := by
  let ops := (tagSources r.size h).map (fun a => (a,r.size+24))
  have same : cnotProgram ops = toggles (tagSources r.size h) (r.size+24) := by
    simp [cnotProgram,ops,toggles,List.map_map,Function.comp_def]
  have inv := reverse_cnots ops (by
    intro pair hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    have b := (tagSource_bounds hq).2
    change q ≠ r.size+24
    exact Nat.ne_of_lt (lt_trans b (by omega : r.size+16 < r.size+24))) (frame r x dim slot ph) [] tape
  have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
  rw [rev,same,toggle_frame] at inv
  exact inv

private theorem stage_shape (n off d m h : Nat) (wide : ¬m≤2^h) (mir : Bool) :
    oriented mir (stage n off d m h) =
    toggles (tagSources n h) (n+24) ++ controlled (n+24) (oriented mir (editPairs off d m h)) ++
      (toggles (tagSources n h) (n+24)).reverse := by
  cases mir <;> simp [oriented,stage,wide,toggles,tagSources,controlled,editPairs,List.map_flatMap,
    List.map_map,Function.comp_def,List.reverse_append,List.append_assoc]

theorem frame_stage (r : Rows) (off d m h : Nat) (mir : Bool) (endp : off+d*m ≤ r.size)
    (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (tape : List Bool) :
    run (oriented mir (stage r.size off d m h)) tape (frame r x dim slot ph) =
      frame (stageRows r slot off d m h mir) x dim slot ph := by
  by_cases short : m ≤ 2^h
  · cases mir <;> simp [stage,stageRows,short,oriented,run]
  rw [stage_shape _ _ _ _ _ short, run_append,run_take,run_append,run_take,toggle_frame]
  let ops := oriented mir (editPairs off d m h)
  have within := edit_bounds r off d m h mir endp
  have sep : ∀ p ∈ ops, p.2 ≠ r.size+24 := fun p hp => by
    have := (within p hp).2; unfold Wire at *; omega
  have bit : (withTag r x dim slot h ph).basis (r.size+24) = enabled r.size slot h := by
    simp [withTag,Matrix.basis,writeBit]
  rw [run_controlled _ _ _ _ sep,bit]
  cases yes : enabled r.size slot h with
  | false => simpa [stageRows,short,yes] using tag_restore r x dim slot h ph _
  | true =>
    simp only [if_true]
    rw [show run (cnotProgram ops) _ (withTag r x dim slot h ph) = withTag (applyOps ops r) x dim slot h ph by
      simpa only [withTag,applyOps_size] using run_ops ops r x dim _ ph _ within]
    simpa only [stageRows,if_neg short,yes,if_true,applyOps_size] using
      tag_restore (applyOps ops r) x dim slot h ph _

def r8Enabled (n slot : Nat) (tags : List Nat) : Bool :=
  xorAt (flags n slot) (tags.map (n + ·))

def r8Ops (off : Nat) (st : R8Step) : List (Wire × Wire) :=
  let pre := st.pre.map (fun p => (off + p.1, off + p.2))
  pre ++ [(off + st.src, off + st.dst)] ++ pre.reverse

def r8StepRows (rows : Rows) (slot off : Nat) (st : R8Step) : Rows :=
  if r8Enabled rows.size slot st.tags then applyOps (r8Ops off st) rows else rows

@[simp] theorem r8StepRows_size (rows : Rows) (s o : Nat) (st : R8Step) :
    (r8StepRows rows s o st).size = rows.size := by
  unfold r8StepRows; split <;> simp

theorem r8Ops_bounds (rows : Rows) (off : Nat) (st : R8Step)
    (hg : Placement.r8StepGood st = true) (endp : off + 16 ≤ rows.size) :
    ∀ p ∈ r8Ops off st, p.1 < rows.size ∧ p.2 < rows.size ∧ p.1 ≠ p.2 := by
  unfold Placement.r8StepGood at hg
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨_, hpre⟩, hsrc, hdst, hne⟩ := hg
  intro p hp
  unfold r8Ops at hp
  rcases List.mem_append.mp hp with hp1 | hp2
  · rcases List.mem_append.mp hp1 with hpA | hpB
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpA
      obtain ⟨h1, h2, h3⟩ := hpre q hq
      unfold Wire at *; dsimp only; omega
    · simp only [List.mem_singleton] at hpB; subst hpB
      unfold Wire at *; dsimp only; omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hp2)
    obtain ⟨h1, h2, h3⟩ := hpre q hq
    unfold Wire at *; dsimp only; omega

def withR8Tag (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat) (ph : Bool) : State :=
  ⟨ph, Matrix.basis r x dim (writeBit (flags r.size slot) (r.size+24) (r8Enabled r.size slot tags))⟩

private theorem toggle_r8_frame (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat)
    (htags : ∀ k ∈ tags, k < 16) (ph : Bool) (tape : List Bool) :
    run (toggles (tags.map (r.size + ·)) (r.size+24)) tape (frame r x dim slot ph) =
      withR8Tag r x dim slot tags ph := by
  have external (q : Wire) (hq : r.size ≤ q) : (frame r x dim slot ph).basis q = flags r.size slot q := by
    simp only [frame, Matrix.basis, if_neg (Nat.not_lt_of_ge hq)]
  have parity := xorAt_congr (tags.map (r.size + ·)) (frame r x dim slot ph).basis (flags r.size slot)
    (fun q hq => by obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq; exact external _ (by omega))
  have sep : r.size+24 ∉ tags.map (r.size + ·) := by
    intro hq; obtain ⟨k, hk, he⟩ := List.mem_map.mp hq; have := htags k hk; unfold Wire at *; omega
  change run _ _ ⟨ph, (frame r x dim slot ph).basis⟩ = _
  rw [run_toggles _ _ sep, parity, external _ (by omega)]
  apply congrArg (State.mk ph)
  funext q
  by_cases eq : q = r.size+24
  · subst q; simp [Matrix.basis, flags, writeBit, r8Enabled]
  · by_cases inside : q < r.size <;> simp [frame, Matrix.basis, inside, writeBit, Function.update_of_ne eq]

private theorem tag_r8_restore (r : Rows) (x : Nat → Bool) (dim slot : Nat) (tags : List Nat)
    (htags : ∀ k ∈ tags, k < 16) (ph : Bool) (tape : List Bool) :
    run (toggles (tags.map (r.size + ·)) (r.size+24)).reverse tape (withR8Tag r x dim slot tags ph) =
      frame r x dim slot ph := by
  let ops := (tags.map (r.size + ·)).map (fun a => (a, r.size+24))
  have same : cnotProgram ops = toggles (tags.map (r.size + ·)) (r.size+24) := by
    simp [cnotProgram, ops, toggles, List.map_map, Function.comp_def]
  have inv := reverse_cnots ops (by
    intro pair hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have := htags k hk; change r.size + k ≠ r.size + 24; unfold Wire at *; omega) (frame r x dim slot ph) [] tape
  have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
  rw [rev, same, toggle_r8_frame r x dim slot tags htags] at inv
  exact inv

theorem frame_r8Step (r : Rows) (off : Nat) (st : R8Step)
    (hg : Placement.r8StepGood st = true) (endp : off + 16 ≤ r.size)
    (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (tape : List Bool) :
    run (r8Step r.size off st) tape (frame r x dim slot ph) =
      frame (r8StepRows r slot off st) x dim slot ph := by
  have hg' := hg
  unfold Placement.r8StepGood at hg'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨⟨htags, hpre⟩, hsrc, hdst, hne⟩ := hg'
  let prePairs : List (Wire × Wire) := st.pre.map (fun p => (off + p.1, off + p.2))
  have hpreB : ∀ p ∈ prePairs, p.1 < r.size ∧ p.2 < r.size := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨h1, h2, _⟩ := hpre q hq; unfold Wire at *; dsimp only; omega
  have hpreA : ∀ p ∈ prePairs, p.1 ≠ p.2 := by
    intro p hp; obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨_, _, h3⟩ := hpre q hq; unfold Wire at *; dsimp only; omega
  have hpreRevB : ∀ p ∈ prePairs.reverse, p.1 < r.size ∧ p.2 < r.size :=
    fun p hp => hpreB p (List.mem_reverse.mp hp)
  have shape : r8Step r.size off st =
      toggles (st.tags.map (r.size + ·)) (r.size+24) ++ cnotProgram prePairs ++
      controlled (r.size+24) [(off+st.src, off+st.dst)] ++ cnotProgram prePairs.reverse ++
      (toggles (st.tags.map (r.size + ·)) (r.size+24)).reverse := by
    simp [r8Step, toggles, cnotProgram, controlled, prePairs, List.map_reverse, List.map_map, Function.comp_def]
  rw [shape, run_append, run_take, run_append, run_take, run_append, run_take, run_append, run_take]
  rw [toggle_r8_frame r x dim slot st.tags htags]
  have sepC : ∀ p ∈ ([(off+st.src, off+st.dst)] : List (Wire × Wire)), p.2 ≠ r.size+24 := by
    intro p hp; simp only [List.mem_singleton] at hp; subst hp; unfold Wire at *; dsimp only; omega
  have hpreRun : ∀ t, run (cnotProgram prePairs) t (withR8Tag r x dim slot st.tags ph) =
      withR8Tag (applyOps prePairs r) x dim slot st.tags ph := fun t => by
    simpa only [withR8Tag, applyOps_size] using run_ops prePairs r x dim _ ph t hpreB
  cases yes : r8Enabled r.size slot st.tags with
  | false =>
    rw [run_controlled _ _ _ _ sepC]
    have bit : ∀ t, (run (cnotProgram prePairs) t (withR8Tag r x dim slot st.tags ph)).basis (r.size+24) = false := fun t => by
      rw [hpreRun]; simp [withR8Tag, Matrix.basis, writeBit, yes]
    rw [bit]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [reverse_cnots prePairs hpreA]
    simpa [r8StepRows, yes] using tag_r8_restore r x dim slot st.tags htags ph _
  | true =>
    rw [hpreRun, run_controlled _ _ _ _ sepC]
    have bit : (withR8Tag (applyOps prePairs r) x dim slot st.tags ph).basis (r.size+24) = true := by
      simp [withR8Tag, Matrix.basis, writeBit, yes]
    rw [bit]; simp only [↓reduceIte]
    have hmidB : ∀ p ∈ ([(off+st.src, off+st.dst)] : List (Wire × Wire)),
        p.1 < (applyOps prePairs r).size ∧ p.2 < (applyOps prePairs r).size := by
      intro p hp; simp only [List.mem_singleton] at hp; subst hp; rw [applyOps_size]; unfold Wire at *; dsimp only; omega
    have h2 : ∀ t, run (cnotProgram [(off+st.src, off+st.dst)]) t (withR8Tag (applyOps prePairs r) x dim slot st.tags ph) =
        withR8Tag (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) x dim slot st.tags ph := fun t => by
      simpa only [withR8Tag, applyOps_size] using run_ops [(off+st.src, off+st.dst)] (applyOps prePairs r) x dim _ ph t hmidB
    rw [h2]
    have hrevB : ∀ p ∈ prePairs.reverse,
        p.1 < (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)).size ∧
        p.2 < (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)).size := by
      intro p hp; rw [applyOps_size, applyOps_size]; exact hpreRevB p hp
    have h3 : ∀ t, run (cnotProgram prePairs.reverse) t (withR8Tag (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) x dim slot st.tags ph) =
        withR8Tag (applyOps prePairs.reverse (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r))) x dim slot st.tags ph := fun t => by
      simpa only [withR8Tag, applyOps_size] using
        run_ops prePairs.reverse (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) x dim _ ph t hrevB
    rw [h3]
    have hcomb : applyOps prePairs.reverse (applyOps [(off+st.src, off+st.dst)] (applyOps prePairs r)) = applyOps (r8Ops off st) r := by
      simp [r8Ops, applyOps, prePairs, List.foldl_append]
    rw [hcomb]
    simpa only [r8StepRows, yes, if_true, applyOps_size] using
      tag_r8_restore (applyOps (r8Ops off st) r) x dim slot st.tags htags ph _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTTriangle ====

-- ==== begin CRTComponents ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Placement

private theorem run_parts {α} (xs : List α) (g : α → Program) (next : Rows → α → Rows)
    (n : Nat) (x : Nat → Bool) (dim slot : Nat) (ph : Bool) (m : List Bool) (r : Rows) (size : r.size = n)
    (keep : ∀ r a, (next r a).size = r.size)
    (step : ∀ a ∈ xs, ∀ r : Rows, r.size = n → ∀ m,
      run (g a) m (frame r x dim slot ph) = frame (next r a) x dim slot ph) :
    run (xs.flatMap g) m (frame r x dim slot ph) = frame (xs.foldl next r) x dim slot ph := by
  induction xs generalizing r m with
  | nil => rfl
  | cons a xs ih =>
    rw [List.flatMap_cons,run_append,run_take,step a (by simp) r size]
    exact ih _ _ ((keep r a).trans size) (fun y hy => step y (List.mem_cons_of_mem _ hy))

private theorem fold_size {α} (xs : List α) (f : Rows → α → Rows) (r : Rows)
    (h : ∀ r a, (f r a).size = r.size) : (xs.foldl f r).size = r.size := by
  induction xs generalizing r with
  | nil => rfl
  | cons a xs ih => exact (ih (f r a)).trans (h r a)

def scalars (r : Rows) (p m off slot : Nat) (mir : Bool) : Rows :=
  (List.range m).foldl (fun a j => scalarRows a p mir slot (off+fieldDegree p*j)) r

def triRows (r : Rows) (off d m slot : Nat) (mir : Bool) : Rows :=
  (oriented mir (List.range 4)).foldl (fun a h => stageRows a slot off d m h mir) r

@[simp] theorem scalars_size (r : Rows) (p m off slot : Nat) (mir : Bool) :
    (scalars r p m off slot mir).size = r.size := fold_size _ _ _ (fun _ _ => scalarRows_size ..)

@[simp] theorem triRows_size (r : Rows) (off d m slot : Nat) (mir : Bool) :
    (triRows r off d m slot mir).size = r.size := fold_size _ _ _ (fun _ _ => stageRows_size ..)

def r8Rows (r : Rows) (off slot : Nat) (mir : Bool) : Rows :=
  (pascalR8Steps mir).foldl (fun a st => r8StepRows a slot off st) r

@[simp] theorem r8Rows_size (r : Rows) (off slot : Nat) (mir : Bool) :
    (r8Rows r off slot mir).size = r.size := fold_size _ _ _ (fun _ _ => r8StepRows_size ..)

def primaryRows (r : Rows) (off p m slot : Nat) (mir : Bool) : Rows :=
  let d := fieldDegree p
  if d == 8 && m == 2 then r8Rows (scalars r p m off slot mir) off slot mir
  else triRows (scalars r p m off slot mir) off d m slot mir

@[simp] theorem primaryRows_size (r : Rows) (off p m slot : Nat) (mir : Bool) :
    (primaryRows r off p m slot mir).size = r.size := by unfold primaryRows; dsimp only; split <;> simp

theorem frame_primary (r : Rows) (p : Nat) (hp : UsedField p) (mir : Bool) (off m slot dim : Nat)
    (small : slot < 32) (endp : off+fieldDegree p*m ≤ r.size) (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (primary r.size off p m mir) tape (frame r x dim slot ph) = frame (primaryRows r off p m slot mir) x dim slot ph := by
  let d := fieldDegree p
  change off+d*m ≤ r.size at endp
  have scalar := run_parts (List.range m) (fun j => renameProgram (fieldPlace r.size (off+d*j)) (fieldCore p mir))
    (fun a j => scalarRows a p mir slot (off+d*j)) r.size x dim slot ph tape r rfl
    (fun _ _ => scalarRows_size ..) (by
      intro j hj a size tape
      have limit := Nat.mul_le_mul_left d (show j+1 ≤ m from List.mem_range.mp hj)
      rw [Nat.mul_succ] at limit
      rw [←size]
      exact frame_field a p hp mir _ _ _ small (by change off+d*j+d ≤ a.size; rw [size]; omega) x ph tape)
  unfold primary primaryRows; dsimp only
  rw [run_append,run_take,scalar]
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : d * m = 16 := by change fieldDegree p * m = 16; rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    unfold pascalR8 r8Rows
    apply run_parts (pascalR8Steps mir) (r8Step r.size off) (fun a st => r8StepRows a slot off st) r.size _ _ _ _ _ _
      (scalars_size ..) (fun _ _ => r8StepRows_size ..)
    intro st hst a size tape
    rw [←size]
    exact frame_r8Step a off st (List.all_eq_true.mp (Placement.pascalR8Steps_good mir) st hst)
      (by rw [size]; omega) x dim slot ph tape
  · rw [if_neg h82, if_neg h82]
    have shape : oriented mir (triangular r.size off d m) =
        (oriented mir (List.range 4)).flatMap (fun h => oriented mir (stage r.size off d m h)) := by
      cases mir <;> simp [oriented,triangular,List.reverse_flatMap,Function.comp_def]
    change run (oriented mir (triangular r.size off d m)) _ (frame (scalars r p m off slot mir) _ _ _ _) = _
    rw [shape]
    apply run_parts _ _ (fun a h => stageRows a slot off d m h mir) r.size _ _ _ _ _ _
      (scalars_size ..) (fun _ _ => stageRows_size ..)
    intro h _ a size tape
    rw [←size]
    exact frame_stage a off d m h mir (by rw [size]; exact endp) x dim slot ph tape

def componentRows (mir : Bool) (slot : Nat) : Nat → List (Nat × Nat) → Rows → Rows
  | _, [], r => r
  | off, (p,m)::ps, r => componentRows mir slot (off+fieldDegree p*m) ps (primaryRows r off p m slot mir)

@[simp] theorem componentRows_size (mir : Bool) (slot off : Nat) (parts : List (Nat × Nat)) (r : Rows) :
    (componentRows mir slot off parts r).size = r.size := by
  induction parts generalizing off r with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    exact (ih _ _).trans (primaryRows_size ..)

theorem frame_components (r : Rows) (mir : Bool) (off slot dim : Nat) (parts : List (Nat × Nat))
    (small : slot < 32) (endp : off+extent parts ≤ r.size) (fields : ∀ pair ∈ parts, UsedField pair.1)
    (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (components r.size mir off parts) tape (frame r x dim slot ph) =
      frame (componentRows mir slot off parts r) x dim slot ph := by
  induction parts generalizing off r tape with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    change off+(fieldDegree p*m+extent tail) ≤ r.size at endp
    rw [components,run_append,run_take,frame_primary r p (fields (p,m) (by simp)) mir off m slot dim small (by omega)]
    let new := primaryRows r off p m slot mir
    have eq : new.size = r.size := primaryRows_size ..
    rw [←eq]
    exact ih new _ (by omega) (fun a ha => fields a (List.mem_cons_of_mem _ ha)) _

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTComponents ====

-- ==== begin CRTCoordinates ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix

/-- Binary coefficient rows of the primary-component coordinates at every supported width. -/
def encoded : Nat → Rows
  | 31 => #[
      2147483647, 715827882, 1288490188, 143165576,
      1894838512, 547397792, 1086374080, 8421504,
      1840700269, 920350134, 1662567985, 623462994,
      692736660, 831283992, 388914361, 777828722,
      1268199004, 151290433, 302580866, 605161732,
      1092653128, 37822608, 75645216, 2059990417,
      257498802, 514997604, 1029995208, 1299749617,
      452015586, 904031172, 649874808]
  | 39 => #[
      549755813887, 183251937962, 329853488332, 36650387592,
      485078659312, 140133834912, 278111764672, 2155905152,
      87262827601, 174525655202, 296693613844, 43631413800,
      53202175537, 88670292562, 159606526612, 301478994712,
      324658945209, 99562076530, 437207379548, 77460701761,
      154921403522, 309842807044, 9682587720, 19365175440,
      38730350880, 431556720017, 191383543474, 382767086948,
      215778360008, 258997787377, 517995574754, 486235335620,
      404376800632, 316852738113, 387858770114, 225961726340,
      451923452680, 354091091472, 158426369056]
  | 46 => #[
      70368744177663, 46912496118442, 14073748835532, 9382499223688,
      53811392606448, 35874261737632, 827867578560, 551911719040,
      5584820966481, 11169641932962, 18988391286036, 37976782572072,
      54479027750449, 20429635406418, 22699594896020, 27239513875224,
      43218598786281, 45989021785402, 21609299393140, 41556344986809,
      12743945795954, 55962544582236, 39659879301697, 8951014425730,
      17902028851460, 4957484912712, 9914969825424, 19829939650848,
      67501766014353, 8437720751794, 16875441503588, 33750883007176,
      42590195456753, 14811646735842, 29623293471684, 21295097728376,
      8806250292225, 17612500584450, 35225001168900, 8867869525000,
      17735739050000, 44257586033696, 18146427889728, 45081246397568,
      19793748617472, 39587497234944]
  | 54 => #[
      18014398509481983, 12009599006321322, 3602879701896396, 2401919801264264,
      13775716507250928, 9183811004833952, 211934100111552, 141289400074368,
      4861028169225297, 9722056338450594, 5718856669676820, 11437713339353640,
      1743328888014385, 2905548146690642, 5229986664043156, 9878863698748184,
      5531980644644073, 14893794043272506, 11773189577063028, 14326411413052601,
      10638424316623218, 16170404961267292, 2291459692986945, 4582919385973890,
      9165838771947780, 2538232275308616, 5076464550617232, 10152929101234464,
      14141250601547153, 6271255952563890, 12542511905127780, 7070625300773576,
      8486839496776433, 16973678993552866, 15932959477623748, 13250619003129208,
      3707581495462657, 6601518178753794, 10067205270597892, 2120012031713800,
      629200329412368, 1258400658824736, 1650379544688448, 1853790747731328,
      6553099458814977, 13106198917629954, 8197999325777924, 12675241821504520,
      7336085133527056, 9966250515084320, 1918102520686656, 7574536873407616,
      15149073746815232, 12283748984148480]
  | 61 => #[
      2305843009213693951, 768614336404564650, 922337203685477580, 614891469123651720,
      1220740416642543856, 45212608023797920, 54255129628557504, 36170086419038336,
      1464027307437266001, 622211605660838050, 366006826859316500, 732013653718633000,
      1785168781326730801, 669438292997524050, 743820325552804500, 892584390663365400,
      708093522514441449, 1906405637538880826, 1506968265864067700, 1833780660870732985,
      1361718312527772018, 2069811835042213468, 1173227362809315905, 40611716404937858,
      81223432809875716, 1299574924958011464, 293306840702328976, 586613681404657952,
      2211897868758349201, 276487233594793650, 552974467189587300, 1105948934379174600,
      1395595524726889201, 485348040240084450, 970696080480168900, 697797762363444600,
      1733089838405733121, 583062270482177282, 586527957574021380, 1173055915148042760,
      1766040254258646800, 1226237499303599648, 1875147824530814784, 866544919202866560,
      2070129647786332161, 1834416286358970370, 1362989563504246788, 420136117794799624,
      1662862727447449616, 1341450760783867936, 1837758139352051776, 1132828370801651840,
      273498291062501632, 546996582125003264, 1093993164250006528, 2187986328500013056,
      1685444194648706337, 1065045380083718722, 787141276634511780, 1574282553269023560,
      842722097324353168]
  | 69 => #[
      590295810358705651711, 196765270119568550570, 236118324143482260684, 157412216095654840456,
      312509546660491227376, 11574427654092267680, 13889313184910721216, 9259542123273814144,
      93697747675985024081, 187395495351970048162, 318572342098349081876, 46848873837992512040,
      57125401002455385649, 95209001670758976082, 171376203007366156948, 323710605680580518680,
      385783876061201331433, 539167826784329571642, 488039843209953491572, 529871829770806647993,
      469447849182907644274, 264935914885403323996, 10396599399664091713, 20793198799328183426,
      41586397598656366852, 75086551219796217928, 150173102439592435856, 300346204879184871712,
      463380499711497139601, 205496515053613555378, 410993030107227110756, 231690249855748569800,
      278096756630370163441, 556193513260740326882, 522091216162775002052, 434196283494537907576,
      364902440192748714241, 139509070026791776770, 279018140053583553540, 249627424652000342280,
      163175666630426434320, 45612805024093589280, 91225610048187178560, 182451220096374357120,
      485960121773281463041, 274978380366911757570, 138937108510395658500, 277874217020791317000,
      82470545576737935120, 164941091153475870240, 216318547681404352320, 242980060886640731520,
      41269460804419129345, 82538921608838258690, 165077843217676517380, 330155686435353034760,
      36250507865652858896, 33623252889775583264, 29507874249916379200, 19579572444511203456,
      2579341300276195584, 5158682600552391168, 10317365201104782336, 20634730402209564672,
      153871082802752507169, 307742165605505014338, 166807837940020476324, 333615675880040952648,
      76935541401376253584]
  | 76 => #[
      75557863725914323419135, 50371909150609548946090, 60446290980731458735308, 40297527320487639156872,
      4444580219171430789360, 2963053479447620526240, 3555664175337144631488, 2370442783558096420992,
      5996655851263041541201, 11993311702526083082402, 20388629894294341240084, 40777259788588682480168,
      58496410626514314905137, 21936153984942868089426, 24373504427714297877140, 29248205313257157452568,
      49380336135833770423529, 69013481828394185170234, 62469099930874046921332, 67823594210663250943161,
      60089324695412178467186, 33911797105331625471580, 5323058892628014957121, 10646117785256029914242,
      21292235570512059828484, 38444314224535663579208, 1330764723157003739280, 2661529446314007478560,
      72479469363473586648465, 9059933670434198331058, 18119867340868396662116, 36239734681736793324232,
      45730874154250705345265, 15903884582587087271394, 31807769165174174542788, 22865437077125352672632,
      364902440192748714241, 729804880385497428482, 1459609760770994856964, 2610810666086822949128,
      4885542149500071648016, 9490345770763384016672, 18980691541526768033344, 37961383083053536066688,
      485960121773281463041, 865274190725617409282, 1319528729227806961924, 2639057458455613923848,
      4804837028446383148816, 9609674056892766297632, 19105784479159985207104, 38021911923843802441088,
      41269460804419129345, 82538921608838258690, 165077843217676517380, 330155686435353034760,
      626546318224358510608, 1214214873607186886688, 2390691115684738986048, 4741946055314156417152,
      9447312307039566622976, 18894624614079133245952, 37789249228158266491904, 20634730402209564672,
      50105303381990658049, 100210606763981316098, 155229759864493707268, 310459519728987414536,
      620919039457974829072, 1215660846240638947360, 2388422171325685887040, 4727217412865410642048,
      9454434825730821284096, 18908869651461642568192, 37791458188802659374080, 25052651690995329024]
  | 84 => #[
      19342813113834066795298815, 12895208742556044530199210, 15474250491067253436239052, 10316166994044835624159368,
      1137812536107886282076400, 758541690738590854717600, 910250028886309025661120, 606833352590872683774080,
      5219489252939351357461585, 10438978505878702714923170, 6140575591693354538190100, 12281151183386709076380200,
      1871885140048458076964401, 3119808566747430128274002, 5615655420145374230893204, 10607349126941262436131608,
      15992089582303756011861225, 8833725674034455701790010, 17667451348068911403580020, 8681420058964896120724665,
      17362840117929792241449330, 14012116586399481458011740, 2725406153025543658046017, 5450812306051087316092034,
      10901624612102174632184068, 340675769128192957255752, 681351538256385914511504, 1362703076512771829023008,
      15184052214546338270475665, 6733709805276808982634162, 13467419610553617965268324, 7592026107273169135237832,
      9112674521263969515641585, 18225349042527939031283170, 17107884971221811267267524, 14227743817549018155470200,
      17076118471517441511854081, 14809423829200816228409346, 10276034544567565661519876, 1209255975301064527740936,
      14658852109145603101822992, 7708116314916868175638560, 3478052422507743616266304, 14360736053979035606052992,
      11947589781001502666846464, 4552366448168938538394112, 9104732896337877076788224, 18209465792675754153576448,
      8009183660250300273086465, 16018367320500600546172930, 14658380792587243237019652, 9973948471340419678740488,
      605083828846772562182160, 9219275035407788096081952, 11940530890865788786110528, 6502703497841497224687744,
      13005406995682994449375488, 6668000877531922103452160, 16509405750438125164745728, 13675998387042183534192640,
      11635962792609356078436353, 3929112471384645361573890, 18285186686932133102981124, 9520607247724580383748104,
      7707501677110297576026128, 15415003354220595152052256, 153491729161366342209600, 306983458322732684419200,
      11040929155183665494135040, 14374906532012808384934400, 17416100533527889116083200, 15489387953221711436867584,
      17982840479888246821580801, 3777981161222922390573058, 7555962322445844781146116, 2871506636566055543713800,
      5743013273132111087427600, 8917027207247462836973600, 153508811465302209990720, 17685276975443195432226944,
      16027740837052324069155072, 5307950923611381997646336, 10615901847222763995292672, 18662826796861156808439808]
  | 91 => #[
      2475880078570760549798248447, 825293359523586849932749482, 1485528047142456329878949068, 165058671904717369986549896,
      291280009243618888211558640, 194186672829079258807705760, 233024007394895110569246912, 155349338263263407046164608,
      1571987351473498761776665681, 668094624376236973755082914, 392996837868374690444166420, 785993675736749380888332840,
      1916810383409621070811547185, 718803893778607901554330194, 798670993087342112838144660, 958405191704810535405773592,
      2046987466534880769518236905, 1130716886276410329829121338, 2261433772552820659658242676, 1111221767547506703452757177,
      2222443535095013406905514354, 1793550923059133626625502812, 1395407950349078352919560769, 314935822127396156040873090,
      629871644254792312081746180, 174425993793634794114945096, 348851987587269588229890192, 697703975174539176459780384,
      2375007252102302487296931217, 296875906512787810912116402, 593751813025575621824232804, 1187503626051151243648465608,
      1498509284286487112753650417, 521138490002213675709052386, 1042276980004427351418104772, 749254642143243556376825208,
      47828492640943959473027329, 95656985281887918946054658, 191313970563775837892109316, 342204175625332057588216072,
      640357780619273391048825616, 1243918600865498269833252640, 11957123160235989868256832, 23914246320471979736513664,
      63695765081067547923794689, 113413218726788125069532418, 172953269597347114113364228, 345906539194694228226728456,
      629779598992524332081647376, 1259559197985048664163294752, 28353304681697031267383104, 31847882540533773961897344,
      1758458249743489129813615617, 1041036420916217709828982786, 2082072841832435419657965572, 263622003095179303251772424,
      527244006190358606503544848, 2097262003890803567118890016, 1718643929210846584439531584, 2076717340146006553575388288,
      1677554601721252557352528128, 879229124871744564906807808, 2048071495424094455018229761, 1620262912277428360238211074,
      764645745984096170678173700, 1529291491968192341356347400, 2316453612655399551742382096, 123764994997921268947431456,
      1957102176919748489941446720, 691359195038171373441511552, 901716993017368575250592000, 1803433986034737150501184000,
      1130987893498713751204119552, 2261975786997427502408239104, 1690833924563814111464083457, 905787770556867673129918466,
      208086511930927911190007812, 416173023861855822380015624, 832346047723711644760031248, 28562088149241854891380768,
      1656079645566761466386509888, 2405011529613265779841740928, 2334142980655771009885233408, 2192405882740781469972218368,
      1041678500783643665315582976, 2083357001567287330631165952, 1143583769053865414048075041, 2287167538107730828096150082,
      1690373020238458520379914660, 904865961906156490961580872, 1809731923812312981923161744]
  | 99 => #[
      633825300114114700748351602687, 211275100038038233582783867562, 380295180068468820449010961612, 42255020007607646716556773512,
      74567682366366435382159012080, 49711788244244290254772674720, 59654145893093148305727209664, 39769430595395432203818139776,
      100607190494303920753706603601, 201214380988607841507413207202, 342064447680633330562602452244, 50303595247151960376853301800,
      61337932269107874265969509937, 102229887115179790443282516562, 184013796807323622797908529812, 347581616191611287507160556312,
      578927045773522088872510125289, 144731761443380522218127531322, 289463522886761044436255062644, 459149036303138208416128720057,
      284472772492161716083905837426, 229574518151569104208064360028, 80623570464613415946463511105, 161247140929226831892927022210,
      322494281858453663785854044420, 89306108822341014586851889224, 178612217644682029173703778448, 357224435289364058347407556896,
      497551022966254412446946620817, 220650202899310476742956228274, 441300405798620953485912456548, 248775511483127206223473310408,
      298604118712777753088543464177, 597208237425555506177086928354, 560591174736996311605822254020, 466214709413446226918447533432,
      115648941863998474420533044225, 231297883727996948841066088450, 462595767455993897682132176900, 225568709153034389334892381192,
      451137418306068778669784762384, 165505347189560999853803287584, 331010694379121999707606575168, 93684280247264146896110580864,
      187368560494528293792221161728, 374737120989056587584442323456, 370954203202467416374957248513, 108083106290820132001562894338,
      216166212581640264003125788676, 432332425163280528006251577352, 497492469326807509511392071696, 10027285309280963468140425248,
      390670274512529154808266453056, 431494492866350507038336741504, 498553612785740239084698530048, 363281925457365777421045457408,
      92738550800616854093739312128, 185477101601233708187478624256, 142815998403097165449964244993, 285631996806194330899928489986,
      552329344033210530516199411716, 470833387952306360284047220744, 307841475790498019819742838800, 477873417252306027965953331232,
      464645654338298984278658969664, 195523657658132588664105119872, 391047315316265177328210239744, 148269330518415653908068876800,
      194160324629302966549578961920, 388320649258605933099157923840, 427313720460500978931024580609, 220802140806887257113697558530,
      76248311668306989373375614980, 359012132000008004301129773064, 353033389642262663378574716944, 72241479170410626008797831200,
      373355132214954318649199956032, 112884964315793936550048309376, 613158873824581267009671303424, 167987363987067048858759852544,
      106828430115125244732756145152, 213656860230250489465512290304, 365539122252602248477583306753, 447867272818875205500739358722,
      261909245523635710253127114756, 158942766863011092912514084872, 317885533726022185825028169744, 364988457672142253823330332704,
      449275673703835334756615589952, 617266194552534348700212744320, 600707088990953996652073885952, 293667896645152413468224270848,
      587335793290304826936448541696, 182769561126301124238791653376, 330435634218965018537215118625, 27045968323815336326078634562,
      358217104334427977691327691172, 82608908554741254634303779656, 165217817109482509268607559312]
  | 106 => #[
      81129638414606681695789005144063, 54086425609737787797192670096042, 16225927682921336339157801028812, 10817285121947557559438534019208,
      19089326685789807457832707092720, 12726217790526538305221804728480, 15271461348631845966266165674176, 10180974232421230644177443782784,
      60926148692681282362985517481728, 40617432461787521575323678321152, 63135905381016872915010898944, 42090603587344581943340599296,
      74277535742372791664718704640, 49518357161581861109812469760, 59422028593898233331774963712, 39614685729265488887849975808,
      6438860191635450928237222630481, 12877720383270901856474445260962, 21892124651560533156006556943636, 43784249303121066312013113887272,
      62810042643566463248352778176049, 23553765991337423718132291816018, 26170851101486026353480324240020, 31405021321783231624176389088024,
      74102661859010827375681296037097, 18525665464752706843920324009274, 37051330929505413687840648018548, 58771076646801690677264476167353,
      36412514878996699658739947190642, 29385538323400845338632238083676, 41279268077882068964589317685825, 1428897741157456233389630227586,
      2857795482314912466779260455172, 45724727717038599468468167282760, 10319817019470517241147329421456, 20639634038941034482294658842912,
      77824237636888247903745842148753, 9728029704611030987968230268594, 19456059409222061975936460537188, 38912118818444123951872921074376,
      49103152227499609710711616871153, 17076666040392537725634228598242, 34153332080785075451268457196484, 24551576113749804855355808435576,
      6268976187433806656048638097665, 12537952374867613312097276195330, 25075904749735226624194552390660, 44853385707563523452202657100040,
      2803336606722720215762666068752, 783622023429225832006079762208, 1567244046858451664012159524416, 3134488093716903328024319048832,
      8348731320705685641467617561345, 14865297404957573129113753214210, 22669330952663480941066876154116, 45338661905326961882133752308232,
      1416833184541467558816679759632, 2833666369082935117633359519264, 3716324351239393282278438303552, 4174365660352842820733808780672,
      749474241978113175168884646913, 1498948483956226350337769293826, 2997896967912452700675538587652, 5296171110065951995321705202696,
      10592342220131903990643410405392, 20447914950841231423801054573600, 40895829901682462847602109147200, 93684280247264146896110580864,
      187368560494528293792221161728, 374737120989056587584442323456, 78965291417352690309170555981825, 76800944420098698922552106819586,
      72472250425590716149315208495108, 63814862436574750602841411846152, 34090233375374886649174027014160, 14588009187933919080680227287072,
      52364344883869934616173097873472, 56841946203022558873641629380736, 50570752321800801598204475142400, 20011866228994921500619945140736,
      40023732457989843001239890281472, 80047464915979686002479780562944, 79370978512667434758993914580993, 77612318610728187822198824017922,
      6256757045060242837251363835908, 12513514090120485674502727671816, 25027028180240971349005455343632, 32802963723072155766131885068320,
      16944103457305281203735800639552, 45830945265874391042545420513408, 10532252117142100389301835882752, 21064504234284200778603671765504,
      40125154231818529113695729931264, 80250308463637058227391459862528, 46062735328676759432812339974145, 10995832242746837169835674804226,
      67261730123764465268698645499908, 18106120535195219625254974648328, 71975292302537223847942305820688, 62820946190467766000095606497312,
      9246909333812560129126122393664, 18493818667625120258252244787328, 72869243086833657152321754009856, 28690125869122228582534581973504,
      11515683832169189858203084993536, 23031367664338379716406169987072]
  | 113 => #[
      10384593717069655257060992658440191, 3461531239023218419020330886146730, 4153837486827862102824397063376076, 2769224991218574735216264708917384,
      4886867631562190709205173015736560, 3257911754374793806136782010491040, 3909494105249752567364138412589248, 2606329403499835044909425608392832,
      5172093368812902229197692841557760, 3448062245875268152798461894371840, 4137674695050321783358154273246208, 2758449796700214522238769515497472,
      4867852582412143274539005027348480, 3245235054941428849692670018232320, 3894282065929714619631204021878784, 2596188043953143079754136014585856,
      5604383910799496487937678577570897, 824174104529337718814364496701602, 6593392836234701750514915973612820, 2802191955399748243968839288785448,
      2009921364594126823947288901633585, 3349868940990211373245481502722642, 6029764093782380471841866704900756, 1004960682297063411973644450816792,
      9485140717953385904087205892748521, 2371285179488346476021801473187130, 4742570358976692952043602946374260, 7522697810790616406689852949421241,
      4660801904511577556318713240402290, 3761348905395308203344926474710620, 365797821736308795747745338262081, 731595643472617591495490676524162,
      1463191286945235182990981353048324, 2641873156984452413733716331892808, 5283746313968904827467432663785616, 182898910868154397873872669131040,
      5919158203488569330000554212521361, 7230265848604605701913189688090290, 4075937980139556146765386717740388, 8151875960279112293530773435480776,
      9784659761980301413205392234158833, 9184725806890947569349791809877474, 7984857896712239881638590961314756, 4892329880990150706602696117079416,
      1304343190821140713788672720402689, 2608686381642281427577345440805378, 5217372763284562855154690881610756, 1342927600341270430584826739405064,
      3978155618922450123309423918127888, 9249562401288590939151952666185504, 8114531085507526621242912673930816, 5844468453945397985424832689421440,
      3902571375221826407039339864476417, 6505236370573492108792234164739330, 1320743545586370388073690958459140, 2641487091172740776147381916918280,
      9169065974035096499182974261038864, 7953538231000537741304955863637536, 9414754380445614469993803035014976, 7143582546145740832050166261458304,
      6001428895683640454101767931498497, 1618264074297625651142543204556802, 3236528148595251302285086409113604, 6473056297190502604570172818227208,
      7011239137031549512487028469403664, 8208681489063208770355369746837536, 295753260127689979703540113305664, 6384953742542343731145184030617728,
      6865460379148762064044480907243776, 3346327041227868871027969156047360, 6692654082455737742055938312094720, 3000714447841820227050883965749248,
      8273464458387942286033683434131457, 6162335199706229315006374209822722, 9255035536310221956157197950259204, 8125477355550788655253403242078216,
      5866360994031922053445813825716240, 9524970658232053914173445486923808, 1233888679676405506640570877800512, 10024776470262496239624593053233280,
      9664959223455337222188193448026368, 8945324729841019187315394237612544, 4664514543864399385773669023142912, 9329029087728798771547338046285824,
      3291248271912944027264372545736705, 6582496543825888054528745091473410, 878558114269831282226588696940548, 4967014063826202803068384288436232,
      6724605642300285122902640727633936, 3064617567530914988744288796827680, 8041081112379874048012237631656000, 5697568507690092838963482604871808,
      2993536226012674198200725939196160, 7898265052085970353074068080947712, 8611257355780477449611837630264320, 6837920994491299642162682602088448,
      6088891372018438417637143078727681, 7552476318132495534622110085386242, 4720358919195335812183227512332292, 5136679174891648545957553902268424,
      10273358349783297091915107804536848, 4406084649550883427155615320616992, 3210774420751694794625157483204672, 338446151155375669847571616977024,
      676892302310751339695143233954048, 7434430612935096477490884172198400, 4484267508800537697920775685956608, 3044445686009219208818571539363840,
      5063326932945767194596369817390369, 10126653865891534389192739634780738, 5825212725153048527855042556393892, 1265831733236441798649092454347592,
      2531663466472883597298184908695184]
  | 120 => #[
      1329227995784915872903807060280344575, 886151997189943915269204706853563050, 1063382396627932698323045648224275660, 708921597751955132215363765482850440,
      1251038113679920821556524292028559600, 834025409119947214371016194685706400, 1000830490943936657245219433622847680, 667220327295957771496812955748565120,
      358680570291167775228011428964537425, 717361140582335550456022857929074850, 421977141519020912032954622311220500, 843954283038041824065909244622441000,
      728931481559469994818216774992447025, 771809804004144700395758938227296850, 857566448893494111550843264696996500, 1029079738672192933861011917636395800,
      1214098011898033395723162354271810793, 303524502974508348930790588567952698, 607049005949016697861581177135905396, 962905319781198900056301177525918905,
      596582643777481927208795294771493234, 481452659890599450028150588762959452, 187288484728990103422845613190185537, 374576969457980206845691226380371074,
      749153938915960413691382452760742148, 23411060591123762927855701648773192, 46822121182247525855711403297546384, 93644242364495051711422806595092768,
      1220916623100638234406136695250023825, 318768077360694263413742969441296050, 637536154721388526827485938882592100, 1275072309442777053654971877765184200,
      279784096405791338096791201353603825, 559568192811582676193582402707207650, 1119136385623165352387164805414415300, 804506046095353605500299130816974200,
      821687246839323906021607092737177857, 314146497893731939139407125194011138, 628292995787463878278814250388022276, 562110988322102654311878430295175432,
      367438935716360384120444166963534608, 102710905854915488252700886592147232, 205421811709830976505401773184294464, 410843623419661953010803546368588928,
      1094284911667535628398443569000696577, 619196265677683152275390801012710658, 312858555057676028099903470711664900, 625717110115352056199806941423329800,
      185707159164219235869219849454522128, 371414318328438471738439698909044256, 487106065365649756294799465323263808, 547142455833767814199221784500348288,
      483533394425297801020077639543268353, 967066788850595602040155279086536706, 604905581916275331176503497892728836, 935267767814695892541050973005972488,
      541307539844475912178294885731600400, 735379490504945804122055343680369696, 141530985224975735340303627080394816, 558902172722505677466437352548037760,
      1117804345445011354932874705096075520, 906380695105106836961942349911806464, 1224734263922309723245726489710001153, 312188191356465109838308349537911810,
      624376382712930219676616699075823620, 1248752765425860439353233398151647240, 1168277535066805005802659736022949904, 217447755321282639823666989091863584,
      434895510642565279647333978183727168, 869791021285130559294667956367454336, 410354046785345245685528852454564096, 612367131961154861622863244855000576,
      608307864485723645363639342121029633, 1216615728971447290727278684242059266, 1104003462157978708550750308203773956, 878778928531041544197693556127203336,
      204318519761354999396645888979767312, 309361899284083211225124156841603104, 10680346977197345236764532771745856, 587922201898443038126560772903268480,
      785709989159372906343618930290258176, 242191982533829939783430800300171776, 484383965067659879566861600600343552, 968767930135319759133723201200687104,
      932502305277587260164462030035308545, 535776614770258647425116999790272514, 653099845994628847893938742773551108, 1306199691989257695787877485547102216,
      1283171388193599518671947910813859856, 487216281643436195738979107775172640, 42772263547955026534884541511561280, 851176867552904572061564998386888832,
      373125739320893271219322936493433088, 746251478641786542438645872986866176, 897739574211854751493019037648999424, 466251152638793630082231015017654272,
      200598528896236393911423233056100353, 401197057792472787822846466112200706, 977030367518817425445959898590318596, 493042918766099999884935039235125256,
      806338321856663739916599075427528720, 283448647928411606929391090574712864, 392271048643957118559268965993943104, 784542097287914237118537931987886208,
      44531911094291295226444696572956928, 288282295412966662293720869858832896, 382456631170288066703807573334111232, 764913262340576133407615146668222464,
      961471513342426722067248467655225345, 1056396441742167676497782368587845634, 783564887699419480091757676895346692, 773596614238046137568471010626842632,
      217965232691176402233134960973340688, 1219403549546700548503291756358119456, 563978835142513078675918761038975040, 498798944570498828008775219222106240,
      997597889140997656017550438444212480, 298203054690885443675198678608523776, 596406109381770887350397357217047552, 480735756671213361033624233827612672]
  | 128 => #[
      340282366920938463463374607431768211455, 226854911280625642308916404954512140970, 272225893536750770770699685945414569164, 181483929024500513847133123963609712776,
      320265757102059730318470218759311257840, 213510504734706486878980145839540838560, 256212605681647784254776175007449006272, 170808403787765189503184116671632670848,
      338958311018522360492699998064329424640, 225972207345681573661799998709552949760, 271166648814817888394159998451463539712, 180777765876545258929439998967642359808,
      319019586840962221640188233472310046720, 212679724560641481093458822314873364480, 255215669472769777312150586777848037376, 170143779648513184874767057851898691584,
      108026148228869353480436383311672448081, 216052296457738706960872766623344896162, 27006537057217338370109095827918112020, 54013074114434676740218191655836224040,
      65861103275020347767104762728729331249, 109768505458367246278507937881215552082, 197583309825061043301314288186187993748, 32930551637510173883552381364364665624,
      155404545522948274652564781346791781609, 208992319841206300394828499052582051130, 77702272761474137326282390673395890804, 123251880931993459207206550723317619897,
      246503761863986918414413101446635239794, 61625940465996729603603275361658809948, 95891704181242932952496953953374995009, 191783408362485865904993907906749990018,
      43284449804033268346613208381731768580, 11986463022655366619062119244171874376, 23972926045310733238124238488343748752, 47945852090621466476248476976687497504,
      193958976011913439805458160435899987345, 236921351327075719640291399699342630578, 133560335733212975817208191966917049700, 267120671466425951634416383933834099400,
      320623731080570516707914292728916646641, 300965095240202569952453978026065081826, 261647823559466676441533348620361952196, 160311865540285258353957146364458323320,
      170962870707308555637708910808621283585, 1643374493678647812043214185474355714, 3286748987357295624086428370948711428, 176020206431930997877614410387300659464,
      181142446362464919099038204365090396944, 191511542298882801186400917566961766176, 42740717676827138909427227702155320896, 85481435353654277818854455404310641792,
      171235468372136767360085747284884802305, 172089607721931830756866501577177160962, 173112498007096739505594821307156459780, 5942629093255015547815035182544708104,
      180960714585912777950786980047581384464, 21639062250887092438199352663394557472, 213163585390952189420903929110178395968, 255758917646537615411730177358326506880,
      312852112403880527933414736805424243713, 285421857886822592403454866179080275970, 230561348852706721343535124926392340484, 236208623021744805396514900642626962440,
      132134879122551147329655193853485713424, 60550639300826160084793373056295875616, 121101278601652320169586746112591751232, 124177105780719681857520493958620083328,
      248354211561439363715040987917240166656, 156426056201940263966707368402712121856, 123513709876134570030395976035501702145, 304705399226102200004810125153736819714,
      269128431531265936546245642875705427972, 197974496141593409629116678319642644488, 55666625362248355794858749207517077520, 20155867692095020733380772893297032224,
      40311735384190041466761545786594064448, 80623470768380082933523091573188128896, 161246941536760165867046183146376257792, 231898038398536516746885291733634956800,
      161444895354460544266724293636042723329, 322889790708921088533448587272085446658, 305497214496903713603522567112402681860, 270712062072868963743670526793037152264,
      316560581516571332750502726235701776400, 219631981203795202240353289103098458144, 67801308132007906863330924607069319232, 41793990071230835098144579641593950336,
      95160897689888399882513920210194723072, 190321795379776799765027840420389446144, 40361223838615136066681073409010680832, 80722447677230272133362146818021361664,
      147147581841618333279583238660873211905, 294295163683236666559166477321746423810, 282449434952396793903501035522206601220, 224616502983855124343627463612644990984,
      108950639046771785223880319793521770512, 272978955417551190141019426465245810720, 324374403235067428015063807249915637824, 178967728302731631541171711075953062016,
      17653089684524799618968814720137912576, 35306179369049599237937629440275825152, 121857487190639199185739461523160355840, 243714974381278398371478923046320711680,
      208889393867128028439809131697070198785, 77496420813317593416243655962372186114, 310687153385404215812033004943910604804, 104172826589989538086381885741102002184,
      2135566317641579612820406135707873296, 4271132635283159225640812271415746592, 206422610395305917418649363309447352384, 72562853869673371373924119187126493312,
      319059250899474100792140139163855655168, 166441781768527450775269603404901904896, 137292940197016622975795934782209602560, 274585880394033245951591869564419205120,
      160468831007532331470524095701296574465, 183160631864275642264319349626995052546, 26038896807612821065264091822221893636, 127050256213805054063430141737259577352,
      254100512427610108126860283474519154704, 9194771524256195785926134118040186912, 156083654341977670208421344813839290432, 194566086329168216271964606020152414336,
      48849805737397969080554604608536617216, 65430374848151763215961744632345408000, 130860749696303526431923489264690816000, 250375598964235397466949351566532392960]
  | _ => #[]

def clipShift (dim k a : Nat) : Nat := (a >>> k) &&& (2^dim-1)

theorem clip_zero (dim k : Nat) : clipShift dim k 0 = 0 := by simp [clipShift]

theorem clip_xor (dim k a b : Nat) : clipShift dim k (a ^^^ b) = clipShift dim k a ^^^ clipShift dim k b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [clipShift,Nat.testBit_and,Nat.testBit_shiftRight,Nat.testBit_xor]
  cases (2^dim-1).testBit i <;> simp

def plain (n dim k : Nat) : Rows := (units n).map (clipShift dim k)
def coded (n dim k : Nat) : Rows := (encoded n).map (clipShift dim k)

@[simp] theorem plain_size (n dim k : Nat) : (plain n dim k).size = n := by simp [plain,units]

theorem encode_of_receipt (n dim k : Nat) (h : applyOps (basisNetwork n) (units n) = encoded n) :
    applyOps (basisNetwork n) (plain n dim k) = coded n dim k := by
  rw [plain,apply_map _ _ (clip_zero dim k) (clip_xor dim k),h,coded]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTCoordinates ====

-- ==== begin CRTWindowRun ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Field

def entryShift (mir : Bool) (slot : Nat) := if mir then slot-1 else 0
def exitShift (mir : Bool) (slot : Nat) := if mir then 0 else slot-1

def CoordinatesOK (n : Nat) : Prop := applyOps (basisNetwork n) (units n) = encoded n

def ActionOK (n slot : Nat) (mir : Bool) : Prop :=
  componentRows mir slot 0 (schedule n) (coded n (n-(slot-1)) (entryShift mir slot)) =
    coded n (n-(slot-1)) (exitShift mir slot)

theorem logical_action (n : Nat) (hn : UsedWidth n) (mir : Bool) (slot : Nat) (small : slot < 32)
    (basisOK : CoordinatesOK n) (action : ActionOK n slot mir)
    (x : Nat → Bool) (ph : Bool) (tape : List Bool) :
    run (logical n mir) tape (frame (plain n (n-(slot-1)) (entryShift mir slot)) x (n-(slot-1)) slot ph) =
      frame (plain n (n-(slot-1)) (exitShift mir slot)) x (n-(slot-1)) slot ph := by
  let dim := n - (slot - 1)
  let ops := basisNetwork n
  have bounds : ∀ o ∈ ops, o.1 < n ∧ o.2 < n := fun o ho => ⟨(basis_pairs n hn o ho).1,(basis_pairs n hn o ho).2.1⟩
  have apart : ∀ o ∈ ops, o.1 ≠ o.2 := fun o ho => (basis_pairs n hn o ho).2.2
  have size (k : Nat) : (coded n dim k).size = n := by rw [←encode_of_receipt n dim k basisOK,applyOps_size,plain_size]
  have fwd (k : Nat) (m : List Bool) : run (cnotProgram ops) m (frame (plain n dim k) x dim slot ph) =
      frame (coded n dim k) x dim slot ph := by
    have step := run_ops ops (plain n dim k) x dim (flags n slot) ph m (by simpa only [plain_size] using bounds)
    rw [show applyOps ops (plain n dim k) = coded n dim k from encode_of_receipt n dim k basisOK] at step
    simpa only [frame,plain_size,size] using step
  have inv (k : Nat) (m : List Bool) : run (cnotProgram ops).reverse m (frame (coded n dim k) x dim slot ph) =
      frame (plain n dim k) x dim slot ph := by
    have hr := reverse_cnots ops apart (frame (plain n dim k) x dim slot ph) [] m
    have rev : cnotProgram ops.reverse = (cnotProgram ops).reverse := List.map_reverse
    rw [rev,fwd] at hr
    exact hr
  have c := frame_components (coded n dim (entryShift mir slot)) mir 0 slot dim (schedule n) small
    (by rw [Placement.schedule_extent n hn,size]; omega) (schedule_fields n hn) x ph
  change run (cnotProgram ops ++ components n mir 0 (schedule n) ++ (cnotProgram ops).reverse) _ _ = _
  rw [run_append,run_take,run_append,run_take,fwd]
  simp only [size] at c
  rw [c,show componentRows mir slot 0 (schedule n) (coded n dim (entryShift mir slot)) = _ from action,inv]

theorem rowValue_congr (x : Nat → Bool) (d a b : Nat) (eq : ∀ i < d, a.testBit i = b.testBit i) :
    rowValue x a d = rowValue x b d := by
  induction d with
  | zero => rfl
  | succ w ih => rw [rowValue,rowValue,eq w (by omega),ih (fun i hi => eq i (by omega))]

theorem plain_bits (n dim k v q : Nat) (small : v < 2^dim) (hq : q < n) :
    rowValue v.testBit (Matrix.read (plain n dim k) q) dim = (v <<< k).testBit q := by
  have rd : Matrix.read (plain n dim k) q = clipShift dim k (2^q) := by
    simp [Matrix.read,plain,units,hq]
  rw [rd]
  by_cases fits : k ≤ q
  · have equal := rowValue_congr v.testBit dim (clipShift dim k (2^q)) (2^(q-k)) (by
      intro i hi
      simp only [clipShift,Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftRight,
        Nat.testBit_two_pow,hi,decide_true,Bool.and_true]
      exact decide_eq_decide.mpr (by omega))
    rw [equal,value_unit,Nat.testBit_shiftLeft]
    by_cases bound : q-k < dim
    · simp [fits,bound]
    · have high := Nat.testBit_lt_two_pow (lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : dim ≤ q-k)))
      simp [fits,bound,high]
  · have equal := rowValue_congr v.testBit dim (clipShift dim k (2^q)) 0 (by
      intro i _
      simp [clipShift,Nat.testBit_shiftRight,show q ≠ k+i by omega])
    rw [equal,rowValue_zero,Nat.testBit_shiftLeft]
    simp [fits]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTWindowRun ====

-- ==== begin CRTBarrelRun ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Placement Matrix Partial

/-- Slot zero has no tag; slot k+1 selects k. The mirror enters on the forward image. -/
theorem barrel_result_of_matrix (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool)
    (slot : Fin 17) (v : Nat) (s : State) (tape : List Bool)
    (basisOK : CoordinatesOK (barrelWidth (start j)))
    (action : ActionOK (barrelWidth (start j)) slot.val mir)
    (small : v < 2^(barrelWidth (start j) - (slot.val - 1)))
    (input : HighBankBarrel.holds (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< entryShift mir slot.val) s)
    (tag : ∀ k : Fin 16, s.basis (tagsP.getD k.val 1560) = decide (slot.val = k.val+1))
    (scratch : ∀ k < 10, s.basis (Shadow7.poolW (start j) (17+k)) = false) :
    HighBankBarrel.Result (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< exitShift mir slot.val) s (run (barrel (start j) mir) tape s) := by
  let n := barrelWidth (start j)
  let dim := n - (slot.val - 1)
  let P := logical n mir
  let f := place (start j)
  let S := Finset.range (n+26)
  let before := entryShift mir slot.val
  let after := exitShift mir slot.val
  have sv : v < 2^dim := small
  have scope : wires P ⊆ S := fun _ hw => Finset.mem_range.mpr (support (logical_fits _ (usedWidth j lo hi) _) _ hw)
  have inj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b :=
    fun a ha b hb => place_inj j lo hi a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb)
  have bank (k i : Nat) (ik : i < n) :
      (frame (plain n dim k) v.testBit dim slot.val s.phase).basis i = (v <<< k).testBit i := by
    simpa only [frame,Matrix.basis,plain_size,if_pos ik] using plain_bits n dim k v i sv ik
  have placed (q : Nat) (hq : q < n) : f q = Shadow7.bankW (start j) q := by simp [f,place,n] at hq ⊢; simp [hq]
  have other (k q : Nat) (qn : n ≤ q) (high : q < n+26) :
      (frame (plain n dim k) v.testBit dim slot.val s.phase).basis q = s.basis (f q) := by
    have outside : ¬q<n := Nat.not_lt.mpr qn
    simp only [frame,Matrix.basis,plain_size,if_neg outside]
    change flags n slot.val q = s.basis (if q<n then Shadow7.bankW (start j) q else if q<n+16 then
      tagsP.getD (q-n) 1560 else Shadow7.poolW (start j) (17+(q-n-16)%10))
    rw [if_neg outside]
    by_cases mid : q < n+16
    · have k16 : q-n < 16 := by omega
      simpa [flags,qn,mid] using (tag ⟨q-n,k16⟩).symm
    · have pos : q-n-16 < 10 := by omega
      have val := scratch (q-n-16) pos
      simpa [flags,mid,Nat.mod_eq_of_lt pos] using val.symm
  have result := run_rename_pool f S inj P scope tape
    (frame (plain n dim before) v.testBit dim slot.val s.phase) s rfl (by
       intro q hq
       by_cases low : q<n
       · rw [bank before q low,placed q low]; exact (input q low).symm
       · exact other before q (Nat.le_of_not_lt low) (Finset.mem_range.mp hq))
  have shift := logical_action n (usedWidth j lo hi) mir slot.val
    (by have := slot.isLt; omega) basisOK action v.testBit s.phase tape
  change run P tape (frame (plain n dim before) _ _ _ _) = frame (plain n dim after) _ _ _ _ at shift
  rw [shift] at result
  change HighBankBarrel.Result (Shadow7.bankW (start j)) n (v <<< after) s (run (renameProgram f P) tape s)
  refine ⟨?_,result.1,?_⟩
  · intro i bound
    have hi : i ∈ S := Finset.mem_range.mpr (Nat.lt_of_lt_of_le bound (Nat.le_add_right _ _))
    have bit := (result.2 i hi).trans (bank after i bound)
    rwa [placed i bound] at bit
  · intro q free
    by_cases hit : q ∈ S.image f
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hit
      have above : n ≤ a := by
        by_contra! low
        exact free a low (placed a low)
      change (run (renameProgram f P) tape s).basis (f a) = s.basis (f a)
      exact Eq.trans (result.2 a ha) (other after a above (Finset.mem_range.mp ha))
    · exact run_rename_pool_outside f S P scope tape s q hit

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelRun ====

-- ==== begin CRTPackedData ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

def width : Nat := 144

def basisWord : Nat → Nat
  | 31 => 18298309563083215549963224224788087059628745554733878014655152579953072213704620403236280901574154702799138791727450150556696794062467673219841860189517067197965904257784961895889829198321802296541089723888047952429627537443371007865196839230700753074478912915966727733596965229752876555625288283240454798907268112553519507426575951921659469608362306148412382688349551528416553014910273837908978738150896218001962204218922163441579747814223561737341411814390810789958036224369406922138350077351317149008264639784726221972857326994437151330808539306714370540854263309189793813034270619279963587778002331261962117425346691305602907876924421651876309447932624892524713384222918692978609449255761351747961718976185667465277063513882615048661105949532878736923190105367805039332749342998259847060108227451420600247005892589634880412859561065043066822528943087004881325911618596528140558253164381623445146302131399687038845784069810854005223267062893115548532324381591384501915620660170788186157903516671588421530688649287885702809320021111443731146668661723584026609343726830981039872829134476348062012497534496485985257767528499916093502581786925650270368325880673173207836350055141980699469079821072660551714578144700585085475714492167845649009759892754745442599815987376540517651582249999845087023096316957818879
  | 39 => 272874995851216425896582628280340215716613537815339492495741036885828045998191841992951714764875132947930597476440018693425927274443993642410785235255041159595967634081264651108128959600335575003897715798112120567141181752505339261449923154678178601478113836080274899082860972649770557709364683726256280901791917622686319159451176953857475278107878706194485623583639301601763566711344690229250033668116388667612859485094896144062318177511990056760115639053475542316569301745025838158327346446824486787240653446133049435011806305009034450039543288952280570064014968800534722428590896471552474154056547380458961287827848977792032165326609681147712288105267362938902032340715510538303025816527034298108053335479436681000139578634143828034481132537116673943423366936563344348235254226553777218227835093265929513324694484772492215635309838541924972415367493461119894887223129805224814029473818864065945268915914680807578265617547420347775013772358598458231035815325433900372339337629346405984150397781656609907961634128413185191988156151682487865171732575570796496178471645855802522831125944064024610560315523567395273096117691706723739185880629918826224105013719536723860089762916911288968319094520439754057367887337642527187404201108216442893331981479596260340500551273170419395615523878752132205697441166191526241619707457659315337747887824958345674972372433875324120739960543774291270890700289057640565992915695269607192141707934016354478410711839428090262128032300545433086137303793844005279060102820047868230591392077488588589064673421619849209338255786318222939781372981755923921890498368802547878816260695078579527308389662594887991205674522063992610881535
  | 46 => 187038042515221429053042567994885150591713294654494187608319226451455151973786040490372749454501799132717580337655078948008897637213055935624271979905951101722741793436432278441285582186929839606101701557845782429752702939842441712435107976861128285718819932926663421657059367528864170563417071994566083399092882895855077502914844318429207282049380719459970357915116478166485629758535920263743419311341516881528967306508597225931785235034819426627339382985607709259010214716189278856165702876244270903886967367025443084010855460029761219533422278095953137085566463628770190374708017336918475830125652401061618477713631992501011351835208690251827749516168300537565430945571968932275701852615407288812153171827671482944902458176033200662762854099614802947511410166064838583856252328221553656101513692525828455239440764985871803980371614291225165946811712825728363610149169530136346267708225647055190393489746666393826697701820620812206200541372654586332371674463697265571516265375630180428612429880879644165070684544679882228639619992940348558024088527132625120089567590900098818207435796808115807742997376965776772319183678291869086426514522154723562749734391586529491457087295521207928535065320333541376127440711035993981271899682108680273602614271697989789148628693955879354589116619519028188007814990078685415935906742075832394113021871748968066554252650239081773106225239223978977975894204362762972773067624603256361345553146757034560745203098949565844783497220063431989824945095139913593269885582171625237578138572344942647527884433631577969255104311119110577888139848085352746508546520240071094375671301611845950651634855355728351134525398837595217332671357619255269428353821674373606381293620392262096229208322914427672835298919747421923168069178151383004928177317953975662083468109402655318503439671918358862245284154570622476678807605101939714456988067014904180273799676244851355894784955831683544428809118164044036981491945613347662768912684388048070246399
  | 54 => 3550241044996737118679120696768099697497120831051386119832679213472614827891648698753117670697451930075070512483872645739319801955306587140552941608883249910344418124104183809954764809639499054711765793546853812944557299767699813106571933744418934529954337549816128184933315318010920627576416216407143380461792156081496806644469616740151013793428875939905873879736682022609466995101252474960704748257931239705836186972194499998337934226002265571718123187094878594681128790297839138760770326784767467419608341502391911749213948562463565371312802181175900235316559233491697669442873683340909495952467358579766297599534989909968070719384075088422472542866701184265402412478342703655776208107663834038846305473397032890799222455240234956195193429471305111505993520125108997377913157832752104285256183820991100535228845309307651846844631247216075891951446845342124616335069179343388297052611081612459987200396824342636514238364547009713184935906023412319319183737264842033383794166854295042725054116066290295284220447353531830621794564014727025422898981199993265074377483757499612426214293051220298363070030388289552928570975309969399736718660689694855304954652092499823607246384419324228925947914542134942702070946252494223910409798932440045567818843181048916341733633719164533951045345186160977307194419772029126983689468762171820871260577923833911268745679399950443581832452319307639470981890354590742849141325809430125501961198430378329151525105513653031060803070128153109787891973371406368361121474442673908942805142268576813074436691783919875399922709615190013629186260788825460931755188322334498071841954011189389721629384955510968678545794836837856935448441179744426687559600431790802587422481913491284463001706083619310886315991487975380188082113243736496896897890492557528340365451841559395529567172347978303985981903106432660296294506391922135421297067659876064967646067433469643934952482473069811872344870700550685794991797294137233395932027505847229690563625804089187684419249586954683398205903136965676536579111166628678703649371792613219254895525058224872619532279713027015459748935083316222752963364338322816520717056891865962932904617119726609530054599882637188607552899107921870707178838201081446776755589996081043328620852588360387613277081172309714042208150941094751596278182505511354558317651296255
  | 61 => 668108379343423482470684985033735519858038423387802993694395196523182605017607343160427050932817214659058004623382111397957356763384405913562660808660592567152300627807513942343695534406683233355111940713907382103832825703721784592578594146358257440957552519473067449340807913296129850876428010260891255285789825025492942637736526419945485848797689300362064758388302736256929952524951581147493099149885626991684717113831389387585900914926914493898501525706401387064607903897095129609563449695459141153207741727838351240198224354609311601256414437771197594920454917449826864181892388742202766675505233640737283617099873234555760923957906472845300140261350488266129163490145103289744174741309197908555381670724163043667771623733412677293044601628962851477768266390536357645872443711422878015292430872262643216787313717677587565605654158831614201982993200686254719722029051986373807174450879735253651894556062703770684000090610741607259398620836918714622025932042136748601422975287305522070909148028384725483827993726172002787438198466956238176263834284288047339453720527964440343975768452008381833610022364069106442707381430732898500342707748943109716867447747138061624973753737911966530839672583727162347110973705237140806657524029411665115558878557975827239604183980518461879389128926886515221306309085836361833232726847008170804125928316581337436491036748374011582729276254509052642957747022620746715407318655742183762150292017376691768455140271341917497954049585470731205638513971744370532106802173711321756218520483706945241872474792549411387126727141619046443428270332168582433881405570374860626727728331967771353033513609937510889960675181715847385298552361041277800578476770054625951065552048803713012740992428436655101330712642234086160556431932063855172590507449532607556760810399116806645065823748279859449957829102221642143283200629943476553673255065728748815473049262577515617171479443310651251726111578125914932454389936600006380366004090851756620185562511630225144664844163376349787281054464266146335838860891098578702924001485382161327976754659542788297188074421755773453387682545049508721562726897220218139914884389042834618386938247312149511915710515540892279294392112740280712391521447373269452137112241860124569088698833990675914975767709591032494889920483661412136780916256689381911806926819476686856344669717778776165470035607379953741085268589893271660292591081666875485886741169103210171416119424382699965924738830484810748896320775555000526985348648870191127527404675288476459368076181037798801406227167415914893054251819782959827813952588005902957868613183239185671465057652360828876975025160191
  | 69 => 3731165868711149678468456289255741616333817439121444688268740578049984193681755073282584974145357531824220849673604084306854645592070904593964712352857669279828548361106303323399886260860165856913018480043111700396245846194792354158061060467559629452307129084912052071168713797281167651544891088765315469033243963309973392990114396294090255222548838242464277150679988217007886499151493195093754009059495322100954958567303224090403265373540051177876080166479133596091933842907851086949116411900296500648445618849442955368846065821008591599320617906760273960786187287616642051686923814862813572825775998608583827416363133992871276647985899364783358058167362809739805941331279241665593951299243451296231576019031511253018123650081078805025862932099724712432039177034964884802576114087345167740610768525202050619493182274761481329865276278572317550468091197417945371183590716320901830516160807985119943691338125451623599738478978067173509571026619729880406701842615740141631167326758709088564429737938163604380717428369593184045549845672908760955514008808401407746592867890234243754638098266793909695516964563585817267125796105949321892818249975909569217147805249463055691691602820490635141660875387472607658847523124474402026075713375819927418191835935516097514652183622045199996313059340205960574537173086227371168949809475113848349053927754394855044345492993316423626635273004650595849715218487691037660770395076503381066221184045448990477795219113304195448550798366244138401101416811532851553699233543555628203624399339514985295339329905520629808740585317707372507043148566797045971168462962849673268629894545285248003116807864877666981475273972077314199219794771283731546758969986914396175065354125437945868691299617415601798634462378871541764003154489938049210555185012095408485980316391485211560160171930381634987332590074240531875747775627677178478648785119442882810133692683389992655801393479810067916672749043221596241317111401451193946888405213300092309346955618556979843265913825374784286990161940543928388083651213794185960129957904325116489891750176819299048530944328491101485240617875528156731486203330149230269236697434719981131912668680212324621719688940342682386634559767789745023322932253834567639689441237400563365901411047813065507071575255990418761882809771839037671604640991411781210958589324883680309109215348457216189052680041072822842790092134764438267545028667080846294275633478870450238836000666039251259195819935498879065578255037132506630595977936365943929489169388667970084608649921876116859679797368015120414606243814010721759803016773980329481334437665080386254767020106633770487106153047758930019851435752488518769244284791838048619643971239194644278946943731305148738882427612765160996342506640155350305940126270196410377692220569358196888908384848871066768040453764172376532529452349076075562299559612174222606740602707940505813906691822378599935747714172995622431469883140597688773020404402945655745765047075956817232943268293278433279
  | 76 => 3332781726656621127595875220249626125583930400899889478824525551355436838976276081141974604989416342675333478886580661893730636988397730626076763422598274420912849349027899901298661737714569723436557104076335288200277670087787138604353661592047224435970450491518422368442183417029914989082778649515071207328920125749556588847889136098743657904569710457639462327223743803578114847789132285813145119870002953168902638579221952863063739431486519645351446389403719432828210157016391644150932096860932029742737388385151052908920788670082939867158962057806759430577014445157291247430526459555898589188821422885936178833873145381886567747471297596510377118644349762388685598051458541410730059887153773846570999419099945672709843353672743249790784330614515954843222688288862476498413810378393135255784633174493491683833394924070334777674776818961270619056693379340655735380949064171056969070031429575395243509679818767891933220244383924254378029583326163343847584618541198369724573833115260083953443233285111717002521846298457914494295817690266507188146406055567976369232655384038809259324085112346966749820296569412016518185546216424617377875307499734592659054762457422624804328302654840015608267986211898040532765655999994354851617890493566902042809014153521980796847059785036912655188937894675444139237784716880660923747258667686027291766606332988624687438722456859888179543546717146363599924580019983750257863433284181609894166624834232817242322428384674570497073815360689525496481950910150852214457899089950623767501142463062630035759661519808899510890914376889390044144910230990582630348550954850848661794007171764550076405765665914956785554870389582544933954068841889257338675380263157214967160431155719861778029379331731838317496086987123097124922760444684604296999123169070026140666505524353464491985111928891704221816021922070083318995370178525075682516514598371609815256921469810157403069885797882358777908503398362273970393862540868232412649140932962597408796537323685382565733084477221841600184196242654567429288743660241690507335883210806383009137801060144131098309280075119008281690747649602543465977999202195630202837603015914818225233904884825977698603112694921658614884289533860347105511021342724590849781504704726198405109646068279510771331474576104566745292747127636660430999385234939116150701549915412419489440075332275997774191030684782115253655562303304320959232715016038789476654468749669047513380255845565007634555620775567631473786770751812073937402540279617575967868995220160103185405493292432396063726756952593117726799478523415710730141346005645605980957628910719169914929950590030098208470835008834727660665865134744210709620426225882339390821504177335441122360719256906292680379746807642484801863322398355206241047602654130176647840760163974633792527759761932793825332898031269573405858144855642076320302436737456069425993213277894491057056416502461278741014760180663139472442263037147042889095486757232178035796264798976062699659603259034608036124778178138787831129645138216510137355295407400301677334854286060830547213761159193311355677520409868350218599541439955469930580822530038193319743756937870750014360621434066006925735120256587098927407008453981246333570545242987676389769939431127366931005707646235493648402645701383847758940040868134911
  | 84 => 151874758881099343662285242911095452683247057301712997008030125024006648389654960041264119288956611060927198403327664354275778923889566904253217025871789679599452645263910133183024282658454518364340734668152289877551255457491443220747001912404811792881108145525663389069772188206535487391151764826632051737128235882369420086320770961375084519476297007241662507722725799349238085653240524524367105739215280696672452357408186172968229643365852580354327192243883006920591313806816481505543194089988534388755712208509991595606035671431214311884805426957265914721996238827769916497952426812943907886728299579691788583475627813782668825228629332163626161581794276544436867242326062338165449918921709898963391971798918149619413161970956625842322201306835409909447524662256605181402019677508052865636103109193044723479392579659941323262696824218524655141434161809979631219447591909426666014329913709463159358475687036688532335176541252233213548842404255088982489028325724305650594314920289535226749228963065011884470814025347620615619316007569572796035921092848015509779452915266708125007835285284119566527023702006596358005534978858069123870755192107523759282610135799482712007223963290609399313194821102452309634303338326827366421815379541692616593217526986447976837751008819594546729213345089572550748460971924648455598121856746227089220498119223294288532276313235818834844490230888814543065593230697424095963817407355429707173719287909097497501274962466874338680915608446004310248436240559832623228032441098418541749462893983047526963870364538357220010518937339553113805820794074675445995534794460308487256838951082802118270444498682990872213918668620812832351904275778101679097337331098789160626123985186059039169647269295096848798024498946299162962577111015184220618649932676596923957696855587944850060699630543734685411247568352183274854953683135103944877845999357004826077389775623067400983914525973646005553184319679449645076499319279301376367909196943552214033921062945872070198338849710357333287816340600497165194752976147202568311135846064863600453662782434369282262402841471998146915320542394702336842893785908908363180782508452305219254719567545251200002369424544471488579856996507061589985463964173520593456255591548280831292685973127867338669526132340759215223032613601485808153685511044986275438291885514228034910423565195281257435484323045581506181867728797683964597372076198590255069855807091325122052067933819349645784830224174819491434786101226184901521124542191604609890489185802757160345529282060707864904192985004596938148868390955080800445390074107910924232490885289307763194140159918173296716873503633989595937285978984315116372477856909119175160999709608190204267253138016172082507623418447625909636890566596954409237763702690273923667335612735455534042867870454692748970359300439030527740807114352269889157309082858270475056604568998309274655263764540610687193615559102929724002072569128734743867869540266872551085003547425256037140172507506024639211958977465110350575374526051605148645092259496184828435687559279104777044802183402315622936544550224709295183176444810888242624807010932588347011627281351587230694201809686878127150808256266284125171717021130339056535453493976711290057257818730337972257464206195443052422391043840491915760313442541523058651998418237280452479295705836501875063275999699143475851537695312999270610972887053899460076364385499213398583193326899500262868496776755182367789909302165909976502289053580680419262977499772350472610088887630536909233872318122442512679554996356926893192541098343782195138644240445340160926480937501513173260237362299559277702913908855400551732477951
  | 91 => 40397831429171399589941295678876555063703194744835304971903337545697545986377705829495175519921040687158965602013166498677337902868338117830018518192034408706852444986863107910672150763787078059374671394912364052353285894489818103343234950068040262190762211593307357389129765711721720656413404589415414223137718543751759085118279198767749455183606585272352414263425694408239939025353958715587474414030292822156067319074997942719178808153668599553480715228069783304989796143474350941989492854476898081995501529858867134238631191624658421165155151603835918665924122015305773778265447880341438080744891332492160293884384277248902895972925781208420098698619615056643757256308423238946135212979557498902106319224960537316483457814430423321466989737667857178560878313195422486046093748272114091211350418953689154626632878372940623899080403573554125406266469522122809847869946967435823997917192726373646516428623370691592164358251674820670691519686931800352391930138442806200703842239763314408041679532920249863211322775223325357580218656793534223333477497616768393918192332146809586987672288587011077010069775635675240528072480213345273597870604051374040445091490842311198333188286654075755222340804452180376747889065791108685781986522558020445776743659309130838589171832648500300691460151071904185136844025981013219055436264612436797935412790809585074844558033782590979643441866624414078425842061647489408343216718419281134756003390747687123868722683694891569599374391214375295101338196590117032079559210295877150832071779770060747232480034700183479410229804930214436318311628965138686875833896510219663152154310178658736860162942620888828757189545775966650707088094236147774197206468517959747001223477156350245892556244893534370286762652149419937950299551435265914591763781090119780811330588043300249787605728399566146417048998443465396812438808902234873257631867744223039573381662457332720070860947331550135161065139951376592239664950873061038392940727716405057018176032452192684130981861875183905482989971182738324425903432235881324795518194577626990008517166652990860214979098697207231600904739107746691668093639069402865467222111672140936319953826401908587138348055467477109571234131319106436627188999174600898550455367143063647490418386467569039399162448368391297394646304566189228370720404483849522016834249583779139438537912822409429447494285267187811926107220941559085114003570523956359687165060317421427567576621199799515952620015909308712297132708432673199590301033540512228902081218483362261819695875789365899465290264863471027919927882991715443701024237903149155258831109835166301666227038501572647647055398895147469798797563979735890196608161887179269014211509558435350402824500334509620455110884177018162446252434804720951865387235720098194051106546466131876252112831023121579856209852096395786208737919852459800109957276507202950472476940655572079957971664732464542163535473844463575980151822150771989218040139366718944746249774960413267533207868928847510259069210943656538034408120185949691498287808374156835379793716874280203098622322139920285936650979585453485100795407102264313626207437487025844901295188077064588673818382870970342457628847847254750229871354190756822849082930317484281193710052120356183932278233490439891888327710526044567391658508096198029254817806503551602776964159800697736513468186459352529230351347471023142008112332107565495937642528769929866644601773795691981634009588196962220790353829924912846495545883544996980011977798354547353055636429477353566079858704327817178216253113157544593143162558447932361285859981492177746041321570355654270900810527774382728085425427745064312155927117946848140617943154022489397619867840973733851225880090832244347112777529030823877749491605804172992450578943092161489896999682709080249695330714928850016072948706099373304625676099947552744242377189837604373624388638239936469100064231952188084431192370147657736371160205798791030204650115791679833973456895
  | 99 => 225608620485496997875762006372302943697493102143595433404919379965678994640103792951944830554693602387302806428213493366084145334296449424528879525465909730219673090121208773598080618851188572336617497906920262833052738720952058576421963337118202184331507719129854308582487077802464224688207534071352040770336514708001929513438658891288857564343340474000948833438658175468469953869987344419425263587741670066885342702072841762304846411852580721563874813527283841907550097865120035468135735475210585015623613758661785727002238701604500019114461641562042837965569124227528365779880872241083416753238829436788360504546593962012497083407911619631226452621800810349201208939548149338269812730507330811992487051267876434920628760174708180265134503616273824318265234624015686634139640639948558878404752310407997883965657331228824032860365957622157148812562801187808855751534861352379581580245765812046569592119375514112443264659837081595486741061468842730754514137719343946317562870023556485718278784610186110264706734496287515973378843185286961671174797311117823710607571722136152635066097054024432248998673691264357056779539120001730265869167722291731946412098374663468539833021323349482489537727011156140230984574797825221311037930876571753551385408402248953471643003822785397933119375385565369091686022171764294832165706748424501766062967725792815030641045585385255188004025225784617866070361300451410811527172997414878868988459595042212136022322134453108124909368933120232327344265833071516701975124449498846365719566612330252122491819933132898917865883195178228472650295762405014166381078533837858987296172361627372823188751300088426640350236197064981457662259681977727376271383944553668263721363097968948939451869580037767944034963587219721015931162454339447297485046436885477884846350771383557660995195295249318584276303999381421537360457256589939264341526991592388897660333074414819478304498386021464538457694346528129607495325135123658124330852550603659730128206487163388078665528522501931384054237338653387729257714352777211456952495887015053571923042814064239744367588206182691906295945536717380575758990638703241648453388777727875348110713086243638591965068775245460569151333903479479577080544431758693381851427601753394188463074662799721188596266613045618958428890948022266061855058971966684832810878625062203169108908927502265150153677035349154337090013881475472581272517370832520178989366347003850692825352550853002386196027354462827022570901584939302583059668004446730936682059993564474991983835938276320741273771888284197838558949833737002191807989960603522102903306907591431796947662599752369148769856667476522929213784435099069095398664719832853490792536826716912406202181095594687267535218919821967906699602039205614022756552862016433538856554083993744990981875299446320942564089888910701533983444184145848923355607731172011557551757929756870607316738496916615769924881589251450064695815117734035758296298779367983381967435478061963515280565086952453278661125218278795500464765309143437336205647913579306558349022123189720656194750952141316614119450232339087665621936589026945202744599980196290406892818065653250666722074573256106468860848541223504286365501534272729441757940945221757535242799932893900416599507369823564835142254872954516617631938351642194839746497332204197530320465693394438423617251968441806679937117910479554374578458894544895932535643901853943742409935141480890391484564659030949157137839915896295559143593071190163444830299292107084287026334044618291850489801602811813344145213667346963186782215352186235269266438886479745558602083344761222749536829522591742160923346579964857997159423471859882178320465390638810484285758528575846375969570002744274061265391695870240400521405073608024509197317253426902689190053049289374679333598818813095177483037268387296628251115516687844055198869540003397565833154671738919939963947491348679445176367760983781069877049638960399705679863463853360467718214056837208647080597641433039554220287470314667815897534663582659086020578379225010019035458516716938283790871242058256373618780211300916302017969767619950412826879692380824907100941606619734026110816947577309703689149444458472367296495808972138722861466448555696433201244838595880134167323469430087031402625889496443637288508083644562328883534007107583
  | 106 => 86268881573517480986718909099571620534966745200101186874443361153038110440089439254825298435696809229750039809805668802380079751759063371343648448531336616725325566725358547087287422870967515805986647534852182265446912386660517375673776564248564891617193400020608608888470785638304508472406240569349983725129265075067289684916250148288583827284298029309373315286053139870071332725220641694755886612963183106032297732879756424633681461462349756838325761105846949911128259268125459279785930766085728712343505094470128508037951508461260162702162327315778505362412553698442216867395726525356071807785633746728292697785331604195395062182401930215647523505328432051894778171886769504914943726400554613071002445650249353989338085583592843120248621604123062017971017377416954393766766161455602224974362660998629059132505265900083343205371793001449454895759311082927822432093063620823968723785528597681950526315069296059093012925160628370416019963071663154684601725773485113654412656013181700444453644738485055493856469251380645083062133802263497521192051799168429934543261038621443096565401289800125144583919689705048292454670593597834824773314172177947944008894115693928729331433208342693269961625130329756335408511023592429992921663191600312736755743330289032355799276091373422551816446530306338859491577744642638913557082535190390859581994542643073270499903164403818535761705801445897848790066908694193847351349625099480481498876146013083553066607133233124057410963247067535881999834030721192564665894478458578105540399213292713444464801954400524959208977441356480619282316234493973740505141648419973939949121900625286006568811359974398609398570410974138544985019543247188725475808230087844865834763401496538039386352345275555162002903642009933573884827198269952187088355553158222609981826772284489877936165898276817905180533865081296728233357522931912584243410370950463735545994584465931712417978644851271652847081099381533415259010353917763768350638196685497295907902316633096661870954228983883910589952827031770525066250333573800430862725504378607683129489728615839395969547401366498130988386546667800379378201150195468627557467385681999951091876286097899354849992999859390664520822833903347844216940501215488962772606636546586634054302475588942124531652387191880970311566419777553120869448770089712999014809328517698410561044480335767314762349380125759088018354101843034843517799371001843367603650780930034482863471027781582321758753067694600329461620021634332824336531542268238247120977718100260862692940238178770971663361737688707576042849890474535073117403100366037128677409725774897586881443915843309475449367435932099585660431334728534005591053965981417743597637816653482348748162648751115515131425693070954986574125844640144061042308391934221961357618966639289712332488760910253733472121072008493078957687887192867011555586112742954165403941877713109617630640074854057328944019166980914972171725433620748329087590686259078108830416133465826714895612542298008331837358983766573985794465584649658467320909618918024792986126309335080664450001692882904738264235332293891107934545870436358326124055025386923677142830654168805935634731669855871813821691403234309049161256264631601183409840062004303735894524974629834584663673153928971973824835687139372973424931477243940439382180562912964049475300554461849472568967490292760911595008895349478737630974925290523807896004468497688851865608084281743525342611035942065421867419418884261141894567909158578351754704857904085380526820077575035777056759148988063543764122303482654183483431445067210243646612203145575867685323179528318018716382303983931860823697304516032931443681416063374286328528154526307478106404113629920797984266471019534230362548612109180474345531712495469068881059901791813291816414475079467418306140445297163295764995734886995129507264973125024731640923428332197199947122631030968895497721998319233889083911122409009363220209882627837662830164645229576662081254430427589703849746521937176877780136950767031084448302867750833953094721478201497984420587076866998404558003581804188083144340518479365211971582630965821588996561696987437555977870696073177413398056034738678921982152394937984444422052713871715296766574650250821761177724608510607431043946454096471909018111517972136774584061515123184484280855838590103854788320912102944461469222733362759872384433372790218516327644822538560407994830235354080075178941652917122015959238442154284795228434823767536224537039777815875539675926322387721789421519150603723731194987067222364042827673972651073429484252610600053427102708080320654445549491489723873107547835127037951
  | 113 => 26012137630015080311024567216205671527404966544034157387038300424781886124791245109346043447561249174970680236325376747611059599505986712173115699085559767774755606787525639855637060169694338720888162726716661680520510548996304578445762510970314798768996071323520136581070532664129199137059428005197653389819883063764125675253669289912140558459878803881632672405197958089097483089656953368757049279519287058320499595374767059010793272920354125905629882916152310268081469124552482510842581225447782120181118497029421830642766677134843712657851030977695849036477392634867474769288794774180897014824755826617324189202101487766998680177496720149347991630188805884591628863605969890806190437549189314268912875860906822358317813239739529662974825407606647320118046153764700384115983653606702564445365274530560040298609578289546150243014503048100650655800109248737373647258610254235665716614563313878601842735035126832167622170898961548170501105454934701774211313487718877675275436308281226454573595150065967452636693596736812450527701135039363331037435628890745462411305917756499347709595845707734621829944126406677917747002182461396282083151972929092280960149457664256087184033115298530179047970844570719401832172046992231107561696353334519920694361773037126692881673485167803782416857677942134333674238954544368071071562163336635726314957028996522314703320460208346956366059576163899536527674690972898027878431372453181599281494485612592576297982369664640922493590589069208714386009153280837232191579866942330432216468339885038046335743857466533191694621026910161536859323173065070181315878440008166210018448121442983234653482972394043870191138471437113785228875817115370455010711847074700047188172227812843483120907016819834497354436946179265287598526862608167599029737399768635533051245201650603985429992530672536827010993139106316817651136471539063640028899841798311908524873764343449322016972357417215958724841189823171233838430304917467793291778400614027426533097601233094249365816049893362619878688320165147970394007483205481981966215228972809486265501186012417388334432079857797524715508279496540782900871523119228805746942752244442012080309013997633277549087165629880468379435544169135985747413793530965584007427928470310373752561487821818490973708981120588947097148038101206591971709211005313631611438018788418991147968068166878527939286492169209040322162470380405897710536417085615473685299200083260019232121029179937080164424189419608834001703687463509239247560212319862142614822543088354866775852935766331394153523852655055116725216786995877105035847721759796507047764524919007634354367589889153709260596533659494378306516826714923232128803933067642633154581912834706572173720946790670634321313014652304362775865544200746475114399229015806252225210758897043510092356632800672336767579613505914970519722357755649644970452507094383895397700713390276474984087393372761667485087522122401161463997105774344072987884460009975014407200373575959275188268398273595169948302745107414505816522524700464140690282463073407460809287945654338336745776030061014923820335657590528295598079367628680566187252802919744292651328449006001826137915383690825033660405412075255379533151386045705550661617694658085948893083306542573797392002762438062626952264717647840873631707630377474788890312138568905936217077248559551206426292750233130391699354178267352969281687534356905610762545327234780453901069889934107254277132740453155766340468570603966971075855013950818175838323927488940450494908445838934068930943726752395128682737744271502013848910417489075903538595493210198520117084965877318369570551386297960026348176551095159575582168227479539830319841614350862910631118855967964141607797961542423730117353459055268500149556354301973074887946965289901254032316674301248186955067601699231621801702857313707221922749269937724325967743918043115662105613321846854470810660830664428480129871938514059411754396516189686376938522916040383847829512555527997525433928504289778681147326867105954474839256133524148344737130221205896566566373854231620878397063233232768049737329742135848021206053191520432858423318199315322114609230616865216385004904217859043744145239641436956317432202007926237571269123859778672390828989274583955657707037438755323522620929401988568265889024976332409018601736081096680311894820148333717553813389934624842727313404669636383061667419163965897867311693591689882252695003689936970764543454953517249940408201035993978924632716566908928426482863360622768531279219541047864750043200593428641717377463568274009973314648129708490262774419713763305583936534813739181092629523513796911366314177048596918676159976240184025591249707467689288117594325633114282964340571259788830024034369076824730214555605437824840760217417968936160815061368897711728443362995761947661973173133207271006995770435451636521792996441973070242400738570233565244046406167157522364645940815038882070689316711948091391
  | 120 => 13549152275408675748430315050731425763905399209076931494893058979003183160164398069338428777178507713375476089087492517147506320766803248421432000007313276041569376388784865469088705815572666233495318921250506630124882128580339164125365966556719182863075718605898727807272070899637956150205742088480815891143429240342799983112366558349105805428675526563714327794745442339170968321322818995166845936582273612681329245880757474519256565102397830632351853165702484227318390257555058644962499364265337955368983438969057415130145737211235921350426240619629489091049158885960831573293590323878872628842188205569049362032271173821517766779795053123403474167010728635727092270241847111877164968671766817487781268481297640559793808243851318118382730515397410059901691699770461702192462075314849472480881792188913227007418738998223666500055570431613073567038432104995468152201017374018946987364409113062280168357133086842690022514966096994458061218518248399236726027977937430295003549678279781581253091625416748463201971056891150932937257082193817396930233452380605154964075286627330173265197945183796533994728988352998778878951818110868021404539795202499629521569042077482932581880474368783294404310423012704913791532763366524860875635101441133000913832429275063978968986685032303312193488357981466917983177114519559018692397275635055453266680559022867208593580313506267025950908583225895931043756803393751624728641587503696944921061973644083045651640828032209178082657017992555781434732428439971237586902783242507652798120023079527049024838266947509917790015537187853572602620364125544747968914792210117797389822408723155838834652149217199558534220718123754789453907607945355551499545709764291404021531835004920328097295206010807964537439647267741819373526626726451689426211787073375164956094909314556108973299065385700775177968151091838663934870650911033137689003722191042874381228746392319413961790282071581625411501491596384393902050676655928156095568484449255925069077124964680194808686827280392950522298734932815632299921733169864608579651863499397455950689852755812816914868969592910292416924663459378486056650161959505570238367543130461801350776549017521139893483153701526643375457707934319682511322144647133062179892313569617800266599051816014940806295309919311183821081826214477866415144171505856814241592224921396830619631247911171942313064108978221247708784706364012437688124473114958218471768737968646258739128307518614851141497053034460701174401563908046385911462038446602751640831320238041074258580231759378308863746917676305177113348884530873510349364347225576221779708058794226645115376950710471275169689400430371048246797353587062251852541805849954825063943372058209887162453917446085741389258925774846655711044931821302889461463892914701543479518847089246481814737700023411140356859890552030069343274121564868868999943021195991107898844112454125831247287362566702520589175933920990395375036286588683416306949823906465638892977741707121897921574965897804679519320030313958122492645911848857219232198451539403157272606495499839958292468332536558216134849288745083191937592872814106539410685152498819461866569273370260625012339289275715599609417586273267429646393748130368333343876189214995893813132676324372157281450929534269527961889680532681347765949777882760170487044126991821809430987329328812018879530616714769379665304027447215760525243738833377441724191426494567739840290403234891689037485000328150032695515399042959766423930540795259414909603542241689774935139284069588554157205755930631171627465497545459756078516698614832765250866823518033857421737128844917679490489978899882283087689551302316657105012782500421196533189398242038217965369283536713200396746958717577493578246772896775549302195063385886914246731333937156223232875250992598940216610572873477276330342339971370777222584495152978044464218662806116126861278775221345988896182948780070975012015662482102218832048913020268445979085607365128362752809501503544964905066155319740093779328876766671761626453226649621898453897386008275313344286507425086980861435434212048684703592882787108862467935593116719518770839242884049902413961798344396418687992627057248355184859613062241180405812958245436158502079899236503124515884085490269226849812114746803870901403270508821310574470378257322332505763157764038429232892143107423701321228403284091213250303695446197285821897299682314017550378464351612705137830968424465286467360856604767956726278306170120126367911829375281881212737312686235472312059127411424423452100348420014271865366256265679569350863859963438434045518672177329665254974659981151101200441567436395731954550082397577212490666861075828705254118523570809865314371274453726720969173038165632020398268534530139437608365824525518029765563357119512673447179181081089679420291398121090917539336661683636791038109221956006161866500399154997152266549378926597297285292589826024484775224712437445855439972112070644979418560433105334977600887858098077401621745049499054552502627813990097835059167021513873122759101118941040912162797729641379511309091498460607992885401318833602788489061333395634681169900333595729095183458685085330988399764191089879840642532463136334655912581140074202784103890551298025631099246035861503
  | 128 => 431670831771285792100338532849165971883183451371943513782907379251047437240189417895784165547167755437040772429281396487550182777291333944674110845267670866990623087574992908886423154782754466073687253796585093266076717570517214750112682094062615773828070130303098623485315757908372636344303327159647477990134571562581846166950985462633718276758799779481987083661744685027871695490193296137920901112100729087620577616412104724246144664233098823844451806197424261709811906141257782990587916486154985128690866252447804185085453693053599276495367074832880033347077943764046636610175568915756877867183190975233936835502660003641468763929359414649739488059540530940435186755457340943794808066939775075565574231634303020963023696570510208964500920044656324038719100876813172430234412338673722467849872152884884687734787702850395949453112599506208233743266347862354271394350295960322747997355550078963138066823130681794610143495983719458090160058699908901674739863467997240838395637361778609452580242240577909751861905015026420944911115973748812866215002722006308998766112087844055480437252331139046599700842094453806671930553680061856993860139345490606358887549068101811837766654095876898824144429704722192536286306490720122468889244447773671042832353269433538616233357201851194179523758999504451300796751061863844710936763588422429236116208051766978102416160004361444792802857478113691591125011202341131163380244203873870721291979192469213194428512356370575934925135924432965915860374211242090979704441777128598661819285612038809869810008437594510040138416225612556704723405387915653589427414086123046311130603578912114830232947037566544286917512229910867721321987327536416888927855931953352986795110514480925910141954212056889407095810429461856119474313412689902027973258385168307358830760900927766698971818462514736638274520163180160962842001175489465443062634139769782700296077226287220542912375835190814674921396716552946550245830916158941911180593767826513295730025349137250731653031097438714512010415342972364401862789232159322628679345849740399172907179208304671517082242847163214500810603793902308152864750710755753725742476881459599718825435454537845636865386554848086913822588263764203425224674591927571688111169807215843863381624660742400644596369007092296456184687482959584647746782647629625853216079842692625619953613692545461277770552251862412482377135847867651415831421463836857199982582500544175881933334491238042361794523552233204666663286085213803457427050149845940388034112940279390764081531048518722422522390784145748602448793663189559152477682516061917073335414299768184441679631270650421240268466088595437023595939172143444405179012032577610064357333948573142031634930851136891963851544634806275764829563745713648131745934121568626076405784015460451360598243682871251978799898646743024322997575267357368985835328397590109666482230808056771998996244216674205944155354173951487494689925968645224930787127479530017907219340153309877765913780222904644076271079908893888028700969994314450843708869423541768780173642962508315329260480626126246017195077079901497046454158803592220997972954866500714495507101521737538934778098805816321089503690162616845942419070530346500303675562657948682082930928409774231748054062698665214762985519253725779864971340584456103374723233929363323335427892706211068276311597818875482450751362887312891897022646503069548789368538272615896392528907828785368866832385770556749240008907891908972783866777038613602699537115647463363930270487397527186092573458097770435572374807814056423025649005831034735353004101260120102594309859531456170768010296357892665612873596943661535001961029812167771365815575363344766697991357694219412086295458717521493761385699819384359393940119175797295128580307334140364271751191011299508910260696068019971380323204136005404316439428525978074703353236756890244646669008580183850004613330366556554624064153643233550673774344459778383031250446838398777352447835097510216697847678054985105736977069600298270349443517742232178167205033158630841124093918658656010887885135764806673401661367566835868513274571119018332729365411460325740693753049270027611991019968622212764727478309875754342373813644316854236964616694605581585870005633623995948438577195203599070707104292746692049698483076534981078243737820372978789023365122670567627611931607637106043165005739762625168902191258280253853376126466568362565372766756173009278634834019559214928230080737077785843028574642347928224519737999560186651521035526346817552531190352825859412545897613573472803261219289319492353778892426565269572728034578959530748588065839063787687246935562664829136122698558085764608907252433259640913707636244822827910475094921070092741750244141359751402616082895245922256013229865894316183830016517938251748461486836402082973912675058843176933900318598651145083899090864827479657625464507244207531149984329163646962084440255753887294511596185738785174306187829624889724011276764947105652839942631115480346236611688344686047534407571276809268988664234459853456342154032175388847046958380598638913651599144218626524041752145537032103812113255048738155453301942765554137482097808377479410905913713001810848011529232333980333394881682812259145399902058661484444194355582016889394006654703907852597089926688261775713588178929144028278832521467987068764923373166401281338687148436845951794456063378461626501244800638823754153338215722023199672799468198118498022600191777343610222191958305392527935993082798496793529309415512627210638531604203940184565658468437071560693849346763611633806787524511241238703243263
  | _ => 0

def digit (w value i : Nat) : Nat := (value / (2^w)^i) % 2^w

def mark (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, m => (if m.testBit 0 then 1 else 0) + 2^w * mark w n (m >>> 1)

def unitDigits (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, i => 2^i + 2^w * unitDigits w n (i+1)

def identityWord (w n : Nat) := unitDigits w n 0

def step (n : Nat) (m : Nat) (v : (Nat × Nat) × Nat) : Nat :=
  let i := v.2
  let mid := m ^^^ (digit width m i * mark width n v.1.2)
  if v.1.1 < n then mid ^^^ (digit width mid v.1.1 <<< (width*i)) else mid

def encoding (n : Nat) := (pivots n).zipIdx.reverse.foldl (step n) (identityWord width n)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPackedData ====

-- ==== begin CRTPivots ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Placement

def sweep (r : Rows) (i mask : Nat) : Rows :=
  let src := Matrix.read r i
  Array.ofFn fun j : Fin r.size => if mask.testBit j.val then Matrix.read r j.val ^^^ src else Matrix.read r j.val

def pivotBack (n : Nat) (r : Rows) (v : (Nat × Nat) × Nat) : Rows :=
  let mid := sweep r v.2 v.1.2
  if v.1.1 < n then applyPair mid (v.1.1,v.2) else mid

def fastBasis (n : Nat) : Rows := (pivots n).zipIdx.reverse.foldl (pivotBack n) (units n)

@[simp] theorem sweep_size (r : Rows) (i m : Nat) : (sweep r i m).size = r.size := by simp [sweep]

@[simp] theorem pivotBack_size (n : Nat) (r : Rows) (v : (Nat × Nat) × Nat) :
    (pivotBack n r v).size = r.size := by unfold pivotBack; dsimp only; split <;> simp

theorem apply_read (r : Rows) (i j q : Nat) (hb : j < r.size) :
    Matrix.read (applyPair r (i,j)) q =
      if q = j then Matrix.read r j ^^^ Matrix.read r i else Matrix.read r q := by
  by_cases e : q = j
  · subst q; simp [applyPair,Matrix.read,hb]
  · simp [applyPair,Matrix.read,e,Ne.symm e]

private theorem read_sweep_list (r : Rows) (i q : Nat) (xs : List Nat) (nd : xs.Nodup)
    (sep : i ∉ xs) (bounds : ∀ j ∈ xs, j < r.size) :
    Matrix.read (applyOps (xs.map (fun j => (i,j))) r) q =
      if q ∈ xs then Matrix.read r q ^^^ Matrix.read r i else Matrix.read r q := by
  induction xs generalizing r with
  | nil => simp [applyOps]
  | cons j xs ih =>
    change Matrix.read (applyOps (xs.map (fun z => (i,z))) (applyPair r (i,j))) q = _
    have hj := bounds j (by simp)
    have distinct : i ≠ j := fun e => sep (by simp [e])
    have rest : i ∉ xs := fun h => sep (List.mem_cons_of_mem _ h)
    rw [ih _ (List.nodup_cons.mp nd).2 rest (by simpa only [applyPair_size] using
      (fun k hk => bounds k (List.mem_cons_of_mem _ hk) : ∀ k ∈ xs, k < r.size))]
    by_cases eq : q = j
    · subst q; simp [apply_read _ _ _ _ hj, (List.nodup_cons.mp nd).1]
    · simp [apply_read _ _ _ _ hj,eq,distinct]

private theorem backward_row (n i donor mask : Nat) (r : Rows) (size : r.size = n) (off : mask.testBit i = false) :
    applyOps (elimStep n i (donor,mask)).reverse r = pivotBack n r ((donor,mask),i) := by
  let xs := (selected n mask).reverse
  have nd : xs.Nodup := List.nodup_reverse.mpr (List.Nodup.filter _ List.nodup_range)
  have sep : i ∉ xs := by simp [xs,selected,off]
  have bound : ∀ j ∈ xs, j < r.size := fun j hj => size ▸ List.mem_range.mp (List.mem_filter.mp (List.mem_reverse.mp hj)).1
  have fast : applyOps (xs.map (fun j => (i,j))) r = sweep r i mask := by
    apply Array.ext
    · simp
    · intro q hq _
      have inside : q < r.size := by simpa only [applyOps_size] using hq
      have step := read_sweep_list r i q xs nd sep bound
      have live : q < n := size ▸ inside
      have correct : Matrix.read (applyOps (xs.map (fun j => (i,j))) r) q = Matrix.read (sweep r i mask) q := by
        simpa [xs,selected,live,sweep,Matrix.read,inside] using step
      simpa only [Matrix.read,Array.getElem?_eq_getElem hq, Array.getElem?_eq_getElem (by simpa using inside : q < (sweep r i mask).size),Option.getD_some] using correct
  unfold elimStep pivotBack
  dsimp only
  rw [List.reverse_append,←List.map_reverse]
  change applyOps (xs.map (fun j => (i,j)) ++ _) r = _
  rw [show ∀ ys zs (a : Rows), applyOps (ys++zs) a = applyOps zs (applyOps ys a) from fun _ _ _ => List.foldl_append,fast]
  split <;> rfl

theorem fast_basis_correct (n : Nat) (hn : UsedWidth n) : applyOps (basisNetwork n) (units n) = fastBasis n := by
  let rows := (pivots n).zipIdx
  have all : ∀ v ∈ rows.reverse, v.1.2.testBit v.2 = false := by
    intro v hv
    obtain ⟨⟨donor,mask⟩,i⟩ := v
    have ok := of_decide_eq_true (List.all_eq_true.mp (good_pivots n hn) _ (List.mem_reverse.mp hv))
    exact ok.2.2
  have fold (xs : List ((Nat × Nat) × Nat)) (r : Rows) (size : r.size = n)
      (h : ∀ v ∈ xs, v.1.2.testBit v.2 = false) :
      applyOps (xs.flatMap (fun (row,i) => (elimStep n i row).reverse)) r = xs.foldl (pivotBack n) r := by
    induction xs generalizing r with
    | nil => rfl
    | cons v xs ih =>
      obtain ⟨⟨donor,mask⟩,i⟩ := v
      rw [List.flatMap_cons]
      unfold applyOps
      rw [List.foldl_append]
      change applyOps _ (applyOps (elimStep n i (donor,mask)).reverse r) = xs.foldl _ _
      rw [backward_row n i donor mask r size (h _ (List.mem_cons_self ..))]
      apply ih _ ((pivotBack_size ..).trans size) (fun z hz => h z (List.mem_cons_of_mem _ hz))
  simpa only [basisNetwork,fastBasis,List.reverse_flatMap,Function.comp_def,rows] using
    fold rows.reverse (units n) (by simp [units]) all

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTPivots ====

-- ==== begin CRTPacked ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Placement

theorem digit_bound (w a i : Nat) : digit w a i < 2^w := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem digit_zero (w lo hi : Nat) (h : lo < 2^w) : digit w (lo+2^w*hi) 0 = lo := by
  simp [digit,Nat.mod_eq_of_lt h]

theorem digit_succ (w lo hi i : Nat) (h : lo < 2^w) : digit w (lo+2^w*hi) (i+1) = digit w hi i := by
  simp only [digit,pow_succ']
  rw [←Nat.div_div_eq_div_mul,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt h,Nat.zero_add]

theorem digit_xor (w a b i : Nat) : digit w (a ^^^ b) i = digit w a i ^^^ digit w b i := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [digit,←Nat.pow_mul,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow,Nat.testBit_xor]
  cases decide (j<w) <;> simp

theorem digit_mark_mul (w n mask v q : Nat) (sv : v < 2^w) (hq : q < n) :
    digit w (v*mark w n mask) q = if mask.testBit q then v else 0 := by
  induction n generalizing mask q with
  | zero => omega
  | succ n ih =>
    have eq : v*mark w (n+1) mask = (if mask.testBit 0 then v else 0) + 2^w*(v*mark w n (mask>>>1)) := by
      rw [mark,Nat.mul_add,Nat.mul_left_comm v (2^w)]
      cases mask.testBit 0 <;> simp
    have low : (if mask.testBit 0 then v else 0) < 2^w := by split <;> first | exact sv | exact Nat.two_pow_pos _
    rw [eq]
    cases q with
    | zero => exact digit_zero _ _ _ low
    | succ q =>
      rw [digit_succ _ _ _ _ low,ih _ _ (by omega),Nat.testBit_shiftRight, Nat.one_add]

theorem digit_single (w v i q : Nat) (sv : v < 2^w) :
    digit w (v <<< (w*i)) q = if q = i then v else 0 := by
  induction i generalizing q with
  | zero =>
    simp only [Nat.mul_zero,Nat.shiftLeft_zero]
    cases q with
    | zero => simp [digit,Nat.mod_eq_of_lt sv]
    | succ q =>
      have h := digit_succ w v 0 q sv
      simpa [digit] using h
  | succ i ih =>
    have e : v <<< (w*(i+1)) = 0 + 2^w*(v <<< (w*i)) := by
      rw [Nat.mul_succ,Nat.shiftLeft_eq,Nat.pow_add,Nat.shiftLeft_eq,Nat.zero_add]; ac_rfl
    rw [e]
    cases q with
    | zero => simpa using digit_zero w 0 _ (Nat.two_pow_pos w)
    | succ q => simpa only [Nat.succ.injEq,ih] using digit_succ w 0 (v <<< (w*i)) q (Nat.two_pow_pos w)

theorem digit_units (w n start q : Nat) (bound : start+n ≤ w) (hq : q < n) :
    digit w (unitDigits w n start) q = 2^(start+q) := by
  induction n generalizing start q with
  | zero => omega
  | succ n ih =>
    have low : 2^start < 2^w := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [unitDigits]
    cases q with
    | zero => simpa using digit_zero w (2^start) _ low
    | succ q =>
      rw [digit_succ _ _ _ _ low,ih _ _ (by omega) (by omega),show start+1+q = start+(q+1) by omega]

def Matches (x : Nat) (r : Rows) : Prop := ∀ q < r.size, Matrix.read r q = digit width x q

theorem matches_step (n : Nat) (x : Nat) (r : Rows) (v : (Nat × Nat) × Nat) (size : r.size = n)
    (hi : v.2 < n) (agree : Matches x r) : Matches (step n x v) (pivotBack n r v) := by
  let i := v.2
  let mask := v.1.2
  let y := x ^^^ (digit width x i * mark width n mask)
  have mid : Matches y (sweep r i mask) := by
    intro q hq
    have sq : q < r.size := by simpa only [sweep_size] using hq
    have si : i < r.size := size ▸ hi
    simp only [sweep,Matrix.read] at hq
    change Matrix.read (sweep r i mask) q = digit width (x ^^^ (digit width x i * mark width n mask)) q
    rw [digit_xor,digit_mark_mul _ _ _ _ _ (digit_bound ..) (size ▸ sq)]
    have readRow : Matrix.read (sweep r i mask) q = if mask.testBit q then Matrix.read r q ^^^ Matrix.read r i else Matrix.read r q := by
      simp [sweep,Matrix.read,sq]
    rw [readRow,agree q sq,agree i si]
    cases mask.testBit q <;> simp
  change Matches (if v.1.1 < n then y ^^^ (digit width y v.1.1 <<< (width*i)) else y)
    (if v.1.1 < n then applyPair (sweep r i mask) (v.1.1,i) else sweep r i mask)
  split
  · rename_i inside
    intro q hq
    have sz : (sweep r i mask).size = n := (sweep_size ..).trans size
    have sq : q < (sweep r i mask).size := by simpa only [applyPair_size] using hq
    rw [apply_read _ _ _ _ (sz ▸ hi),digit_xor,digit_single _ _ _ _ (digit_bound ..),
      mid q sq,mid i (sz ▸ hi),mid v.1.1 (sz ▸ inside)]
    by_cases hit : q = i <;> simp [hit]
  · exact mid

theorem encoding_matches (n : Nat) (hn : UsedWidth n) (bound : n ≤ width) : Matches (encoding n) (fastBasis n) := by
  have fold (xs : List ((Nat × Nat) × Nat)) (x : Nat) (r : Rows) (size : r.size = n)
      (agree : Matches x r) (good : ∀ v ∈ xs, v.2 < n) :
      Matches (xs.foldl (step n) x) (xs.foldl (pivotBack n) r) := by
    induction xs generalizing x r with
    | nil => exact agree
    | cons v xs ih =>
      exact ih (step n x v) (pivotBack n r v) ((pivotBack_size ..).trans size)
        (matches_step n x r v size (good _ (List.mem_cons_self ..)) agree) (fun a ha => good a (List.mem_cons_of_mem _ ha))
  apply fold _ _ _ (by simp [units])
  · intro q hq
    have sq : q < n := by simpa [units] using hq
    simpa [units,Matrix.read,sq,identityWord] using (digit_units width n 0 q (by simpa using bound) sq).symm
  · intro v hv
    obtain ⟨⟨donor,mask⟩,i⟩ := v
    have h := of_decide_eq_true (List.all_eq_true.mp (good_pivots n hn) _ (List.mem_reverse.mp hv))
    exact h.1

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPacked ====

-- ==== begin CRTBasisReceipt ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

/-- Spread four bits across four 144-bit lanes with two fixed masks. -/
def spreadFour (x : Nat) : Nat :=
  let pairs := (x ||| (x <<< (2*(width-1)))) &&& (3 ||| (3 <<< (2*width)))
  (pairs ||| (pairs <<< (width-1))) &&& (1 ||| (1 <<< width) ||| (1 <<< (2*width)) ||| (1 <<< (3*width)))

private theorem four_checked : ∀ a : Fin 16, spreadFour a.val = mark width 4 a.val := by decide +kernel

private theorem mark_congr (n a b : Nat) (eq : ∀ i < n, a.testBit i = b.testBit i) : mark width n a = mark width n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [mark,eq 0 (Nat.zero_lt_succ _)]
    rw [ih (a>>>1) (b>>>1) (fun i hi => by simp only [Nat.testBit_shiftRight]; exact eq _ (by omega))]

private theorem four (a : Nat) : mark width 4 a = spreadFour (a%16) := by
  rw [four_checked ⟨a%16,Nat.mod_lt _ (by decide)⟩]
  apply mark_congr
  intro i hi
  change a.testBit i = (a % 2^4).testBit i
  rw [Nat.testBit_mod_two_pow]
  simp [hi]

private theorem mark_add (n m bits : Nat) :
    mark width (n+m) bits = mark width n bits + 2^(width*n) * mark width m (bits>>>n) := by
  induction n generalizing bits with
  | zero => simp [mark]
  | succ n ih =>
    rw [Nat.succ_add,mark,ih,mark,←Nat.shiftRight_add,Nat.one_add,Nat.mul_succ,Nat.pow_add]
    ring

def spreadChunks (r : Nat) : Nat → Nat → Nat
  | 0, a => mark width r a
  | c+1, a => spreadFour (a%16) + (spreadChunks r c (a>>>4) <<< (4*width))

private theorem spreadChunks_eq (r c bits : Nat) : mark width (4*c+r) bits = spreadChunks r c bits := by
  induction c generalizing bits with
  | zero => simp [spreadChunks]
  | succ c ih =>
    rw [show 4*(c+1)+r = 4+(4*c+r) by omega,mark_add,four,ih,spreadChunks,Nat.shiftLeft_eq]
    simp [Nat.mul_comm]

def capture (w value i : Nat) : Nat := (value >>> (w*i)) &&& (2^w-1)

theorem capture_eq (w value i : Nat) : capture w value i = digit w value i := by
  simp only [capture,digit,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow,Nat.pow_mul]

def quickStep (n : Nat) (bits : Nat) (v : (Nat × Nat) × Nat) : Nat :=
  let i := v.2
  let marks := spreadChunks (n%4) (n/4) v.1.2
  let mid := bits ^^^ (capture width bits i * marks)
  if v.1.1<n then mid ^^^ (capture width mid v.1.1 <<< (width*i)) else mid

private theorem quickStep_eq (n : Nat) : quickStep n = step n := by
  funext bits v
  unfold quickStep step
  simp only [capture_eq,←spreadChunks_eq,Nat.div_add_mod]

def quickEncoding (n : Nat) := (pivots n).zipIdx.reverse.foldl (quickStep n) (identityWord width n)

theorem quickEncoding_eq (n : Nat) : quickEncoding n = encoding n := by
  simp only [quickEncoding,encoding,quickStep_eq]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Matrix Packed
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

private theorem packed_identity (n : Nat) (hn : UsedWidth n) : encoding n = basisWord n := by
  rw [←quickEncoding_eq]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem recorded (n : Nat) (hn : UsedWidth n) :
    n ≤ width ∧ (encoded n).size = n ∧ ∀ i : Fin n, Matrix.read (encoded n) i.val = digit width (basisWord n) i.val := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem coordinates_checked (n : Nat) (hn : UsedWidth n) : CoordinatesOK n := by
  obtain ⟨bound,sz,data⟩ := recorded n hn
  have checks := encoding_matches n hn bound
  rw [packed_identity n hn] at checks
  have fs : (fastBasis n).size = n := by rw [←fast_basis_correct n hn,applyOps_size]; simp [units]
  unfold CoordinatesOK
  rw [fast_basis_correct n hn]
  apply Array.ext (fs.trans sz.symm)
  intro q hf he
  have equal := (checks q hf).trans (data ⟨q,fs ▸ hf⟩).symm
  simpa only [Matrix.read,Array.getElem?_eq_getElem hf,Array.getElem?_eq_getElem he,Option.getD_some] using equal

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBasisReceipt ====

-- ==== begin CRTFastField ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Field Matrix

/-- Once the slot is known, only one group of scalar terms can contribute. -/
def fastScalar (p : Nat) (mir : Bool) (slot : Nat) (data : Nat → Nat) (q : Nat) : Nat :=
  if 1 ≤ slot ∧ slot ≤ 16 then
    let d := fieldDegree p
    (selected d (rowMask p mir q >>> ((slot-1)*d))).foldl (fun a j => a ^^^ data j) (data q)
  else data q

private theorem zeros (n a : Nat) : (List.replicate n 0).foldl Nat.xor a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,List.foldl_cons,show Nat.xor a 0 = a from Nat.xor_zero a,ih]

theorem scalar_fast (p : Nat) (mir : Bool) (slot : Nat) (data : Nat → Nat) (q : Nat) :
    scalarRow p mir (fun k => decide (slot = k+1)) data q = fastScalar p mir slot data q := by
  let js := fun k => selected (fieldDegree p) (rowMask p mir q >>> (k*fieldDegree p))
  have all (ks : List Nat) (nd : ks.Nodup) (a : Nat) :
      (ks.flatMap (fun k => (js k).map fun j => if decide (slot=k+1) then data j else 0)).foldl Nat.xor a =
      if 1 ≤ slot ∧ slot-1 ∈ ks then (js (slot-1)).foldl (fun v j => v ^^^ data j) a else a := by
    induction ks generalizing a with
    | nil => simp
    | cons k ks ih =>
      rw [List.flatMap_cons,List.foldl_append,ih (List.nodup_cons.mp nd).2]
      by_cases eq : slot = k+1
      · subst slot
        simp [List.nodup_cons.mp nd,List.foldl_map]
        rfl
      · have no : 1 ≤ slot → slot-1 ≠ k := by omega
        by_cases low : 1 ≤ slot <;> simp [eq,low,no,zeros]
  unfold scalarRow accumulate fastScalar
  change _ = if 1 ≤ slot ∧ slot ≤ 16 then (js (slot-1)).foldl _ (data q) else data q
  rw [all (List.range 16) List.nodup_range]
  simp only [List.mem_range]
  by_cases valid : 1 ≤ slot ∧ slot ≤ 16
  · rw [if_pos valid,if_pos (by omega)]
  · rw [if_neg valid,if_neg (by omega)]

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTFastField ====

-- ==== begin CRTPackedActions ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Field

def pack (w : Nat) : List Nat → Nat
  | [] => 0
  | a::xs => a + 2^w * pack w xs

def codedWord (n dim k : Nat) := pack width (coded n dim k).toList

def put (x q value : Nat) := x ^^^ ((digit width x q ^^^ value) <<< (width*q))

def replace (x : Nat) (indices : List Nat) (value : Nat → Nat) := indices.foldl (fun acc q => put acc q (value q)) x

def scalarWord (x p : Nat) (mir : Bool) (slot off : Nat) : Nat :=
  let d := fieldDegree p
  let localData := fun j => digit width x (off+j)
  replace x ((List.range d).map (off+·)) (fun q => fastScalar p mir slot localData (q-off))

def cxWord (x : Nat) (op : Wire × Wire) := x ^^^ (digit width x op.1 <<< (width*op.2))

def stageWord (n x slot off d m h : Nat) (mir : Bool) :=
  if m ≤ 2^h then x else if enabled n slot h then (oriented mir (editPairs off d m h)).foldl cxWord x else x

def r8StepWord (n x slot off : Nat) (st : R8Step) : Nat :=
  if r8Enabled n slot st.tags then (r8Ops off st).foldl cxWord x else x

def primaryWord (n x off p m slot : Nat) (mir : Bool) :=
  let d := fieldDegree p
  let scalar := (List.range m).foldl (fun a j => scalarWord a p mir slot (off+d*j)) x
  if d == 8 && m == 2 then (pascalR8Steps mir).foldl (fun a st => r8StepWord n a slot off st) scalar
  else (oriented mir (List.range 4)).foldl (fun a h => stageWord n a slot off d m h mir) scalar

def componentWord (n : Nat) (mir : Bool) (slot : Nat) : Nat → List (Nat × Nat) → Nat → Nat
  | _, [], x => x
  | off, (p,m)::ps, x => componentWord n mir slot (off+fieldDegree p*m) ps (primaryWord n x off p m slot mir)

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPackedActions ====

-- ==== begin CRTPrototype ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix

def prototype : Nat → Rows
  | 7 => #[31111530689914373802365678393761665047405, 37333836827897248562838814072513998056886]
  | 11 => #[19891781826937379155528292012389348046057, 26751016939674406450538047878730502544698, 9945890913468689577764146006194674023028, 14335269661968236889415737841593606611112, 3583817415492059222353934460398401652778, 2778256082484571133056277085397870717472]
  | 13 => #[15776240759295162778522438492584655346873, 31552481518590325557044876985169310693746, 7888120379647581389261219246292327673436, 14303366242839227460136622698029229148328, 2945749032911870636771631589110852397090, 736437258227967659192907897277713099272]
  | 19 => #[40006995905761713665020287229952780727697, 10445392358955229623541529622652388974258, 20890784717910459247083059245304777948516, 41781569435820918494166118490609555897032]
  | 21 => #[6913673486647638622747928531947036677201, 13827346973295277245495857063894073354402, 23506489854601971317342957008619924702484, 3456836743323819311373964265973518338600]
  | 25 => #[9167965271024970566755654085954890144497, 18335930542049941133511308171909780288994, 36671861084099882267022616343819560577988, 26362054118452546945033801918610610605432]
  | 31 => #[23885626787740712790203327282952504133169, 25290663657607813542568228887832063199826, 28100737397342015047298032097591181333140, 33720884876810418056757638517109417599768, 723806872355779175460706887362197094944, 3406149987556607884520973587586809858562, 851537496889151971130243396896702464640, 11580909957692466807371310197795153519112]
  | 37 => #[27932194474876813705862654941247809506593, 12308245983873504088413360131229287946818, 8936042180094617128646825586564267571620, 17872084360189234257293651173128535143240, 35744168720378468514587302346257070286480]
  | 67 => #[5612898168739760699118325677947147851841, 16508956679978163768089428834160722520258, 33017913359956327536178857668321445040516, 22479683754032531749045765585376559014664, 1403224542184940174779581419486786962960, 2806449084369880349559162838973573925920]
  | 73 => #[5540409574916258348366490672861666378305, 11080819149832516696732981345723332756610, 22161638299665033393465962691446665513220, 6137069067599547708959805053015999680584, 12274138135199095417919610106031999361168, 24548276270398190835839220212063998722336]
  | 257 => #[43556142965880123323311949751266331066367, 14518714321960041107770649917088777022122, 26133685779528073993987169850759798639820, 2903742864392008221554129983417755404424, 38431890852247167638216426251117350940912, 11102546246204737317706967583656123605152, 22034284088621709445910751050640614539456, 170808403787765189503184116671632670848, 338958311018522360492699998064329424640, 225972207345681573661799998709552949760, 271166648814817888394159998451463539712, 180777765876545258929439998967642359808, 319019586840962221640188233472310046720, 212679724560641481093458822314873364480, 255215669472769777312150586777848037376, 170143779648513184874767057851898691584]
  | 313 => #[20587904885963616363440185356714713970945, 41175809771927232726880370713429427941890, 38795476577974342130448791675592524817412, 30120868495474515782654579864382903267592, 4604813216334664944122908100978077145872, 13462523852215482876258010607405922012960, 26925047704430965752516021214811844025920, 10293952442981808181720092678357356985472]
  | 471 => #[12761683044446859915504946222260308626177, 37603149969025162811728073319071680421122, 41006996528519712355110547713119341834500, 38457850091159301386909145674972352602632, 24341008765972543683850384107703124397840, 5125874566064964044388818464139917729312, 20289823233726321533760005767584502871872, 28158913005163491619408447986763319846272]
  | 1193 => #[6437934716980772870274157670577252049921, 12875869433961545740548315341154504099842, 25751738867923091481096630682309008199684, 1937620457626437122713387937801468019720, 3875240915252874245426775875602936039440, 1421680106984580013938291802783368721440, 2843360213969160027876583605566737442880, 804741839622596608784269708822156506240, 1609483679245193217568539417644313012480, 3218967358490386435137078835288626024960]
  | 1571 => #[10672267084425226937395008806420316257281, 11534023507617071494296172170402087797762, 23068047015234142988592344340804175595524, 2579951064588162653872738930342020124680, 5159902129176325307745477860684040249360, 360438234613033484196755380325065243680, 720876469226066968393510760650130487360, 1441752938452133936787021521300260974720, 2883505876904267873574043042600521949440, 5336133542212613468697504403210158128640]
  | 4593 => #[1522574363038214398120222723363115569153, 3045148726076428796240445446726231138306, 6090297452152857592480890893452462276612, 12180594904305715184961781786904924553224, 23115479165219448384796601424164171943952, 1240479081966610592630477111398403092512, 1088648408894823297253454746902373953600, 722358723913107762024893794505130373248, 95160897689888399882513920210194723072, 190321795379776799765027840420389446144, 380643590759553599530055680840778892288, 761287181519107199060111361681557784576]
  | 5349 => #[1848559416446310650596456275819714269185, 3697118832892621301192912551639428538370, 5726967305687412209317494754430497984516, 11453934611374824418634989508860995969032, 22907869222749648837269979017721991938064, 1293826056180366580531143248760550445088, 1004939137076944354941813022113452060736, 178967728302731631541171711075953062016, 357935456605463263082343422151906124032, 715870913210926526164686844303812248064, 462139854111577662649114068954928567296, 924279708223155325298228137909857134592]
  | 5981 => #[1910301228471820345756682168855911256065, 3820602456943640691513364337711822512130, 6776052124883235021616150546147506622468, 11673773301901897295841118538421221191688, 22120489416178641704732169889200641617936, 684835866477160086152390027134952169504, 546704977316244380882023970741215563840, 1093409954632488761764047941482431127680, 1339906351662289491182263961459160289536, 847006515610404377702018818268438327808, 477575307117955086439170542213977814016, 955150614235910172878341084427955628032]
  | 6891 => #[2542445399454101575714146347723674054657, 3245701934152721813434690816512908955650, 6491403868305443626869381633025817911300, 11356368364604774348354792186985610555400, 22712736729209548696709584373971221110800, 689759505366133122712675348981576609824, 1176930755104793060598545167109143924800, 534848453250106679735339213451920625792, 1069696906500213359470678426903841251584, 405712741769090226679336352064113619456, 811425483538180453358672704128227238912, 1271222699727050787857073173861837027328]
  | _ => #[]

def prototypeWord (p m dim k : Nat) : Nat :=
  pack width (((prototype p).toList.take (fieldDegree p*m)).map (clipShift dim k))

def prototypeTest (p m slot : Nat) (mir : Bool) : Bool :=
  let dim := 135 - (slot - 1)
  primaryWord (fieldDegree p*m) (prototypeWord p m dim (entryShift mir slot)) 0 p m slot mir ==
    prototypeWord p m dim (exitShift mir slot)

def UsedPrimary (p m : Nat) : Prop :=
  p = 7 ∧ m = 1 ∨ p = 11 ∧ m = 1 ∨ p = 13 ∧ m = 1 ∨ p = 19 ∧ m = 1 ∨ p = 21 ∧ m = 1 ∨ p = 25 ∧ m = 1 ∨ p = 31 ∧ m = 1 ∨ p = 37 ∧ m = 1 ∨ p = 67 ∧ m = 1 ∨ p = 73 ∧ m = 1 ∨ p = 257 ∧ m = 1 ∨ p = 257 ∧ m = 2 ∨ p = 313 ∧ m = 1 ∨ p = 471 ∧ m = 1 ∨ p = 1193 ∧ m = 1 ∨ p = 1571 ∧ m = 1 ∨ p = 4593 ∧ m = 1 ∨ p = 5349 ∧ m = 1 ∨ p = 5981 ∧ m = 1 ∨ p = 6891 ∧ m = 1

set_option synthInstance.maxSize 1024 in
instance (p m : Nat) : Decidable (UsedPrimary p m) := by unfold UsedPrimary; infer_instance

def tableOK (n : Nat) : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | off, (p,m)::ps => decide (UsedPrimary p m) &&
      (List.range (fieldDegree p*m)).all (fun j =>
        Matrix.read (encoded n) (off+j) == (Matrix.read (prototype p) j &&& (2^n-1))) &&
      tableOK n (off+fieldDegree p*m) ps

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPrototype ====

-- ==== begin CRTPrototypeReceipt ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

private theorem p7m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 7 1 s.val b = true := by decide +kernel

private theorem p11m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 11 1 s.val b = true := by decide +kernel

private theorem p13m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 13 1 s.val b = true := by decide +kernel

private theorem p19m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 19 1 s.val b = true := by decide +kernel

private theorem p21m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 21 1 s.val b = true := by decide +kernel

private theorem p25m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 25 1 s.val b = true := by decide +kernel

private theorem p31m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 31 1 s.val b = true := by decide +kernel

private theorem p37m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 37 1 s.val b = true := by decide +kernel

private theorem p67m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 67 1 s.val b = true := by decide +kernel

private theorem p73m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 73 1 s.val b = true := by decide +kernel

private theorem p257m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 257 1 s.val b = true := by decide +kernel

private theorem p257m2 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 257 2 s.val b = true := by decide +kernel

private theorem p313m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 313 1 s.val b = true := by decide +kernel

private theorem p471m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 471 1 s.val b = true := by decide +kernel

private theorem p1193m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 1193 1 s.val b = true := by decide +kernel

private theorem p1571m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 1571 1 s.val b = true := by decide +kernel

private theorem p4593m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 4593 1 s.val b = true := by decide +kernel

private theorem p5349m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 5349 1 s.val b = true := by decide +kernel

private theorem p5981m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 5981 1 s.val b = true := by decide +kernel

private theorem p6891m1 : ∀ s : Fin 17, ∀ b : Bool, prototypeTest 6891 1 s.val b = true := by decide +kernel

theorem prototype_checked (p m : Nat) (hm : UsedPrimary p m) (slot : Fin 17) (mir : Bool) :
    prototypeTest p m slot.val mir = true := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact p7m1 slot mir
  · exact p11m1 slot mir
  · exact p13m1 slot mir
  · exact p19m1 slot mir
  · exact p21m1 slot mir
  · exact p25m1 slot mir
  · exact p31m1 slot mir
  · exact p37m1 slot mir
  · exact p67m1 slot mir
  · exact p73m1 slot mir
  · exact p257m1 slot mir
  · exact p257m2 slot mir
  · exact p313m1 slot mir
  · exact p471m1 slot mir
  · exact p1193m1 slot mir
  · exact p1571m1 slot mir
  · exact p4593m1 slot mir
  · exact p5349m1 slot mir
  · exact p5981m1 slot mir
  · exact p6891m1 slot mir

theorem prototype_size (p m : Nat) (hm : UsedPrimary p m) : fieldDegree p*m ≤ (prototype p).size := by
  rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide +kernel

theorem table_checked (n : Nat) (hn : UsedWidth n) : 15 ≤ n ∧ n ≤ 135 ∧ tableOK n 0 (schedule n) = true := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPrototypeReceipt ====

-- ==== begin CRTPackedRun ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Placement Field

theorem digit_pack (xs : List Nat) (q : Nat) (hq : q < xs.length)
    (bound : ∀ v ∈ xs, v < 2^width) : digit width (pack width xs) q = (xs[q]?).getD 0 := by
  induction xs generalizing q with
  | nil => simp at hq
  | cons a xs ih =>
    rw [pack]
    have low := bound a (List.mem_cons_self ..)
    cases q with
    | zero => exact digit_zero _ _ _ low
    | succ q =>
      rw [digit_succ _ _ _ _ low]
      apply ih _ (by simpa using hq) (fun v hv => bound v (List.mem_cons_of_mem _ hv))

theorem coded_matches (n dim k : Nat) (hd : dim ≤ width) : Matches (codedWord n dim k) (coded n dim k) := by
  have bound : ∀ v ∈ (coded n dim k).toList, v < 2^width := by
    intro v hv
    simp only [coded,Array.toList_map,List.mem_map] at hv
    obtain ⟨a,_,rfl⟩ := hv
    exact lt_of_le_of_lt Nat.and_le_right (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by decide : 0<1))
      (Nat.pow_le_pow_right (by decide) hd))
  intro q hq
  simpa only [codedWord,Matrix.read,Array.getElem?_toList] using
    (digit_pack (coded n dim k).toList q (by simpa using hq) bound).symm

theorem digit_put (x i q v : Nat) (hv : v < 2^width) : digit width (put x i v) q =
    if q = i then v else digit width x q := by
  rw [put,digit_xor,digit_single _ _ _ _ (Nat.xor_lt_two_pow (digit_bound ..) hv)]
  by_cases e : q=i <;> simp [e]

private theorem digit_replace (x q : Nat) (xs : List Nat) (v : Nat → Nat) (bound : ∀ j ∈ xs, v j < 2^width) :
    digit width (replace x xs v) q = if q ∈ xs then v q else digit width x q := by
  induction xs generalizing x with
  | nil => simp [replace]
  | cons a xs ih =>
    change digit width (replace (put x a (v a)) xs v) q = _
    rw [ih _ (fun j hj => bound j (List.mem_cons_of_mem _ hj)),digit_put _ _ _ _ (bound a (List.mem_cons_self ..))]
    by_cases ha : q=a <;> by_cases hx : q∈xs <;> simp [ha,hx]

private theorem fast_bound (p : Nat) (mir : Bool) (slot : Nat) (v : Nat → Nat) (q : Nat)
    (h : ∀ j, v j < 2^width) : fastScalar p mir slot v q < 2^width := by
  have fold (xs : List Nat) (a : Nat) (ha : a < 2^width) : xs.foldl (fun w j => w ^^^ v j) a < 2^width := by
    induction xs generalizing a with
    | nil => exact ha
    | cons j xs ih => exact ih _ (Nat.xor_lt_two_pow ha (h j))
  unfold fastScalar
  split
  · exact fold _ _ (h q)
  · exact h q

theorem digit_scalar (p : Nat) (mir : Bool) (slot off x q : Nat) :
    digit width (scalarWord x p mir slot off) q = if off ≤ q ∧ q < off+fieldDegree p then
      fastScalar p mir slot (fun j => digit width x (off+j)) (q-off) else digit width x q := by
  unfold scalarWord
  rw [digit_replace _ _ _ _ (fun j _ => fast_bound _ _ _ _ _ (fun _ => digit_bound ..))]
  have within : q ∈ (List.range (fieldDegree p)).map (off+·) ↔ off ≤ q ∧ q < off+fieldDegree p := by
    constructor
    · rintro hit
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hit
      exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (List.mem_range.mp hj) _⟩
    · rintro ⟨lo,hi⟩
      exact List.mem_map.mpr ⟨q-off,List.mem_range.mpr ((Nat.sub_lt_iff_lt_add lo).mpr (Nat.add_comm off _ ▸ hi)),Nat.add_sub_of_le lo⟩
  simp only [within]

theorem digit_cx (x a b q : Nat) : digit width (cxWord x (a,b)) q =
    if q = b then digit width x q ^^^ digit width x a else digit width x q := by
  rw [cxWord,digit_xor,digit_single _ _ _ _ (digit_bound ..)]
  by_cases eq : q = b <;> simp [eq]

private theorem scalar_matches (p : Nat) (mir : Bool) (slot off x : Nat) (r : Rows)
    (endp : off+fieldDegree p ≤ r.size) (h : Matches x r) :
    Matches (scalarWord x p mir slot off) (scalarRows r p mir slot off) := by
  intro q hq
  have sq : q < r.size := by simpa only [scalarRows_size] using hq
  let d := fieldDegree p
  let data := fun j => digit width x (off+j)
  let v := fun t => fastScalar p mir slot data (t-off)
  let xs := (List.range d).map (off+·)
  change Matrix.read (scalarRows r p mir slot off) q = digit width (replace x xs v) q
  rw [scalar_read sq,digit_replace _ _ _ _ (fun j _ => fast_bound _ _ _ _ _ (fun _ => digit_bound ..))]
  have loc : q ∈ xs ↔ off ≤ q ∧ q < off+fieldDegree p := by
    constructor
    · rintro hq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
      exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left (List.mem_range.mp hj) _⟩
    · rintro ⟨lo,hi⟩
      exact List.mem_map.mpr ⟨q-off,List.mem_range.mpr ((Nat.sub_lt_iff_lt_add lo).mpr (Nat.add_comm off d ▸ hi)),Nat.add_sub_of_le lo⟩
  simp only [loc]
  split
  · rename_i live
    have jBound : q-off < d := (Nat.sub_lt_iff_lt_add live.1).mpr (Nat.add_comm off d ▸ live.2)
    change scalarRow p mir _ _ _ = fastScalar p mir slot data (q-off)
    rw [←scalar_fast]
    apply accumulate_congr
    · exact h _ (lt_of_lt_of_le (Nat.add_lt_add_left jBound _) endp)
    · intro k j hj
      dsimp only
      rw [show Matrix.read r (off+j) = data j from h _ (lt_of_lt_of_le (Nat.add_lt_add_left hj _) endp)]
  · exact h q sq

private theorem cx_matches (x : Nat) (r : Rows) (p : Wire × Wire) (ha : p.1 < r.size) (hb : p.2 < r.size)
    (h : Matches x r) : Matches (cxWord x p) (applyPair r p) := by
  obtain ⟨a,b⟩ := p
  intro q hq
  have sq : q < r.size := by simpa only [applyPair_size] using hq
  rw [apply_read _ _ _ _ hb,cxWord,digit_xor,digit_single _ _ _ _ (digit_bound ..)]
  by_cases eq : q=b <;> simp [eq,h q sq,h a ha,h b hb]

private theorem fold_matches {α} (xs : List α) (f : Nat → α → Nat) (g : Rows → α → Rows) (n x : Nat) (r : Rows)
    (size : r.size=n) (h : Matches x r) (keep : ∀ r a, (g r a).size = r.size)
    (step : ∀ a∈xs, ∀ x r, r.size = n → Matches x r → Matches (f x a) (g r a)) :
    Matches (xs.foldl f x) (xs.foldl g r) := by
  induction xs generalizing x r with
  | nil => exact h
  | cons a xs ih =>
    exact ih _ _ ((keep r a).trans size) (step a (List.mem_cons_self ..) x r size h)
      (fun b hb => step b (List.mem_cons_of_mem _ hb))

private theorem stage_matches (n x slot off d m h : Nat) (mir : Bool) (r : Rows) (size : r.size=n)
    (endp : off+d*m ≤ n) (agree : Matches x r) :
    Matches (stageWord n x slot off d m h mir) (stageRows r slot off d m h mir) := by
  unfold stageWord stageRows
  rw [size]
  by_cases short : m ≤ 2^h
  · simpa only [if_pos short] using agree
  · simp only [if_neg short]
    split
    · apply fold_matches _ _ applyPair n _ _ size agree (fun _ _ => applyPair_size ..)
      intro p hp z a sz matcha
      obtain ⟨ha,hb⟩ := edit_bounds a off d m h mir (sz ▸ endp) p hp
      exact cx_matches z a p ha hb matcha
    · exact agree

private theorem r8Step_matches (n x slot off : Nat) (st : R8Step) (hg : r8StepGood st = true)
    (r : Rows) (size : r.size = n) (endp : off + 16 ≤ n) (agree : Matches x r) :
    Matches (r8StepWord n x slot off st) (r8StepRows r slot off st) := by
  unfold r8StepWord r8StepRows
  rw [size]
  split
  · apply fold_matches _ _ applyPair n _ _ size agree (fun _ _ => applyPair_size ..)
    intro p hp z a sz matcha
    obtain ⟨ha, hb, _⟩ := r8Ops_bounds a off st hg (sz ▸ endp) p hp
    exact cx_matches z a p ha hb matcha
  · exact agree

private theorem primary_matches (n x off p m slot : Nat) (mir : Bool) (r : Rows) (size : r.size=n)
    (endp : off+fieldDegree p*m ≤ n) (agree : Matches x r) :
    Matches (primaryWord n x off p m slot mir) (primaryRows r off p m slot mir) := by
  let d := fieldDegree p
  have scalar := fold_matches (List.range m) (fun a j => scalarWord a p mir slot (off+d*j))
    (fun a j => scalarRows a p mir slot (off+d*j)) n _ _ size agree (fun _ _ => scalarRows_size ..) (by
      intro j hj z a sz matcha
      have kj := Nat.mul_le_mul_left (fieldDegree p) (show j+1 ≤ m from List.mem_range.mp hj)
      rw [Nat.mul_succ] at kj
      exact scalar_matches p mir slot _ _ a (by dsimp [d]; rw [sz]; omega) matcha)
  unfold primaryWord primaryRows; dsimp only
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : fieldDegree p * m = 16 := by rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    unfold r8Rows
    apply fold_matches (pascalR8Steps mir) (fun a st => r8StepWord n a slot off st)
      (fun a st => r8StepRows a slot off st) n _ (scalars r p m off slot mir) ((scalars_size ..).trans size) scalar
      (fun _ _ => r8StepRows_size ..)
    exact fun st hst z a sz ma => r8Step_matches n z slot off st (List.all_eq_true.mp (pascalR8Steps_good mir) st hst) a sz (by omega) ma
  · rw [if_neg h82, if_neg h82]
    apply fold_matches (oriented mir (List.range 4)) _ (fun a h => stageRows a slot off d m h mir)
      n _ (scalars r p m off slot mir) ((scalars_size ..).trans size) scalar (fun _ _ => stageRows_size ..)
    exact fun h _ z a sz ma => stage_matches n z slot off d m h mir a sz endp ma

private theorem components_match (n x off slot : Nat) (mir : Bool) (ps : List (Nat × Nat)) (r : Rows)
    (size : r.size=n) (endp : off+extent ps ≤ n) (agree : Matches x r) :
    Matches (componentWord n mir slot off ps x) (componentRows mir slot off ps r) := by
  induction ps generalizing x r off with
  | nil => exact agree
  | cons pair tail ih =>
    obtain ⟨p,m⟩ := pair
    change off+(fieldDegree p*m+extent tail) ≤ n at endp
    exact ih _ _ _ ((primaryRows_size ..).trans size) (by omega)
      (primary_matches n x off p m slot mir r size (by omega) agree)

theorem action_of_digits (n slot : Nat) (hn : UsedWidth n) (bound : n ≤ width) (mir : Bool)
    (tested : ∀ q < n, digit width (componentWord n mir slot 0 (schedule n) (codedWord n (n-(slot-1)) (entryShift mir slot))) q =
      digit width (codedWord n (n-(slot-1)) (exitShift mir slot)) q) : ActionOK n slot mir := by
  let dim := n - (slot - 1)
  have hdim : dim ≤ width := by omega
  have src (k : Nat) : (coded n dim k).size = n := by
    rw [←encode_of_receipt n dim k (coordinates_checked n hn),applyOps_size,plain_size]
  let input := coded n dim (entryShift mir slot)
  let out := componentRows mir slot 0 (schedule n) input
  have exactRun : Matches (componentWord n mir slot 0 (schedule n) (codedWord n dim (entryShift mir slot))) out :=
    components_match n _ 0 slot mir (schedule n) input (src _) (by rw [schedule_extent n hn]; omega)
      (coded_matches n dim _ hdim)
  have outSize : out.size = n := (componentRows_size ..).trans (src _)
  change out = coded n dim (exitShift mir slot)
  apply Array.ext (outSize.trans (src _).symm)
  intro q ho he
  have result := (exactRun q ho).trans ((tested q (outSize ▸ ho)).trans (coded_matches n dim _ hdim q he).symm)
  simpa only [Matrix.read,Array.getElem?_eq_getElem ho,Array.getElem?_eq_getElem he,Option.getD_some] using result

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTPackedRun ====

-- ==== begin CRTSlice ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Field

structure Slice (f : Nat → Nat) (off len original bank block : Nat) : Prop where
  same : ∀ i < len, digit width bank (off+i) = f (digit width block i)
  exterior : ∀ q, (q < off ∨ off+len ≤ q) → digit width bank q = digit width original q

private theorem scalar_linear (p : Nat) (mir : Bool) (slot i : Nat) (hi : i < fieldDegree p) (f : Nat → Nat)
    (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (u v : Nat → Nat)
    (rel : ∀ j < fieldDegree p, u j = f (v j)) :
    fastScalar p mir slot u i = f (fastScalar p mir slot v i) := by
  rw [←scalar_fast,←scalar_fast]
  unfold scalarRow
  rw [map_accumulate p mir i f Nat.xor Nat.xor fx]
  apply accumulate_congr
  · exact rel i hi
  · intro k j hj
    by_cases hot : slot=k+1
    · simpa [hot] using rel j hj
    · simpa [hot] using fz.symm

theorem slice_scalar (p : Nat) (mir : Bool) (slot off len j original bank block : Nat) (f : Nat → Nat)
    (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) (endp : j+fieldDegree p ≤ len)
    (h : Slice f off len original bank block) :
    Slice f off len original (scalarWord bank p mir slot (off+j)) (scalarWord block p mir slot j) := by
  constructor
  · intro t ht
    rw [digit_scalar,digit_scalar]
    by_cases inside : j ≤ t ∧ t < j+fieldDegree p
    · have outer : off+j ≤ off+t ∧ off+t < off+j+fieldDegree p := by omega
      rw [if_pos outer, if_pos inside, show off+t-(off+j)=t-j by omega]
      apply scalar_linear _ _ _ _ ((Nat.sub_lt_iff_lt_add inside.1).mpr (Nat.add_comm j _ ▸ inside.2)) f fz fx
      intro z hz
      rw [Nat.add_assoc]
      exact h.same _ (by omega)
    · rw [if_neg inside, if_neg (show ¬(off+j ≤ off+t ∧ off+t < off+j+fieldDegree p) by omega)]
      exact h.same t ht
  · intro q exterior
    rw [digit_scalar,if_neg (by omega)]
    exact h.exterior q exterior

private theorem slice_cx (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (off len original bank block a b : Nat) (ha : a < len) (hb : b < len)
    (h : Slice f off len original bank block) :
    Slice f off len original (cxWord bank (off+a,off+b)) (cxWord block (a,b)) := by
  constructor
  · intro q hq
    rw [digit_cx,digit_cx]
    by_cases eq : q=b <;> simp [eq,h.same _ hq,h.same a ha,h.same b hb,fx]
  · intro q external
    rw [digit_cx,if_neg (by omega)]
    exact h.exterior q external

private theorem parity_map (xs : List Nat) (n s : Nat) :
    xorAt (flags n s) (xs.map (n+·)) = xorAt (fun k => decide (k<16 ∧ s=k+1)) xs := by
  induction xs with
  | nil => rfl
  | cons k xs ih => simp [xorAt,ih,flags]

theorem enabled_same (n m slot h : Nat) : enabled n slot h = enabled m slot h := by
  simp only [enabled,tagSources,parity_map]

private theorem shift_edits (off d m h : Nat) : editPairs off d m h =
    (editPairs 0 d m h).map (fun (a,b) => (off+a,off+b)) := by
  simp [editPairs,List.map_flatMap,List.map_map,Function.comp_def,Nat.add_assoc]

private theorem slice_stage (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off d m original bank block slot h : Nat) (mir : Bool) (prev : Slice f off (d*m) original bank block) :
    Slice f off (d*m) original (stageWord n bank slot off d m h mir) (stageWord (d*m) block slot 0 d m h mir) := by
  unfold stageWord
  rw [enabled_same n (d*m)]
  by_cases small : m ≤ 2^h
  · simpa only [if_pos small] using prev
  simp only [if_neg small]
  split
  · let ops := oriented mir (editPairs 0 d m h)
    have bounds : ∀ p ∈ ops, p.1 < d*m ∧ p.2 < d*m := by
      intro p hp
      simpa only [units,Array.size_ofFn] using edit_bounds (units (d*m)) 0 d m h mir (by simp [units]) p hp
    have shape : oriented mir (editPairs off d m h) = ops.map (fun (a,b) => (off+a,off+b)) := by
      rw [shift_edits]
      cases mir <;> simp [oriented,ops]
    rw [shape,List.foldl_map]
    change Slice f off (d*m) original (ops.foldl _ bank) (ops.foldl _ block)
    have run (xs : List (Nat × Nat)) (z t : Nat) (hz : Slice f off (d*m) original z t)
        (loc : ∀ e ∈ xs, e.1 < d*m ∧ e.2 < d*m) :
        Slice f off (d*m) original (xs.foldl (fun acc e => cxWord acc (off+e.1,off+e.2)) z) (xs.foldl cxWord t) := by
      induction xs generalizing z t with
      | nil => exact hz
      | cons e xs ih =>
        obtain ⟨a,b⟩ := e
        obtain ⟨ha,hb⟩ := loc (a,b) (List.mem_cons_self ..)
        exact ih _ _ (slice_cx f fx off _ original z t a b ha hb hz)
          (fun w hw => loc w (List.mem_cons_of_mem _ hw))
    exact run ops bank block prev bounds
  · exact prev

theorem r8Enabled_same (n m slot : Nat) (tags : List Nat) : r8Enabled n slot tags = r8Enabled m slot tags := by
  simp only [r8Enabled, parity_map]

private theorem shift_r8Ops (off : Nat) (st : R8Step) :
    r8Ops off st = (r8Ops 0 st).map (fun (a,b) => (off+a, off+b)) := by
  simp [r8Ops, List.map_append, List.map_reverse]

private theorem slice_r8Step (f : Nat → Nat) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off original bank block slot : Nat) (st : R8Step) (hg : Placement.r8StepGood st = true)
    (prev : Slice f off 16 original bank block) :
    Slice f off 16 original (r8StepWord n bank slot off st) (r8StepWord 16 block slot 0 st) := by
  unfold r8StepWord
  rw [r8Enabled_same n 16]
  split
  · have bounds : ∀ p ∈ r8Ops 0 st, p.1 < 16 ∧ p.2 < 16 := by
      intro p hp
      obtain ⟨h1, h2, _⟩ := r8Ops_bounds (units 16) 0 st hg (by simp [units]) p hp
      simpa [units] using And.intro h1 h2
    rw [shift_r8Ops, List.foldl_map]
    have run (xs : List (Nat × Nat)) (z t : Nat) (hz : Slice f off 16 original z t)
        (loc : ∀ e ∈ xs, e.1 < 16 ∧ e.2 < 16) :
        Slice f off 16 original (xs.foldl (fun acc e => cxWord acc (off+e.1,off+e.2)) z) (xs.foldl cxWord t) := by
      induction xs generalizing z t with
      | nil => exact hz
      | cons e xs ih =>
        obtain ⟨a,b⟩ := e
        obtain ⟨ha,hb⟩ := loc (a,b) (List.mem_cons_self ..)
        exact ih _ _ (slice_cx f fx off 16 original z t a b ha hb hz)
          (fun w hw => loc w (List.mem_cons_of_mem _ hw))
    exact run (r8Ops 0 st) bank block prev bounds
  · exact prev

theorem primary_slice (f : Nat → Nat) (fz : f 0 = 0) (fx : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (n off p m slot original bank block : Nat) (mir : Bool) (prev : Slice f off (fieldDegree p*m) original bank block) :
    Slice f off (fieldDegree p*m) original (primaryWord n bank off p m slot mir)
      (primaryWord (fieldDegree p*m) block 0 p m slot mir) := by
  let d := fieldDegree p
  have fold {α} (xs : List α) (g u : Nat → α → Nat) (b l : Nat) (rel : Slice f off (d*m) original b l)
      (one : ∀ a ∈ xs, ∀ b l, Slice f off (d*m) original b l → Slice f off (d*m) original (g b a) (u l a)) :
      Slice f off (d*m) original (xs.foldl g b) (xs.foldl u l) := by
    induction xs generalizing b l with
    | nil => exact rel
    | cons a xs ih => exact ih _ _ (one a (List.mem_cons_self ..) b l rel) (fun z hz => one z (List.mem_cons_of_mem _ hz))
  have sc : Slice f off (d*m) original
      ((List.range m).foldl (fun a j => scalarWord a p mir slot (off+d*j)) bank)
      ((List.range m).foldl (fun a j => scalarWord a p mir slot (0+d*j)) block) := by
    apply fold _ _ _ _ _ prev
    intro j hj b l carry
    have h := Nat.mul_le_mul_left d (show j+1 ≤ m from List.mem_range.mp hj)
    rw [Nat.mul_succ] at h
    simpa only [Nat.zero_add] using slice_scalar p mir slot off (d*m) (d*j) original b l f fz fx h carry
  unfold primaryWord; dsimp only
  by_cases h82 : (fieldDegree p == 8 && m == 2) = true
  · have h82' := h82; simp only [Bool.and_eq_true, beq_iff_eq] at h82'
    have h16 : d * m = 16 := by change fieldDegree p * m = 16; rw [h82'.1, h82'.2]
    rw [if_pos h82, if_pos h82]
    apply fold (pascalR8Steps mir) (fun a st => r8StepWord n a slot off st)
      (fun a st => r8StepWord (d*m) a slot 0 st) _ _ sc
    intro st hst b l carry
    rw [h16] at carry ⊢
    exact slice_r8Step f fx n off original b l slot st (List.all_eq_true.mp (Placement.pascalR8Steps_good mir) st hst) carry
  · rw [if_neg h82, if_neg h82]
    apply fold _ _ _ _ _ sc
    exact fun h _ b l carry => slice_stage f fx n off d m original b l slot h mir carry

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTSlice ====

-- ==== begin CRTTemplateAction ====
section

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed
open Matrix Placement

private theorem prototype_digit (p m dim k : Nat) (use : UsedPrimary p m) (hd : dim ≤ width) (q : Nat) (hq : q < fieldDegree p*m) :
    digit width (prototypeWord p m dim k) q = clipShift dim k (Matrix.read (prototype p) q) := by
  let xs := ((prototype p).toList.take (fieldDegree p*m)).map (clipShift dim k)
  have bound : ∀ a ∈ xs, a < 2^width := by
    intro a ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    exact lt_of_le_of_lt Nat.and_le_right (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos _) (by decide : 0<1))
      (Nat.pow_le_pow_right (by decide) hd))
  have len : xs.length = fieldDegree p*m := by simp [xs,Nat.min_eq_left (prototype_size p m use)]
  have h := digit_pack xs q (len ▸ hq) bound
  have inList : q < (prototype p).size := lt_of_lt_of_le hq (prototype_size p m use)
  simpa [xs,prototypeWord,Matrix.read,List.getElem?_map,List.getElem?_take,hq,inList] using h

private theorem clip_factor (n sh k v : Nat) (high : n ≤ 135) (hk : k ≤ sh) :
    clipShift (n-sh) k (v &&& (2^n-1)) = clipShift (n-sh) 0 (clipShift (135-sh) k v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [clipShift,Nat.testBit_and,Nat.testBit_two_pow_sub_one,Nat.testBit_shiftRight, Nat.zero_add]
  by_cases h : i < n-sh
  · simp [h,show k+i<n by omega,show i<135-sh by omega]
  · simp [h]

private theorem shift_le_slot (mir : Bool) (slot : Fin 17) :
    entryShift mir slot.val ≤ slot.val - 1 ∧ exitShift mir slot.val ≤ slot.val - 1 := by
  cases mir <;> simp [entryShift,exitShift]

private theorem digits_source (n sh off p m k : Nat) (use : UsedPrimary p m) (high : n ≤ 135)
    (sk : k ≤ sh) (size : (coded n (n-sh) k).size = n) (endp : off+fieldDegree p*m ≤ n)
    (table : ∀ j < fieldDegree p*m, Matrix.read (encoded n) (off+j) = (Matrix.read (prototype p) j &&& (2^n-1))) :
    ∀ j < fieldDegree p*m, digit width (codedWord n (n-sh) k) (off+j) = clipShift (n-sh) 0 (digit width (prototypeWord p m (135-sh) k) j) := by
  intro j hj
  have inner : off+j < n := by omega
  have sz : (encoded n).size = n := by simpa only [coded, Array.size_map] using size
  have h := (coded_matches n (n-sh) k (by unfold width; omega) (off+j) (by rwa [size])).symm
  rw [h,prototype_digit p m (135-sh) k use (by unfold width; omega) j hj]
  have readMap : Matrix.read (coded n (n-sh) k) (off+j) = clipShift (n-sh) k (Matrix.read (encoded n) (off+j)) := by
    simp [Matrix.read,coded,show off+j < (encoded n).size by rwa [sz]]
  rw [readMap,table j hj,clip_factor n sh k _ high sk]

theorem template_action (n : Nat) (hn : UsedWidth n) (slot : Fin 17) (mir : Bool) : ActionOK n slot.val mir := by
  obtain ⟨_low,high,checked⟩ := table_checked n hn
  let sh := slot.val - 1
  let dim := n - sh
  let pdim := 135 - sh
  let a := entryShift mir slot.val
  let b := exitShift mir slot.val
  let src := codedWord n dim a
  let dst := codedWord n dim b
  let crop := clipShift dim 0
  have sz (k : Nat) : (coded n dim k).size = n := by
    rw [←encode_of_receipt n dim k (coordinates_checked n hn),applyOps_size,plain_size]
  have ks := shift_le_slot mir slot
  have sweep (ps : List (Nat × Nat)) (off bank : Nat) (endp : off+extent ps = n) (hc : tableOK n off ps = true)
      (inv : ∀ q<n, digit width bank q = if q<off then digit width dst q else digit width src q) :
      ∀ q<n, digit width (componentWord n mir slot.val off ps bank) q = digit width dst q := by
    induction ps generalizing off bank with
    | nil =>
      change off+0 = n at endp
      intro q hq
      simpa only [componentWord,if_pos (show q<off by omega)] using inv q hq
    | cons pair tail ih =>
      obtain ⟨p,m⟩ := pair
      let len := fieldDegree p*m
      change off+(len+extent tail) = n at endp
      have endHead : off+len ≤ n := by omega
      simp only [tableOK,Bool.and_eq_true] at hc
      obtain ⟨⟨ok,tbl⟩,rest⟩ := hc
      have valid : UsedPrimary p m := of_decide_eq_true ok
      have rows (j : Nat) (hj : j<len) := beq_iff_eq.mp (List.all_eq_true.mp tbl j (List.mem_range.mpr hj))
      have left := digits_source n sh off p m a valid high ks.1 (sz _) endHead rows
      have right := digits_source n sh off p m b valid high ks.2 (sz _) endHead rows
      have before : Slice crop off len bank bank (prototypeWord p m pdim a) := by
        refine ⟨?_,fun _ _ => rfl⟩
        intro j hj
        rw [inv _ (by omega),if_neg (by omega)]
        exact left j hj
      have after := primary_slice crop (clip_zero dim 0) (clip_xor dim 0) n off p m slot.val bank bank _ mir before
      have expected : primaryWord len (prototypeWord p m pdim a) 0 p m slot.val mir = prototypeWord p m pdim b :=
        beq_iff_eq.mp (prototype_checked p m valid slot mir)
      rw [expected] at after
      change ∀ q<n, digit width (componentWord n mir slot.val (off+len) tail _) q = digit width dst q
      apply ih _ _ (by omega) rest
      intro q hq
      by_cases earlier : q < off
      · rw [after.exterior q (Or.inl earlier),inv q hq,if_pos earlier,if_pos (by omega)]
      · by_cases contained : q < off+len
        · have j : q-off < len := by omega
          have pos : off+(q-off) = q := Nat.add_sub_of_le (Nat.le_of_not_lt earlier)
          rw [if_pos contained,←pos,after.same _ j,right _ j]
        · rw [after.exterior q (Or.inr (Nat.le_of_not_lt contained)),inv q hq,if_neg earlier,if_neg contained]
  apply action_of_digits n slot.val hn (by unfold width; omega) mir
  exact sweep (schedule n) 0 src (by rw [schedule_extent n hn]; omega) checked (by simp [src])

end ECDSAAdd.Entrant.StairPacket.CRTBarrel.Packed

end
-- ==== end CRTTemplateAction ====

-- ==== begin CRTBarrelCorrect ====
section

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

namespace ECDSAAdd.Entrant.StairPacket.CRTBarrel
open Partial

/-- The forward barrel shifts every bank word with clear high padding, and its measured mirror
restores every forward image. Both preserve the exterior and the incoming phase on every tape. -/
theorem barrel_result (j : Fin 26) (lo : 0 ≤ j.val) (hi : j.val ≤ 24) (mir : Bool)
    (slot : Fin 17) (v : Nat) (s : State) (tape : List Bool)
    (small : v < 2^(barrelWidth (start j) - (slot.val - 1)))
    (input : HighBankBarrel.holds (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< entryShift mir slot.val) s)
    (tag : ∀ k : Fin 16, s.basis (tagsP.getD k.val 1560) = decide (slot.val = k.val+1))
    (scratch : ∀ k < 10, s.basis (Shadow7.poolW (start j) (17+k)) = false) :
    HighBankBarrel.Result (Shadow7.bankW (start j)) (barrelWidth (start j))
      (v <<< exitShift mir slot.val) s (run (barrel (start j) mir) tape s) := by
  let n := barrelWidth (start j)
  have hn : UsedWidth n := usedWidth j lo hi
  exact barrel_result_of_matrix j lo hi mir slot v s tape (coordinates_checked n hn)
    (Packed.template_action n hn slot mir) small input tag scratch

end ECDSAAdd.Entrant.StairPacket.CRTBarrel

end
-- ==== end CRTBarrelCorrect ====

-- ==== begin DeadJoinSemantic (credited to spariev 65b176b3) ====
-- Generic semantic factoring for the specialized leave; circuit definitions above are unchanged.
section

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-- Generic trajectory facts, independent of the admission structure in Main. -/
structure RawValid (s : State) (gs : List Gate) : Prop where
  physical : ∀ g ∈ gs, proper g = true
  prepared : Prepared s gs
  ready : Ready s gs

theorem RawValid.tail {s : State} {g : Gate} {gs : List Gate} (v : RawValid s (g::gs)) :
    RawValid (transition g s) gs :=
  ⟨fun x hx => v.physical x (List.mem_cons_of_mem _ hx),v.prepared.2,v.ready.2⟩

theorem RawValid.default_run {s : State} {gs : List Gate} (v : RawValid s gs) (m : List Bool) :
    run (GateMirror.forward gs) m s = run (GateMirror.forward gs) [] s := by
  induction gs generalizing s m with
  | nil => rfl
  | cons g gs ih =>
    change run ([front g] ++ GateMirror.forward gs) m s = run ([front g] ++ GateMirror.forward gs) [] s
    simp only [run_append,run_take,List.drop_nil]
    rw [head_default g s v.prepared.1 (v.physical _ List.mem_cons_self)]
    exact ih v.tail _

theorem RawValid.parts {s : State} {a b : List Gate} (ok : RawValid s (a++b)) :
    RawValid s a ∧ RawValid (run (GateMirror.forward a) [] s) b := by
  induction a generalizing s with
  | nil => exact ⟨⟨by simp,trivial,trivial⟩,ok⟩
  | cons g gs ih =>
    obtain ⟨left,right⟩ := ih ok.tail
    refine ⟨⟨fun x hx => ok.physical x (List.mem_append_left _ hx),⟨ok.prepared.1,left.prepared⟩,⟨ok.ready.1,left.ready⟩⟩,?_⟩
    change RawValid (run ([front g]++GateMirror.forward gs) [] s) b
    simpa only [run_append,run_take,List.drop_nil] using right

theorem RawValid.undo_run {s : State} {a : List Gate} (v : RawValid s a) (m n : List Bool) :
    run (GateMirror.inverse a) n (run (GateMirror.forward a) m s) = s :=
  invert a s v.physical v.prepared v.ready m n

theorem raw_append {s : State} {a b : List Gate} (va : RawValid s a)
    (vb : RawValid (run (GateMirror.forward a) [] s) b) : RawValid s (a++b) := by
  induction a generalizing s with
  | nil => exact vb
  | cons g gs ih =>
    have after : RawValid (run (GateMirror.forward gs) [] (transition g s)) b := by
      change RawValid (run ([front g]++GateMirror.forward gs) [] s) b at vb
      rw [run_append,run_take,List.drop_nil] at vb
      exact vb
    have rest := ih va.tail after
    exact ⟨fun x hx => by
      rcases List.mem_cons.mp hx with rfl | ht
      · exact va.physical _ List.mem_cons_self
      · exact rest.physical x ht,
      ⟨va.prepared.1,rest.prepared⟩,⟨va.ready.1,rest.ready⟩⟩

theorem raw_replace (a b c : List Gate) (fwd rev : Program) (s : State) (v : RawValid s (a++(b++c)))
    (same : ∀ t, run fwd t (run (GateMirror.forward a) [] s) = run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s))
    (back : ∀ t, run rev t (run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s)) = run (GateMirror.forward a) [] s) :
    (∀ m, run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s = run (GateMirror.forward (a++(b++c))) m s) ∧
    (∀ m n, run (GateMirror.inverse c ++ rev ++ GateMirror.inverse a) n (run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s) = s) := by
  obtain ⟨va,vbc⟩ := v.parts
  obtain ⟨vb,vc⟩ := vbc.parts
  let u := run (GateMirror.forward a) [] s
  let z := run (GateMirror.forward b) [] u
  have emitted (m : List Bool) : run (GateMirror.forward a ++ fwd ++ GateMirror.forward c) m s = run (GateMirror.forward c) [] z := by
    simp only [run_append,run_take,va.default_run,same]
    exact vc.default_run _
  have old (m : List Bool) : run (GateMirror.forward (a++(b++c))) m s = run (GateMirror.forward c) [] z := by
    simp only [forward_app,run_append,va.default_run,vb.default_run]
    exact vc.default_run _
  refine ⟨fun m => (emitted m).trans (old m).symm,?_⟩
  intro m n
  rw [emitted]
  have undoC (l : List Bool) : run (GateMirror.inverse c) l (run (GateMirror.forward c) [] z) = z := vc.undo_run [] l
  have undoB (l : List Bool) : run rev l z = u := back l
  simp only [run_append,run_take,undoC,undoB]
  exact va.undo_run [] _

theorem high_pair_identity (a sh tu : Wire) (s : State) (m : List Bool)
    (nd : [a,sh,tu].Nodup)
    (prepared : Prepared s [.cx sh tu,.cx tu sh,.pop a tu sh])
    (zero : s.basis sh = false) :
    run (GateMirror.forward [.cx sh tu,.cx tu sh,.pop a tu sh]) m s = s := by
  obtain ⟨has,hat,hst⟩ : a≠sh ∧ a≠tu ∧ sh≠tu := by simpa [and_assoc] using nd
  have clean : if s.basis a then s.basis sh=false else s.basis tu=false := by
    cases ha : s.basis a
    · have hv := prepared.2.2.1
      change (transition (.cx tu sh) (transition (.cx sh tu) s)).basis sh =
        ((transition (.cx tu sh) (transition (.cx sh tu) s)).basis a &&
          (transition (.cx tu sh) (transition (.cx sh tu) s)).basis tu) at hv
      simpa [transition,front,run,writeBit,Function.update,zero,ha,has,hat,hst,Ne.symm hst] using hv
    · simpa [ha] using zero
  have result := pair_runM false a sh tu nd s m clean
  change run (pairM false a sh tu) m s = s
  apply State.extensionality
  · exact result.1
  · funext q
    by_cases es : q=sh
    · subst q; exact result.2.2.1.trans zero.symm
    · by_cases et : q=tu
      · subst q; simpa [zero] using result.2.1
      · exact result.2.2.2 q es et

theorem raw_delete_identity {s : State} {a b c : List Gate} (v : RawValid s (a++(b++c)))
    (id : run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s) =
      run (GateMirror.forward a) [] s) : RawValid s (a++c) := by
  obtain ⟨va,vbc⟩ := v.parts
  obtain ⟨vb,vc⟩ := vbc.parts
  rw [id] at vc
  exact raw_append va vc

theorem raw_drop_identity (a b c : List Gate) (s : State) (v : RawValid s (a++(b++c)))
    (id : ∀ m, run (GateMirror.forward b) m (run (GateMirror.forward a) [] s) = run (GateMirror.forward a) [] s) :
    RawValid s (a++c) ∧
    (∀ m, run (GateMirror.forward (a++c)) m s = run (GateMirror.forward (a++(b++c))) m s) := by
  have w := raw_delete_identity v (id [])
  refine ⟨w,?_⟩
  intro m
  calc
    run (GateMirror.forward (a++c)) m s = run (GateMirror.forward (a++c)) [] s := w.default_run m
    _ = run (GateMirror.forward (a++(b++c))) [] s := by
      simp only [forward_app,run_append,run_take,List.drop_nil,id []]
    _ = run (GateMirror.forward (a++(b++c))) m s := (v.default_run m).symm

theorem dest_forward (gs : List Gate) :
    (GateMirror.forward gs).map LeaveReadoutFrame.destination = gs.map target := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [GateMirror.forward,List.map_cons] at ih ⊢
    rw [ih]
    cases g <;> rfl

theorem post_keeps (j : Fin 26) (hi : j.val≤24) (s : State) (m : List Bool) :
    (run (GateMirror.forward (postEntry (start j))) m s).basis (Shadow7.a0P (start j) - 1 + 16) =
      s.basis (Shadow7.a0P (start j) - 1 + 16) := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,e⟩ := List.mem_map.mp hit
  exact of_decide_eq_true (List.all_eq_true.mp (post_keeps_checked j hi) g hg) e

theorem pair_zero (j : Fin 26) (hi : j.val≤24) (s : State)
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j))) [] s).basis (Shadow7.a0P (start j) - 1 + 16) = false) :
    (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false := by
  rw [forward_app,run_append,run_take,List.drop_nil,post_keeps j hi]
  exact zero

theorem raw_reference_pair (j : Fin 26) (hi : j.val≤24) (s : State)
    (valid : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false) :
    RawValid s (shortenedOps (start j)) ∧
    (∀ m, run (GateMirror.forward (shortenedOps (start j))) m s = run (GateMirror.forward (referenceOps (start j))) m s) := by
  let a := LeaveJ7.entryOps (start j) ++ postEntry (start j)
  have shape : referenceOps (start j) = a ++ (pair16 (start j) ++ afterWord (start j)) := by
    rw [reference_shape j hi]; simp only [a,List.append_assoc]
  rw [shape] at valid
  have vb := valid.parts.2.parts.1
  have same (m : List Bool) : run (GateMirror.forward (pair16 (start j))) m
      (run (GateMirror.forward a) [] s) = run (GateMirror.forward a) [] s :=
    high_pair_identity _ _ _ _ m (pair_layout_checked j hi) vb.prepared zero
  obtain ⟨w,pair⟩ := raw_drop_identity a (pair16 (start j)) (afterWord (start j)) s valid same
  exact ⟨w,by simpa only [shortenedOps,a,shape,List.append_assoc] using pair⟩

theorem raw_prefix_replace {s : State} {a b anew : List Gate}
    (v : RawValid s (a++b)) (phys : ∀ g∈anew,proper g=true) (ready : Ready s anew)
    (same : ∀ m,run (GateMirror.forward anew) m s=run (GateMirror.forward a) [] s) :
    RawValid s (anew++b) ∧
    (∀ m,run (GateMirror.forward (anew++b)) m s=run (GateMirror.forward (a++b)) m s) := by
  have quiet (m : List Bool) : (run (GateMirror.forward anew) m s).phase=s.phase :=
    (congrArg State.phase (same m)).trans (no_phase a s)
  have va : RawValid s anew := ⟨phys,all_prepared anew s phys quiet,ready⟩
  have vb := v.parts.2
  rw [←same []] at vb
  have w := raw_append va vb
  refine ⟨w,?_⟩
  intro m
  calc
    run (GateMirror.forward (anew++b)) m s = run (GateMirror.forward (anew++b)) [] s := w.default_run m
    _ = run (GateMirror.forward (a++b)) [] s := by
      simp only [forward_app,run_append,run_take,List.drop_nil,same]
    _ = run (GateMirror.forward (a++b)) m s := (v.default_run m).symm

theorem scan_ready (s h : Nat) (st : State) : Ready st (DeadScan.fix0M s h) :=
  ready_plain _ (by simp [DeadScan.fix0M,Shadow7.fix0P,plainGate]) st

theorem raw_scan_join_valid (j : Fin 26) (hi : j.val≤24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s) :
    RawValid s (scanShortenedOps (start j)) ∧
    (∀ m,run (GateMirror.forward (scanShortenedOps (start j))) m s=
      run (GateMirror.forward (referenceOps (start j))) m s) := by
  obtain ⟨v,same⟩ := raw_reference_pair j hi s original zero
  rw [shortened_scan_shape] at v
  have phys : ∀ x∈DeadScan.fix0M (start j) (Shadow7.sbP (start j)),proper x=true :=
    fun x hx => List.all_eq_true.mp (scan_physical j hi) x hx
  obtain ⟨w,eq⟩ := raw_prefix_replace v phys (scan_ready _ _ s) scanEq
  refine ⟨w,?_⟩
  intro m
  exact (eq m).trans (by rw [←shortened_scan_shape]; exact same m)

theorem flag_geometry : ∀ j : Fin 26, j.val≤24 →
    (Shadow7.e0P (start j)+3 : Wire) ≠ Shadow7.e0P (start j)+4 ∧
    (Shadow7.e0P (start j)+6 : Wire) ≠ Shadow7.e0P (start j)+3 ∧
    (Shadow7.e0P (start j)+6 : Wire) ≠ Shadow7.e0P (start j)+4 ∧
    (Shadow7.e0P (start j)+3 : Wire) ≠ 1559 ∧ (Shadow7.e0P (start j)+4 : Wire) ≠ 1559 := by decide +kernel

theorem raw_all_valid (j : Fin 26) (hi : j.val≤24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s)
    (rel : FlagLeave.Rel (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) false s) :
    RawValid s (allOps (start j)) ∧
    (∀ m,run (GateMirror.forward (allOps (start j))) m s=run (GateMirror.forward (referenceOps (start j))) m s) ∧
    run (GateMirror.forward (beforeAll (start j))) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s := by
  obtain ⟨fu,cf,cu,fl,ul⟩ := flag_geometry j hi
  obtain ⟨v,same⟩ := raw_scan_join_valid j hi s original zero scanEq
  obtain ⟨phys,prepared,ready,eq⟩ := FlagLeave.cut_valid _ _ _ 1559 2 false
    (scanShortenedOps (start j)) s ⟨fu,cf,cu⟩ fl ul (all_checked j hi) rel v.physical v.prepared v.ready
  have w : RawValid s (allOps (start j)) := ⟨phys,prepared,ready⟩
  refine ⟨w,?_,?_⟩
  · intro m
    exact (w.default_run m).trans (eq.trans ((v.default_run m).symm.trans (same m)))
  · rw [scan_shortened_shape] at v
    have vb := v.parts.1
    have flagEq := (FlagLeave.cut_valid _ _ _ 1559 2 false (beforeScan (start j)) s ⟨fu,cf,cu⟩ fl ul
      (before_all_checked j hi) rel vb.physical vb.prepared vb.ready).2.2.2
    apply flagEq.trans
    have before_shape : CRTBarrel.beforeReference (start j) =
        Shadow7.fix0P (start j) (Shadow7.sbP (start j)) ++ beforeScanTail (start j) := by
      simp only [CRTBarrel.beforeReference,beforeScanTail,List.append_assoc]
    rw [beforeScan,before_shape,forward_app,forward_app,run_append,run_append,run_take,run_take,
      List.drop_nil,scanEq []]
    simp only [List.drop_nil]

theorem raw_crt_all_pair (j : Fin 26) (hi : j.val≤24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s)
    (rel : FlagLeave.Rel (Shadow7.e0P (start j)+3) (Shadow7.e0P (start j)+4) (Shadow7.e0P (start j)+6) false s)
    (barrelSame : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s))
    (barrelBack : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s)) =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s) :
    (∀ m,run (GateMirror.forward (beforeAll (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (afterAll (start j))) m s=
      run (GateMirror.forward (referenceOps (start j))) m s) ∧
    (∀ m n,run (GateMirror.inverse (afterAll (start j)) ++ CRTBarrel.barrel (start j) true ++ GateMirror.inverse (beforeAll (start j))) n
      (run (GateMirror.forward (beforeAll (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (afterAll (start j))) m s)=s) := by
  obtain ⟨v,same,beforeEq⟩ := raw_all_valid j hi s original zero scanEq rel
  rw [all_split j hi] at v
  have same' : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (beforeAll (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (beforeAll (start j))) [] s) := by
    simpa only [beforeEq] using barrelSame
  have back' : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (beforeAll (start j))) [] s)) =
      run (GateMirror.forward (beforeAll (start j))) [] s := by
    simpa only [beforeEq] using barrelBack
  obtain ⟨f,r⟩ := raw_replace _ _ _ _ _ s v same' back'
  exact ⟨fun m => (f m).trans (by rw [←all_split j hi]; exact same m),r⟩

end ECDSAAdd.Entrant.StairPacket.DeadJoin

end
-- ==== end DeadJoinSemantic ====

-- ==== begin FlagCut57Semantic (credited to ercumentyildirim ae9d602d) ====
section
namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

theorem raw_swap_mid {s : State} {a b b' c : List Gate}
    (v : RawValid s (a ++ (b ++ c)))
    (vb' : RawValid (run (GateMirror.forward a) [] s) b')
    (eq : run (GateMirror.forward b') [] (run (GateMirror.forward a) [] s) =
          run (GateMirror.forward b) [] (run (GateMirror.forward a) [] s)) :
    RawValid s (a ++ (b' ++ c)) ∧
    (∀ m, run (GateMirror.forward (a ++ (b' ++ c))) m s = run (GateMirror.forward (a ++ (b ++ c))) m s) := by
  obtain ⟨va, vbc⟩ := v.parts
  obtain ⟨vb, vc⟩ := vbc.parts
  have vc' : RawValid (run (GateMirror.forward b') [] (run (GateMirror.forward a) [] s)) c := by
    rwa [eq]
  have w : RawValid s (a ++ (b' ++ c)) := raw_append va (raw_append vb' vc')
  refine ⟨w, fun m => ?_⟩
  calc
    run (GateMirror.forward (a ++ (b' ++ c))) m s
        = run (GateMirror.forward (a ++ (b' ++ c))) [] s := w.default_run m
    _ = run (GateMirror.forward (a ++ (b ++ c))) [] s := by
        simp only [forward_app, run_append, run_take, List.drop_nil, eq]
    _ = run (GateMirror.forward (a ++ (b ++ c))) m s := (v.default_run m).symm

theorem keeps_of_targets57 (gs : List Gate) (q : Wire) (h : ∀ g ∈ gs, target g ≠ q) (m : List Bool) (t : State) :
    (run (GateMirror.forward gs) m t).basis q = t.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  intro hit
  obtain ⟨g, hg, e⟩ := List.mem_map.mp hit
  exact h g hg e

theorem swap_make57 (t x y : Wire) (u : State) (hxy : x ≠ y) (htx : t ≠ x) (hty : t ≠ y) (hy : u.basis y = false) :
    run (GateMirror.forward [.make t x y, .cx y x]) [] u =
    run (GateMirror.forward [.cx x y, .ccx t y x, .cx x y]) [] u := by
  obtain ⟨ph, f⟩ := u
  simp only at hy
  simp only [GateMirror.forward, List.map, GateMirror.front, run, State.mk.injEq, true_and]
  funext q
  by_cases hqx : q = x
  · subst hqx
    cases h1 : f q <;> cases h2 : f t <;>
      simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy]
  · by_cases hqy : q = y
    · subst hqy
      cases h1 : f x <;> cases h2 : f t <;>
        simp [writeBit, Function.update_apply, hxy, htx, hty, Ne.symm hxy, Ne.symm htx, Ne.symm hty, h1, h2, hy, hqx]
    · simp [writeBit, Function.update_apply, hqx, hqy]

theorem row0_distinct57 : ∀ j : Fin 26, j.val ≤ 24 →
    (Shadow7.a0P (start j) - 1 + 0 : Wire) ≠ Shadow7.e0P (start j) + 6 ∧
    (tagsP.getD 0 0 : Wire) ≠ Shadow7.a0P (start j) - 1 + 0 ∧
    (tagsP.getD 0 0 : Wire) ≠ Shadow7.e0P (start j) + 6 := by decide +kernel

theorem pre5Cut_targets : ∀ j : Fin 26, j.val ≤ 24 →
    (beforePre5Cut (start j)).all (fun g => decide (target g ≠ Shadow7.e0P (start j) + 6)) = true := by decide +kernel

theorem lowRest7_1558 (s : Nat) (t : State) :
    (run (GateMirror.forward (lowRest7 s)) [] t).basis 1558 = false := by
  obtain ⟨X, hX⟩ : ∃ X, lowRest7 s =
      X ++ [.pop (Shadow7.b0P s - 1) 1557 1558, .cx (Shadow7.a0P s - 1) 1557, .x 1557] := ⟨_, rfl⟩
  rw [hX, forward_app, run_append, run_take, List.drop_nil]
  generalize run (GateMirror.forward X) [] t = u
  obtain ⟨ph, f⟩ := u
  simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit, Function.update_apply]

theorem storeHead7_targets : ∀ j : Fin 26, j.val ≤ 24 →
    ((storeHead7 (start j)).drop 1).all (fun g => decide (target g ≠ 1558)) = true := by decide +kernel

theorem afterPre7Tail_1558 (j : Fin 26) (hi : j.val ≤ 24) (t : State) :
    (run (GateMirror.forward (afterPre7Tail (start j))) [] t).basis 1558 = true := by
  have hT := List.all_eq_true.mp (storeHead7_targets j hi)
  have e : storeHead7 (start j) = [.x 1558] ++ (storeHead7 (start j)).drop 1 := rfl
  rw [afterPre7Tail, forward_app, run_append, run_take, List.drop_nil, e, forward_app, run_append, run_take, List.drop_nil]
  rw [keeps_of_targets57 _ _ (fun g hg => of_decide_eq_true (hT g hg))]
  have z := lowRest7_1558 (start j) t
  generalize run (GateMirror.forward (lowRest7 (start j))) [] t = u at z ⊢
  obtain ⟨ph, f⟩ := u
  simp only at z
  simp [GateMirror.forward, GateMirror.front, run, writeBit, Function.update_apply, z]

theorem chainMid7_targets (s : Nat) : ∀ g ∈ chainMid7 s, target g ≠ 1558 := by
  have hb : AllAT (fun _ => True) (fun q => q ≠ 1558)
      [GateMirror.Gate.cx (Shadow7.storeW s (Shadow7.liveW s - Shadow7.lowsP s + 1)) 1557, GateMirror.Gate.x 1557] :=
    allAT_cons (ok_cx (A := fun _ => True) (T := fun q => q ≠ 1558) trivial (by decide))
      (allAT_cons (ok_x (A := fun _ => True) (T := fun q => q ≠ 1558) (by decide)) allAT_nil)
  have h := allAT_chainG (A := fun _ => True) (T := fun q => q ≠ 1558) (Shadow7.storeW s)
    (fun i => if i = 0 then Shadow7.a0P s + Shadow7.lowsP s - 2 else Shadow7.bankW s (Shadow7.lowsP s + i - 1)) _ hb
    1 (Shadow7.liveW s - Shadow7.lowsP s)
    (fun k h1 h2 => ⟨trivial, fun hk => by
      simp only [Shadow7.storeW, Partial.storeW]; split_ifs <;> ((try unfold Wire at *); omega)⟩)
    (fun _ _ _ => trivial)
  intro g hg
  exact (h g hg).2

theorem make_cx_1558 (top : Wire) (u : State) (h1558 : u.basis 1558 = true) :
    run (GateMirror.forward [.cx top 1559]) [] u =
    run (GateMirror.forward [.make 1558 top 1559]) [] u := by
  simp [GateMirror.forward, GateMirror.front, run, writeBit, h1558]

theorem pop_cx_1558 (top : Wire) (u : State) (h1558 : u.basis 1558 = true)
    (val : ValueOK u (.pop 1558 top 1559)) :
    run (GateMirror.forward [.cx top 1559]) [] u =
    run (GateMirror.forward [.pop 1558 top 1559]) [] u := by
  change u.basis 1559 = (u.basis 1558 && u.basis top) at val
  rw [h1558, Bool.true_and] at val
  simp [GateMirror.forward, GateMirror.front, GateMirror.erase, run, measureAndCorrect, ECDSAAdd.correct, writeBit, val]

end ECDSAAdd.Entrant.StairPacket.DeadJoin

-- ==== begin KeptParity semantics (credited to GordoAR a2ce2c3a) ====
namespace ECDSAAdd.Entrant.StairPacket.KeptParity
open Arithmetic Partial GateMirror Challenge

set_option maxRecDepth 16000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false

/-- The digit is active on one of the first eight rows when it is set. -/
def relation (v : BasisState) : Prop :=
  (v 1 && v 0) = (v 0 ^^ (v 2 && v 0) ^^ (v 3 && v 0) ^^ (v 4 && v 0) ^^ (v 5 && v 0) ^^ (v 6 && v 0) ^^ (v 7 && v 0) ^^ (v 8 && v 0))

def tag (k : LeaveSelector.Mode) (i : Nat) := LeaveSelector.enabled k && decide (i = LeaveSelector.key k)
def digitBit (k : LeaveSelector.Mode) (cross sign : Bool) :=
  ((LeaveSelector.enabled k ^^ cross) ^^ sign) ^^ (cross && sign)

private theorem finiteModes : ∀ (k : LeaveSelector.Mode) (cross sign : Bool),
    (k.val = 0 → cross = false ∧ sign = false) → (8 ≤ LeaveSelector.key k → sign = true) →
    let digit := digitBit k cross sign
    (tag k 0 && digit) = (digit ^^ (tag k 1 && digit) ^^ (tag k 2 && digit) ^^ (tag k 3 && digit) ^^ (tag k 4 && digit) ^^ (tag k 5 && digit) ^^ (tag k 6 && digit) ^^ (tag k 7 && digit)) := by decide +kernel

theorem relationOfMode (v : BasisState) (k : LeaveSelector.Mode) (cross sign : Bool)
    (inactive : k.val = 0 → cross = false ∧ sign = false) (high : 8 ≤ LeaveSelector.key k → sign = true)
    (digit : v 0 = digitBit k cross sign) (ports : ∀ i, i < 8 → v (i+1) = tag k i) : relation v := by
  unfold relation
  rw [ports 0 (by decide), ports 1 (by decide), ports 2 (by decide), ports 3 (by decide), ports 4 (by decide), ports 5 (by decide), ports 6 (by decide), ports 7 (by decide), digit]
  exact finiteModes k cross sign inactive high

private def shifted (s : State) (x : Bool) : State :=
  ⟨s.phase, writeBit s.basis 9 (s.basis 9 ^^ x)⟩

private def bareStep (h y : Wire) (s : State) : State :=
  ⟨s.phase, writeBit s.basis y (s.basis y ^^ (s.basis h && s.basis 0))⟩

private theorem twice (a b c d : Bool) : (((a ^^ b) ^^ c) ^^ (c ^^ d)) = (a ^^ (b ^^ d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem liftedStep (h y : Wire) (hn : h ≠ 9) (yn : y ≠ 9) (s : State) (x : Bool)
    (tail : Program) (m : List Bool) :
    run (.CX y 9 :: .CCX h 0 y :: .CX y 9 :: tail) m (shifted s x) =
      run tail m (shifted (bareStep h y s) (x ^^ (s.basis h && s.basis 0))) := by
  simp only [run]
  apply congrArg (run tail m)
  apply State.extensionality
  · rfl
  funext q
  by_cases endBit : q = 9
  · subst q
    simp [shifted, bareStep, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn, twice]
  · by_cases dataBit : q = y
    · subst q
      simp [shifted, bareStep, writeBit, Function.update_of_ne, hn, yn, Ne.symm yn]
    · simp [shifted, bareStep, writeBit, Function.update_of_ne, endBit, dataBit]

private def bare (i : Nat) (n : Nat) : Program :=
  match n with
  | 0 => []
  | n+1 => .CCX (i+2) 0 (i+10) :: bare (i+1) n

private def lifted (i : Nat) (n : Nat) : Program :=
  match n with
  | 0 => []
  | n+1 => .CX (i+10) 9 :: .CCX (i+2) 0 (i+10) :: .CX (i+10) 9 :: lifted (i+1) n

private def parity (v : BasisState) (i n : Nat) (x : Bool) : Bool :=
  match n with
  | 0 => x
  | n+1 => parity v (i+1) n (x ^^ (v (i+2) && v 0))

private theorem ladder (v : BasisState) (m : List Bool) (i n : Nat) (bound : i+n ≤ 7)
    (s : State) (keep : ∀ q : Nat, q ≤ 8 → s.basis q = v q) (x : Bool) :
    run (lifted i n) m (shifted s x) = shifted (run (bare i n) m s) (parity v i n x) := by
  induction n generalizing i s x with
  | zero => rfl
  | succ n ih =>
    have hn : (i+2 : Wire) ≠ 9 := by unfold Wire at *; omega
    have yn : (i+10 : Wire) ≠ 9 := by unfold Wire at *; omega
    simp only [lifted, bare, parity, liftedStep _ _ hn yn, run]
    rw [← keep (i+2) (by omega), ← keep 0 (by decide)]
    apply ih (i+1) (by omega) (bareStep (i+2) (i+10) s)
    intro q hq
    have ne : (q : Wire) ≠ i+10 := by unfold Wire at *; omega
    simpa [bareStep, writeBit, Function.update_of_ne ne] using keep q hq

private theorem parity_left (v : BasisState) (i n : Nat) (a b : Bool) :
    parity v i n (a ^^ b) = (a ^^ parity v i n b) := by
  induction n generalizing i b with
  | zero => rfl
  | succ n ih => simp only [parity, Bool.xor_assoc, ih]

private theorem shift_shift (s : State) (a b : Bool) : shifted (shifted s a) b = shifted s (a ^^ b) := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 9
  · subst q; simp [shifted, writeBit, Bool.xor_assoc]
  · simp [shifted, writeBit, Function.update_of_ne h]

private theorem shift_zero (s : State) : shifted s false = s := by
  apply State.extensionality
  · rfl
  funext q
  by_cases h : q = 9
  · subst q; simp [shifted, writeBit]
  · simp [shifted, writeBit, Function.update_of_ne h]

theorem same (s : State) (m : List Bool) (mode : relation s.basis) :
    run (GateMirror.forward replacement) m s = run (GateMirror.forward old) m s := by
  have newProgram : GateMirror.forward replacement = .CX 0 9 :: lifted 0 7 := rfl
  have oldProgram : GateMirror.forward old = .CCX 1 0 9 :: bare 0 7 := rfl
  rw [newProgram, oldProgram]
  let top := s.basis 1 && s.basis 0
  let t := shifted s top
  change run (lifted 0 7) m (shifted s (s.basis 0)) = run (bare 0 7) m t
  have prepared : shifted t (top ^^ s.basis 0) = shifted s (s.basis 0) := by
    rw [show shifted t _ = shifted s (top ^^ (top ^^ s.basis 0)) from shift_shift _ _ _]
    congr 1
    cases top <;> cases s.basis 0 <;> rfl
  have keep (q : Nat) (hq : q ≤ 8) : t.basis q = s.basis q := by
    have ne : (q : Wire) ≠ 9 := by unfold Wire at *; omega
    simp [t, shifted, writeBit, Function.update_of_ne ne]
  have parityEq : parity s.basis 0 7 (s.basis 0) = top := mode.symm
  rw [← prepared, ladder s.basis m 0 7 (by decide) t keep, parity_left, parityEq, Bool.xor_self, shift_zero]

private theorem geometry : ∀ j : Fin 26, j.val ≤ 24 → ∀ (a b : Fin 17), port (start j) a = port (start j) b → a = b := by
  decide +kernel

private theorem rename_eq (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (p q : Program) (hp : wires p ⊆ S) (hq : wires q ⊆ S)
    (mp mq : List Bool) (t s : State) (hph : t.phase = s.phase)
    (hb : ∀ a ∈ S, t.basis a = s.basis (f a))
    (heq : run p mp t = run q mq t) :
    run (renameProgram f p) mp s = run (renameProgram f q) mq s := by
  have rp := run_rename_pool f S hf p hp mp t s hph hb
  have rq := run_rename_pool f S hf q hq mq t s hph hb
  have hph_eq : (run (renameProgram f p) mp s).phase = (run (renameProgram f q) mq s).phase := by
    rw [rp.1, rq.1, heq]
  have hb_eq : (run (renameProgram f p) mp s).basis = (run (renameProgram f q) mq s).basis := by
    funext w
    by_cases hw : w ∈ S.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      rw [rp.2 a ha, rq.2 a ha, heq]
    · rw [run_rename_pool_outside f S p hp mp s w hw, run_rename_pool_outside f S q hq mq s w hw]
  cases h1 : run (renameProgram f p) mp s
  cases h2 : run (renameProgram f q) mq s
  rw [h1, h2] at hph_eq hb_eq
  simp only at hph_eq hb_eq
  rw [hph_eq, hb_eq]

set_option maxRecDepth 16000 in
/-- The parity pass runs like the kept pass, and is a valid trajectory, when `relation` holds at its input. -/
theorem placed_pair (j : Fin 26) (hi : j.val ≤ 24) (s : State) (h : relation (fun q => s.basis (port (start j) q))) :
    (∀ m, run (GateMirror.forward (placed (start j))) m s = run (GateMirror.forward (Shadow7.moveKept (start j))) [] s) ∧
    DeadJoin.RawValid s (placed (start j)) := by
  let f := port (start j)
  let t : State := ⟨s.phase, fun q => s.basis (f q)⟩
  have inj (a : Wire) (ha : a ∈ Finset.range 17) (b : Wire) (hb : b ∈ Finset.range 17)
      (eq : f a = f b) : a = b :=
    congrArg Fin.val (geometry j hi ⟨a, Finset.mem_range.mp ha⟩ ⟨b, Finset.mem_range.mp hb⟩ eq)
  have sameF (m : List Bool) : run (GateMirror.forward (placed (start j))) m s =
      run (GateMirror.forward (Shadow7.moveKept (start j))) [] s := by
    have eq : run (GateMirror.forward replacement) m t = run (GateMirror.forward old) [] t :=
      (same t m h).trans (run_take (GateMirror.forward old) m t).symm
    have boundedNew : wires (GateMirror.forward replacement) ⊆ Finset.range 17 := by decide
    have boundedOld : wires (GateMirror.forward old) ⊆ Finset.range 17 := by decide
    exact rename_eq f (Finset.range 17) inj _ _ boundedNew boundedOld m [] t s rfl (fun _ _ => rfl) eq
  have phys : ∀ g ∈ placed (start j), proper g = true := List.all_eq_true.mp (physical j hi)
  refine ⟨sameF, ⟨phys, ?_, ready_plain _ (by rfl) _⟩⟩
  exact all_prepared _ s phys (fun m => (congrArg State.phase (sameF m)).trans (no_phase _ s))

end ECDSAAdd.Entrant.StairPacket.KeptParity

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
-- ==== end KeptParity semantics ====

end ECDSAAdd.Entrant.StairPacket.DeadJoin

-- ==== begin SelectorReceiver semantics (credited to spariev 59c20890) ====
namespace ECDSAAdd.Entrant.StairPacket.DI7Affine
open Arithmetic Partial GateMirror DeadJoin
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
theorem clear_valid (c : Bool) (qs : List Wire) (t : Wire) (away : ∀ q∈qs,q≠t) (s : State) :
    RawValid s (clear c qs t) := by
  have phys : Proper (clear c qs t) := by
    intro g hg
    simp only [clear,List.mem_append] at hg
    rcases hg with hx | hc
    · cases c <;> simp_all [proper]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      simpa [proper] using away q hq
  have plain : ∀ g∈clear c qs t,plainGate g=true := by
    intro g hg
    simp only [clear,List.mem_append] at hg
    rcases hg with hx | hc
    · cases c <;> simp_all [plainGate]
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
      rfl
  exact ⟨phys,all_prepared _ s phys (fun m => by simp only [clear_run c qs t away]),ready_plain _ (List.all_eq_true.mpr plain) s⟩

/-- Replace a prepared pop with its preserved XOR receiver, transporting the
whole basis, phase, and both independent inverse measurement tapes. -/
theorem raw_replace_pop (a b : List Gate) (x y t : Wire) (c : Bool) (qs : List Wire)
    (s : State) (v : RawValid s (a ++ (Gate.pop x y t :: b)))
    (away : ∀ q∈qs,q≠t)
    (rel : eval (c,t::qs) (run (GateMirror.forward a) [] s).basis=false) :
    RawValid s (a ++ (clear c qs t ++ b)) ∧
    (∀ m,run (GateMirror.forward (a ++ (clear c qs t ++ b))) m s=
      run (GateMirror.forward (a ++ (Gate.pop x y t :: b))) m s) := by
  let u := run (GateMirror.forward a) [] s
  have va := v.parts.1
  have vb := v.parts.2.tail
  have e : run (GateMirror.forward (clear c qs t)) [] u = transition (Gate.pop x y t) u := by
    rw [clear_run c qs t away]
    have z : (u.basis t ^^ (c ^^ parity qs u.basis))=false := by
      change (c ^^ (u.basis t ^^ parity qs u.basis))=false at rel
      have shuffle (c t p : Bool) : (c ^^ (t ^^ p)) = (t ^^ (c ^^ p)) := by
        cases c <;> cases t <;> cases p <;> rfl
      rw [←shuffle]; exact rel
    simp only [z,transition,front,erase,run,measureAndCorrect,ECDSAAdd.correct,
      List.headD,Bool.false_and,Bool.xor_false,Bool.false_eq_true,if_false]
  rw [←e] at vb
  have w := raw_append va (raw_append (clear_valid c qs t away u) vb)
  refine ⟨w,?_⟩
  intro m
  rw [w.default_run m,v.default_run m]
  simp only [forward_app,run_append,run_take,List.drop_nil]
  change run (GateMirror.forward b) [] (run (GateMirror.forward (clear c qs t)) [] u) =
    run (GateMirror.forward b) [] (transition (Gate.pop x y t) u)
  rw [e]

end ECDSAAdd.Entrant.StairPacket.DI7Affine

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge DI7Affine
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem keeps_targets (gs : List Gate) (q : Wire) (h : ∀ g∈gs,target g≠q) (s : State) :
    (run (GateMirror.forward gs) [] s).basis q=s.basis q := by
  apply LeaveReadoutFrame.preserved
  rw [dest_forward]
  rintro hit
  obtain ⟨g,hg,eq⟩ := List.mem_map.mp hit
  exact h g hg eq

theorem expr_kept (gs : List Gate) (e : Expr)
    (h : gs.all (fun g => !e.2.contains (target g))=true) (s : State) :
    eval e (run (GateMirror.forward gs) [] s).basis=eval e s.basis := by
  unfold eval
  rw [parity_congr e.2 _ _]
  intro q hq
  apply keeps_targets
  intro g hg eq
  have hh := List.all_eq_true.mp h g hg
  simp only [Bool.not_eq_true'] at hh
  have mem : e.2.contains (target g)=true := List.contains_iff_mem.mpr (eq ▸ hq)
  rw [mem] at hh
  contradiction

theorem sel_pre_pull : ∀ j : Fin 26, j.val ≤ 24 →
    pull (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j))) (selectorExpr (start j)) =
      some (selectorExpr (start j)) := by decide +kernel

theorem sel_before_pull : ∀ j : Fin 26, j.val ≤ 24 →
    pull (before5 (start j)) (selectorExpr (start j)) = some (false,[Shadow7.e0P (start j)+7]) := by decide +kernel

theorem sel_barrel_quiet : ∀ j : Fin 26, j.val ≤ 24 →
    (Shadow7.leaveBarrel (start j)).all (fun g => !(selectorExpr (start j)).2.contains (target g)) = true := by
  decide +kernel

theorem sel_away : ∀ j : Fin 26, j.val ≤ 24 → (selectorSources (start j)).all (fun q => decide (q ≠ 1565)) = true := by
  decide +kernel

/-- The selector relation in front of the selector pop of the CRT chain: `1565 ⊕ 1559 ⊕ 1561..1564 ⊕ e0P+7 = 0`. -/
theorem sel_rel (j : Fin 26) (hi : j.val ≤ 24) (s : State) (zero7 : s.basis (Shadow7.e0P (start j)+7) = false) :
    eval (selectorExpr (start j))
      (run (GateMirror.forward (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++
        (keptHead (start j) ++ (KeptParity.placed (start j) ++ selPre (start j)))))) [] s).basis = false := by
  rw [forward_app, run_append, run_take, List.drop_nil, forward_app, run_append, run_take, List.drop_nil]
  rw [← pull_sound _ _ _ (sel_pre_pull j hi), expr_kept _ _ (sel_barrel_quiet j hi),
    ← pull_sound _ _ _ (sel_before_pull j hi)]
  simpa [eval, parity] using zero7

end ECDSAAdd.Entrant.StairPacket.DeadJoin
-- ==== end SelectorReceiver semantics ====

namespace ECDSAAdd.Entrant.StairPacket.DeadJoin
open Arithmetic Partial GateMirror HighBankJoin Challenge
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

theorem raw_crt_all_pair57 (j : Fin 26) (hi : j.val ≤ 24) (s : State)
    (original : RawValid s (referenceOps (start j)))
    (zero : (run (GateMirror.forward (LeaveJ7.entryOps (start j) ++ postEntry (start j))) [] s).basis
      (Shadow7.a0P (start j) - 1 + 16) = false)
    (scanEq : ∀ m, run (GateMirror.forward (DeadScan.fix0M (start j) (Shadow7.sbP (start j)))) m s =
      run (GateMirror.forward (Shadow7.fix0P (start j) (Shadow7.sbP (start j)))) [] s)
    (rel : FlagLeave.Rel (Shadow7.e0P (start j) + 3) (Shadow7.e0P (start j) + 4) (Shadow7.e0P (start j) + 6) false s)
    (zero6 : s.basis (Shadow7.e0P (start j) + 6) = false)
    (barrelSame : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s))
    (barrelBack : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s)) =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s)
    (t0 : State)
    (ht0 : run (GateMirror.forward (Shadow7.leaveAdjustCore (start j))) [] t0 =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s)
    (ht0_undo : run (GateMirror.inverse (Shadow7.leaveAdjustCore (start j))) []
      (run (GateMirror.forward (Shadow7.leaveAdjustCore (start j))) [] t0) = t0)
    (adjSame : ∀ m, run (GateMirror.forward (AdjustShort.core (start j))) m t0 =
      run (GateMirror.forward (Shadow7.leaveAdjustCore (start j))) [] t0)
    (adjBack : ∀ n, run (GateMirror.inverse (AdjustShort.core (start j))) n
      (run (GateMirror.forward (Shadow7.leaveAdjustCore (start j))) [] t0) = t0)
    (keptRel : KeptParity.relation (fun q => (run (GateMirror.forward (CRTBarrel.beforeReference (start j) ++
      (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s).basis (KeptParity.port (start j) q)))
    (zero7 : s.basis (Shadow7.e0P (start j) + 7) = false) :
    (∀ m, run (GateMirror.forward (AdjustShort.before5Short (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (after7S (start j))) m s =
      run (GateMirror.forward (referenceOps (start j))) m s) ∧
    (∀ m n, run (GateMirror.inverse (after7S (start j)) ++ CRTBarrel.barrel (start j) true ++ GateMirror.inverse (AdjustShort.before5Short (start j))) n
      (run (GateMirror.forward (AdjustShort.before5Short (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (after7S (start j))) m s) = s) := by
  obtain ⟨v0, same0, beforeEq⟩ := raw_all_valid j hi s original zero scanEq rel
  -- Step 1: FlagCut5 (row0Old -> row0New inside beforeAll)
  have shape0 : allOps (start j) =
      beforePre5Cut (start j) ++ (row0Old (start j) ++ (beforePost5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterAll (start j)))) := by
    rw [all_split j hi, beforeAll_split5 j hi]
    simp only [List.append_assoc]
  rw [shape0] at v0
  have hy6 : (run (GateMirror.forward (beforePre5Cut (start j))) [] s).basis (Shadow7.e0P (start j) + 6) = false :=
    (keeps_of_targets57 _ _ (fun g hg => of_decide_eq_true (List.all_eq_true.mp (pre5Cut_targets j hi) g hg)) [] s).trans zero6
  obtain ⟨hxy, htx, hty⟩ := row0_distinct57 j hi
  have eqRow0 : run (GateMirror.forward (row0New (start j))) [] (run (GateMirror.forward (beforePre5Cut (start j))) [] s) =
      run (GateMirror.forward (row0Old (start j))) [] (run (GateMirror.forward (beforePre5Cut (start j))) [] s) :=
    swap_make57 _ _ _ _ hxy htx hty hy6
  have vRow0 : RawValid (run (GateMirror.forward (beforePre5Cut (start j))) [] s) (row0New (start j)) :=
    ⟨fun x hx => List.all_eq_true.mp (row0New_proper j hi) x hx, ⟨trivial, trivial, trivial⟩, ⟨hy6, trivial, trivial⟩⟩
  obtain ⟨v5, same5⟩ := raw_swap_mid v0 vRow0 eqRow0
  have before5Eq : run (GateMirror.forward (before5 (start j))) [] s =
      run (GateMirror.forward (beforeAll (start j))) [] s := by
    rw [before5, beforeAll_split5 j hi]
    simp only [forward_app, run_append, run_take, List.drop_nil, eqRow0]
  -- Step 2: FlagCut7 part A (.make 1558 top 1559 -> .cx top 1559)
  let pre7 := before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (afterPre7HeadCut (start j) ++ afterPre7Tail (start j)))
  have shape5 : beforePre5Cut (start j) ++ (row0New (start j) ++ (beforePost5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterAll (start j)))) =
      pre7 ++ ([.make 1558 (topW7 (start j)) 1559] ++ (chainMid7 (start j) ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j)))) := by
    rw [afterAll_split7 j hi]
    simp only [pre7, before5, List.append_assoc]
  rw [shape5] at v5
  have h1558A : (run (GateMirror.forward pre7) [] s).basis 1558 = true := by
    have sp : pre7 = (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ afterPre7HeadCut (start j))) ++ afterPre7Tail (start j) := by
      simp only [pre7, List.append_assoc]
    rw [sp, forward_app, run_append, run_take, List.drop_nil]
    exact afterPre7Tail_1558 j hi _
  have vCxA : RawValid (run (GateMirror.forward pre7) [] s) [.cx (topW7 (start j)) 1559] :=
    ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact top_cx_proper j hi, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  obtain ⟨v7a, same7a⟩ := raw_swap_mid v5 vCxA (make_cx_1558 _ _ h1558A)
  -- Step 3: FlagCut7 part B (.pop 1558 top 1559 -> .cx top 1559)
  let pre7b := pre7 ++ ([.cx (topW7 (start j)) 1559] ++ chainMid7 (start j))
  have shape7a : pre7 ++ ([.cx (topW7 (start j)) 1559] ++ (chainMid7 (start j) ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j)))) =
      pre7b ++ ([.pop 1558 (topW7 (start j)) 1559] ++ afterPost7 (start j)) := by
    simp only [pre7b, List.append_assoc]
  rw [shape7a] at v7a
  have h1558B : (run (GateMirror.forward pre7b) [] s).basis 1558 = true := by
    simp only [pre7b, forward_app, run_append, run_take, List.drop_nil]
    rw [keeps_of_targets57 _ 1558 (chainMid7_targets (start j))]
    rw [keeps_of_targets57 [.cx (topW7 (start j)) 1559] 1558 (fun g hg => by
      rw [List.mem_singleton.mp hg]; simp [target])]
    exact h1558A
  have valB : ValueOK (run (GateMirror.forward pre7b) [] s) (.pop 1558 (topW7 (start j)) 1559) :=
    v7a.parts.2.parts.1.prepared.1
  have vCxB : RawValid (run (GateMirror.forward pre7b) [] s) [.cx (topW7 (start j)) 1559] :=
    ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact top_cx_proper j hi, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩
  obtain ⟨v7, same7b⟩ := raw_swap_mid v7a vCxB (pop_cx_1558 _ _ h1558B valB)
  -- Step 4: Splice in the CRT barrel
  have shape7 : pre7b ++ ([.cx (topW7 (start j)) 1559] ++ afterPost7 (start j)) =
      before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7 (start j)) := by
    simp only [pre7b, pre7, after7, List.append_assoc]
  rw [shape7] at v7
  have bEq : run (GateMirror.forward (before5 (start j))) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j))) [] s :=
    before5Eq.trans beforeEq
  have same' : ∀ m, run (CRTBarrel.barrel (start j) false) m (run (GateMirror.forward (before5 (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (before5 (start j))) [] s) := by
    simpa only [bEq] using barrelSame
  have back' : ∀ n, run (CRTBarrel.barrel (start j) true) n
      (run (GateMirror.forward (Shadow7.leaveBarrel (start j))) [] (run (GateMirror.forward (before5 (start j))) [] s)) =
      run (GateMirror.forward (before5 (start j))) [] s := by
    simpa only [bEq] using barrelBack
  -- Step 3b: KeptParity (GordoAR a2ce2c3a): the kept pass inside after7 -> the parity pass
  have shapeK : before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7 (start j)) =
      (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j))) ++
        (Shadow7.moveKept (start j) ++ afterRest7 (start j)) := by
    rw [after7_kept j hi]
    simp only [List.append_assoc]
  rw [shapeK] at v7
  have keptIn : run (GateMirror.forward (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s =
      run (GateMirror.forward (CRTBarrel.beforeReference (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s := by
    simp only [forward_app, run_append, run_take, List.drop_nil, bEq]
  have relK : KeptParity.relation (fun q => (run (GateMirror.forward (before5 (start j) ++
      (Shadow7.leaveBarrel (start j) ++ keptHead (start j)))) [] s).basis (KeptParity.port (start j) q)) := by
    rw [keptIn]
    exact keptRel
  obtain ⟨keptF, keptV⟩ := KeptParity.placed_pair j hi _ relK
  obtain ⟨v7K, same7K⟩ := raw_swap_mid v7 keptV (keptF [])
  have shapeK2 : (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ keptHead (start j))) ++
      (KeptParity.placed (start j) ++ afterRest7 (start j)) =
      before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7K (start j)) := by
    simp only [after7K, List.append_assoc]
  rw [shapeK2] at v7K
  -- Step 3c: selector receiver (spariev 59c20890 Core150): pop 1560 (sig s+1048) 1565 -> cx q 1565
  have shapeS : before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7K (start j)) =
      (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (keptHead (start j) ++ (KeptParity.placed (start j) ++
        selPre (start j))))) ++ (Gate.pop 1560 (OB5.sig (start j+14) (start j+1048)) 1565 :: (selPost (start j) ++ selTail (start j))) := by
    rw [after7K_sel j hi]; simp only [List.append_assoc, selectorPop]
  rw [shapeS] at v7K
  obtain ⟨v7S, same7S⟩ := DI7Affine.raw_replace_pop _ _ 1560 (OB5.sig (start j+14) (start j+1048)) 1565 false
    (selectorSources (start j)) s v7K (fun q hq => of_decide_eq_true (List.all_eq_true.mp (sel_away j hi) q hq))
    (sel_rel j hi s zero7)
  have shapeS2 : (before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ (keptHead (start j) ++ (KeptParity.placed (start j) ++
      selPre (start j))))) ++ (DI7Affine.clear false (selectorSources (start j)) 1565 ++ (selPost (start j) ++ selTail (start j))) =
      before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7S (start j)) := by
    rw [after7S_sel, ← clear_receiver]; simp only [List.append_assoc]
  rw [shapeS2] at v7S
  -- TruncatedAdjust (credit Mahmoud514 50c0ac46): the adjust core is replaced next to the barrel, from the
  -- pre-adjust state t0 of the reference (identified through the undo of the old adjust)
  have vPreAdj : RawValid s (AdjustShort.before5Pre (start j) ++ Shadow7.leaveAdjustCore (start j)) := by
    rw [← AdjustShort.before5_split_core]; exact v7S.parts.1
  have hstep1 : run (GateMirror.forward (Shadow7.leaveAdjustCore (start j))) []
      (run (GateMirror.forward (AdjustShort.before5Pre (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveAdjustCore (start j))) [] t0 := by
    have hsplit : run (GateMirror.forward (before5 (start j))) [] s =
        run (GateMirror.forward (Shadow7.leaveAdjustCore (start j))) []
          (run (GateMirror.forward (AdjustShort.before5Pre (start j))) [] s) := by
      rw [AdjustShort.before5_split_core, forward_app, run_append, run_take, List.drop_nil]
    rw [← hsplit, bEq, ht0]
  have hpreEq : run (GateMirror.forward (AdjustShort.before5Pre (start j))) [] s = t0 := by
    have hinv := congrArg (run (GateMirror.inverse (Shadow7.leaveAdjustCore (start j))) []) hstep1
    rw [vPreAdj.parts.2.undo_run [] [], ht0_undo] at hinv
    exact hinv
  have sameAB : ∀ m, run (GateMirror.forward (AdjustShort.core (start j)) ++ CRTBarrel.barrel (start j) false) m
      (run (GateMirror.forward (AdjustShort.before5Pre (start j))) [] s) =
      run (GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))) []
        (run (GateMirror.forward (AdjustShort.before5Pre (start j))) [] s) := by
    intro m
    rw [hpreEq, run_append, run_take, adjSame, forward_app, run_append, run_take, List.drop_nil, ht0]
    exact barrelSame _
  have backAB : ∀ n, run (CRTBarrel.barrel (start j) true ++ GateMirror.inverse (AdjustShort.core (start j))) n
      (run (GateMirror.forward (Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j))) []
        (run (GateMirror.forward (AdjustShort.before5Pre (start j))) [] s)) =
      run (GateMirror.forward (AdjustShort.before5Pre (start j))) [] s := by
    intro n
    rw [hpreEq, run_append, run_take, forward_app, run_append, run_take, List.drop_nil, ht0, barrelBack _, ← ht0]
    exact adjBack _
  have hspA : before5 (start j) ++ (Shadow7.leaveBarrel (start j) ++ after7S (start j)) =
      AdjustShort.before5Pre (start j) ++ ((Shadow7.leaveAdjustCore (start j) ++ Shadow7.leaveBarrel (start j)) ++ after7S (start j)) := by
    rw [AdjustShort.before5_split_core]; simp only [List.append_assoc]
  rw [hspA] at v7S
  obtain ⟨f, r⟩ := raw_replace _ _ _ _ _ s v7S sameAB backAB
  have hfprog : GateMirror.forward (AdjustShort.before5Short (start j)) ++ CRTBarrel.barrel (start j) false ++ GateMirror.forward (after7S (start j)) =
      GateMirror.forward (AdjustShort.before5Pre (start j)) ++ (GateMirror.forward (AdjustShort.core (start j)) ++ CRTBarrel.barrel (start j) false) ++ GateMirror.forward (after7S (start j)) := by
    rw [AdjustShort.before5Short_split_core, forward_app]; simp only [List.append_assoc]
  have hrprog : GateMirror.inverse (after7S (start j)) ++ CRTBarrel.barrel (start j) true ++ GateMirror.inverse (AdjustShort.before5Short (start j)) =
      GateMirror.inverse (after7S (start j)) ++ (CRTBarrel.barrel (start j) true ++ GateMirror.inverse (AdjustShort.core (start j))) ++ GateMirror.inverse (AdjustShort.before5Pre (start j)) := by
    rw [AdjustShort.before5Short_split_core, inverse_append]; simp only [List.append_assoc]
  refine ⟨fun m => ?_, fun m n => by rw [hfprog, hrprog]; exact r m n⟩
  have h0 := f m
  rw [← hfprog, ← hspA, ← shapeS2] at h0
  have hS := same7S m
  rw [← shapeS, ← shapeK2] at hS
  have h1 := h0.trans hS
  have hK := same7K m
  rw [← shapeK, ← shape7] at hK
  have h2 := (same7b m)
  rw [← shape7a] at h2
  have h3 := (same7a m)
  rw [← shape5] at h3
  have h4 := (same5 m)
  rw [← shape0] at h4
  exact h1.trans (hK.trans (h2.trans (h3.trans (h4.trans (same0 m)))))

end ECDSAAdd.Entrant.StairPacket.DeadJoin
end
-- ==== end FlagCut57Semantic ====

-- ==== begin ScanRowGordo (margin 16, credited to GordoAR e2530dcd) ====
section
namespace ECDSAAdd.Entrant.StairPacket.ScanRowGordo
open Arithmetic GateMirror Partial Challenge MeasuredCodec5
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pre5_prefix (s : Nat) :
    DeadJoin.beforePre5 s = (firstRows s (Shadow7.sbP s) ++ cell s (Shadow7.sbP s)) ++
      ((DeadScan.fix0M s (Shadow7.sbP s)).drop 50 ++ leaveFix1 s (Shadow7.sbP s) ++
        Shadow7.fix2P s (Shadow7.sbP s) ++ leaveFix3 s (Shadow7.sbP s) ++
        leaveFix4 s (Shadow7.sbP s) ++ (Shadow7.fix5P s (Shadow7.sbP s)).take 27) := rfl

private theorem prefix_cut_noop : ∀ j : Fin 26, j.val ≤ 24 →
    let s := start j; let h := Shadow7.sbP s
    FlagLeave.cut (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 (firstRows s h ++ cell s h) =
      firstRows s h ++ cell s h ∧
    FlagLeave.removed (Shadow7.e0P s + 3) (Shadow7.e0P s + 4) 1559 2 (firstRows s h ++ cell s h) = [] := by
  decide +kernel

theorem before5_split (j : Fin 26) (hi : j.val ≤ 24) :
    DeadJoin.before5 (start j) =
      firstRows (start j) (Shadow7.sbP (start j)) ++
        (cell (start j) (Shadow7.sbP (start j)) ++ before5Tail (start j)) := by
  obtain ⟨hc, hr⟩ := prefix_cut_noop j hi
  unfold DeadJoin.before5 DeadJoin.beforePre5Cut before5Tail
  rw [pre5_prefix, FlagLeave.cut_append, hc, hr]
  simp only [List.length_nil, Nat.sub_zero, List.append_assoc]

theorem before5Short_split (j : Fin 26) (hi : j.val ≤ 24) :
    AdjustShort.before5Short (start j) =
      firstRows (start j) (Shadow7.sbP (start j)) ++
        (cell (start j) (Shadow7.sbP (start j)) ++ AdjustShort.before5TailShort (start j)) := by
  obtain ⟨hc, hr⟩ := prefix_cut_noop j hi
  unfold AdjustShort.before5Short DeadJoin.beforePre5Cut AdjustShort.before5TailShort
  rw [pre5_prefix, FlagLeave.cut_append, hc, hr]
  simp only [List.length_nil, Nat.sub_zero, List.append_assoc]

private theorem fwd_app (a b : List Gate) :
    GateMirror.forward (a ++ b) = GateMirror.forward a ++ GateMirror.forward b := List.map_append

private theorem inv_app (a b : List Gate) :
    inverse (a ++ b) = inverse b ++ inverse a := DeadJoin.inverse_append a b

theorem before5Row_counts (j : Fin 26) (hi : j.val ≤ 24) :
    toffoliCount (GateMirror.forward (before5Row (start j))) + 1 =
      toffoliCount (GateMirror.forward (DeadJoin.before5 (start j))) ∧
    toffoliCount (inverse (before5Row (start j))) =
      toffoliCount (inverse (DeadJoin.before5 (start j))) ∧
    measurementCount (GateMirror.forward (before5Row (start j))) =
      measurementCount (GateMirror.forward (DeadJoin.before5 (start j))) + 1 ∧
    measurementCount (inverse (before5Row (start j))) =
      measurementCount (inverse (DeadJoin.before5 (start j))) ∧
    gateSlots (GateMirror.forward (before5Row (start j))) =
      gateSlots (GateMirror.forward (DeadJoin.before5 (start j))) + 5 ∧
    gateSlots (inverse (before5Row (start j))) =
      gateSlots (inverse (DeadJoin.before5 (start j))) + 4 := by
  let s := start j; let h := Shadow7.sbP s
  have cells :
      toffoliCount (GateMirror.forward (shortCell s h)) + 1 = toffoliCount (GateMirror.forward (cell s h)) ∧
      toffoliCount (inverse (shortCell s h)) = toffoliCount (inverse (cell s h)) ∧
      measurementCount (GateMirror.forward (shortCell s h)) = measurementCount (GateMirror.forward (cell s h)) + 1 ∧
      measurementCount (inverse (shortCell s h)) = measurementCount (inverse (cell s h)) ∧
      gateSlots (GateMirror.forward (shortCell s h)) = gateSlots (GateMirror.forward (cell s h)) + 5 ∧
      gateSlots (inverse (shortCell s h)) = gateSlots (inverse (cell s h)) + 4 := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨a,b,c,d,e,f⟩ := cells
  rw [before5_split j hi, before5Row]
  simp only [s, h, fwd_app, inv_app, toffoliCount_append,
    measurementCount_append, gateSlots_append] at a b c d e f ⊢
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem before5Row_allW {P : Wire → Prop} (j : Fin 26) (hi : j.val ≤ 24)
    (covered : AllW P (DeadJoin.before5 (start j))) :
    AllW P (before5Row (start j)) := by
  let s := start j; let b := Shadow7.sbP s
  rw [before5_split j hi, allW_append_iff, allW_append_iff] at covered
  have hz : P (b+1579) :=
    covered.1 (.cx (s+b+47) (b+1579)) (List.mem_cons_self ..) _ (by simp [Gate.wires])
  have onCell := covered.2.1 (.ccx (s+30) (b+801) (s+b+46)) (by simp [cell, s, b])
  have hc := onCell (s+30) (by simp [Gate.wires])
  have hy := onCell (b+801) (by simp [Gate.wires])
  have hx := onCell (s+b+46) (by simp [Gate.wires])
  have sub : AllW P (shortCell s b) := by
    intro gate hg q hq
    simp only [shortCell, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp only [Gate.wires, List.mem_cons, List.not_mem_nil, or_false] at hq <;> aesop
  rw [before5Row, allW_append_iff, allW_append_iff]
  exact ⟨covered.1, sub, covered.2.2⟩

theorem before5Row_proper (j : Fin 26) (hi : j.val ≤ 24)
    (old : ∀ g ∈ DeadJoin.before5 (start j), proper g = true) :
    ∀ g ∈ before5Row (start j), proper g = true := by
  have physical : ∀ i : Fin 26, (shortCell (start i) (Shadow7.sbP (start i))).all proper = true := by decide +kernel
  have keep := List.all_eq_true.mpr old
  rw [before5_split j hi] at keep
  simp only [List.all_append, Bool.and_eq_true] at keep
  apply List.all_eq_true.mp
  simp only [before5Row, List.all_append, Bool.and_eq_true]
  exact ⟨keep.1, physical j, keep.2.2⟩

def oldRow : List Gate := [.cx 1 2, .ccx 0 2 1, .cx 1 2]
def newRow : List Gate := [.cx 1 2, .cx 2 1, .cx 3 1, .pop 0 2 1, .cx 3 1, .cx 2 1, .cx 1 2]

private def packed (a b c d : Bool) := a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat
private theorem packed_bits : ∀ a b c d : Bool, let x := packed a b c d
    x < 16 ∧ x.testBit 0 = a ∧ x.testBit 1 = b ∧ x.testBit 2 = c ∧ x.testBit 3 = d := by decide
private theorem forward_check : ∀ (x : Fin 16) (p m : Bool),
    (sim (GateMirror.forward oldRow) [] p x.val).2.testBit 2 = x.val.testBit 3 →
    sim (GateMirror.forward newRow) [m] p x.val = sim (GateMirror.forward oldRow) [] p x.val := by decide +kernel
private theorem return_check : ∀ (x : Fin 16) (p : Bool),
    (sim (GateMirror.forward oldRow) [] p x.val).2.testBit 2 = x.val.testBit 3 →
    sim (GateMirror.forward oldRow ++ GateMirror.inverse newRow) [] p x.val = (p,x.val) := by decide +kernel

private abbrev sites : Finset Wire := Finset.range 4
private theorem old_sites : wires (GateMirror.forward oldRow) ⊆ sites := by decide
private theorem new_sites : wires (GateMirror.forward newRow) ⊆ sites := by decide
private theorem return_sites : wires (GateMirror.forward oldRow ++ GateMirror.inverse newRow) ⊆ sites := by decide

private theorem run_rename_eq_of_eq (f : Wire → Wire) (S : Finset Wire)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b)
    (p q : Program) (hp : wires p ⊆ S) (hq : wires q ⊆ S)
    (mp mq : List Bool) (t s : State) (hph : t.phase = s.phase)
    (hb : ∀ a ∈ S, t.basis a = s.basis (f a))
    (heq : run p mp t = run q mq t) :
    run (renameProgram f p) mp s = run (renameProgram f q) mq s := by
  have rp := run_rename_pool f S hf p hp mp t s hph hb
  have rq := run_rename_pool f S hf q hq mq t s hph hb
  have hph_eq : (run (renameProgram f p) mp s).phase = (run (renameProgram f q) mq s).phase := by
    rw [rp.1, rq.1, heq]
  have hb_eq : (run (renameProgram f p) mp s).basis = (run (renameProgram f q) mq s).basis := by
    funext w
    by_cases hw : w ∈ S.image f
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      rw [rp.2 a ha, rq.2 a ha, heq]
    · rw [run_rename_pool_outside f S p hp mp s w hw, run_rename_pool_outside f S q hq mq s w hw]
  cases h1 : run (renameProgram f p) mp s
  cases h2 : run (renameProgram f q) mq s
  rw [h1, h2] at hph_eq hb_eq
  simp only at hph_eq hb_eq
  rw [hph_eq, hb_eq]

theorem placed_pair (f : Wire → Wire) (inj : ∀ a ∈ sites, ∀ b ∈ sites, f a = f b → a=b)
    (s : State) (companion : (run (renameProgram f (GateMirror.forward oldRow)) [] s).basis (f 2) = s.basis (f 3)) :
    (∀ m, run (renameProgram f (GateMirror.forward newRow)) m s = run (renameProgram f (GateMirror.forward oldRow)) [] s) ∧
    (∀ n, run (renameProgram f (GateMirror.inverse newRow)) n (run (renameProgram f (GateMirror.forward oldRow)) [] s) = s) := by
  let x := packed (s.basis (f 0)) (s.basis (f 1)) (s.basis (f 2)) (s.basis (f 3))
  obtain ⟨lt,h0,h1,h2,h3⟩ := packed_bits (s.basis (f 0)) (s.basis (f 1)) (s.basis (f 2)) (s.basis (f 3))
  let t : State := ⟨s.phase, bitsOf x⟩
  have reads : ∀ q ∈ sites, t.basis q = s.basis (f q) := by
    intro q hq
    have hq' : q < 4 := Finset.mem_range.mp hq
    change x.testBit q = s.basis (f q)
    interval_cases q <;> assumption
  have physical := (run_rename_pool f sites inj _ old_sites [] t s rfl reads).2 2 (by decide)
  have allowed : (sim (GateMirror.forward oldRow) [] s.phase x).2.testBit 2 = x.testBit 3 := by
    have eq := physical.symm.trans (companion.trans (reads 3 (by decide)).symm)
    simpa only [t,run_sim,bitsOf] using eq
  constructor
  · intro m
    have trimmed : run (GateMirror.forward newRow) m t = run (GateMirror.forward newRow) [m.headD false] t := by cases m <;> rfl
    apply run_rename_eq_of_eq f sites inj _ _ new_sites old_sites m [] t s rfl reads
    rw [trimmed]
    simpa only [t,run_sim] using congrArg (fun y : Bool × Nat => State.mk y.1 (bitsOf y.2))
      (forward_check ⟨x,lt⟩ s.phase (m.headD false) allowed)
  · intro n
    have local_eq : run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) n t = run [] [] t := by
      have trimmed : run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) n t = run (GateMirror.forward oldRow ++ GateMirror.inverse newRow) [] t := rfl
      rw [trimmed]
      simpa only [t,run_sim,sim] using congrArg (fun y : Bool × Nat => State.mk y.1 (bitsOf y.2))
        (return_check ⟨x,lt⟩ s.phase allowed)
    have eq := run_rename_eq_of_eq f sites inj _ [] return_sites (by decide) n [] t s rfl reads local_eq
    change run (renameProgram f (GateMirror.forward oldRow) ++ renameProgram f (GateMirror.inverse newRow)) n s = s at eq
    rw [run_append] at eq
    exact eq

private theorem split_scan (s h : Nat) :
    Shadow7.fix0P s h = firstRows s h ++ (cell s h ++ (suffix s h ++ lastTwo h)) := rfl

private theorem lastTwo_zero (h : Nat) (t : State)
    (clean : (run (GateMirror.forward (lastTwo h)) [] t).basis (h+801) = false) :
    t.basis (h+801) = t.basis (h+1579) := by
  simp [lastTwo, GateMirror.forward, front, run, writeBit] at clean
  cases hb : t.basis (h+801) <;> cases hn : t.basis (h+1579) <;> simp_all

private theorem geometry : ∀ i : Fin 26, i.val ≤ 24 →
    let s := start i; let h := Shadow7.sbP s
    (suffix s h).all (fun g => decide (target g ≠ h+801)) = true ∧
    (suffix s h).all (fun g => decide (target g ≠ h+1579)) = true ∧
    (cell s h).all (fun g => decide (target g ≠ h+1579)) = true := by decide +kernel

private theorem ports_injective : ∀ j : Fin 26, j.val ≤ 24 →
    ∀ a ∈ sites, ∀ b ∈ sites,
      port (start j) (Shadow7.sbP (start j)) a = port (start j) (Shadow7.sbP (start j)) b → a = b := by
  have finite : ∀ (j : Fin 26) (a b : Fin 4),
      port (start j) (Shadow7.sbP (start j)) a.val = port (start j) (Shadow7.sbP (start j)) b.val → a = b := by
    decide +kernel
  intro j _ a ha b hb eq
  exact congrArg Fin.val (finite j ⟨a, Finset.mem_range.mp ha⟩ ⟨b, Finset.mem_range.mp hb⟩ eq)

private theorem firstRows_pure : ∀ j : Fin 26, j.val ≤ 24 →
    (firstRows (start j) (Shadow7.sbP (start j))).all (fun g => match g with | .make _ _ _ | .pop _ _ _ => false | _ => true) = true := by
  decide +kernel

private theorem pure_list_roundtrip (gs : List Gate)
    (hp : gs.all (fun g => match g with | .make _ _ _ | .pop _ _ _ => false | _ => true) = true)
    (phys : ∀ g ∈ gs, proper g = true) :
    (∀ m s, run (GateMirror.forward gs) m s = run (GateMirror.forward gs) [] s) ∧
    (∀ m s, run (inverse gs) m (run (GateMirror.forward gs) [] s) = s) ∧
    (∀ m s, run (GateMirror.forward gs) [] (run (inverse gs) m s) = s) := by
  induction gs with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons g tl ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨fih, rih, rih2⟩ := ih hp.2 (fun x hx => phys x (List.mem_cons_of_mem g hx))
    have pg := phys g (List.mem_cons_self ..)
    have hstep : (∀ m s, run (GateMirror.forward [g]) m s = run (GateMirror.forward [g]) [] s) ∧
        (∀ m s, run (inverse [g]) m (run (GateMirror.forward [g]) [] s) = s) ∧
        (∀ m s, run (GateMirror.forward [g]) [] (run (inverse [g]) m s) = s) := by
      cases g with
      | x a => refine ⟨fun _ _ => rfl, fun _ s => ?_, fun _ s => ?_⟩ <;>
          (obtain ⟨ph, f⟩ := s; simp [GateMirror.forward, inverse, front, back, run, writeBit])
      | cx a b =>
        simp only [proper, decide_eq_true_eq] at pg
        refine ⟨fun _ _ => rfl, fun _ s => ?_, fun _ s => ?_⟩ <;>
          (obtain ⟨ph, f⟩ := s; simp [GateMirror.forward, inverse, front, back, run, writeBit, pg, Ne.symm pg])
      | ccx a b c =>
        simp only [proper, decide_eq_true_eq] at pg
        refine ⟨fun _ _ => rfl, fun _ s => ?_, fun _ s => ?_⟩ <;>
          (obtain ⟨ph, f⟩ := s; simp [GateMirror.forward, inverse, front, back, run, writeBit, pg.1, pg.2, Ne.symm pg.1, Ne.symm pg.2])
      | make _ _ _ => simp at hp
      | pop _ _ _ => simp at hp
    have fcons : GateMirror.forward (g :: tl) = GateMirror.forward [g] ++ GateMirror.forward tl := rfl
    have icons : inverse (g :: tl) = inverse tl ++ inverse [g] := DeadJoin.inverse_append [g] tl
    refine ⟨fun m s => ?_, fun m s => ?_, fun m s => ?_⟩
    · rw [fcons, run_append, run_append, List.take_nil, List.drop_nil, hstep.1, fih]
    · rw [fcons, icons, run_append, run_append, List.take_nil, List.drop_nil, rih, hstep.2.1]
    · rw [fcons, icons, run_append, run_append, List.take_nil, List.drop_nil, hstep.2.2, rih2]

section
attribute [local irreducible] run

theorem companion_eq_sign (j : Fin 26) (hj : j.val ≤ 24) (t : State) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) t.basis)
    (fresh : t.basis (Shadow7.e0P (start j) + 5) = false)
    (small : u < 2^15 * 2^(Shadow7.sbP (start j))) :
    let s := start j; let h := Shadow7.sbP s
    let before := run (GateMirror.forward (firstRows s h)) [] t
    (run (GateMirror.forward (cell s h)) [] before).basis (h+801) = before.basis (h+1579) := by
  let s := start j; let h := Shadow7.sbP s
  have scan := ((LeaveJ7.inputScan_result j (Nat.zero_le _) hj t [] u v G sg ready fresh).2.2.1
    15 (by decide)).2
  have pos : Shadow7.b0P (start j) - 1 + 15 = h + 801 := by
    simp only [Shadow7.b0P, h, s]; omega
  have clean : (run (GateMirror.forward (Shadow7.fix0P s h)) [] t).basis (h+801) = false := by
    rw [← pos, scan]
    apply Nat.testBit_lt_two_pow
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (lt_of_le_of_lt (Nat.sub_le _ _) small)
  let before := run (GateMirror.forward (firstRows s h)) [] t
  let after := run (GateMirror.forward (cell s h)) [] before
  let tailState := run (GateMirror.forward (suffix s h)) [] after
  rw [split_scan, fwd_app, fwd_app, fwd_app, run_append, run_append, run_append] at clean
  simp only [List.take_nil, List.drop_nil] at clean
  have tailEq := lastTwo_zero h tailState clean
  obtain ⟨clearB, clearN, cellN⟩ := geometry j hj
  have keeps (gs : List Gate) (q : Wire) (a : State)
      (safe : gs.all (fun g => decide (target g ≠ q)) = true) :
      (run (GateMirror.forward gs) [] a).basis q = a.basis q :=
    DeadJoin.keeps_of_targets57 gs q
      (fun g hg => of_decide_eq_true ((List.all_eq_true.mp safe) g hg)) [] a
  exact (keeps _ _ after clearB).symm.trans
    (tailEq.trans ((keeps _ _ after clearN).trans (keeps _ _ before cellN)))

theorem cell_pair (j : Fin 26) (hj : j.val ≤ 24) (t : State) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) t.basis)
    (fresh : t.basis (Shadow7.e0P (start j) + 5) = false)
    (small : u < 2^15 * 2^(Shadow7.sbP (start j))) :
    let s := start j; let h := Shadow7.sbP s
    let before := run (GateMirror.forward (firstRows s h)) [] t
    (∀ m, run (GateMirror.forward (shortCell s h)) m before = run (GateMirror.forward (cell s h)) [] before) ∧
    (∀ n, run (inverse (shortCell s h)) n (run (GateMirror.forward (cell s h)) [] before) = before) := by
  let s := start j; let h := Shadow7.sbP s
  let before := run (GateMirror.forward (firstRows s h)) [] t
  have sign := companion_eq_sign j hj t u v G sg ready fresh small
  have oldP : renameProgram (port s h) (GateMirror.forward oldRow) = GateMirror.forward (cell s h) := by
    simp only [oldRow, cell, port, GateMirror.forward, front, renameProgram, renameInstr, List.map_cons, List.map_nil, List.append_nil, List.cons_append]
  have newP : renameProgram (port s h) (GateMirror.forward newRow) = GateMirror.forward (shortCell s h) := by
    simp only [newRow, shortCell, port, GateMirror.forward, front, GateMirror.erase, renameProgram, renameInstr, renameCorrection, List.map_cons, List.map_nil, List.append_nil, List.cons_append]
  have invP : renameProgram (port s h) (inverse newRow) = inverse (shortCell s h) := by
    simp only [newRow, shortCell, port, inverse, GateMirror.forward, back, front, GateMirror.erase, renameProgram, renameInstr, renameCorrection, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.append_nil]
  obtain ⟨fwd, rev⟩ := placed_pair (port s h) (ports_injective j hj) before (by rw [oldP]; exact sign)
  rw [oldP, newP] at fwd; rw [oldP, invP] at rev
  exact ⟨fwd, rev⟩

theorem before5Row_pair (j : Fin 26) (hi : j.val ≤ 24) (s : State) (u v : Nat) (G sg : Bool)
    (ready : Shadow7.onRails j 15 (SkywalkRails.encode G sg u v) s.basis)
    (fresh : s.basis (Shadow7.e0P (start j) + 5) = false)
    (small : u < 2^15 * 2^(Shadow7.sbP (start j)))
    (phys : ∀ g ∈ AdjustShort.before5Short (start j), proper g = true)
    (orig_det : ∀ m, run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) [] s)
    (fwd5 : ∀ m, run (GateMirror.forward (AdjustShort.before5Short (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7S (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s)
    (rev5 : ∀ m n, run (inverse (DeadJoin.after7S (start j)) ++ CRTBarrel.barrel (start j) true ++
        inverse (AdjustShort.before5Short (start j))) n
      (run (GateMirror.forward (AdjustShort.before5Short (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7S (start j))) m s) = s) :
    (∀ m, run (GateMirror.forward (AdjustShort.before5RowShort (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7S (start j))) m s =
      run (GateMirror.forward (DeadJoin.referenceOps (start j))) m s) ∧
    (∀ m n, run (inverse (DeadJoin.after7S (start j)) ++ CRTBarrel.barrel (start j) true ++
        inverse (AdjustShort.before5RowShort (start j))) n
      (run (GateMirror.forward (AdjustShort.before5RowShort (start j)) ++ CRTBarrel.barrel (start j) false ++
        GateMirror.forward (DeadJoin.after7S (start j))) m s) = s) := by
  let st := start j; let h := Shadow7.sbP st
  have sp := before5Short_split j hi
  have pFR : ∀ g ∈ firstRows st h, proper g = true := fun g hg => phys g (by rw [sp]; exact List.mem_append_left _ hg)
  have pC : ∀ g ∈ cell st h, proper g = true := fun g hg => phys g (by rw [sp]; exact List.mem_append_right _ (List.mem_append_left _ hg))
  obtain ⟨fFR, rFR, rFR2⟩ := pure_list_roundtrip (firstRows st h) (firstRows_pure j hi) pFR
  obtain ⟨fC, rC, rC2⟩ := pure_list_roundtrip (cell st h) rfl pC
  obtain ⟨cFwd, cRev⟩ := cell_pair j hi s u v G sg ready fresh small
  have hmcF : measurementCount (GateMirror.forward (firstRows st h)) = 0 := by
    have := firstRows_pure j hi
    revert this; generalize firstRows st h = l; intro hl
    induction l with
    | nil => rfl
    | cons g tl ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hl
      have h1 : measurementCount (GateMirror.forward [g]) = 0 := by cases g <;> simp_all [GateMirror.forward, front, measurementCount]
      change measurementCount (GateMirror.forward [g] ++ GateMirror.forward tl) = 0
      rw [measurementCount_append, h1, ih hl.2]
  have hmcC : measurementCount (GateMirror.forward (cell st h)) = 0 := rfl
  have hFwd : ∀ m, run (GateMirror.forward (AdjustShort.before5RowShort st) ++ CRTBarrel.barrel st false ++
      GateMirror.forward (DeadJoin.after7S st)) m s =
      run (GateMirror.forward (DeadJoin.referenceOps st)) m s := by
    intro m
    let m' := m.drop (measurementCount (GateMirror.forward (shortCell st h)))
    have h5m := fwd5 m'
    rw [AdjustShort.before5RowShort, fwd_app, fwd_app]
    simp only [List.append_assoc]
    rw [run_append, run_append, fFR, hmcF, List.drop_zero, cFwd]
    rw [sp, fwd_app, fwd_app] at h5m
    simp only [List.append_assoc] at h5m
    rw [run_append, run_append, fFR, hmcF, List.drop_zero, fC, hmcC, List.drop_zero] at h5m
    exact h5m.trans ((orig_det m').trans (orig_det m).symm)
  refine ⟨hFwd, fun m n => ?_⟩
  rw [hFwd m, orig_det m, ← orig_det [], ← fwd5 []]
  let endS := run (GateMirror.forward (AdjustShort.before5Short st) ++ CRTBarrel.barrel st false ++
    GateMirror.forward (DeadJoin.after7S st)) [] s
  have hrev := rev5 [] n
  change run (inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (AdjustShort.before5Short st)) n endS = s at hrev
  let midP := inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (AdjustShort.before5TailShort st)
  have hInv5 : inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (AdjustShort.before5Short st) =
      midP ++ (inverse (cell st h) ++ inverse (firstRows st h)) := by
    rw [sp, inv_app, inv_app]; simp only [midP, st, h, List.append_assoc]
  have hInvR : inverse (DeadJoin.after7S st) ++ CRTBarrel.barrel st true ++ inverse (AdjustShort.before5RowShort st) =
      midP ++ (inverse (shortCell st h) ++ inverse (firstRows st h)) := by
    rw [AdjustShort.before5RowShort, inv_app, inv_app]; simp only [midP, st, h, List.append_assoc]
  rw [hInv5, run_append, run_append] at hrev
  have hMid : run midP (n.take (measurementCount midP)) endS =
      run (GateMirror.forward (cell st h)) [] (run (GateMirror.forward (firstRows st h)) [] s) := by
    have h1 := congrArg (run (GateMirror.forward (firstRows st h)) []) hrev
    rw [rFR2] at h1
    have h2 := congrArg (run (GateMirror.forward (cell st h)) []) h1
    rw [rC2] at h2
    exact h2
  rw [hInvR, run_append, run_append, hMid, cRev, rFR]

end

end ECDSAAdd.Entrant.StairPacket.ScanRowGordo
end
-- ==== end ScanRowGordo ====



end

-- ==== begin folded FredCut ====
section

/-!
# FRED-CUT core (VAST3, 11-23) — ported (harvest-opus) from ercumentyildirim a7d65b7b (commit 841b74b)
onto the 18-module layout: leave tail from `DeadJoin.after7`, rows from the tree's `leaveLowClose` range,
symbolic portal / exit wires.

Each window boundary `leave_k → enter_{k+1}` (and `portal → enter_0`, `leave_24 → park → portalInv`) carries the
same two controlled swaps at the tail of the first piece and at the head of the second; the gates between them
never touch the swaps' wires.  The swaps are measurement-free and self-inverse, so both copies can be dropped:
the run is unchanged for every state and tape.
-/

set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairPacket.FredCut
open ECDSAAdd ECDSAAdd.Arithmetic

/-! ## Generic layer -/

/-- One controlled swap `c ? (a ↔ b)` as three CNOT/Toffoli instructions (`GateMirror.cswapG` mirrored). -/
def cs (c a b : Wire) : Program := [.CX b a, .CCX c a b, .CX b a]

theorem cs_measure (c a b : Wire) : measurementCount (cs c a b) = 0 := rfl

theorem cs_run (c a b : Wire) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) (m : List Bool) (t : State) :
    run (cs c a b) m t =
      ⟨t.phase, fun q => if t.basis c then (if q = a then t.basis b else if q = b then t.basis a else t.basis q)
        else t.basis q⟩ := by
  have hba : b ≠ a := Ne.symm hab
  simp only [cs, run, writeBit]
  congr 1
  funext q
  simp only [Function.update_apply, if_neg hba, if_neg hca, if_neg hcb, if_neg hab, if_true]
  by_cases hqa : q = a
  · subst hqa
    simp only [if_true, if_neg hab]
    cases t.basis c <;> cases t.basis q <;> cases t.basis b <;> rfl
  · by_cases hqb : q = b
    · subst hqb
      simp only [if_neg hqa, if_true]
      cases t.basis c <;> cases t.basis a <;> cases t.basis q <;> rfl
    · simp only [if_neg hqa, if_neg hqb]
      cases t.basis c <;> rfl

/-- Two controlled swaps on disjoint pairs under one control. -/
def S2 (c a b a' b' : Wire) : Program := cs c a b ++ cs c a' b'

theorem S2_measure (c a b a' b' : Wire) : measurementCount (S2 c a b a' b') = 0 := rfl

theorem S2_inv (c a b a' b' : Wire) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) (hca' : c ≠ a') (hcb' : c ≠ b')
    (hab' : a' ≠ b') (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b')
    (t : State) (m1 m2 : List Bool) : run (S2 c a b a' b') m2 (run (S2 c a b a' b') m1 t) = t := by
  simp only [S2, run_append, cs_measure, List.take_zero, List.drop_zero]
  rw [cs_run c a b hca hcb hab, cs_run c a' b' hca' hcb' hab', cs_run c a b hca hcb hab,
    cs_run c a' b' hca' hcb' hab']
  apply State.extensionality
  · rfl
  · funext q
    have e1 := hca.symm; have e2 := hcb.symm; have e3 := hab.symm; have e4 := hca'.symm; have e5 := hcb'.symm
    have e6 := hab'.symm; have e7 := h1.symm; have e8 := h2.symm; have e9 := h3.symm; have e10 := h4.symm
    by_cases hc : t.basis c
    · by_cases hqa : q = a
      · subst hqa
        simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      · by_cases hqb : q = b
        · subst hqb
          simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa]
        · by_cases hqa' : q = a'
          · subst hqa'
            simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa,
              hqb]
          · by_cases hqb' : q = b'
            · subst hqb'
              simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
                hqa, hqb, hqa']
            · simp [hc, hca, hcb, hca', hcb', hqa, hqb, hqa', hqb']
    · simp [hc, hca, hcb, hca', hcb']

/-- Cancellation of a measurement-free block pair around a middle `M` that never touches `W ⊇ wires E`: the
middle commutes past `E` (disjoint wires), then `D` undoes `E`. -/
theorem cancel_free (E M D : Program) (W : Finset Wire)
    (hE : wires E ⊆ W) (hM : ∀ q ∈ W, q ∉ wires M)
    (inv : ∀ t (a b : List Bool), run D b (run E a t) = t)
    (x : State) (me mm md : List Bool) :
    run D md (run M mm (run E me x)) = run M mm x := by
  have dis : Disjoint (wires M) (wires E) :=
    Finset.disjoint_left.mpr (fun q hqM hqE => hM q (hE hqE) hqM)
  rw [run_disjoint_commute M E dis mm me x]
  exact inv _ _ _

/-- FRED cancellation: a measurement-free self-inverse block `S` on both sides of a middle `M` that never touches
`wires S` can be dropped, for every state and tape. -/
theorem fred_cancel (S M Y : Program) (hM : ∀ q ∈ wires S, q ∉ wires M)
    (h0 : measurementCount S = 0) (inv : ∀ t (a b : List Bool), run S b (run S a t) = t)
    (m : List Bool) (s : State) :
    run (S ++ (M ++ (S ++ Y))) m s = run (M ++ Y) m s := by
  rw [run_append S, h0, List.take_zero, List.drop_zero, run_append M, run_append S, h0, List.take_zero,
    List.drop_zero, run_append M]
  congr 1
  exact cancel_free S M S (wires S) (Finset.Subset.refl _) hM inv s [] _ []

/-- The same with an arbitrary prefix. -/
theorem fred_cancel_pre (X S M Y : Program) (hM : ∀ q ∈ wires S, q ∉ wires M)
    (h0 : measurementCount S = 0) (inv : ∀ t (a b : List Bool), run S b (run S a t) = t)
    (m : List Bool) (s : State) :
    run (X ++ (S ++ (M ++ (S ++ Y)))) m s = run (X ++ (M ++ Y)) m s := by
  rw [run_append X, run_append X]
  exact fred_cancel S M Y hM h0 inv _ _

/-! ## Piece-list cuts -/

/-- `Cut n ps ps'`: `ps'` is `ps` with `n` boundary block pairs removed (each block 2 Toffolis).  `pair`: the tail block `E` of one piece (followed by
that piece's suffix `M1`) and the head block `D` of the next piece (preceded by its prefix `M2`) cancel around
`M1 ++ M2`; `triple`: the same across one whole intermediate piece `Q`.  Blocks are measurement-free, act inside
`W`, `D` undoes `E`, and the gates between them avoid `W`. -/
inductive Cut : Nat → List Program → List Program → Prop
  | nil : Cut 0 [] []
  | keep (p : Program) {n : Nat} {ps ps' : List Program} : Cut n ps ps' → Cut n (p :: ps) (p :: ps')
  | pair (A E M1 M2 D B : Program) (W : Finset Wire) {n : Nat} {ps ps' : List Program}
      (hE : wires E ⊆ W) (hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires (M1 ++ M2))
      (mE : measurementCount E = 0) (mD : measurementCount D = 0)
      (tE : toffoliCount E = 2) (tD : toffoliCount D = 2)
      (inv : ∀ t (a b : List Bool), run D b (run E a t) = t) :
      Cut n ps ps' → Cut (n+1) ((A ++ (E ++ M1)) :: (M2 ++ (D ++ B)) :: ps) ((A ++ M1) :: (M2 ++ B) :: ps')
  | triple (A E M1 Q M2 D B : Program) (W : Finset Wire) {n : Nat} {ps ps' : List Program}
      (hE : wires E ⊆ W) (hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires (M1 ++ (Q ++ M2)))
      (mE : measurementCount E = 0) (mD : measurementCount D = 0)
      (tE : toffoliCount E = 2) (tD : toffoliCount D = 2)
      (inv : ∀ t (a b : List Bool), run D b (run E a t) = t) :
      Cut n ps ps' → Cut (n+1) ((A ++ (E ++ M1)) :: Q :: (M2 ++ (D ++ B)) :: ps) ((A ++ M1) :: Q :: (M2 ++ B) :: ps')

theorem app_congr (X T T' : Program) (h : ∀ m s, run T m s = run T' m s) (m : List Bool) (s : State) :
    run (X ++ T) m s = run (X ++ T') m s := by
  rw [run_append, run_append, h]

/-- Core block cancellation with a prefix and a run-equal suffix. -/
theorem block_cancel (A E M D Y Y' : Program) (W : Finset Wire)
    (hE : wires E ⊆ W) (_hD : wires D ⊆ W) (hM : ∀ q ∈ W, q ∉ wires M)
    (mE : measurementCount E = 0) (mD : measurementCount D = 0)
    (inv : ∀ t (a b : List Bool), run D b (run E a t) = t)
    (hY : ∀ m s, run Y' m s = run Y m s) (m : List Bool) (s : State) :
    run (A ++ (M ++ Y')) m s = run (A ++ (E ++ (M ++ (D ++ Y)))) m s := by
  rw [run_append A (M ++ Y'), run_append A (E ++ (M ++ (D ++ Y)))]
  generalize run A (m.take (measurementCount A)) s = t
  generalize m.drop (measurementCount A) = m'
  rw [run_append M Y', run_append E (M ++ (D ++ Y)), mE, List.take_zero, List.drop_zero,
    run_append M (D ++ Y), run_append D Y, mD, List.take_zero, List.drop_zero, hY,
    cancel_free E M D W hE hM inv t [] _ []]

theorem Cut.run_eq {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') (m : List Bool) (s : State) :
    run ps'.flatten m s = run ps.flatten m s := by
  induction h generalizing m s with
  | nil => rfl
  | keep p _ ih =>
    simp only [List.flatten_cons]
    exact app_congr p _ _ (fun m s => ih m s) m s
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, List.append_assoc]
    have h := block_cancel A E (M1 ++ M2) D (B ++ _) (B ++ _) W hE hD hM mE mD inv
      (fun m s => app_congr B _ _ (fun m s => ih m s) m s) m s
    simpa only [List.append_assoc] using h
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, List.append_assoc]
    have h := block_cancel A E (M1 ++ (Q ++ M2)) D (B ++ _) (B ++ _) W hE hD hM mE mD inv
      (fun m s => app_congr B _ _ (fun m s => ih m s) m s) m s
    simpa only [List.append_assoc] using h


theorem Cut.mc_eq {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    measurementCount ps'.flatten = measurementCount ps.flatten := by
  induction h with
  | nil => rfl
  | keep p _ ih => simp only [List.flatten_cons, measurementCount_append, ih]
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, measurementCount_append, ih, mE, mD]; omega
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, measurementCount_append, ih, mE, mD]; omega

theorem Cut.wires_sub {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    wires ps'.flatten ⊆ wires ps.flatten := by
  induction h with
  | nil => exact Finset.Subset.refl _
  | keep p _ ih =>
    simp only [List.flatten_cons, wires_append]
    exact Finset.union_subset_union (Finset.Subset.refl _) ih
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with ((hq | hq) | (hq | hq) | hq) <;> tauto
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, wires_append]
    intro q hq
    simp only [Finset.mem_union] at hq ⊢
    rcases hq with ((hq | hq) | hq | (hq | hq) | hq) <;> tauto

/-- Each cancelled pair removes two blocks of two Toffolis. -/
theorem Cut.tc_eq {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    toffoliCount ps'.flatten + 4 * n = toffoliCount ps.flatten := by
  induction h with
  | nil => rfl
  | keep p _ ih => simp only [List.flatten_cons, toffoliCount_append]; omega
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, toffoliCount_append]; omega
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, toffoliCount_append]; omega

/-- Every instruction of the cut list is an instruction of the original. -/
theorem Cut.mem {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    ∀ i ∈ ps'.flatten, i ∈ ps.flatten := by
  induction h with
  | nil => exact fun _ h => h
  | keep p _ ih =>
    intro i hi
    simp only [List.flatten_cons, List.mem_append] at hi ⊢
    have := ih i
    tauto
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    intro i hi
    simp only [List.flatten_cons, List.mem_append] at hi ⊢
    have := ih i
    tauto
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    intro i hi
    simp only [List.flatten_cons, List.mem_append] at hi ⊢
    have := ih i
    tauto

theorem Cut.slots_le {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Challenge.gateSlots ps'.flatten ≤ Challenge.gateSlots ps.flatten := by
  induction h with
  | nil => exact le_refl _
  | keep p _ ih => simp only [List.flatten_cons, Challenge.gateSlots_append]; omega
  | pair A E M1 M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, Challenge.gateSlots_append]; omega
  | triple A E M1 Q M2 D B W hE hD hM mE mD tE tD inv _ ih =>
    simp only [List.flatten_cons, Challenge.gateSlots_append]; omega

/-- The two swaps in the other order undo the block too. -/
theorem S2_inv_swap (c a b a' b' : Wire) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b) (hca' : c ≠ a') (hcb' : c ≠ b')
    (hab' : a' ≠ b') (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b')
    (t : State) (m1 m2 : List Bool) : run (S2 c a' b' a b) m2 (run (S2 c a b a' b') m1 t) = t := by
  simp only [S2, run_append, cs_measure, List.take_zero, List.drop_zero]
  rw [cs_run c a b hca hcb hab, cs_run c a' b' hca' hcb' hab', cs_run c a' b' hca' hcb' hab',
    cs_run c a b hca hcb hab]
  apply State.extensionality
  · rfl
  · funext q
    have e1 := hca.symm; have e2 := hcb.symm; have e3 := hab.symm; have e4 := hca'.symm; have e5 := hcb'.symm
    have e6 := hab'.symm; have e7 := h1.symm; have e8 := h2.symm; have e9 := h3.symm; have e10 := h4.symm
    by_cases hc : t.basis c
    · by_cases hqa : q = a
      · subst hqa
        simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
      · by_cases hqb : q = b
        · subst hqb
          simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa]
        · by_cases hqa' : q = a'
          · subst hqa'
            simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hqa,
              hqb]
          · by_cases hqb' : q = b'
            · subst hqb'
              simp [hc, hca, hcb, hca', hcb', hab, hab', h1, h2, h3, h4, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10,
                hqa, hqb, hqa']
            · simp [hc, hca, hcb, hca', hcb', hqa, hqb, hqa', hqb']
    · simp [hc, hca, hcb, hca', hcb']


/-! ## pp7 shapes -/
theorem range_split2 (k : Nat) : List.range (k+2) = List.range k ++ [k, k+1] := by
  rw [List.range_succ, List.range_succ, List.append_assoc]; rfl

/-- The leave's low close ends with the two controlled swaps of its last two rows. -/
theorem lowClose_split (s : Nat) (hL : 2 ≤ Shadow7.lowsP s) :
    ∃ V, Shadow7.leaveLowClose s = V ++
      (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) ++
       Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1))) := by
  have hr : List.range (Shadow7.lowsP s) = List.range (Shadow7.lowsP s - 2) ++ [Shadow7.lowsP s - 2, Shadow7.lowsP s - 1] := by
    have e := range_split2 (Shadow7.lowsP s - 2)
    rwa [show Shadow7.lowsP s - 2 + 2 = Shadow7.lowsP s by omega, show Shadow7.lowsP s - 2 + 1 = Shadow7.lowsP s - 1 by omega] at e
  refine ⟨Partial.xsG ((List.range 15).map (s+16+·)) ++
      (List.range (Shadow7.lowsP s)).map (fun i => GateMirror.Gate.cx (Shadow7.e0P s + 5) (Shadow7.b0P s - 1 + i)) ++
      (List.range (Shadow7.lowsP s - 2)).flatMap
        (fun i => Partial.cswapG (s+30) (Shadow7.b0P s - 1 + i) (Shadow7.a0P s - 1 + i)), ?_⟩
  unfold Shadow7.leaveLowClose
  simp only []
  rw [hr, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem suffix_after (s : Nat) :
    (Shadow7.leaveLowClose s ++ Shadow7.leaveClose s) <:+ CRTBarrel.afterPart s := by
  unfold CRTBarrel.afterPart DeadJoin.after7S DeadJoin.afterRest7S DeadJoin.afterPost7
  simp only [List.append_assoc, List.cons_append]
  repeat (first
    | (with_reducible exact List.suffix_refl _)
    | refine List.IsSuffix.trans ?_ (List.suffix_append _ _)
    | refine List.IsSuffix.trans ?_ (List.suffix_cons _ _))

/-- The window leave (CRT barrel leave) as prefix ++ (two controlled swaps ++ leaveClose). -/
theorem leave_shape (k : Fin 26) (hk : k.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start k)) :
    ∃ X, CRTBarrel.params.leave k = X ++ (GateMirror.forward
      (Partial.cswapG (start k + 30) (Shadow7.b0P (start k) - 1 + (Shadow7.lowsP (start k) - 2))
          (Shadow7.a0P (start k) - 1 + (Shadow7.lowsP (start k) - 2)) ++
        Partial.cswapG (start k + 30) (Shadow7.b0P (start k) - 1 + (Shadow7.lowsP (start k) - 1))
          (Shadow7.a0P (start k) - 1 + (Shadow7.lowsP (start k) - 1))) ++
      GateMirror.forward (Shadow7.leaveClose (start k))) := by
  obtain ⟨Z, hZ⟩ := suffix_after (start k)
  obtain ⟨V, hV⟩ := lowClose_split (start k) hL
  refine ⟨GateMirror.forward (CRTBarrel.before (start k)) ++ CRTBarrel.barrel (start k) false ++
    GateMirror.forward Z ++ GateMirror.forward V, ?_⟩
  show CRTBarrel.leave k = _
  unfold CRTBarrel.leave
  simp only [if_pos hk]
  rw [← hZ, hV]
  simp only [GateMirror.forward, List.map_append, List.append_assoc]


/-! ## pp7 window pieces -/
open ECDSAAdd.Entrant ECDSAAdd.Entrant.StairPacket

abbrev P : WindowFold.Pieces Program := CRTBarrel.params

def K (j : Fin 26) : Nat := (GateMirror.forward (Shadow7.leaveClose (start j))).length

def leaveC (j : Fin 26) : Program :=
  if j.val ≤ 24 then (P.leave j).take ((P.leave j).length - K j - 6) ++ (P.leave j).drop ((P.leave j).length - K j)
  else P.leave j
def unleaveC (j : Fin 26) : Program :=
  if j.val ≤ 24 then (P.leaveInv j).take (K j) ++ (P.leaveInv j).drop (K j + 6) else P.leaveInv j
def enterC (j : Fin 26) : Program := (P.enter j).drop 6
def enterInvC (j : Fin 26) : Program := (P.enterInv j).take ((P.enterInv j).length - 6)
def portalC (t : Nat) : Program := (P.portal t).take ((P.portal t).length - 6)
def portalInvC (t : Nat) : Program := (P.portalInv t).drop 6

def Pcut : WindowFold.Pieces Program where
  enter := enterC
  enterInv := enterInvC
  leave := leaveC
  leaveInv := unleaveC
  load := P.load
  restore := P.restore
  portal := portalC
  portalInv := portalInvC
  park := P.park
  parkInv := P.parkInv
  exitLoad := P.exitLoad
  exitRestore := P.exitRestore
  routed := P.routed
  unrouted := P.unrouted
  pack := P.pack
  unpack := P.unpack
  tick := P.tick
  receiver := P.receiver

attribute [irreducible] enterC enterInvC leaveC unleaveC portalC portalInvC

theorem Pcut_enter (j : Fin 26) : Pcut.enter j = enterC j := rfl
theorem Pcut_enterInv (j : Fin 26) : Pcut.enterInv j = enterInvC j := rfl
theorem Pcut_leave (j : Fin 26) : Pcut.leave j = leaveC j := rfl
theorem Pcut_leaveInv (j : Fin 26) : Pcut.leaveInv j = unleaveC j := rfl
theorem Pcut_portal (t : Nat) : Pcut.portal t = portalC t := rfl
theorem Pcut_portalInv (t : Nat) : Pcut.portalInv t = portalInvC t := rfl
theorem Pcut_park (t : Nat) : Pcut.park t = P.park t := rfl
theorem Pcut_parkInv (t : Nat) : Pcut.parkInv t = P.parkInv t := rfl

/-- The leave's tail block, as a program. -/
def Eblk (s : Nat) : Program := GateMirror.forward
  (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) ++
   Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)))

theorem Eblk_S2 (s : Nat) : Eblk s = S2 (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2))
    (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1))
    (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)) := rfl

theorem tc_Eblk (s : Nat) : toffoliCount (Eblk s) = 2 := rfl

theorem leaveC_eq (j : Fin 26) (hj : j.val ≤ 24) (X : Program)
    (hX : P.leave j = X ++ (Eblk (start j) ++ GateMirror.forward (Shadow7.leaveClose (start j)))) :
    Pcut.leave j = X ++ GateMirror.forward (Shadow7.leaveClose (start j)) := by
  rw [Pcut_leave]
  have hE : (Eblk (start j)).length = 6 := rfl
  unfold leaveC
  rw [if_pos hj, hX]
  simp only [List.length_append, hE, K]
  rw [show X.length + (6 + (GateMirror.forward (Shadow7.leaveClose (start j))).length) -
      (GateMirror.forward (Shadow7.leaveClose (start j))).length - 6 = X.length by omega,
    show X.length + (6 + (GateMirror.forward (Shadow7.leaveClose (start j))).length) -
      (GateMirror.forward (Shadow7.leaveClose (start j))).length = X.length + 6 by omega]
  rw [List.take_left' rfl, ← List.append_assoc, List.drop_left' (by simp [hE])]

/-- Forward boundary leave_k → enter_{k+1}. -/
theorem bnd_fwd (k : Nat) (hk : k < 24)
    (hhead : (P.enter ⟨k+1, by omega⟩).take 6 = Eblk (start ⟨k, by omega⟩))
    (hL : 2 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Eblk (start ⟨k, by omega⟩)),
      q ∉ wires (GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++ []))
    (inv : ∀ t (a b : List Bool), run (Eblk (start ⟨k, by omega⟩)) b (run (Eblk (start ⟨k, by omega⟩)) a t) = t)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.leave ⟨k, by omega⟩ :: P.enter ⟨k+1, by omega⟩ :: ps)
      (Pcut.leave ⟨k, by omega⟩ :: Pcut.enter ⟨k+1, by omega⟩ :: ps') := by
  obtain ⟨X, hX⟩ := leave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hX' : P.leave ⟨k, by omega⟩ = X ++ (Eblk (start ⟨k, by omega⟩) ++
      GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩))) := hX
  have hC := leaveC_eq ⟨k, by omega⟩ (by simp; omega) X hX'
  have hEn : P.enter ⟨k+1, by omega⟩ = [] ++ (Eblk (start ⟨k, by omega⟩) ++ enterC ⟨k+1, by omega⟩) := by
    rw [← hhead]; simp only [List.nil_append, enterC, List.take_append_drop]
  have hEnC : Pcut.enter ⟨k+1, by omega⟩ = [] ++ enterC ⟨k+1, by omega⟩ := by
    rw [Pcut_enter, List.nil_append]
  rw [hX', hC, hEn, hEnC]
  exact Cut.pair X _ _ [] _ _ (wires (Eblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl (tc_Eblk _) (tc_Eblk _) inv h

/-- Forward boundary portal → enter_0. -/
theorem bnd_portal (t : Nat) (j : Fin 26)
    (hhead : (P.enter j).take 6 = (P.portal t).drop ((P.portal t).length - 6))
    (inv : ∀ u (a b : List Bool), run ((P.portal t).drop ((P.portal t).length - 6)) b
      (run ((P.portal t).drop ((P.portal t).length - 6)) a u) = u)
    (m0 : measurementCount ((P.portal t).drop ((P.portal t).length - 6)) = 0)
    (t0 : toffoliCount ((P.portal t).drop ((P.portal t).length - 6)) = 2)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.portal t :: P.enter j :: ps) (Pcut.portal t :: Pcut.enter j :: ps') := by
  have h1 : P.portal t = portalC t ++ ((P.portal t).drop ((P.portal t).length - 6) ++ []) := by
    simp only [portalC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.portal t = portalC t ++ [] := by
    rw [Pcut_portal, List.append_nil]
  have h3 : P.enter j = [] ++ ((P.portal t).drop ((P.portal t).length - 6) ++ enterC j) := by
    rw [← hhead]; simp only [List.nil_append, enterC, List.take_append_drop]
  have h4 : Pcut.enter j = [] ++ enterC j := by
    rw [Pcut_enter, List.nil_append]
  rw [h1, h2, h3, h4]
  exact Cut.pair _ _ [] [] _ _ (wires ((P.portal t).drop ((P.portal t).length - 6))) (Finset.Subset.refl _)
    (Finset.Subset.refl _) (by intro q _; simp [wires]) m0 m0 t0 t0 inv h

/-- Forward exit boundary leave_24 → park → portalInv. -/
theorem bnd_exit (k : Nat) (hk : k ≤ 24) (e : Nat)
    (hL : 2 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Eblk (start ⟨k, by omega⟩)),
      q ∉ wires (GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++ (P.park e ++ [])))
    (hsub : wires ((P.portalInv e).take 6) ⊆ wires (Eblk (start ⟨k, by omega⟩)))
    (inv : ∀ u (a b : List Bool), run ((P.portalInv e).take 6) b (run (Eblk (start ⟨k, by omega⟩)) a u) = u)
    (mD : measurementCount ((P.portalInv e).take 6) = 0)
    (tD : toffoliCount ((P.portalInv e).take 6) = 2)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.leave ⟨k, by omega⟩ :: P.park e :: P.portalInv e :: ps)
      (Pcut.leave ⟨k, by omega⟩ :: Pcut.park e :: Pcut.portalInv e :: ps') := by
  obtain ⟨X, hX⟩ := leave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hX' : P.leave ⟨k, by omega⟩ = X ++ (Eblk (start ⟨k, by omega⟩) ++
      GateMirror.forward (Shadow7.leaveClose (start ⟨k, by omega⟩))) := hX
  have hC := leaveC_eq ⟨k, by omega⟩ (by simp; omega) X hX'
  have hPI : P.portalInv e = [] ++ ((P.portalInv e).take 6 ++ portalInvC e) := by
    simp only [List.nil_append, portalInvC, List.take_append_drop]
  have hPIC : Pcut.portalInv e = [] ++ portalInvC e := by
    rw [Pcut_portalInv, List.nil_append]
  have hPark : Pcut.park e = P.park e := Pcut_park e
  rw [hX', hC, hPI, hPIC, hPark]
  exact Cut.triple X _ _ (P.park e) [] _ _ (wires (Eblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) hsub
    havoid rfl mD (tc_Eblk _) tD inv h

/-- Ends of the reverse walk use the inverse window pieces. -/
theorem inv_app (a b : List GateMirror.Gate) : GateMirror.inverse (a ++ b) = GateMirror.inverse b ++ GateMirror.inverse a := by
  simp only [GateMirror.inverse, List.map_append, List.reverse_append]

/-- The reverse leave: inverse leaveClose, then the swapped block, then the rest. -/
def Dblk (s : Nat) : Program := GateMirror.inverse
  (Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) ++
   Partial.cswapG (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1)))

theorem tc_Dblk (s : Nat) : toffoliCount (Dblk s) = 2 := rfl

theorem unleave_shape (k : Fin 26) (hk : k.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start k)) :
    ∃ R, CRTBarrel.params.leaveInv k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ (Dblk (start k) ++ R) := by
  obtain ⟨Z, hZ⟩ := suffix_after (start k)
  obtain ⟨V, hV⟩ := lowClose_split (start k) hL
  refine ⟨GateMirror.inverse V ++ GateMirror.inverse Z ++ CRTBarrel.barrel (start k) true ++
    GateMirror.inverse (CRTBarrel.before (start k)), ?_⟩
  show CRTBarrel.unleave k = _
  unfold CRTBarrel.unleave
  simp only [if_pos hk]
  rw [← hZ, hV]
  simp only [Dblk, inv_app, List.append_assoc]

theorem unleaveC_eq (j : Fin 26) (hj : j.val ≤ 24) (R : Program)
    (hR : P.leaveInv j = GateMirror.inverse (Shadow7.leaveClose (start j)) ++ (Dblk (start j) ++ R)) :
    Pcut.leaveInv j = GateMirror.inverse (Shadow7.leaveClose (start j)) ++ R := by
  rw [Pcut_leaveInv]
  have hD : (Dblk (start j)).length = 6 := rfl
  have hK : (GateMirror.inverse (Shadow7.leaveClose (start j))).length = K j := by
    simp only [K, GateMirror.inverse, GateMirror.forward, List.length_reverse, List.length_map]
  unfold unleaveC
  rw [if_pos hj, hR, ← hK, List.take_left' rfl]
  rw [show (GateMirror.inverse (Shadow7.leaveClose (start j))).length + 6 =
      (GateMirror.inverse (Shadow7.leaveClose (start j)) ++ Dblk (start j)).length by simp [hD]]
  rw [← List.append_assoc, List.drop_left' rfl]

/-- Reverse boundary enterInv_{k+1} → leaveInv_k. -/
theorem bnd_rev (k : Nat) (hk : k < 24)
    (htail : (P.enterInv ⟨k+1, by omega⟩).drop ((P.enterInv ⟨k+1, by omega⟩).length - 6) = Dblk (start ⟨k, by omega⟩))
    (hL : 2 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Dblk (start ⟨k, by omega⟩)),
      q ∉ wires ([] ++ GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩))))
    (inv : ∀ u (a b : List Bool), run (Dblk (start ⟨k, by omega⟩)) b (run (Dblk (start ⟨k, by omega⟩)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.enterInv ⟨k+1, by omega⟩ :: P.leaveInv ⟨k, by omega⟩ :: ps)
      (Pcut.enterInv ⟨k+1, by omega⟩ :: Pcut.leaveInv ⟨k, by omega⟩ :: ps') := by
  obtain ⟨R, hR⟩ := unleave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hR' : P.leaveInv ⟨k, by omega⟩ = GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++
      (Dblk (start ⟨k, by omega⟩) ++ R) := hR
  have hC := unleaveC_eq ⟨k, by omega⟩ (by simp; omega) R hR'
  have h1 : P.enterInv ⟨k+1, by omega⟩ = enterInvC ⟨k+1, by omega⟩ ++ (Dblk (start ⟨k, by omega⟩) ++ []) := by
    rw [← htail]; simp only [enterInvC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.enterInv ⟨k+1, by omega⟩ = enterInvC ⟨k+1, by omega⟩ ++ [] := by
    rw [Pcut_enterInv, List.append_nil]
  rw [h1, h2, hR', hC]
  exact Cut.pair _ _ [] _ _ R (wires (Dblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) (Finset.Subset.refl _)
    havoid rfl rfl (tc_Dblk _) (tc_Dblk _) inv h

/-- Reverse exit boundary portal → parkInv → leaveInv_24. -/
theorem bnd_rev_exit (k : Nat) (hk : k ≤ 24) (e : Nat)
    (htail : (P.portal e).drop ((P.portal e).length - 6) = Eblk (start ⟨k, by omega⟩))
    (hL : 2 ≤ Shadow7.lowsP (start ⟨k, by omega⟩))
    (havoid : ∀ q ∈ wires (Eblk (start ⟨k, by omega⟩)),
      q ∉ wires ([] ++ (P.parkInv e ++ GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩)))))
    (hsub : wires (Dblk (start ⟨k, by omega⟩)) ⊆ wires (Eblk (start ⟨k, by omega⟩)))
    (inv : ∀ u (a b : List Bool), run (Dblk (start ⟨k, by omega⟩)) b (run (Eblk (start ⟨k, by omega⟩)) a u) = u)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.portal e :: P.parkInv e :: P.leaveInv ⟨k, by omega⟩ :: ps)
      (Pcut.portal e :: Pcut.parkInv e :: Pcut.leaveInv ⟨k, by omega⟩ :: ps') := by
  obtain ⟨R, hR⟩ := unleave_shape ⟨k, by omega⟩ (by simp; omega) hL
  have hR' : P.leaveInv ⟨k, by omega⟩ = GateMirror.inverse (Shadow7.leaveClose (start ⟨k, by omega⟩)) ++
      (Dblk (start ⟨k, by omega⟩) ++ R) := hR
  have hC := unleaveC_eq ⟨k, by omega⟩ (by simp; omega) R hR'
  have h1 : P.portal e = portalC e ++ (Eblk (start ⟨k, by omega⟩) ++ []) := by
    rw [← htail]; simp only [portalC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.portal e = portalC e ++ [] := by
    rw [Pcut_portal, List.append_nil]
  have h3 : Pcut.parkInv e = P.parkInv e := Pcut_parkInv e
  rw [h1, h2, h3, hR', hC]
  exact Cut.triple _ _ [] (P.parkInv e) _ _ R (wires (Eblk (start ⟨k, by omega⟩))) (Finset.Subset.refl _) hsub
    havoid rfl rfl (tc_Eblk _) (tc_Dblk _) inv h

/-- Reverse end boundary enterInv_0 → portalInv. -/
theorem bnd_rev_end (j : Fin 26) (t : Nat)
    (hhead : (P.portalInv t).take 6 = (P.enterInv j).drop ((P.enterInv j).length - 6))
    (inv : ∀ u (a b : List Bool), run ((P.enterInv j).drop ((P.enterInv j).length - 6)) b
      (run ((P.enterInv j).drop ((P.enterInv j).length - 6)) a u) = u)
    (m0 : measurementCount ((P.enterInv j).drop ((P.enterInv j).length - 6)) = 0)
    (t0 : toffoliCount ((P.enterInv j).drop ((P.enterInv j).length - 6)) = 2)
    {n : Nat} {ps ps' : List Program} (h : Cut n ps ps') :
    Cut (n+1) (P.enterInv j :: P.portalInv t :: ps) (Pcut.enterInv j :: Pcut.portalInv t :: ps') := by
  have h1 : P.enterInv j = enterInvC j ++ ((P.enterInv j).drop ((P.enterInv j).length - 6) ++ []) := by
    simp only [enterInvC, List.append_nil, List.take_append_drop]
  have h2 : Pcut.enterInv j = enterInvC j ++ [] := by
    rw [Pcut_enterInv, List.append_nil]
  have h3 : P.portalInv t = [] ++ ((P.enterInv j).drop ((P.enterInv j).length - 6) ++ portalInvC t) := by
    rw [← hhead]; simp only [List.nil_append, portalInvC, List.take_append_drop]
  have h4 : Pcut.portalInv t = [] ++ portalInvC t := by
    rw [Pcut_portalInv, List.nil_append]
  rw [h1, h2, h3, h4]
  exact Cut.pair _ _ [] [] _ _ (wires ((P.enterInv j).drop ((P.enterInv j).length - 6))) (Finset.Subset.refl _)
    (Finset.Subset.refl _) (by intro q _; simp [wires]) m0 m0 t0 t0 inv h


/-! ## List-based wire checks (cheap kernel decides) -/

def cwl : List Correction → List Wire
  | [] => []
  | .Z t :: cs => t :: cwl cs
  | .CZ a b :: cs => a :: b :: cwl cs

def iwl : Instr → List Wire
  | .X t => [t]
  | .CX c t => [c, t]
  | .CCX a b t => [a, b, t]
  | .measureX t c0 c1 => t :: (cwl c0 ++ cwl c1)

def wl : Program → List Wire
  | [] => []
  | i :: p => iwl i ++ wl p

theorem mem_cwl (q : Wire) (cs : List Correction) : q ∈ correctionWires cs ↔ q ∈ cwl cs := by
  induction cs with
  | nil => simp [correctionWires, cwl]
  | cons c cs ih => cases c <;> simp [correctionWires, cwl, ih]

theorem mem_iwl (q : Wire) (i : Instr) : q ∈ i.wires ↔ q ∈ iwl i := by
  cases i <;> simp [Instr.wires, iwl, mem_cwl, or_assoc]

theorem mem_wl (q : Wire) (P : Program) : q ∈ wires P ↔ q ∈ wl P := by
  induction P with
  | nil => simp [wires, wl]
  | cons i p ih => simp [wires, wl, mem_iwl, ih]

theorem avoid_of_check (E M : Program) (h : (wl E).all (fun q => !((wl M).contains q)) = true) :
    ∀ q ∈ wires E, q ∉ wires M := by
  intro q hq hm
  rw [mem_wl] at hq hm
  have h1 := List.all_eq_true.mp h q hq
  have h2 : q ∉ wl M := by simpa using h1
  exact h2 hm

theorem sub_of_check (D E : Program) (h : (wl D).all (fun q => (wl E).contains q) = true) :
    wires D ⊆ wires E := by
  intro q hq
  rw [mem_wl] at hq ⊢
  have h1 := List.all_eq_true.mp h q hq
  simpa using h1

/-! ## Block facts -/

def dist5 (c a b a' b' : Wire) : Prop :=
  c ≠ a ∧ c ≠ b ∧ a ≠ b ∧ c ≠ a' ∧ c ≠ b' ∧ a' ≠ b' ∧ a ≠ a' ∧ a ≠ b' ∧ b ≠ a' ∧ b ≠ b'

instance (c a b a' b' : Wire) : Decidable (dist5 c a b a' b') := by unfold dist5; infer_instance

theorem inv_of_eq (X : Program) (c a b a' b' : Wire) (hX : X = S2 c a b a' b') (hd : dist5 c a b a' b') :
    ∀ t (m1 m2 : List Bool), run X m2 (run X m1 t) = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hd
  intro t m1 m2; subst hX; exact S2_inv c a b a' b' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 t m1 m2

theorem inv_swap_of_eq (X Y : Program) (c a b a' b' : Wire) (hX : X = S2 c a b a' b') (hY : Y = S2 c a' b' a b)
    (hd : dist5 c a b a' b') : ∀ t (m1 m2 : List Bool), run Y m2 (run X m1 t) = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hd
  intro t m1 m2; subst hX; subst hY; exact S2_inv_swap c a b a' b' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 t m1 m2

theorem S2_measure0 (X : Program) (c a b a' b' : Wire) (hX : X = S2 c a b a' b') : measurementCount X = 0 := by
  subst hX; rfl

theorem Dblk_S2 (s : Nat) : Dblk s = S2 (s+30) (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 1)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 1))
    (Shadow7.b0P s - 1 + (Shadow7.lowsP s - 2)) (Shadow7.a0P s - 1 + (Shadow7.lowsP s - 2)) := rfl

theorem rest7_eq : WindowParams7.rest7 = ([⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩] : List (Fin 26)) := by
  decide

set_option maxHeartbeats 4000000 in
theorem fwd_cut (d : Bool) :
    Cut 26 (WindowFold.forwardL P d WindowParams.first WindowParams7.rest7)
      (WindowFold.forwardL Pcut d WindowParams.first WindowParams7.rest7) := by
  rw [rest7_eq]
  simp only [WindowFold.forwardL, WindowFold.firstF, WindowFold.chainF, WindowFold.nextF, WindowFold.exitF,
    List.cons_append, List.nil_append]
  apply bnd_portal (start WindowParams.first) WindowParams.first (by decide +kernel)
    (inv_of_eq _ (start WindowParams.first + 15) (801 + Shadow7.sbP (start WindowParams.first)) (Shadow7.a0P (start WindowParams.first) - 1) (801 + Shadow7.sbP (start WindowParams.first) + 1) (Shadow7.a0P (start WindowParams.first) - 1 + 1) (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ (start WindowParams.first + 15) (801 + Shadow7.sbP (start WindowParams.first)) (Shadow7.a0P (start WindowParams.first) - 1) (801 + Shadow7.sbP (start WindowParams.first) + 1) (Shadow7.a0P (start WindowParams.first) - 1 + 1) (by decide +kernel)) (by decide +kernel)
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 0 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 1 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 2 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 3 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 4 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 5 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 6 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 7 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 8 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 9 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 10 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 11 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 12 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 13 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 14 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 15 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 16 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 17 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 18 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 19 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 20 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 21 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 22 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_fwd 23 (by decide) (by decide +kernel) (by decide +kernel) (avoid_of_check _ _ (by decide +kernel))
    (inv_of_eq _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel))
  apply Cut.keep; apply Cut.keep; apply Cut.keep; apply Cut.keep
  apply bnd_exit 24 (by decide) _ (by decide +kernel) (avoid_of_check _ _ (by decide +kernel)) (sub_of_check _ _ (by decide +kernel))
    (inv_swap_of_eq _ _ _ _ _ _ _ (Eblk_S2 _) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel)
  apply Cut.keep; apply Cut.keep; apply Cut.keep
  exact Cut.nil

set_option maxHeartbeats 4000000 in
theorem rev_cut (d : Bool) :
    Cut 26 (WindowFold.reverseL P d WindowParams.first WindowParams7.rest7)
      (WindowFold.reverseL Pcut d WindowParams.first WindowParams7.rest7) := by
  rw [rest7_eq]
  simp only [WindowFold.reverseL, WindowFold.exitR, WindowFold.chainR, WindowFold.nextR, WindowFold.firstR,
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
    (inv_of_eq _ (start WindowParams.first + 15) (801 + Shadow7.sbP (start WindowParams.first) + 1) (Shadow7.a0P (start WindowParams.first) - 1 + 1) (801 + Shadow7.sbP (start WindowParams.first)) (Shadow7.a0P (start WindowParams.first) - 1) (by decide +kernel) (by decide +kernel))
    (S2_measure0 _ (start WindowParams.first + 15) (801 + Shadow7.sbP (start WindowParams.first) + 1) (Shadow7.a0P (start WindowParams.first) - 1 + 1) (801 + Shadow7.sbP (start WindowParams.first)) (Shadow7.a0P (start WindowParams.first) - 1) (by decide +kernel)) (by decide +kernel)
  exact Cut.nil


/-! ## Per-piece count deltas (for the ledger) -/

theorem tc_S2 (c a b a' b' : Wire) : toffoliCount (S2 c a b a' b') = 2 := rfl

theorem tail_counts (X : Program) (hE : ∃ c a b a' b', X.drop (X.length - 6) = S2 c a b a' b') :
    toffoliCount X = toffoliCount (X.take (X.length - 6)) + 2 ∧
      measurementCount X = measurementCount (X.take (X.length - 6)) := by
  obtain ⟨c, a, b, a', b', h⟩ := hE
  have e := List.take_append_drop (X.length - 6) X
  have t1 : toffoliCount X = toffoliCount (X.take (X.length - 6)) + toffoliCount (X.drop (X.length - 6)) := by
    rw [← toffoliCount_append, e]
  have m1 : measurementCount X = measurementCount (X.take (X.length - 6)) +
      measurementCount (X.drop (X.length - 6)) := by
    rw [← measurementCount_append, e]
  rw [h, tc_S2] at t1
  rw [h, S2_measure0 _ c a b a' b' rfl] at m1
  exact ⟨t1, by omega⟩

theorem head_counts (X : Program) (hE : ∃ c a b a' b', X.take 6 = S2 c a b a' b') :
    toffoliCount X = toffoliCount (X.drop 6) + 2 ∧ measurementCount X = measurementCount (X.drop 6) := by
  obtain ⟨c, a, b, a', b', h⟩ := hE
  have e := List.take_append_drop 6 X
  have t1 : toffoliCount X = toffoliCount (X.take 6) + toffoliCount (X.drop 6) := by
    rw [← toffoliCount_append, e]
  have m1 : measurementCount X = measurementCount (X.take 6) + measurementCount (X.drop 6) := by
    rw [← measurementCount_append, e]
  rw [h, tc_S2] at t1
  rw [h, S2_measure0 _ c a b a' b' rfl] at m1
  exact ⟨by omega, by omega⟩


theorem enter_counts (j : Fin 26) (hE : ∃ c a b a' b', (P.enter j).take 6 = S2 c a b a' b') :
    toffoliCount (P.enter j) = toffoliCount (Pcut.enter j) + 2 ∧
      measurementCount (P.enter j) = measurementCount (Pcut.enter j) := by
  rw [Pcut_enter, enterC]
  exact head_counts _ hE

theorem leave_counts (k : Fin 26) (hk : k.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start k)) :
    toffoliCount (P.leave k) = toffoliCount (Pcut.leave k) + 2 ∧
      measurementCount (P.leave k) = measurementCount (Pcut.leave k) := by
  obtain ⟨X, hX⟩ := leave_shape k hk hL
  have hX' : P.leave k = X ++ (Eblk (start k) ++ GateMirror.forward (Shadow7.leaveClose (start k))) := hX
  rw [leaveC_eq k hk X hX', hX']
  simp only [toffoliCount_append, measurementCount_append, Eblk_S2, tc_S2,
    S2_measure0 _ _ _ _ _ _ rfl]
  constructor <;> omega

theorem leaveInv_counts (k : Fin 26) (hk : k.val ≤ 24) (hL : 2 ≤ Shadow7.lowsP (start k)) :
    toffoliCount (P.leaveInv k) = toffoliCount (Pcut.leaveInv k) + 2 ∧
      measurementCount (P.leaveInv k) = measurementCount (Pcut.leaveInv k) := by
  obtain ⟨R, hR⟩ := unleave_shape k hk hL
  have hR' : P.leaveInv k = GateMirror.inverse (Shadow7.leaveClose (start k)) ++ (Dblk (start k) ++ R) := hR
  rw [unleaveC_eq k hk R hR', hR']
  simp only [toffoliCount_append, measurementCount_append, Dblk_S2, tc_S2,
    S2_measure0 _ _ _ _ _ _ rfl]
  constructor <;> omega

/-- FRED-CUT on the window walk: the cut walk has the same run as the original, for every state and tape. -/
theorem walk_run_eq (d : Bool) (m : List Bool) (s : State) :
    run (WindowFold.forwardW Pcut d WindowParams.first WindowParams7.rest7) m s =
      run (WindowFold.forwardW P d WindowParams.first WindowParams7.rest7) m s :=
  (fwd_cut d).run_eq m s

theorem walk_run_eq_rev (d : Bool) (m : List Bool) (s : State) :
    run (WindowFold.reverseW Pcut d WindowParams.first WindowParams7.rest7) m s =
      run (WindowFold.reverseW P d WindowParams.first WindowParams7.rest7) m s :=
  (rev_cut d).run_eq m s


theorem walk_mc_eq (d : Bool) :
    measurementCount (WindowFold.forwardW Pcut d WindowParams.first WindowParams7.rest7) =
      measurementCount (WindowFold.forwardW P d WindowParams.first WindowParams7.rest7) :=
  (fwd_cut d).mc_eq

theorem walk_mc_eq_rev (d : Bool) :
    measurementCount (WindowFold.reverseW Pcut d WindowParams.first WindowParams7.rest7) =
      measurementCount (WindowFold.reverseW P d WindowParams.first WindowParams7.rest7) :=
  (rev_cut d).mc_eq

theorem walk_wires_sub (d : Bool) :
    wires (WindowFold.forwardW Pcut d WindowParams.first WindowParams7.rest7) ⊆
      wires (WindowFold.forwardW P d WindowParams.first WindowParams7.rest7) :=
  (fwd_cut d).wires_sub

theorem walk_wires_sub_rev (d : Bool) :
    wires (WindowFold.reverseW Pcut d WindowParams.first WindowParams7.rest7) ⊆
      wires (WindowFold.reverseW P d WindowParams.first WindowParams7.rest7) :=
  (rev_cut d).wires_sub

end ECDSAAdd.Entrant.StairPacket.FredCut
end
-- ==== end folded FredCut ====
