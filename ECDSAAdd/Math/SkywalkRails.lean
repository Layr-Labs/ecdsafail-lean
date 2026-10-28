import Mathlib.Tactic

namespace ECDSAAdd.SkywalkRails

/-- Arithmetic sign, including the unique nonnegative encoding of zero. -/
def neg (x : Int) : Bool := decide (x<0)

def odd (x : Int) : Bool := decide (x%2≠0)

def sameSign (x y : Int) : Bool := decide (neg x=neg y)

@[ext] structure State where
  a : Int
  b : Int
  g : Bool
  deriving DecidableEq

@[ext] structure Tick where
  h : Int
  k : Int
  g : Bool
  s : Bool
  deriving DecidableEq

/-- Exactly one rail is even. The parity of the first rail chooses it. -/
def route (a b : Int) : Int×Int := if odd a then (b,a) else (a,b)

/-- Signed Skywalk tick. Arithmetic remains over unbounded exact integers;
word-width bounds are separate obligations for the circuit implementation. -/
def step (z : State) : Tick :=
  let eo := route z.a z.b
  let h := eo.1/2
  let k := if sameSign eo.1 eo.2 then eo.2-h else eo.2+h
  ⟨h,k,z.g ^^ odd z.a,neg eo.2 ^^ neg k⟩

/-- Undo the signed arithmetic and routing from the orientation/sign history. -/
def unstep (prev : Bool) (t : Tick) : State :=
  let c := t.g ^^ prev
  let q := decide (neg t.h=(neg t.k ^^ t.s))
  let e := 2*t.h
  let o := if q then t.k+t.h else t.k-t.h
  if c then ⟨o,e,prev⟩ else ⟨e,o,prev⟩

theorem route_even (a b : Int) (hp : (a+b)%2=1) : (route a b).1%2=0 := by
  by_cases ha : a%2=0
  · simp [route,odd,ha]
  · have hb : b%2=0 := by omega
    simp [route,odd,ha,hb]

/-- Arithmetic right shift preserves sign on even integers, including zero. -/
theorem neg_half (e : Int) (he : e%2=0) : neg (e/2)=neg e := by
  by_cases hn : e<0
  · have hh : e/2<0 := by omega
    simp [neg,hn,hh]
  · have hh : ¬e/2<0 := by omega
    simp [neg,hn,hh]

theorem half_zero_iff (e : Int) (he : e%2=0) : e/2=0 ↔ e=0 := by omega

theorem double_half (e : Int) (he : e%2=0) : 2*(e/2)=e := by omega

private theorem sign_cancel (a b : Bool) : (b ^^ (a ^^ b))=a := by
  cases a <;> cases b <;> rfl

private theorem orientation_cancel (g c : Bool) : ((g ^^ c) ^^ g)=c := by
  cases g <;> cases c <;> rfl

/-- The recorded sign flip reconstructs the pre-add sign even when the
post-add rail is exactly zero. No strict-order assumption is needed. -/
theorem sign_recovery (o k : Int) : (neg k ^^ (neg o ^^ neg k))=neg o :=
  sign_cancel (neg o) (neg k)

theorem arithmetic_reverse (e o : Int) (he : e%2=0) :
    let h := e/2
    let k := if sameSign e o then o-h else o+h
    let s := neg o ^^ neg k
    let q := decide (neg h=(neg k ^^ s))
    (2*h,if q then k+h else k-h)=(e,o) := by
  dsimp only
  rw [sign_recovery,neg_half e he]
  change (2*(e/2),if sameSign e o then
    (if sameSign e o then o-e/2 else o+e/2)+e/2 else
    (if sameSign e o then o-e/2 else o+e/2)-e/2)=(e,o)
  rw [double_half e he]
  split_ifs <;> simp

/-- Every signed tick is exactly invertible on the odd-sum invariant. -/
theorem unstep_step (z : State) (hp : (z.a+z.b)%2=1) :
    unstep z.g (step z)=z := by
  have he := route_even z.a z.b hp
  have hr := arithmetic_reverse (route z.a z.b).1 (route z.a z.b).2 he
  dsimp only at hr
  rw [sign_recovery,neg_half _ he] at hr
  have ho := orientation_cancel z.g (odd z.a)
  dsimp only [unstep,step] at ⊢
  rw [ho,sign_recovery,neg_half _ he]
  have hd := double_half (route z.a z.b).1 he
  cases hc : odd z.a
  · simp only [route,hc,Bool.false_eq_true,if_false] at hr hd ⊢
    have hv := congrArg Prod.snd hr
    dsimp only at hv
    rw [hd,hv]
  · simp only [route,hc,if_true] at hr hd ⊢
    have hv := congrArg Prod.snd hr
    dsimp only at hv
    rw [hd,hv]

def signed (s : Bool) (u : Int) : Int := if s then -u else u

/-- g=true means that the first rail is the smaller one. The larger rail
is positive; a zero smaller rail has the unique value zero for either s. -/
def encode (g s : Bool) (u v : Int) : State :=
  if g then ⟨signed s u,u+v,g⟩ else ⟨u+v,signed s u,g⟩

theorem encode_odd_sum (g s : Bool) (u v : Int) (hv : v%2=1) :
    ((encode g s u v).a+(encode g s u v).b)%2=1 := by
  cases g <;> cases s <;> simp only [encode,signed,if_true,if_false,
    Bool.false_eq_true]
  all_goals omega

theorem encode_route_even (g s : Bool) (u v : Int) (hv : v%2=1) :
    (route (encode g s u v).a (encode g s u v).b).1%2=0 :=
  route_even _ _ (encode_odd_sum g s u v hv)

/-- Terminal states are retained exactly: one tick changes (v,0) to (0,v),
and all following ticks keep (0,v), without a fabricated negative zero. -/
theorem terminal_step (g s : Bool) (v : Int) (hv : 0<v) (hodd : v%2=1) :
    step (encode g s 0 v)=⟨0,v,true,false⟩ := by
  have hvn : ¬v<0 := by omega
  have hvodd : v%2≠0 := by omega
  cases g <;> cases s <;>
    simp [step,encode,signed,route,odd,sameSign,neg,hvn,hvodd]

theorem zero_sign (s : Bool) : signed s 0=0 := by cases s <;> simp [signed]

/-- The new orientation identifies the even-u branch, independently of the
old orientation and the smaller rail's sign. -/
theorem step_orientation (g s : Bool) (u v : Int) (hv : v%2=1) :
    (step (encode g s u v)).g=decide (u%2=0) := by
  by_cases hu : u%2=0
  · have hl : (u+v)%2≠0 := by omega
    have hs : (-u)%2=0 := by omega
    cases g <;> cases s <;> simp [step,encode,signed,odd,hu,hl,hs]
  · have hl : (u+v)%2=0 := by omega
    cases g <;> cases s <;> simp [step,encode,signed,odd,hu,hl]

theorem step_encode_even (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) (hue : u%2=0) :
    step (encode g s u v)=⟨signed s (u/2),u/2+v,true,false⟩ := by
  by_cases hz : u=0
  · subst u
    simpa [signed] using terminal_step g s v hv hvo
  · have hup : 0<u := by omega
    have hLodd : (u+v)%2≠0 := by omega
    have hnue : (-u)%2=0 := by omega
    have hLp : ¬u+v<0 := by omega
    have hun : ¬u<0 := by omega
    have hdiv : (-u)/2=-(u/2) := by omega
    have hdiff : u+v-u/2=u/2+v := by omega
    have hsum : u+v+-(u/2)=u/2+v := by omega
    have hkn : ¬u/2+v<0 := by omega
    cases g <;> cases s <;>
      simp [step,encode,signed,route,odd,sameSign,neg,hue,hLodd,hnue,
        hLp,hun,hup,hdiv,hdiff,hsum,hkn]

/-- At equality the positive small rail records no flip, and the negative
small rail records a flip. Both produce the identical zero-valued rail. -/
theorem step_encode_odd (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) (huo : u%2≠0) :
    step (encode g s u v)=
      ⟨(u+v)/2,if s then (v-u)/2 else (u-v)/2,false,
        decide (if s then u≤v else u<v)⟩ := by
  have hup : 0<u := by omega
  have hLe : (u+v)%2=0 := by omega
  have hLp : ¬u+v<0 := by omega
  have hun : ¬u<0 := by omega
  have hdiff : u-(u+v)/2=(u-v)/2 := by omega
  have hsum : -u+(u+v)/2=(v-u)/2 := by omega
  have hsmall : ((u-v)/2<0) ↔ u<v := by omega
  have hflip : (!decide ((v-u)/2<0))=decide (u≤v) := by
    by_cases hle : u≤v
    · have hn : ¬(v-u)/2<0 := by omega
      simp [hle,hn]
    · have hn : (v-u)/2<0 := by omega
      simp [hle,hn]
  cases g <;> cases s <;>
    simp [step,encode,signed,route,odd,sameSign,neg,huo,hLe,
      hLp,hun,hup,hdiff,hsum,hsmall,hflip]

/-- The orientation/sign-flip transcript has only three possible letters. -/
theorem ternary_history (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) :
    ((step (encode g s u v)).g && (step (encode g s u v)).s)=false := by
  by_cases he : u%2=0
  · rw [step_encode_even g s u v hu hv hvo he]
    rfl
  · rw [step_encode_odd g s u v hu hv hvo he]
    rfl

theorem odd_flip_order (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) (huo : u%2≠0) :
    ((step (encode g s u v)).s=false → v≤u) ∧
    ((step (encode g s u v)).s=true → u≤v) := by
  rw [step_encode_odd g s u v hu hv hvo huo]
  cases s <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    constructor <;> intro h <;> simp_all; omega

/-- The orientation points to a strictly smaller magnitude, and the other
rail is positive. This includes a zero small rail after an equality step. -/
def Frame (t : Tick) : Prop :=
  if t.g then 0<t.k ∧ |t.h|<t.k else 0<t.h ∧ |t.k|<t.h

theorem step_frame (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) :
    Frame (step (encode g s u v)) := by
  by_cases he : u%2=0
  · rw [step_encode_even g s u v hu hv hvo he]
    simp only [Frame,if_true]
    constructor
    · omega
    · cases s <;> simp only [signed,Bool.false_eq_true,if_false,if_true]
      all_goals apply abs_lt.mpr; constructor <;> omega
  · rw [step_encode_odd g s u v hu hv hvo he]
    simp only [Frame,Bool.false_eq_true,if_false]
    constructor
    · omega
    · cases s <;> simp only [Bool.false_eq_true,if_false,if_true]
      all_goals apply abs_lt.mpr; constructor <;> omega

/-- Neither signed output magnitude grows beyond the input larger rail.
This provides a safe exact word bound independently of empirical envelopes. -/
theorem step_abs_bounds (g s : Bool) (u v : Int)
    (hu : 0≤u) (hv : 0<v) (hvo : v%2=1) :
    |(step (encode g s u v)).h|≤u+v ∧ |(step (encode g s u v)).k|≤u+v := by
  by_cases he : u%2=0
  · rw [step_encode_even g s u v hu hv hvo he]
    dsimp only
    constructor
    · cases s <;> simp only [signed,Bool.false_eq_true,if_false,if_true]
      all_goals apply abs_le.mpr; constructor <;> omega
    · apply abs_le.mpr; constructor <;> omega
  · rw [step_encode_odd g s u v hu hv hvo he]
    dsimp only
    constructor
    · apply abs_le.mpr; constructor <;> omega
    · cases s <;> simp only [Bool.false_eq_true,if_false,if_true]
      all_goals apply abs_le.mpr; constructor <;> omega

end ECDSAAdd.SkywalkRails
