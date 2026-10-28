import ECDSAAdd.Math.BitcoinPrimes
import ECDSAAdd.Math.SkywalkNat

namespace ECDSAAdd
open Secp256k1

/-- The butterfly payload corresponding to logical Stein rails (u,v).
The common scale κ is unchanged by every exact replay cell. -/
def skywalkPayloadFor (u v : Nat) (κ : Fp) : Fp × Fp :=
  ((2*(u : Fp)+(v : Fp))*κ,(v : Fp)*κ)

/-- Forward division replay: signed half-add, then the recorded swap.
The payload never participates in selecting g or s. -/
def skywalkPayloadCell (g s : Bool) (q : Fp × Fp) : Fp × Fp :=
  let t := (q.1+(if g then q.2 else -q.2))/2
  if s then (q.2,t) else (t,q.2)

/-- Multiplication replay: undo the recorded swap, then double and signed add. -/
def skywalkPayloadUncell (g s : Bool) (q : Fp × Fp) : Fp × Fp :=
  let t := if s then (q.2,q.1) else q
  (2*t.1+(if g then -t.2 else t.2),t.2)

private theorem skywalk_two_ne_zero : (2 : Fp)≠0 := by
  change (2 : ZMod p)≠0
  decide

/-- Exact inverse on every field pair and every Boolean record. -/
theorem skywalkPayloadUncell_cell (g s : Bool) (q : Fp × Fp) :
    skywalkPayloadUncell g s (skywalkPayloadCell g s q)=q := by
  cases g <;> cases s <;> apply Prod.ext <;>
    simp [skywalkPayloadCell,skywalkPayloadUncell] <;>
    field_simp [skywalk_two_ne_zero] <;> ring

/-- Exact inverse in the other direction, with no trajectory or nonzero-payload premise. -/
theorem skywalkPayloadCell_uncell (g s : Bool) (q : Fp × Fp) :
    skywalkPayloadCell g s (skywalkPayloadUncell g s q)=q := by
  cases g <;> cases s <;> apply Prod.ext <;>
    simp [skywalkPayloadCell,skywalkPayloadUncell] <;>
    field_simp [skywalk_two_ne_zero]

private theorem skywalk_cast_half (n : Nat) (he : n%2=0) :
    ((n/2 : Nat) : Fp)=(n : Fp)/2 := by
  apply (eq_div_iff skywalk_two_ne_zero).2
  norm_cast
  exact congrArg (fun k : Nat => (k : Fp))
    (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero he))

/-- The even-rail branch; zero is included, so terminal padding is exact. -/
theorem skywalkPayload_even (u v : Nat) (κ : Fp) (he : u%2=0) :
    skywalkPayloadCell true false (skywalkPayloadFor u v κ)=skywalkPayloadFor (u/2) v κ := by
  apply Prod.ext
  · change ((2*(u : Fp)+(v : Fp))*κ+(v : Fp)*κ)/2=
      (2*((u/2 : Nat) : Fp)+(v : Fp))*κ
    rw [skywalk_cast_half u he]
    field_simp [skywalk_two_ne_zero]
    ring
  · rfl

/-- Odd rails with u≤v: use the recorded swap, including the equality case. -/
theorem skywalkPayload_odd_le (u v : Nat) (κ : Fp)
    (hu : u%2=1) (hv : v%2=1) (hle : u≤v) :
    skywalkPayloadCell false true (skywalkPayloadFor u v κ)=skywalkPayloadFor ((v-u)/2) u κ := by
  have he : (v-u)%2=0 := by omega
  apply Prod.ext
  · change (v : Fp)*κ=(2*(((v-u)/2 : Nat) : Fp)+(u : Fp))*κ
    rw [skywalk_cast_half (v-u) he,Nat.cast_sub hle]
    field_simp [skywalk_two_ne_zero]
    ring
  · change ((2*(u : Fp)+(v : Fp))*κ+(-((v : Fp)*κ)))/2=(u : Fp)*κ
    field_simp [skywalk_two_ne_zero]
    ring

/-- Odd rails with v≤u: retain order, also including equality. -/
theorem skywalkPayload_odd_ge (u v : Nat) (κ : Fp)
    (hu : u%2=1) (hv : v%2=1) (hle : v≤u) :
    skywalkPayloadCell false false (skywalkPayloadFor u v κ)=skywalkPayloadFor ((u-v)/2) v κ := by
  have he : (u-v)%2=0 := by omega
  apply Prod.ext
  · change ((2*(u : Fp)+(v : Fp))*κ+(-((v : Fp)*κ)))/2=
      (2*(((u-v)/2 : Nat) : Fp)+(v : Fp))*κ
    rw [skywalk_cast_half (u-v) he,Nat.cast_sub hle]
    field_simp [skywalk_two_ne_zero]
    ring
  · rfl

/-- Equality accepts either sign record, and both logical updates are (0,u). -/
theorem skywalkPayload_equal (u : Nat) (κ : Fp) (s : Bool) (hu : u%2=1) :
    skywalkPayloadCell false s (skywalkPayloadFor u u κ)=skywalkPayloadFor 0 u κ := by
  cases s
  · simpa using skywalkPayload_odd_ge u u κ hu hu (Nat.le_refl u)
  · simpa using skywalkPayload_odd_le u u κ hu hu (Nat.le_refl u)

/-- secp256k1 initialization represents arbitrary Y, including Y=0. -/
theorem skywalkPayload_init (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadFor x p (Y/(x : Fp))=(2*Y,0) := by
  have hnx : (x : Fp)≠0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx] at hv
    simp only [ZMod.val_zero] at hv
    omega
  apply Prod.ext
  · change (2*(x : Fp)+(p : Fp))*(Y/(x : Fp))=2*Y
    rw [ZMod.natCast_self]
    field_simp [hnx]
    ring
  · change (p : Fp)*(Y/(x : Fp))=0
    rw [ZMod.natCast_self]
    simp

/-- At the exact coprime terminal rails, both payload registers contain κ. -/
theorem skywalkPayload_terminal (κ : Fp) : skywalkPayloadFor 0 1 κ=(κ,κ) := by
  simp [skywalkPayloadFor]

/-- Any correctly classified physical record preserves the logical invariant.
Only odd rails use sign/order constraints; equality may choose either record. -/
theorem skywalkPayload_step_record (z : SkywalkNat.State) (κ : Fp) (g s : Bool)
    (hv : z.v%2=1) (hg : g=decide (z.u%2=0))
    (hsEven : z.u%2=0 → s=false)
    (hsLe : z.u%2≠0 → s=true → z.u≤z.v)
    (hsGe : z.u%2≠0 → s=false → z.v≤z.u) :
    skywalkPayloadCell g s (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor (SkywalkNat.step z).u (SkywalkNat.step z).v κ := by
  by_cases he : z.u%2=0
  · have hgt : g=true := by simpa [he] using hg
    have hsf : s=false := hsEven he
    have hstep : SkywalkNat.step z=⟨z.u/2,z.v⟩ := by
      by_cases hz : z.u=0
      · apply SkywalkNat.State.ext <;> simp [SkywalkNat.step,hz]
      · simp [SkywalkNat.step,hz,he]
    rw [hgt,hsf,hstep]
    exact skywalkPayload_even z.u z.v κ he
  · have hgf : g=false := by simpa [he] using hg
    have hu : z.u%2=1 := by omega
    have hz : z.u≠0 := by omega
    rw [hgf]
    cases hs : s
    · have hle := hsGe he hs
      simpa [SkywalkNat.step,hz,he,hle] using skywalkPayload_odd_ge z.u z.v κ hu hv hle
    · have hle := hsLe he hs
      by_cases hge : z.v≤z.u
      · have heq : z.u=z.v := by omega
        have hv0 : z.v≠0 := by omega
        have heV : z.v%2≠0 := by omega
        simpa [SkywalkNat.step,heq,hv0,heV] using skywalkPayload_equal z.v κ true hv
      · simpa [SkywalkNat.step,hz,he,hge] using skywalkPayload_odd_le z.u z.v κ hu hv hle

/-- Canonical logical records; equality uses the unswapped form.
The equality lemma above also permits the physical sign convention's swapped form. -/
def skywalkPayloadCode (z : SkywalkNat.State) : Bool × Bool :=
  (decide (z.u%2=0),decide (z.u%2≠0 ∧ z.u<z.v))

/-- The invariant follows the exact logical Stein recurrence, including terminal padding. -/
theorem skywalkPayload_step (z : SkywalkNat.State) (κ : Fp) (hv : z.v%2=1) :
    skywalkPayloadCell (skywalkPayloadCode z).1 (skywalkPayloadCode z).2
      (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor (SkywalkNat.step z).u (SkywalkNat.step z).v κ := by
  by_cases hz : z.u=0
  · simpa [skywalkPayloadCode,SkywalkNat.step,hz] using skywalkPayload_even 0 z.v κ (by omega)
  by_cases he : z.u%2=0
  · simpa [skywalkPayloadCode,SkywalkNat.step,hz,he] using skywalkPayload_even z.u z.v κ he
  have hu : z.u%2=1 := by omega
  by_cases hle : z.v≤z.u
  · have hlt : ¬z.u<z.v := by omega
    simpa [skywalkPayloadCode,SkywalkNat.step,hz,he,hle,hlt] using
      skywalkPayload_odd_ge z.u z.v κ hu hv hle
  · have hlt : z.u<z.v := by omega
    simpa [skywalkPayloadCode,SkywalkNat.step,hz,he,hle,hlt] using
      skywalkPayload_odd_le z.u z.v κ hu hv (by omega)

/-- All records are replayed in time order; they are produced independently by the integer walk. -/
def skywalkPayloadReplay : List (Bool × Bool) → Fp × Fp → Fp × Fp
  | [], q => q
  | (g,s)::cs, q => skywalkPayloadReplay cs (skywalkPayloadCell g s q)

/-- Replay inversion is a separately specified forward formula, in reverse record order. -/
def skywalkPayloadReplayInverse : List (Bool × Bool) → Fp × Fp → Fp × Fp
  | [], q => q
  | (g,s)::cs, q => skywalkPayloadUncell g s (skywalkPayloadReplayInverse cs q)

theorem skywalkPayloadReplayInverse_replay (cs : List (Bool × Bool)) (q : Fp × Fp) :
    skywalkPayloadReplayInverse cs (skywalkPayloadReplay cs q)=q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨g,s⟩
    simp only [skywalkPayloadReplay,skywalkPayloadReplayInverse,ih,skywalkPayloadUncell_cell]

theorem skywalkPayloadReplay_replayInverse (cs : List (Bool × Bool)) (q : Fp × Fp) :
    skywalkPayloadReplay cs (skywalkPayloadReplayInverse cs q)=q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨g,s⟩
    simp only [skywalkPayloadReplay,skywalkPayloadReplayInverse,skywalkPayloadCell_uncell,ih]
/-- A complete exact logical record stream, padded to a user-chosen length. -/
def skywalkPayloadTrace : Nat → SkywalkNat.State → List (Bool × Bool)
  | 0, _ => []
  | n+1, z => skywalkPayloadCode z::skywalkPayloadTrace n (SkywalkNat.step z)

theorem skywalkPayloadReplay_trace (n : Nat) (z : SkywalkNat.State) (κ : Fp)
    (hv0 : 0<z.v) (hv : z.v%2=1) :
    skywalkPayloadReplay (skywalkPayloadTrace n z) (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor ((SkywalkNat.step^[n]) z).u ((SkywalkNat.step^[n]) z).v κ := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have hv' := SkywalkNat.step_v_odd_pos z hv0 hv
    simp only [skywalkPayloadTrace,skywalkPayloadReplay,skywalkPayload_step z κ hv,
      ih (SkywalkNat.step z) hv'.1 hv'.2,Function.iterate_succ_apply]

/-- Universal exact division with a conservative 512-round schedule and arbitrary Y. -/
theorem skywalkPayload_quotient (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadReplay (skywalkPayloadTrace 512 (SkywalkNat.init x p)) (2*Y,0)=
      (Y/(x : Fp),Y/(x : Fp)) := by
  have hp0 : 0<p := by norm_num [p]
  have hpodd : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have hc : x.Coprime p := by
    apply Nat.Coprime.symm
    apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have ht := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc
  have hr := skywalkPayloadReplay_trace 512 (SkywalkNat.init x p) (Y/(x : Fp)) hp0 hpodd
  change skywalkPayloadReplay _ (skywalkPayloadFor x p (Y/(x : Fp)))=_ at hr
  rw [skywalkPayload_init x Y hx0 hx] at hr
  have hu : ((SkywalkNat.step^[512]) (SkywalkNat.init x p)).u=0 := ht.1
  have hv : ((SkywalkNat.step^[512]) (SkywalkNat.init x p)).v=1 := ht.2
  rw [hu,hv,skywalkPayload_terminal] at hr
  exact hr

/-- Reverse replay gives exact multiplication from the duplicated terminal payload. -/
theorem skywalkPayload_product (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadReplayInverse (skywalkPayloadTrace 512 (SkywalkNat.init x p)) (Y,Y)=
      (2*(Y*(x : Fp)),0) := by
  have hnx : (x : Fp)≠0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx] at hv
    simp only [ZMod.val_zero] at hv
    omega
  have hq := skywalkPayload_quotient x (Y*(x : Fp)) hx0 hx
  rw [mul_div_cancel_right₀ Y hnx] at hq
  rw [←hq,skywalkPayloadReplayInverse_replay]


end ECDSAAdd
