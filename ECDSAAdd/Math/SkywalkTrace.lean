import ECDSAAdd.Math.SkywalkRailsBridge
import ECDSAAdd.Math.SkywalkPayload

namespace ECDSAAdd.SkywalkTrace
open SkywalkRails Secp256k1

def next (r : SkywalkRails.State) : SkywalkRails.State := railsOf (SkywalkRails.step r)

/-- The transcript records the actual signed tick, including its zero/tie sign. -/
def code (r : SkywalkRails.State) : Bool×Bool :=
  let t := SkywalkRails.step r
  (t.g,t.s)

def trace : Nat → SkywalkRails.State → List (Bool×Bool)
  | 0, _ => []
  | n+1, r => code r::trace n (next r)

theorem trace_length (n : Nat) (r : SkywalkRails.State) : (trace n r).length=n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp [trace,ih]

/-- Full physical signed representation is preserved at every iteration.
Orientation and the actual smaller sign are retained rather than projected away. -/
theorem iter_encoded (i : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    ∃ G S : Bool, (next^[i] (encode g s (z.u : Int) (z.v : Int)))=
      encode G S ((SkywalkNat.step^[i] z).u : Int) ((SkywalkNat.step^[i] z).v : Int) := by
  induction i with
  | zero => exact ⟨g,s,rfl⟩
  | succ i ih =>
    obtain ⟨G,S,henc⟩ := ih
    let zi := SkywalkNat.step^[i] z
    have hvalid := SkywalkNat.iter_valid i z hv hvo
    let t := SkywalkRails.step (encode G S (zi.u : Int) (zi.v : Int))
    refine ⟨t.g,smallerSign t,?_⟩
    rw [Function.iterate_succ_apply',henc]
    have hr := step_reencode G S zi hvalid.1 hvalid.2.1
    simpa only [next,zi,Function.iterate_succ_apply'] using hr

/-- All premises of the field trajectory are supplied by the actual integer
record. Weak order is intentional: either sign is valid at u=v. -/
theorem code_classified (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let c := code (encode g s (z.u : Int) (z.v : Int))
    c.1=decide (z.u%2=0) ∧
    (z.u%2=0 → c.2=false) ∧
    (z.u%2≠0 → c.2=true → z.u≤z.v) ∧
    (z.u%2≠0 → c.2=false → z.v≤z.u) := by
  dsimp only
  have hvi : (z.v : Int)%2=1 := by omega
  have hpar : ((z.u : Int)%2=0) ↔ z.u%2=0 := by omega
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [code,hpar] using step_orientation g s (z.u : Int) (z.v : Int) hvi
  · intro he
    change (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).s=false
    rw [step_encode_even g s _ _ (by omega) (by omega) hvi (by omega)]
  · intro he hs
    change (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).s=true at hs
    have horder := odd_flip_order g s (z.u : Int) (z.v : Int)
      (by omega) (by omega) hvi (by omega)
    have hle := horder.2 hs
    omega
  · intro he hs
    change (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).s=false at hs
    have horder := odd_flip_order g s (z.u : Int) (z.v : Int)
      (by omega) (by omega) hvi (by omega)
    have hle := horder.1 hs
    omega

theorem iter_code_classified (i : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let zi := SkywalkNat.step^[i] z
    let c := code (next^[i] (encode g s (z.u : Int) (z.v : Int)))
    c.1=decide (zi.u%2=0) ∧
    (zi.u%2=0 → c.2=false) ∧
    (zi.u%2≠0 → c.2=true → zi.u≤zi.v) ∧
    (zi.u%2≠0 → c.2=false → zi.v≤zi.u) := by
  dsimp only
  obtain ⟨G,S,henc⟩ := iter_encoded i g s z hv hvo
  rw [henc]
  have hvalid := SkywalkNat.iter_valid i z hv hvo
  exact code_classified G S _ hvalid.1 hvalid.2.1

theorem trace_ternary (n : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    ∀ c∈trace n (encode g s (z.u : Int) (z.v : Int)), (c.1 && c.2)=false := by
  induction n generalizing g s z with
  | zero => simp [trace]
  | succ n ih =>
    intro c hc
    simp only [trace,List.mem_cons] at hc
    rcases hc with rfl|hc
    · exact ternary_history g s _ _ (by omega) (by omega) (by omega)
    · let t := SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))
      have heq := step_reencode g s z hv hvo
      change next (encode g s (z.u : Int) (z.v : Int))=
        encode t.g (smallerSign t) ((SkywalkNat.step z).u : Int)
          ((SkywalkNat.step z).v : Int) at heq
      rw [heq] at hc
      have hvalid := SkywalkNat.step_v_odd_pos z hv hvo
      exact ih t.g (smallerSign t) (SkywalkNat.step z) hvalid.1 hvalid.2 c hc

/-- A single actual integer letter drives the exact butterfly field invariant.
The scale κ may be zero; payloads do not classify the integer record. -/
theorem payload_step (g s : Bool) (z : SkywalkNat.State) (κ : Fp)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    let c := code (encode g s (z.u : Int) (z.v : Int))
    skywalkPayloadCell c.1 c.2 (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor (SkywalkNat.step z).u (SkywalkNat.step z).v κ := by
  have hc := code_classified g s z hv hvo
  exact skywalkPayload_step_record z κ _ _ hvo hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-- Replay is coupled to the actual signed transcript, not a tie convention
chosen separately from the integer implementation. -/
theorem payload_trace (n : Nat) (g s : Bool) (z : SkywalkNat.State) (κ : Fp)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    skywalkPayloadReplay (trace n (encode g s (z.u : Int) (z.v : Int)))
      (skywalkPayloadFor z.u z.v κ)=
      skywalkPayloadFor (SkywalkNat.step^[n] z).u (SkywalkNat.step^[n] z).v κ := by
  induction n generalizing g s z with
  | zero => rfl
  | succ n ih =>
    let r := encode g s (z.u : Int) (z.v : Int)
    let t := SkywalkRails.step r
    have hcell := payload_step g s z κ hv hvo
    have heq := step_reencode g s z hv hvo
    change next r=encode t.g (smallerSign t) ((SkywalkNat.step z).u : Int)
      ((SkywalkNat.step z).v : Int) at heq
    change skywalkPayloadReplay (trace n (next r))
      (skywalkPayloadCell (code r).1 (code r).2 (skywalkPayloadFor z.u z.v κ))=_
    rw [hcell,heq]
    have hvalid := SkywalkNat.step_v_odd_pos z hv hvo
    simpa only [Function.iterate_succ_apply] using
      ih t.g (smallerSign t) (SkywalkNat.step z) hvalid.1 hvalid.2

/-- Universal secp256k1 quotient trajectory for all canonical nonzero x and
all Y, driven by the actual512 signed-rail records. -/
theorem quotient512 (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadReplay (trace 512 (encode false false (x : Int) (p : Int)))
      (2*Y,0)=(Y/(x : Fp),Y/(x : Fp)) := by
  have hp0 : 0<p := by norm_num [p]
  have hpodd : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have hc : x.Coprime p := by
    apply Nat.Coprime.symm
    apply Secp256k1.p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have ht := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc
  have hr := payload_trace 512 false false (SkywalkNat.init x p)
    (Y/(x : Fp)) hp0 hpodd
  change skywalkPayloadReplay _ (skywalkPayloadFor x p (Y/(x : Fp)))=_ at hr
  rw [skywalkPayload_init x Y hx0 hx] at hr
  have hu : ((SkywalkNat.step^[512]) (SkywalkNat.init x p)).u=0 := ht.1
  have hv : ((SkywalkNat.step^[512]) (SkywalkNat.init x p)).v=1 := ht.2
  rw [hu,hv,skywalkPayload_terminal] at hr
  exact hr

/-- The same actual transcript gives exact multiplication in reverse. -/
theorem product512 (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p) :
    skywalkPayloadReplayInverse (trace 512 (encode false false (x : Int) (p : Int)))
      (Y,Y)=(2*(Y*(x : Fp)),0) := by
  have hnx : (x : Fp)≠0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt hx] at hv
    simp only [ZMod.val_zero] at hv
    omega
  have hq := quotient512 x (Y*(x : Fp)) hx0 hx
  rw [mul_div_cancel_right₀ Y hnx] at hq
  rw [←hq,skywalkPayloadReplayInverse_replay]

end ECDSAAdd.SkywalkTrace
