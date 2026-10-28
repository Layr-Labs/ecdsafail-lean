import ECDSAAdd.Math.Divsteps.Recovery

namespace ECDSAAdd.Arithmetic.Paper935

/-- Public payload widths; each signed row additionally has one sign wire. -/
structure RowWindow where
  f : Nat
  g : Nat
  fv : Nat
  gv : Nat
  deriving DecidableEq, Repr

def RowWindow.payload (w : RowWindow) : Nat := w.f+w.g+w.fv+w.gv

def initialWindow : RowWindow := ⟨256,256,1,1⟩

/-- Schedule.fg_pair/v_pair pad both rows to the previous pair maximum. -/
def RowWindow.pairPad (w : RowWindow) : RowWindow :=
  ⟨max w.f w.g,max w.f w.g,max w.fv w.gv,max w.fv w.gv⟩

/-- F4 gives each padded payload one additional high bit. F6 shifts reuse
this headroom rather than allocating a further bit. -/
def RowWindow.addPad (w : RowWindow) : RowWindow :=
  ⟨max w.f w.g+1,max w.f w.g+1,max w.fv w.gv+1,max w.fv w.gv+1⟩

def RowWindow.Le (u v : RowWindow) : Prop :=
  u.f≤v.f ∧ u.g≤v.g ∧ u.fv≤v.fv ∧ u.gv≤v.gv

theorem RowWindow.pairPad_covers (w : RowWindow) : w.Le w.pairPad :=
  ⟨Nat.le_max_left _ _,Nat.le_max_right _ _,Nat.le_max_left _ _,Nat.le_max_right _ _⟩

theorem RowWindow.addPad_covers (w : RowWindow) : w.pairPad.Le w.addPad := by
  simp [Le,pairPad,addPad]

def windowBefore (exits : List RowWindow) : Nat → Option RowWindow
  | 0 => some initialWindow
  | t+1 => exits[t]?

/-- Payload width W plus a dedicated sign represents [-2^W,2^W). -/
def PayloadFits (width : Nat) (x : Int) : Prop :=
  -((2^width:Nat):Int)≤x ∧ x<((2^width:Nat):Int)

theorem PayloadFits.mono {a b : Nat} {x : Int} (h : a≤b) (hx : PayloadFits a x) :
    PayloadFits b x := by
  have hp : ((2^a:Nat):Int)≤((2^b:Nat):Int) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) h
  unfold PayloadFits at *
  omega

/-- One payload headroom bit suffices for exact signed addition/subtraction
of two values that fit the shared pair width. -/
theorem PayloadFits.add {w : Nat} {x y : Int} (hx : PayloadFits w x) (hy : PayloadFits w y) :
    PayloadFits (w+1) (x+y) := by
  simp only [PayloadFits,Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at *
  omega

theorem PayloadFits.sub {w : Nat} {x y : Int} (hx : PayloadFits w x) (hy : PayloadFits w y) :
    PayloadFits (w+1) (x-y) := by
  simp only [PayloadFits,Nat.pow_succ,Nat.cast_mul,Nat.cast_ofNat] at *
  omega

def RowWindow.Fits (w : RowWindow) (s : ECDSAAdd.Divsteps.ZState) : Prop :=
  PayloadFits w.f s.f ∧ PayloadFits w.g s.g ∧
  PayloadFits w.fv s.fv ∧ PayloadFits w.gv s.gv

theorem RowWindow.Fits.mono {u v : RowWindow} {s : ECDSAAdd.Divsteps.ZState}
    (h : u.Le v) (hs : u.Fits s) : v.Fits s :=
  ⟨hs.1.mono h.1,hs.2.1.mono h.2.1,hs.2.2.1.mono h.2.2.1,hs.2.2.2.mono h.2.2.2⟩

theorem RowWindow.padded_fits (w : RowWindow) (s : ECDSAAdd.Divsteps.ZState) (h : w.Fits s) :
    w.pairPad.Fits s ∧ w.addPad.Fits s := by
  have hp := h.mono w.pairPad_covers
  exact ⟨hp,hp.mono w.addPad_covers⟩

/-- Exit-window failure is a trajectory event, not allocator exhaustion.
A trace argument must be tied to the actual implementation separately. -/
def ExitWindowFailure (exits : List RowWindow) (trace : Nat → ECDSAAdd.Divsteps.ZState) : Prop :=
  ∃ (t : Nat) (w : RowWindow), exits[t]?=some w ∧ ¬w.Fits (trace (t+1))

theorem no_exit_failure_iff (exits : List RowWindow) (trace : Nat → ECDSAAdd.Divsteps.ZState) :
    ¬ExitWindowFailure exits trace ↔
      ∀ (t : Nat) (w : RowWindow),exits[t]?=some w → w.Fits (trace (t+1)) := by
  simp [ExitWindowFailure]

theorem windowBefore_success (exits : List RowWindow) (t : Nat) (h : t≤exits.length) :
    ∃ w,windowBefore exits t=some w := by
  cases t with
  | zero => exact ⟨initialWindow,rfl⟩
  | succ t =>
    have ht : t<exits.length := by omega
    exact ⟨exits[t],by simp [windowBefore,ht]⟩

end ECDSAAdd.Arithmetic.Paper935
