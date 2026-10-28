import ECDSAAdd.Arithmetic.MixedTranscriptFieldCell
import ECDSAAdd.Arithmetic.SkywalkDialog

namespace ECDSAAdd.Arithmetic
open Secp256k1

/-- The complete exact divisor-one transcript, computed from the same pure
integer transition as the actual recorded transcript. These are build-time
Boolean gate parameters; there is no approximate or truncated transcript. -/
def mixedTranscriptUnitTrace : List (Bool×Bool) :=
  SkywalkTrace.trace 512 (SkywalkRails.encode false false (1 : Int) (p : Int))

abbrev MixedTranscriptLetter := (Wire×Wire)×(Bool×Bool)

def mixedTranscriptTape (w : Nat → Wire) : List MixedTranscriptLetter :=
  (skywalkSharedTape w).zip mixedTranscriptUnitTrace

def MixedTranscriptReplayLayout (w : Nat → Wire) (b effG effS : Wire)
    (ls : List MixedTranscriptLetter) : Prop :=
  ∀ l∈ls, MixedTranscriptFieldLayout w b l.1.1 l.1.2 effG effS

private theorem mixedTranscript_zip_record (rs : List (Wire×Wire))
    (cs : List (Bool×Bool)) (l : MixedTranscriptLetter) (hl : l∈rs.zip cs) :
    l.1∈rs := by
  induction rs generalizing cs with
  | nil => simp at hl
  | cons r rs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      simp only [List.zip_cons_cons,List.mem_cons] at hl
      rcases hl with rfl|hl
      · simp
      · exact List.mem_cons_of_mem r (ih cs hl)

theorem mixedTranscriptTape_layout (w : Nat → Wire) (b effG effS : Wire)
    (hl : ∀ r∈skywalkSharedTape w,
      MixedTranscriptFieldLayout w b r.1 r.2 effG effS) :
    MixedTranscriptReplayLayout w b effG effS (mixedTranscriptTape w) := by
  intro l hm
  exact hl l.1 (mixedTranscript_zip_record _ _ l hm)

def mixedTranscriptControls (base : BasisState) (b : Wire)
    (ls : List MixedTranscriptLetter) : List (Bool×Bool) :=
  ls.map fun l => (mixedTranscriptBit base b l.1.1 l.2.1,
    mixedTranscriptBit base b l.1.2 l.2.2)

def mixedTranscriptReplay (w : Nat → Wire) (b effG effS : Wire) :
    List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => mixedTranscriptFieldCell w b l.1.1 l.1.2 effG effS l.2.1 l.2.2 ++
      mixedTranscriptReplay w b effG effS ls

/-- Independently emitted inverse cells in reverse record order. -/
def mixedTranscriptInverseReplay (w : Nat → Wire) (b effG effS : Wire) :
    List MixedTranscriptLetter → Program
  | [] => []
  | l::ls => mixedTranscriptInverseReplay w b effG effS ls ++
      mixedTranscriptInverseFieldCell w b l.1.1 l.1.2 effG effS l.2.1 l.2.2

theorem mixedTranscriptReplay_spec (w : Nat → Wire) (b effG effS : Wire)
    (ls : List MixedTranscriptLetter) (hl : MixedTranscriptReplayLayout w b effG effS ls)
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (mixedTranscriptReplay w b effG effS ls)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).1.val
        (skywalkPayloadReplay (mixedTranscriptControls base b ls) (X,Y)).2.val) := by
  induction ls generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons l ls ih =>
    have hl0 := hl l (by simp)
    have hl' : MixedTranscriptReplayLayout w b effG effS ls :=
      fun q hq => hl q (by simp [hq])
    let Q := skywalkPayloadCell (mixedTranscriptBit base b l.1.1 l.2.1)
      (mixedTranscriptBit base b l.1.2 l.2.2) (X,Y)
    have h1 := mixedTranscriptFieldCell_frame w b l.1.1 l.1.2 effG effS
      l.2.1 l.2.2 hl0 base hg0 hs0 hk hu X Y
    have h2 := ih hl' Q.1 Q.2
    simpa only [mixedTranscriptReplay,mixedTranscriptControls,List.map_cons,
      skywalkPayloadReplay,Q] using h1.seq h2

theorem mixedTranscriptInverseReplay_spec (w : Nat → Wire) (b effG effS : Wire)
    (ls : List MixedTranscriptLetter) (hl : MixedTranscriptReplayLayout w b effG effS ls)
    (base : BasisState) (hg0 : base effG=false) (hs0 : base effS=false)
    (hk : regValue (skywalkSharedField w).work base=0)
    (hu : regValue (skywalkSharedUnused w) base=0) (X Y : Fp) :
    Triple (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base X.val Y.val)
      (mixedTranscriptInverseReplay w b effG effS ls)
      (PairFrame (skywalkSharedField w).z (skywalkSharedField w).a base
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).1.val
        (skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)).2.val) := by
  induction ls generalizing X Y with
  | nil => intro s m h; exact ⟨rfl,h⟩
  | cons l ls ih =>
    have hl0 := hl l (by simp)
    have hl' : MixedTranscriptReplayLayout w b effG effS ls :=
      fun q hq => hl q (by simp [hq])
    let Q := skywalkPayloadReplayInverse (mixedTranscriptControls base b ls) (X,Y)
    have h1 := ih hl' X Y
    have h2 := mixedTranscriptInverseFieldCell_frame w b l.1.1 l.1.2 effG effS
      l.2.1 l.2.2 hl0 base hg0 hs0 hk hu Q.1 Q.2
    simpa only [mixedTranscriptInverseReplay,mixedTranscriptControls,List.map_cons,
      skywalkPayloadReplayInverse,Q] using h1.seq h2

theorem mixedTranscriptReplay_counts (w : Nat → Wire) (b effG effS : Wire)
    (ls : List MixedTranscriptLetter) (hl : MixedTranscriptReplayLayout w b effG effS ls) :
    toffoliCount (mixedTranscriptReplay w b effG effS ls)=ls.length*1796 ∧
    measurementCount (mixedTranscriptReplay w b effG effS ls)=ls.length*1540 := by
  induction ls with
  | nil => simp [mixedTranscriptReplay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have hc := mixedTranscriptFieldCell_counts w b l.1.1 l.1.2 effG effS
      l.2.1 l.2.2 (hl l (by simp))
    have hi := ih (fun q hq => hl q (by simp [hq]))
    simp only [mixedTranscriptReplay,toffoliCount_append,measurementCount_append,
      hc.1,hc.2,hi.1,hi.2,List.length_cons,Nat.add_mul]
    omega

theorem mixedTranscriptInverseReplay_counts (w : Nat → Wire) (b effG effS : Wire)
    (ls : List MixedTranscriptLetter) (hl : MixedTranscriptReplayLayout w b effG effS ls) :
    toffoliCount (mixedTranscriptInverseReplay w b effG effS ls)=ls.length*1796 ∧
    measurementCount (mixedTranscriptInverseReplay w b effG effS ls)=ls.length*1540 := by
  induction ls with
  | nil => simp [mixedTranscriptInverseReplay,toffoliCount,measurementCount]
  | cons l ls ih =>
    have hc := mixedTranscriptInverseFieldCell_counts w b l.1.1 l.1.2 effG effS
      l.2.1 l.2.2 (hl l (by simp))
    have hi := ih (fun q hq => hl q (by simp [hq]))
    simp only [mixedTranscriptInverseReplay,toffoliCount_append,measurementCount_append,
      hc.1,hc.2,hi.1,hi.2,List.length_cons,Nat.add_mul]
    trivial

theorem mixedTranscriptUnitTrace_length : mixedTranscriptUnitTrace.length=512 :=
  SkywalkTrace.trace_length _ _

theorem mixedTranscriptTape_length (w : Nat → Wire) : (mixedTranscriptTape w).length=512 := by
  simp [mixedTranscriptTape,List.length_zip,skywalkShared_tape_length,
    mixedTranscriptUnitTrace_length]

theorem mixedTranscriptControls_zip (base : BasisState) (b : Wire)
    (rs : List (Wire×Wire)) (cs : List (Bool×Bool)) (hlen : rs.length=cs.length) :
    mixedTranscriptControls base b (rs.zip cs)=
      if base b then skywalkTapeControls base rs else cs := by
  induction rs generalizing cs with
  | nil =>
    cases cs with
    | nil => cases base b <;> rfl
    | cons c cs => simp at hlen
  | cons r rs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have ht : rs.length=cs.length := by simpa using hlen
      change (mixedTranscriptBit base b r.1 c.1,mixedTranscriptBit base b r.2 c.2)::
        mixedTranscriptControls base b (rs.zip cs)=_
      rw [ih cs ht]
      cases hb : base b <;> simp [mixedTranscriptBit,skywalkTapeControls,hb]

theorem mixedTranscriptTape_controls (w : Nat → Wire) (base : BasisState) (b : Wire) :
    mixedTranscriptControls base b (mixedTranscriptTape w)=
      if base b then skywalkTapeControls base (skywalkSharedTape w) else mixedTranscriptUnitTrace := by
  exact mixedTranscriptControls_zip base b _ _
    ((skywalkShared_tape_length w).trans mixedTranscriptUnitTrace_length.symm)

/-- Use the actual denominator when enabled and divisor one otherwise. -/
theorem mixedTranscriptTape_quotient (w : Nat → Wire) (base : BasisState) (b : Wire)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplay (mixedTranscriptControls base b (mixedTranscriptTape w)) (2*Y,0)=
      (if base b then Y/(x : Fp) else Y,if base b then Y/(x : Fp) else Y) := by
  rw [mixedTranscriptTape_controls]
  cases hb : base b
  · simpa [mixedTranscriptUnitTrace] using
      (SkywalkTrace.quotient512 1 Y (by omega) (by norm_num [p]))
  · simpa only [hb,if_true,hr] using SkywalkTrace.quotient512 x Y hx0 hx

theorem mixedTranscriptTape_product (w : Nat → Wire) (base : BasisState) (b : Wire)
    (x : Nat) (Y : Fp) (hx0 : 0<x) (hx : x<p)
    (hr : skywalkTapeControls base (skywalkSharedTape w)=
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (x : Int) (p : Int))) :
    skywalkPayloadReplayInverse (mixedTranscriptControls base b (mixedTranscriptTape w)) (Y,Y)=
      (2*(if base b then Y*(x : Fp) else Y),0) := by
  rw [mixedTranscriptTape_controls]
  cases hb : base b
  · simpa [mixedTranscriptUnitTrace] using
      (SkywalkTrace.product512 1 Y (by omega) (by norm_num [p]))
  · simpa only [hb,if_true,hr] using SkywalkTrace.product512 x Y hx0 hx

end ECDSAAdd.Arithmetic

#print axioms ECDSAAdd.Arithmetic.mixedTranscriptTape_layout
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptReplay_spec
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptInverseReplay_spec
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptReplay_counts
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptInverseReplay_counts
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptTape_controls
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptTape_quotient
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptTape_product

#print axioms ECDSAAdd.Arithmetic.mixedTranscriptUnitTrace
#print axioms ECDSAAdd.Arithmetic.MixedTranscriptLetter
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptTape
#print axioms ECDSAAdd.Arithmetic.MixedTranscriptReplayLayout
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptControls
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptReplay
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptInverseReplay
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptUnitTrace_length
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptTape_length
#print axioms ECDSAAdd.Arithmetic.mixedTranscriptControls_zip
